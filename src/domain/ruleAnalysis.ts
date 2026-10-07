import type {
  MatchWitness,
  BusinessRule,
  RuleAnalysis,
  RuleCondition,
  RuleField,
  RuleOverlap,
  RuleProject,
  SampleInput,
} from '../models/ruleModel';

const MAX_CASES = 120_000;
const MAX_EXAMPLES = 4;
const ONE = 1n;
const ZERO = 0n;
const WORD_BITS = 32;
const WORD_MASK = 0xffffffffn;
const BYTE_COUNTS = Uint8Array.from({ length: 256 }, (_value, index) => {
  let count = 0;
  let current = index;
  while (current) {
    count += current & 1;
    current >>= 1;
  }
  return count;
});

export function analyzeRules(project: RuleProject): RuleAnalysis {
  const candidates = project.fields.map((field) => valuesForField(field, project));
  const { checkedCases, truncated, multipliers } = enumerateCaseBounds(candidates.map((values) => values.length));

  if (!checkedCases) {
    return emptyAnalysis(truncated);
  }

  const universe = (ONE << BigInt(checkedCases)) - ONE;
  const fieldIndexes = new Map<string, FieldIndex>();
  project.fields.forEach((field, index) => {
    fieldIndexes.set(field.id, {
      field,
      values: candidates[index],
      stride: multipliers[index],
    });
  });

  const context: MaskContext = { checkedCases, universe, fieldIndexes };
  const ruleMasks = project.rules.map((rule) => conditionMask(rule.conditions, context));
  const ordered = project.rules
    .map((rule, originalIndex) => ({ rule, originalIndex, mask: ruleMasks[originalIndex] }))
    .sort((a, b) => b.rule.priority - a.rule.priority || a.originalIndex - b.originalIndex);

  let covered = ZERO;
  for (const mask of ruleMasks) covered |= mask;

  const seen = new Set<string>();
  const visible = new Set<string>();
  ruleMasks.forEach((mask, index) => {
    if (mask !== ZERO) seen.add(project.rules[index].id);
  });

  let remaining = universe;
  for (const entry of ordered) {
    if ((remaining & entry.mask) !== ZERO) visible.add(entry.rule.id);
    remaining &= universe ^ entry.mask;
    if (remaining === ZERO) break;
  }

  const coveredCases = bitCount(covered);
  const uncoveredExamples: SampleInput[] = [];
  let uncoveredBits = universe ^ covered;
  while (uncoveredBits !== ZERO && uncoveredExamples.length < MAX_EXAMPLES) {
    const caseIndex = lowestSetBitIndex(uncoveredBits);
    uncoveredExamples.push(valuesAt(caseIndex, project.fields, candidates));
    uncoveredBits &= uncoveredBits - ONE;
  }

  const overlaps = findOverlaps(ordered, context, (caseIndex) => valuesAt(caseIndex, project.fields, candidates));
  const unreachableRuleIds = project.rules.filter((rule) => !seen.has(rule.id)).map((rule) => rule.id);
  const shadowedRuleIds = project.rules.filter((rule) => seen.has(rule.id) && !visible.has(rule.id)).map((rule) => rule.id);

  return {
    checkedCases,
    coveredCases,
    coveragePercent: checkedCases ? Math.round((coveredCases / checkedCases) * 100) : 0,
    overlaps,
    unreachableRuleIds,
    shadowedRuleIds,
    uncoveredExamples,
    truncated,
  };
}

interface CaseBounds {
  checkedCases: number;
  truncated: boolean;
  multipliers: number[];
}

function emptyAnalysis(truncated: boolean): RuleAnalysis {
  return {
    checkedCases: 0,
    coveredCases: 0,
    coveragePercent: 0,
    overlaps: [],
    unreachableRuleIds: [],
    shadowedRuleIds: [],
    uncoveredExamples: [],
    truncated,
  };
}

function enumerateCaseBounds(counts: number[]): CaseBounds {
  const multipliers = new Array<number>(counts.length).fill(0);
  let total = 1;
  let stride = 1;

  for (let index = counts.length - 1; index >= 0; index -= 1) {
    multipliers[index] = Math.min(stride, MAX_CASES);
    const count = counts[index];
    if (total <= MAX_CASES) total = Math.min(MAX_CASES + 1, total * count);
    stride = Math.min(MAX_CASES + 1, stride * count);
  }

  return {
    checkedCases: Math.min(total, MAX_CASES),
    truncated: total > MAX_CASES,
    multipliers,
  };
}

interface FieldIndex {
  field: RuleField;
  values: ScalarCandidate[];
  stride: number;
}

interface MaskContext {
  checkedCases: number;
  universe: bigint;
  fieldIndexes: Map<string, FieldIndex>;
}

interface OrderedRuleMask {
  rule: BusinessRule;
  originalIndex: number;
  mask: bigint;
}

function conditionMask(condition: RuleCondition, context: MaskContext): bigint {
  if (condition.kind === 'group') {
    if (condition.operator === 'or') {
      let mask = ZERO;
      for (const child of condition.conditions) mask |= conditionMask(child, context);
      return mask;
    }
    let mask = context.universe;
    for (const child of condition.conditions) mask &= conditionMask(child, context);
    return mask;
  }

  const index = context.fieldIndexes.get(condition.fieldId);
  if (!index) return ZERO;

  if (condition.operator === 'isTrue' || condition.operator === 'isFalse') {
    if (index.field.type !== 'boolean') return ZERO;
    return positionMask(index, condition.operator === 'isTrue' ? 1 : 0, context);
  }

  if (typeof condition.value === 'object') {
    if (index.field.type !== 'number') return ZERO;
    const values = index.values as number[];
    const start = lowerBound(values, condition.value.min);
    const end = upperBound(values, condition.value.max) - 1;
    return rangeMask(index, start, end, context);
  }

  if (typeof condition.value === 'number') {
    if (index.field.type !== 'number') return ZERO;
    const values = index.values as number[];
    const position = lowerBound(values, condition.value);

    switch (condition.operator) {
      case 'eq':
        return values[position] === condition.value ? rangeMask(index, position, position, context) : ZERO;
      case 'gt':
        return rangeMask(index, upperBound(values, condition.value), values.length - 1, context);
      case 'gte':
        return rangeMask(index, lowerBound(values, condition.value), values.length - 1, context);
      case 'lt':
        return rangeMask(index, 0, lowerBound(values, condition.value) - 1, context);
      case 'lte':
        return rangeMask(index, 0, upperBound(values, condition.value) - 1, context);
      default:
        return ZERO;
    }
  }

  if (index.field.type !== 'enum') return ZERO;
  const position = index.values.indexOf(condition.value);
  const equalMask = position < 0 ? ZERO : positionMask(index, position, context);
  return condition.operator === 'eq' ? equalMask : context.universe ^ equalMask;
}

function positionMask(index: FieldIndex, position: number, context: MaskContext): bigint {
  return rangeMask(index, position, position, context);
}

function rangeMask(index: FieldIndex, first: number, last: number, context: MaskContext): bigint {
  if (first < 0 || last < first || first >= index.values.length) return ZERO;
  const end = Math.min(last, index.values.length - 1);
  const stride = index.stride;
  const blockLength = (end - first + 1) * stride;
  const blockStart = first * stride;
  const block = ((ONE << BigInt(blockLength)) - ONE) << BigInt(blockStart);
  const period = index.values.length * stride;
  return repeatWithinUniverse(block, period, context);
}

function repeatWithinUniverse(block: bigint, period: number, context: MaskContext): bigint {
  let mask = block;
  let span = period;
  while (span < context.checkedCases) {
    const nextSpan = Math.min(span * 2, context.checkedCases);
    if (span < context.checkedCases) mask |= mask << BigInt(span);
    span = nextSpan;
  }
  return mask & context.universe;
}

function lowerBound(values: number[], target: number): number {
  let low = 0;
  let high = values.length;
  while (low < high) {
    const middle = low + Math.floor((high - low) / 2);
    if (values[middle] < target) low = middle + 1;
    else high = middle;
  }
  return low;
}

function upperBound(values: number[], target: number): number {
  let low = 0;
  let high = values.length;
  while (low < high) {
    const middle = low + Math.floor((high - low) / 2);
    if (values[middle] <= target) low = middle + 1;
    else high = middle;
  }
  return low;
}

function bitCount(value: bigint): number {
  let count = 0;
  const hex = value.toString(16);
  for (let index = 0; index < hex.length; index += 1) {
    const nibble = Number.parseInt(hex[index], 16);
    count += BYTE_COUNTS[nibble];
  }
  return count;
}

function lowestSetBitIndex(value: bigint): number {
  const lowest = value & -value;
  let index = 0;
  let current = lowest;
  while (current > WORD_MASK) {
    current >>= BigInt(WORD_BITS);
    index += WORD_BITS;
  }
  return index + current.toString(2).length - 1;
}

function valuesAt(caseIndex: number, fields: RuleField[], candidates: ScalarCandidate[][]): SampleInput {
  const positions = new Array<number>(fields.length);
  let remaining = caseIndex;
  for (let fieldIndex = fields.length - 1; fieldIndex >= 0; fieldIndex -= 1) {
    const count = candidates[fieldIndex].length;
    positions[fieldIndex] = remaining % count;
    remaining = Math.floor(remaining / count);
  }

  const values: SampleInput = {};
  fields.forEach((field, index) => {
    values[field.id] = candidates[index][positions[index]];
  });
  return values;
}

function findOverlaps(
  ordered: OrderedRuleMask[],
  context: MaskContext,
  witnessForCase: (caseIndex: number) => SampleInput,
): RuleOverlap[] {
  const active = ordered.filter((entry) => entry.mask !== ZERO);
  const overlaps = new Map<string, RuleOverlap>();
  if (active.length < 2) return [];

  const words = active.map((entry) => toUint32Words(entry.mask, context.checkedCases));
  const maximumPairs = (active.length * (active.length - 1)) / 2;
  const wordCount = Math.ceil(context.checkedCases / WORD_BITS);
  const pairKnown = Array.from({ length: active.length }, () => new Uint8Array(active.length));

  outer:
  for (let wordIndex = 0; wordIndex < wordCount; wordIndex += 1) {
    const casesInWord = Math.min(WORD_BITS, context.checkedCases - wordIndex * WORD_BITS);
    for (let bitIndex = 0; bitIndex < casesInWord; bitIndex += 1) {
      const bit = 1 << bitIndex;
      let first = -1;
      let second = -1;

      for (let ruleIndex = 0; ruleIndex < active.length; ruleIndex += 1) {
        if ((words[ruleIndex][wordIndex] & bit) !== 0) {
          if (first < 0) first = ruleIndex;
          else {
            second = ruleIndex;
            break;
          }
        }
      }
      if (second < 0) continue;

      const matched = [first, second];
      for (let ruleIndex = second + 1; ruleIndex < active.length; ruleIndex += 1) {
        if ((words[ruleIndex][wordIndex] & bit) !== 0) matched.push(ruleIndex);
      }

      const caseIndex = wordIndex * WORD_BITS + bitIndex;
      let witness: SampleInput | undefined;
      for (let left = 0; left < matched.length; left += 1) {
        for (let right = left + 1; right < matched.length; right += 1) {
          const leftIndex = matched[left];
          const rightIndex = matched[right];
          if (pairKnown[leftIndex][rightIndex]) continue;
          pairKnown[leftIndex][rightIndex] = 1;
          const ruleA = active[leftIndex].rule;
          const ruleB = active[rightIndex].rule;
          witness ??= witnessForCase(caseIndex);

          overlaps.set(`${leftIndex}|${rightIndex}`, {
            ruleAId: ruleA.id,
            ruleBId: ruleB.id,
            conflict: ruleA.priority === ruleB.priority && ruleA.result !== ruleB.result,
            witness: { ...witness },
          });
          if (overlaps.size === maximumPairs) break outer;
        }
      }
    }
  }

  return [...overlaps.values()];
}

function toUint32Words(mask: bigint, checkedCases: number): Uint32Array {
  const wordCount = Math.ceil(checkedCases / WORD_BITS);
  const words = new Uint32Array(wordCount);
  const hex = mask.toString(16).padStart(wordCount * 8, '0');

  for (let wordIndex = 0; wordIndex < wordCount; wordIndex += 1) {
    const start = (wordCount - 1 - wordIndex) * 8;
    words[wordIndex] = Number.parseInt(hex.slice(start, start + 8), 16);
  }
  return words;
}

type ScalarCandidate = string | number | boolean;

function valuesForField(field: RuleField, project: RuleProject): ScalarCandidate[] {
  if (field.type === 'boolean') return [false, true];
  if (field.type === 'enum') return field.enumValues ?? [];
  const min = field.min ?? 0;
  const max = field.max ?? min;
  const breaks = new Set<number>([min, max]);
  for (const rule of project.rules) collectBreaks(rule.conditions, field.id, min, max, breaks);
  const sorted = [...breaks].sort((a, b) => a - b);
  const values = new Set<number>(sorted);
  for (let index = 0; index < sorted.length - 1; index += 1) {
    values.add(sorted[index] + (sorted[index + 1] - sorted[index]) / 2);
  }
  return [...values].sort((a, b) => a - b);
}

function collectBreaks(
  condition: RuleCondition,
  fieldId: string,
  min: number,
  max: number,
  breaks: Set<number>,
): void {
  if (condition.kind === 'group') {
    condition.conditions.forEach((child) => collectBreaks(child, fieldId, min, max, breaks));
    return;
  }
  if (condition.fieldId !== fieldId) return;
  let boundaries: number[];
  if (typeof condition.value === 'number') boundaries = [condition.value];
  else if (typeof condition.value === 'object' && condition.value !== null && 'min' in condition.value && 'max' in condition.value) boundaries = [condition.value.min, condition.value.max];
  else return;
  for (const value of boundaries) if (value >= min && value <= max) breaks.add(value);
}

export const ruleAnalysisService = { analyze: analyzeRules };

export function firstOverlapWitness(analysis: RuleAnalysis): MatchWitness | undefined {
  const overlap = analysis.overlaps[0];
  return overlap ? { values: overlap.witness, ruleIds: [overlap.ruleAId, overlap.ruleBId] } : undefined;
}
