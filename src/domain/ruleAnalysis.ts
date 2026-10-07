import type {
  MatchWitness,
  RuleAnalysis,
  RuleCondition,
  RuleField,
  RuleOverlap,
  RuleProject,
  SampleInput,
  ScalarValue,
} from '../models/ruleModel';
import { MddBudgetExceeded, RuleDiagram } from './ruleDiagram';

const MAX_CASES = 120_000;
const MAX_EXAMPLES = 4;
const BITS_PER_BATCH = 64;

interface CompiledGroup {
  kind: 'group';
  operator: 'and' | 'or';
  conditions: CompiledCondition[];
}

interface CompiledPredicate {
  kind: 'predicate';
  fieldIndex: number;
  first: number;
  last: number;
  complement: boolean;
  matches: boolean;
}

type CompiledCondition = CompiledGroup | CompiledPredicate;

interface CompiledRule {
  rule: RuleProject['rules'][number];
  originalIndex: number;
  root: CompiledGroup;
}

interface BatchContext {
  start: number;
  width: number;
  allMask: bigint;
  counts: number[];
  strides: number[];
}

const neverMatches = (): CompiledPredicate => ({
  kind: 'predicate',
  fieldIndex: -1,
  first: 0,
  last: 0,
  complement: false,
  matches: false,
});

export function analyzeRules(project: RuleProject): RuleAnalysis {
  const candidates = buildFieldCandidates(project);
  const counts = candidates.map((values) => values.length);
  if (counts.some((count) => count === 0)) {
    return emptyAnalysis(0, false);
  }

  const totalCases = countCases(counts);
  if (totalCases <= MAX_CASES) {
    try {
      return analyzeWithDiagram(project, candidates, counts, totalCases);
    } catch (error) {
      if (!(error instanceof MddBudgetExceeded)) throw error;
    }
  }
  return analyzeByBatches(project, candidates, counts, totalCases);
}

function analyzeWithDiagram(
  project: RuleProject,
  candidates: ScalarValue[][],
  counts: number[],
  totalCases: number,
): RuleAnalysis {
  const diagram = new RuleDiagram(counts);
  const ordered = project.rules
    .map((rule, originalIndex) => ({
      rule,
      originalIndex,
      root: compileCondition(rule.conditions, project.fields, candidates) as CompiledGroup,
      diagram: 0,
    }))
    .sort((a, b) => b.rule.priority - a.rule.priority || a.originalIndex - b.originalIndex);

  for (const compiled of ordered) {
    compiled.diagram = conditionToDiagram(compiled.root, diagram);
  }

  const seen = new Set<string>();
  const visible = new Set<string>();
  let remaining = diagram.one;

  for (const compiled of ordered) {
    if (compiled.diagram === diagram.zero) continue;
    seen.add(compiled.rule.id);
    const winning = diagram.and(compiled.diagram, remaining);
    if (winning !== diagram.zero) visible.add(compiled.rule.id);
    remaining = diagram.and(remaining, diagram.not(compiled.diagram));
  }

  const coveredCases = totalCases - diagram.modelCount(remaining);
  const uncoveredExamples = diagram.firstWitnesses(remaining, MAX_EXAMPLES)
    .map((digits) => valuesForDigits(digits, candidates, project));

  const overlapRecords: Array<{ index: number; overlap: RuleOverlap; orderLeft: number; orderRight: number }> = [];
  for (let left = 0; left < ordered.length; left += 1) {
    for (let right = left + 1; right < ordered.length; right += 1) {
      const shared = diagram.and(ordered[left].diagram, ordered[right].diagram);
      if (shared === diagram.zero) continue;
      const digits = diagram.firstWitness(shared);
      if (!digits) continue;
      const ruleA = ordered[left].rule;
      const ruleB = ordered[right].rule;
      overlapRecords.push({
        index: digitsToIndex(digits, counts),
        orderLeft: left,
        orderRight: right,
        overlap: {
          ruleAId: ruleA.id,
          ruleBId: ruleB.id,
          conflict: ruleA.priority === ruleB.priority && ruleA.result !== ruleB.result,
          witness: valuesForDigits(digits, candidates, project),
        },
      });
    }
  }
  overlapRecords.sort((a, b) => a.index - b.index || a.orderLeft - b.orderLeft || a.orderRight - b.orderRight);

  const unreachableRuleIds = project.rules.filter((rule) => !seen.has(rule.id)).map((rule) => rule.id);
  const shadowedRuleIds = project.rules.filter((rule) => seen.has(rule.id) && !visible.has(rule.id)).map((rule) => rule.id);

  return {
    checkedCases: totalCases,
    coveredCases,
    coveragePercent: totalCases ? Math.round((coveredCases / totalCases) * 100) : 0,
    overlaps: overlapRecords.map((record) => record.overlap),
    unreachableRuleIds,
    shadowedRuleIds,
    uncoveredExamples,
    truncated: false,
  };
}

function analyzeByBatches(
  project: RuleProject,
  candidates: ScalarValue[][],
  counts: number[],
  totalCases: number,
): RuleAnalysis {
  const checkedCases = Math.min(totalCases, MAX_CASES);
  const ordered: CompiledRule[] = project.rules
    .map((rule, originalIndex) => ({
      rule,
      originalIndex,
      root: compileCondition(rule.conditions, project.fields, candidates) as CompiledGroup,
    }))
    .sort((a, b) => b.rule.priority - a.rule.priority || a.originalIndex - b.originalIndex);

  const overlaps = new Map<string, RuleOverlap>();
  const seen = new Set<string>();
  const visible = new Set<string>();
  const processedMatchSets = new Set<bigint>();
  const uncoveredExamples: SampleInput[] = [];
  const strides = buildStrides(counts);
  const maxPairCount = ordered.length > 1 ? ordered.length * (ordered.length - 1) / 2 : 0;
  let coveredCases = 0;

  for (let start = 0; start < checkedCases; start += BITS_PER_BATCH) {
    const width = Math.min(BITS_PER_BATCH, checkedCases - start);
    const context: BatchContext = {
      start,
      width,
      allMask: (1n << BigInt(width)) - 1n,
      counts,
      strides,
    };
    const masks = ordered.map((compiled) => evaluateCondition(compiled.root, context));
    let unmatched = context.allMask;
    let multipleMatches = 0n;

    for (let ruleIndex = 0; ruleIndex < ordered.length; ruleIndex += 1) {
      const mask = masks[ruleIndex];
      if (!mask) continue;
      seen.add(ordered[ruleIndex].rule.id);

      const winningMask = mask & unmatched;
      if (winningMask) visible.add(ordered[ruleIndex].rule.id);

      const alreadyMatched = context.allMask ^ unmatched;
      multipleMatches |= alreadyMatched & mask;
      unmatched &= ~mask;
    }

    const matchedMask = context.allMask ^ unmatched;
    coveredCases += countBits(matchedMask);
    collectUncoveredExamples(unmatched, context, candidates, project, uncoveredExamples);

    if (multipleMatches && overlaps.size < maxPairCount) {
      collectOverlaps({
        multipleMatches,
        masks,
        ordered,
        context,
        candidates,
        project,
        overlaps,
        processedMatchSets,
      });
    }
  }

  const unreachableRuleIds = project.rules.filter((rule) => !seen.has(rule.id)).map((rule) => rule.id);
  const shadowedRuleIds = project.rules.filter((rule) => seen.has(rule.id) && !visible.has(rule.id)).map((rule) => rule.id);

  return {
    checkedCases,
    coveredCases,
    coveragePercent: checkedCases ? Math.round((coveredCases / checkedCases) * 100) : 0,
    overlaps: [...overlaps.values()],
    unreachableRuleIds,
    shadowedRuleIds,
    uncoveredExamples,
    truncated: totalCases > MAX_CASES,
  };
}

function buildFieldCandidates(project: RuleProject): ScalarValue[][] {
  const fieldsById = new Map(project.fields.map((field) => [field.id, field]));
  const numericBreaks = new Map<string, Set<number>>();

  for (const field of project.fields) {
    if (field.type === 'number') {
      const min = field.min ?? 0;
      const max = field.max ?? min;
      numericBreaks.set(field.id, new Set<number>([min, max]));
    }
  }

  const collectBreaks = (condition: RuleCondition): void => {
    if (condition.kind === 'group') {
      condition.conditions.forEach(collectBreaks);
      return;
    }
    const field = fieldsById.get(condition.fieldId);
    const breaks = field?.type === 'number' ? numericBreaks.get(condition.fieldId) : undefined;
    if (!field || !breaks) return;

    let boundaries: number[];
    if (typeof condition.value === 'number') boundaries = [condition.value];
    else if (typeof condition.value === 'object' && condition.value !== null && 'min' in condition.value && 'max' in condition.value) {
      boundaries = [condition.value.min, condition.value.max];
    } else return;

    const min = field.min ?? 0;
    const max = field.max ?? min;
    for (const boundary of boundaries) {
      if (boundary >= min && boundary <= max) breaks.add(boundary);
    }
  };

  for (const rule of project.rules) collectBreaks(rule.conditions);

  return project.fields.map((field) => {
    if (field.type === 'boolean') return [false, true];
    if (field.type === 'enum') return [...(field.enumValues ?? [])];
    const min = field.min ?? 0;
    const max = field.max ?? min;
    const sortedBreaks = [...(numericBreaks.get(field.id) ?? new Set<number>([min, max]))].sort((a, b) => a - b);
    const values = new Set<number>(sortedBreaks);
    for (let index = 0; index < sortedBreaks.length - 1; index += 1) {
      values.add(sortedBreaks[index] + (sortedBreaks[index + 1] - sortedBreaks[index]) / 2);
    }
    return [...values].sort((a, b) => a - b);
  });
}

function compileCondition(
  condition: RuleCondition,
  fields: RuleField[],
  candidates: ScalarValue[][],
): CompiledCondition {
  if (condition.kind === 'group') {
    return {
      kind: 'group',
      operator: condition.operator,
      conditions: condition.conditions.map((child) => compileCondition(child, fields, candidates)),
    };
  }

  const fieldIndex = fields.findIndex((field) => field.id === condition.fieldId);
  if (fieldIndex < 0) return neverMatches();
  const field = fields[fieldIndex];
  const values = candidates[fieldIndex];

  if (field.type === 'boolean') {
    if (condition.operator === 'isTrue') return exactPredicate(fieldIndex, 1);
    if (condition.operator === 'isFalse') return exactPredicate(fieldIndex, 0);
    return neverMatches();
  }

  if (field.type === 'enum') {
    if (typeof condition.value !== 'string') return neverMatches();
    const valueIndex = values.indexOf(condition.value);
    if (valueIndex < 0) return neverMatches();
    if (condition.operator === 'eq') return exactPredicate(fieldIndex, valueIndex);
    if (condition.operator === 'notEq') {
      return { kind: 'predicate', fieldIndex, first: valueIndex, last: valueIndex, complement: true, matches: true };
    }
    return neverMatches();
  }

  if (condition.operator === 'between') {
    const range = condition.value;
    if (typeof range !== 'object' || range === null || !Number.isFinite(range.min) || !Number.isFinite(range.max)) {
      return neverMatches();
    }
    const numericValues = values as number[];
    const first = lowerBound(numericValues, range.min);
    const last = upperBound(numericValues, range.max) - 1;
    return numericPredicate(fieldIndex, first, last);
  }

  if (typeof condition.value !== 'number' || !Number.isFinite(condition.value)) return neverMatches();
  const numericValues = values as number[];
  const threshold = condition.value;

  switch (condition.operator) {
    case 'eq': {
      const index = lowerBound(numericValues, threshold);
      return numericValues[index] === threshold ? exactPredicate(fieldIndex, index) : neverMatches();
    }
    case 'gt':
      return numericPredicate(fieldIndex, upperBound(numericValues, threshold), values.length - 1);
    case 'gte':
      return numericPredicate(fieldIndex, lowerBound(numericValues, threshold), values.length - 1);
    case 'lt':
      return numericPredicate(fieldIndex, 0, lowerBound(numericValues, threshold) - 1);
    case 'lte':
      return numericPredicate(fieldIndex, 0, upperBound(numericValues, threshold) - 1);
    default:
      return neverMatches();
  }
}

function conditionToDiagram(
  condition: CompiledCondition,
  diagram: RuleDiagram,
): number {
  if (condition.kind === 'group') {
    let result = condition.operator === 'and' ? diagram.one : diagram.zero;
    for (const child of condition.conditions) {
      const childDiagram = conditionToDiagram(child, diagram);
      result = condition.operator === 'and'
        ? diagram.and(result, childDiagram)
        : diagram.or(result, childDiagram);
      if ((condition.operator === 'and' && result === diagram.zero)
        || (condition.operator === 'or' && result === diagram.one)) {
        return result;
      }
    }
    return result;
  }
  return predicateToDiagram(condition, diagram);
}

function predicateToDiagram(
  predicate: CompiledPredicate,
  diagram: RuleDiagram,
): number {
  if (!predicate.matches) return diagram.zero;
  if (predicate.fieldIndex < 0) return diagram.one;
  const interval = diagram.interval(predicate.fieldIndex, predicate.first, predicate.last);
  return predicate.complement
    ? diagram.not(interval)
    : interval;
}

function exactPredicate(fieldIndex: number, index: number): CompiledPredicate {
  return { kind: 'predicate', fieldIndex, first: index, last: index, complement: false, matches: true };
}

function numericPredicate(fieldIndex: number, first: number, last: number): CompiledPredicate {
  if (first > last) return neverMatches();
  return { kind: 'predicate', fieldIndex, first, last, complement: false, matches: true };
}

function evaluateCondition(condition: CompiledCondition, context: BatchContext): bigint {
  if (condition.kind === 'predicate') return evaluatePredicate(condition, context);

  if (condition.operator === 'and') {
    let mask = context.allMask;
    for (const child of condition.conditions) {
      mask &= evaluateCondition(child, context);
      if (!mask) break;
    }
    return mask;
  }

  let mask = 0n;
  for (const child of condition.conditions) {
    mask |= evaluateCondition(child, context);
    if (mask === context.allMask) break;
  }
  return mask;
}

function evaluatePredicate(predicate: CompiledPredicate, context: BatchContext): bigint {
  if (!predicate.matches) return 0n;
  if (predicate.fieldIndex < 0) return context.allMask;
  const mask = intervalMask({
    start: context.start,
    width: context.width,
    allMask: context.allMask,
    stride: context.strides[predicate.fieldIndex],
    count: context.counts[predicate.fieldIndex],
    first: predicate.first,
    last: predicate.last,
  });
  return predicate.complement ? context.allMask ^ mask : mask;
}

interface IntervalMaskOptions {
  start: number;
  width: number;
  allMask: bigint;
  stride: number;
  count: number;
  first: number;
  last: number;
}

function intervalMask(options: IntervalMaskOptions): bigint {
  const { start, width, allMask, stride, count, first, last } = options;
  if (!count || first > last) return 0n;
  if (first === 0 && last === count - 1) return allMask;

  if (stride >= width) {
    const valueIndex = Math.floor(start / stride) % count;
    return valueIndex >= first && valueIndex <= last ? allMask : 0n;
  }

  const period = stride * count;
  const intervalLength = stride * (last - first + 1);
  const periodBlock = ((1n << BigInt(intervalLength)) - 1n) << BigInt(stride * first);

  if (period >= width) {
    let mask = 0n;
    const firstCycle = Math.floor(start / period);
    for (let cycle = firstCycle; cycle <= firstCycle + 1; cycle += 1) {
      const blockStart = cycle * period + stride * first;
      const localStart = Math.max(0, blockStart - start);
      const blockEnd = blockStart + intervalLength;
      const localEnd = Math.min(width, blockEnd - start);
      if (localEnd > localStart) {
        mask |= ((1n << BigInt(localEnd - localStart)) - 1n) << BigInt(localStart);
      }
    }
    return mask;
  }

  const phase = start % period;
  const repeatCount = Math.ceil((phase + width) / period);
  const repeatedLength = repeatCount * period;
  const repeater = period === 1
    ? (1n << BigInt(repeatedLength)) - 1n
    : ((1n << BigInt(repeatedLength)) - 1n) / ((1n << BigInt(period)) - 1n);
  return (periodBlock * repeater >> BigInt(phase)) & allMask;
}

function collectOverlaps(options: {
  multipleMatches: bigint;
  masks: bigint[];
  ordered: CompiledRule[];
  context: BatchContext;
  candidates: ScalarValue[][];
  project: RuleProject;
  overlaps: Map<string, RuleOverlap>;
  processedMatchSets: Set<bigint>;
}): void {
  const { multipleMatches, masks, ordered, context, candidates, project, overlaps, processedMatchSets } = options;
  const signatures = new Array<bigint>(context.width).fill(0n);

  for (let ruleIndex = 0; ruleIndex < ordered.length; ruleIndex += 1) {
    let bits = masks[ruleIndex] & multipleMatches;
    const ruleBit = 1n << BigInt(ruleIndex);
    while (bits) {
      const localIndex = bitIndex(bits & -bits);
      signatures[localIndex] |= ruleBit;
      bits &= bits - 1n;
    }
  }

  let bits = multipleMatches;
  while (bits) {
    const localIndex = bitIndex(bits & -bits);
    bits &= bits - 1n;
    const signature = signatures[localIndex];
    if (processedMatchSets.has(signature)) continue;
    processedMatchSets.add(signature);

    for (let left = 0; left < ordered.length; left += 1) {
      if (!(signature & (1n << BigInt(left)))) continue;
      for (let right = left + 1; right < ordered.length; right += 1) {
        if (!(signature & (1n << BigInt(right)))) continue;
        const ruleA = ordered[left].rule;
        const ruleB = ordered[right].rule;
        const key = [ruleA.id, ruleB.id].sort().join('|');
        if (overlaps.has(key)) continue;
        overlaps.set(key, {
          ruleAId: ruleA.id,
          ruleBId: ruleB.id,
          conflict: ruleA.priority === ruleB.priority && ruleA.result !== ruleB.result,
          witness: valuesAt(context.start + localIndex, candidates, project),
        });
      }
    }
  }
}

function collectUncoveredExamples(
  uncoveredMask: bigint,
  context: BatchContext,
  candidates: ScalarValue[][],
  project: RuleProject,
  examples: SampleInput[],
): void {
  let bits = uncoveredMask;
  while (bits && examples.length < MAX_EXAMPLES) {
    const localIndex = bitIndex(bits & -bits);
    examples.push(valuesAt(context.start + localIndex, candidates, project));
    bits &= bits - 1n;
  }
}

function valuesAt(index: number, candidates: ScalarValue[][], project: RuleProject): SampleInput {
  const digits = new Array<number>(candidates.length);
  let remaining = index;
  for (let fieldIndex = candidates.length - 1; fieldIndex >= 0; fieldIndex -= 1) {
    digits[fieldIndex] = remaining % candidates[fieldIndex].length;
    remaining = Math.floor(remaining / candidates[fieldIndex].length);
  }
  return valuesForDigits(digits, candidates, project);
}

function valuesForDigits(digits: number[], candidates: ScalarValue[][], project: RuleProject): SampleInput {
  const values: SampleInput = {};
  for (let fieldIndex = 0; fieldIndex < candidates.length; fieldIndex += 1) {
    values[project.fields[fieldIndex].id] = candidates[fieldIndex][digits[fieldIndex]];
  }
  return values;
}

function digitsToIndex(digits: number[], counts: number[]): number {
  let index = 0;
  for (let fieldIndex = 0; fieldIndex < digits.length; fieldIndex += 1) {
    index = index * counts[fieldIndex] + digits[fieldIndex];
  }
  return index;
}

function buildStrides(counts: number[]): number[] {
  const cappedMax = MAX_CASES + 1;
  const strides = new Array<number>(counts.length).fill(1);
  for (let index = counts.length - 2; index >= 0; index -= 1) {
    const nextStride = strides[index + 1];
    if (nextStride === cappedMax) strides[index] = cappedMax;
    else strides[index] = Math.min(cappedMax, nextStride * counts[index + 1]);
  }
  return strides;
}

function countCases(counts: number[]): number {
  let total = 1;
  for (const count of counts) {
    if (total > MAX_CASES / count) return MAX_CASES + 1;
    total *= count;
  }
  return total;
}

function countBits(mask: bigint): number {
  let count = 0;
  let remaining = mask;
  while (remaining) {
    count += 1;
    remaining &= remaining - 1n;
  }
  return count;
}

function bitIndex(bit: bigint): number {
  return bit.toString(2).length - 1;
}

function lowerBound(values: number[], target: number): number {
  let low = 0;
  let high = values.length;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (values[middle] < target) low = middle + 1;
    else high = middle;
  }
  return low;
}

function upperBound(values: number[], target: number): number {
  let low = 0;
  let high = values.length;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (values[middle] <= target) low = middle + 1;
    else high = middle;
  }
  return low;
}

function emptyAnalysis(checkedCases: number, truncated: boolean): RuleAnalysis {
  return {
    checkedCases,
    coveredCases: 0,
    coveragePercent: 0,
    overlaps: [],
    unreachableRuleIds: [],
    shadowedRuleIds: [],
    uncoveredExamples: [],
    truncated,
  };
}

export const ruleAnalysisService = { analyze: analyzeRules };

export function firstOverlapWitness(analysis: RuleAnalysis): MatchWitness | undefined {
  const overlap = analysis.overlaps[0];
  return overlap ? { values: overlap.witness, ruleIds: [overlap.ruleAId, overlap.ruleBId] } : undefined;
}
