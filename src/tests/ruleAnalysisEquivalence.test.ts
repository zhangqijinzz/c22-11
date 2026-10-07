import { describe, expect, it } from 'vitest';
import { matchesRule } from '../domain/conditionEvaluator';
import { analyzeRules } from '../domain/ruleAnalysis';
import type {
  BusinessRule,
  ConditionGroup,
  RuleAnalysis,
  RuleCondition,
  RuleField,
  RuleOverlap,
  RuleProject,
  SampleInput,
} from '../models/ruleModel';

const MAX_CASES = 120_000;
const MAX_EXAMPLES = 4;

function analyzeRulesByEnumeration(project: RuleProject): RuleAnalysis {
  const candidates = project.fields.map((field) => valuesForField(field, project));
  const overlaps = new Map<string, RuleOverlap>();
  const seen = new Set<string>();
  const visible = new Set<string>();
  const processedMatchSets = new Set<string>();
  const uncoveredExamples: SampleInput[] = [];
  const ordered = [...project.rules].sort((a, b) => b.priority - a.priority || project.rules.indexOf(a) - project.rules.indexOf(b));
  let checkedCases = 0;
  let coveredCases = 0;
  let truncated = false;

  const visit = (fieldIndex: number, values: SampleInput): void => {
    if (checkedCases >= MAX_CASES) {
      truncated = true;
      return;
    }
    if (fieldIndex < project.fields.length) {
      const field = project.fields[fieldIndex];
      for (const value of candidates[fieldIndex]) {
        values[field.id] = value;
        visit(fieldIndex + 1, values);
        if (truncated) break;
      }
      delete values[field.id];
      return;
    }
    checkedCases += 1;
    const matched = ordered.filter((rule) => matchesRule(rule, values));
    for (const rule of matched) seen.add(rule.id);
    if (matched.length) coveredCases += 1;
    else if (uncoveredExamples.length < MAX_EXAMPLES) uncoveredExamples.push({ ...values });
    if (matched[0]) visible.add(matched[0].id);
    const matchSetKey = matched.length > 1 ? matched.map((rule) => rule.id).sort().join('|') : '';
    if (matched.length > 1 && !processedMatchSets.has(matchSetKey)) {
      processedMatchSets.add(matchSetKey);
      for (let left = 0; left < matched.length; left += 1) {
        for (let right = left + 1; right < matched.length; right += 1) {
          const ruleA = matched[left];
          const ruleB = matched[right];
          const key = [ruleA.id, ruleB.id].sort().join('|');
          if (!overlaps.has(key)) {
            overlaps.set(key, {
              ruleAId: ruleA.id,
              ruleBId: ruleB.id,
              conflict: ruleA.priority === ruleB.priority && ruleA.result !== ruleB.result,
              witness: { ...values },
            });
          }
        }
      }
    }
  };

  visit(0, {});
  return {
    checkedCases,
    coveredCases,
    coveragePercent: checkedCases ? Math.round((coveredCases / checkedCases) * 100) : 0,
    overlaps: [...overlaps.values()],
    unreachableRuleIds: project.rules.filter((rule) => !seen.has(rule.id)).map((rule) => rule.id),
    shadowedRuleIds: project.rules.filter((rule) => seen.has(rule.id) && !visible.has(rule.id)).map((rule) => rule.id),
    uncoveredExamples,
    truncated,
  };
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

function mulberry32(seed: number): () => number {
  let state = seed;
  return () => {
    state += 0x6d2b79f5;
    let value = state;
    value = Math.imul(value ^ (value >>> 15), value | 1);
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
}

function pick<T>(values: T[], random: () => number): T {
  return values[Math.floor(random() * values.length)];
}

function makeProject(seed: number, enumSize = 5, enumFieldCount = 1): RuleProject {
  const random = mulberry32(seed);
  const enumFields: RuleField[] = Array.from({ length: enumFieldCount }, (_value, index) => ({
    id: `level${index}`,
    name: `等级${index}`,
    type: 'enum',
    enumValues: Array.from({ length: enumSize }, (_value, valueIndex) => `L${index}-${valueIndex}`),
  }));
  const fields: RuleField[] = [
    { id: 'score', name: '分数', type: 'number', min: 0, max: 4 },
    ...enumFields,
    { id: 'enabled', name: '启用', type: 'boolean' },
  ];

  const makeCondition = (depth: number): RuleCondition => {
    if (depth < 2 && random() < 0.35) {
      const operator = random() < 0.5 ? 'and' : 'or';
      return {
        kind: 'group',
        operator,
        conditions: [makeCondition(depth + 1), makeCondition(depth + 1), ...(random() < 0.3 ? [makeCondition(depth + 1)] : [])],
      };
    }

    const field = pick(fields, random);
    if (field.type === 'number') {
      const operator = pick(['eq', 'gt', 'gte', 'lt', 'lte', 'between'] as const, random);
      return operator === 'between'
        ? { kind: 'predicate', fieldId: field.id, operator, value: { min: Math.floor(random() * 5), max: Math.floor(random() * 5) } }
        : { kind: 'predicate', fieldId: field.id, operator, value: Math.floor(random() * 5) };
    }
    if (field.type === 'enum') {
      return {
        kind: 'predicate',
        fieldId: field.id,
        operator: random() < 0.5 ? 'eq' : 'notEq',
        value: pick(field.enumValues ?? [], random),
      };
    }
    return {
      kind: 'predicate',
      fieldId: field.id,
      operator: random() < 0.5 ? 'isTrue' : 'isFalse',
      value: true,
    };
  };

  const ruleCount = 2 + Math.floor(random() * 18);
  const rules: BusinessRule[] = Array.from({ length: ruleCount }, (_value, index) => {
    const group: ConditionGroup = {
      kind: 'group',
      operator: random() < 0.25 ? 'or' : 'and',
      conditions: [makeCondition(0), ...(random() < 0.6 ? [makeCondition(0)] : [])],
    };
    return {
      id: `r${index}`,
      name: `规则 ${index}`,
      conditions: group,
      priority: Math.floor(random() * 4),
      result: random() < 0.5 ? '通过' : pick(['通过', '拒绝', '人工审核'], random),
    };
  });

  return { id: 'p', title: '随机项目', fields, rules, sampleInputs: {}, versions: [], updatedAt: seed };
}

function overlapMap(analysis: RuleAnalysis): Map<string, RuleOverlap> {
  return new Map(analysis.overlaps.map((overlap) => [`${overlap.ruleAId}|${overlap.ruleBId}`, overlap]));
}

function expectSameAnalysis(actual: RuleAnalysis, expected: RuleAnalysis): void {
  expect({ ...actual, overlaps: [...overlapMap(actual).entries()].sort(([a], [b]) => a.localeCompare(b)) }).toEqual({
    ...expected,
    overlaps: [...overlapMap(expected).entries()].sort(([a], [b]) => a.localeCompare(b)),
  });
}

describe('analyzeRules bitmask implementation', () => {
  it('preserves empty AND/OR groups, duplicate priorities, and zero-field semantics', () => {
    const project: RuleProject = {
      id: 'edge',
      title: '边界项目',
      fields: [],
      rules: [
        { id: 'and-empty', name: '全中', conditions: { kind: 'group', operator: 'and', conditions: [] }, priority: 2, result: '通过' },
        { id: 'or-empty', name: '全不命中', conditions: { kind: 'group', operator: 'or', conditions: [] }, priority: 2, result: '拒绝' },
      ],
      sampleInputs: {},
      versions: [],
      updatedAt: 1,
    };
    expectSameAnalysis(analyzeRules(project), analyzeRulesByEnumeration(project));
  });

  it('matches exhaustive enumeration across randomized predicates, groups, priorities and results', () => {
    for (let seed = 1; seed <= 120; seed += 1) {
      const project = makeProject(seed);
      expectSameAnalysis(analyzeRules(project), analyzeRulesByEnumeration(project));
    }
  });

  it('matches exhaustive enumeration after the input-space truncation limit', () => {
    const project = makeProject(777, 40, 3);
    const totalCases = project.fields.reduce((total, field) => total * valuesForField(field, project).length, 1);
    expect(totalCases).toBeGreaterThan(MAX_CASES);
    expect(analyzeRules(project).truncated).toBe(true);
    expectSameAnalysis(analyzeRules(project), analyzeRulesByEnumeration(project));
  });
});
