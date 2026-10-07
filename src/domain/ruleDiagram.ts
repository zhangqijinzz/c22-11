export type SegmentChild = number;

interface Segment {
  first: number;
  last: number;
  child: SegmentChild;
}

interface MddNode {
  id: number;
  level: number;
  defaultChild: number;
  segments: Segment[];
}

export class MddBudgetExceeded extends Error {
  constructor() {
    super('MDD node budget exceeded');
    this.name = 'MddBudgetExceeded';
  }
}

export class RuleDiagram {
  private static readonly ZERO = 0;
  private static readonly ONE = 1;
  private static readonly COUNT_LIMIT = 120_000;

  private readonly nodes = new Map<number, MddNode>();
  private readonly uniqueNodes = new Map<string, number>();
  private readonly andCache = new Map<string, Map<number, number>>();
  private readonly orCache = new Map<string, Map<number, number>>();
  private readonly notCache = new Map<number, number>();
  private readonly countCache = new Map<string, number>();
  private readonly suffixCounts: number[];
  private nextId = 2;

  constructor(
    private readonly counts: number[],
    private readonly nodeBudget = 30_000,
  ) {
    this.suffixCounts = new Array<number>(counts.length + 1).fill(1);
    for (let level = counts.length - 1; level >= 0; level -= 1) {
      this.suffixCounts[level] = Math.min(
        RuleDiagram.COUNT_LIMIT + 1,
        this.suffixCounts[level + 1] * counts[level],
      );
    }
  }

  get zero(): number { return RuleDiagram.ZERO; }
  get one(): number { return RuleDiagram.ONE; }

  interval(level: number, first: number, last: number, allowed = true): number {
    const child = allowed ? RuleDiagram.ONE : RuleDiagram.ZERO;
    const defaultChild = allowed ? RuleDiagram.ZERO : RuleDiagram.ONE;
    if (first > last) return defaultChild;
    if (first === 0 && last === this.counts[level] - 1) return child;
    return this.makeNode(level, defaultChild, [{ first, last, child }]);
  }

  and(left: number, right: number): number {
    if (left === RuleDiagram.ZERO || right === RuleDiagram.ZERO) return RuleDiagram.ZERO;
    if (left === RuleDiagram.ONE) return right;
    if (right === RuleDiagram.ONE) return left;
    return this.applyRecursive('and', left, right);
  }

  or(left: number, right: number): number {
    if (left === RuleDiagram.ONE || right === RuleDiagram.ONE) return RuleDiagram.ONE;
    if (left === RuleDiagram.ZERO) return right;
    if (right === RuleDiagram.ZERO) return left;
    return this.applyRecursive('or', left, right);
  }

  not(node: number): number {
    if (node === RuleDiagram.ZERO) return RuleDiagram.ONE;
    if (node === RuleDiagram.ONE) return RuleDiagram.ZERO;
    const cached = this.notCache.get(node);
    if (cached !== undefined) return cached;

    const current = this.nodes.get(node);
    if (!current) throw new Error('Unknown MDD node');
    const segments = current.segments.map((segment) => ({ ...segment, child: this.not(segment.child) }));
    const result = this.makeNode(current.level, this.not(current.defaultChild), segments);
    this.notCache.set(node, result);
    return result;
  }

  modelCount(root: number): number {
    return this.count(root, 0);
  }

  firstWitness(root: number): number[] | undefined {
    if (root === RuleDiagram.ZERO) return undefined;
    const digits = new Array<number>(this.counts.length).fill(0);
    return this.writeWitness(root, 0, digits) ? digits : undefined;
  }

  firstWitnesses(root: number, limit: number): number[][] {
    const witnesses: number[][] = [];
    const digits = new Array<number>(this.counts.length).fill(0);
    this.collectWitnesses(root, 0, digits, witnesses, limit);
    return witnesses;
  }

  private applyRecursive(operator: 'and' | 'or', leftId: number, rightId: number): number {
    const left = this.nodes.get(leftId);
    const right = this.nodes.get(rightId);
    if (!left || !right) throw new Error('Unknown MDD node');

    const level = Math.min(left.level, right.level);
    const lowId = Math.min(leftId, rightId);
    const highId = Math.max(leftId, rightId);
    const cacheKey = `${lowId}|${highId}`;
    const cacheRoot = operator === 'and' ? this.andCache : this.orCache;
    let cache = cacheRoot.get(cacheKey);
    if (!cache) {
      cache = new Map<number, number>();
      cacheRoot.set(cacheKey, cache);
    }
    const cached = cache.get(level);
    if (cached !== undefined) return cached;

    const leftAtLevel = left.level === level ? left : undefined;
    const rightAtLevel = right.level === level ? right : undefined;
    const leftBase = leftAtLevel ? left.defaultChild : leftId;
    const rightBase = rightAtLevel ? right.defaultChild : rightId;
    const base = this.combineAtLevel(operator, leftBase, rightBase);

    const valueCount = this.counts[level];
    const boundaries = new Set<number>([0, valueCount]);
    for (const node of [leftAtLevel, rightAtLevel]) {
      if (!node) continue;
      for (const segment of node.segments) {
        boundaries.add(segment.first);
        boundaries.add(Math.min(valueCount, segment.last + 1));
      }
    }

    const sortedBoundaries = [...boundaries].sort((a, b) => a - b);
    const rawSegments: Segment[] = [];
    let leftPointer = 0;
    let rightPointer = 0;

    for (let index = 0; index < sortedBoundaries.length - 1; index += 1) {
      const first = sortedBoundaries[index];
      const last = sortedBoundaries[index + 1] - 1;
      while (leftAtLevel && leftPointer < leftAtLevel.segments.length && leftAtLevel.segments[leftPointer].last < first) {
        leftPointer += 1;
      }
      while (rightAtLevel && rightPointer < rightAtLevel.segments.length && rightAtLevel.segments[rightPointer].last < first) {
        rightPointer += 1;
      }
      const leftSegment = leftAtLevel?.segments[leftPointer];
      const rightSegment = rightAtLevel?.segments[rightPointer];
      const leftChild = leftSegment && first >= leftSegment.first && first <= leftSegment.last
        ? leftSegment.child
        : leftBase;
      const rightChild = rightSegment && first >= rightSegment.first && first <= rightSegment.last
        ? rightSegment.child
        : rightBase;
      const child = this.combineAtLevel(operator, leftChild, rightChild);
      rawSegments.push({ first, last, child });
    }

    const result = this.makeNode(level, base, rawSegments);
    cache.set(level, result);
    return result;
  }

  private combineAtLevel(operator: 'and' | 'or', left: number, right: number): number {
    if (left === RuleDiagram.ZERO || right === RuleDiagram.ZERO) {
      return operator === 'and' ? RuleDiagram.ZERO : (left === RuleDiagram.ZERO ? right : left);
    }
    if (left === RuleDiagram.ONE || right === RuleDiagram.ONE) {
      return operator === 'or' ? RuleDiagram.ONE : (left === RuleDiagram.ONE ? right : left);
    }
    return this.applyRecursive(operator, left, right);
  }

  private makeNode(level: number, defaultChild: number, rawSegments: Segment[]): number {
    const valueCount = this.counts[level];
    const segments: Segment[] = [];

    const append = (segment: Segment): void => {
      if (segment.child === defaultChild || segment.first > segment.last) return;
      const previous = segments[segments.length - 1];
      if (previous && previous.child === segment.child && previous.last + 1 === segment.first) {
        previous.last = segment.last;
      } else {
        segments.push({ ...segment });
      }
    };

    for (const segment of [...rawSegments].sort((a, b) => a.first - b.first)) {
      const first = Math.max(0, segment.first);
      const last = Math.min(valueCount - 1, segment.last);
      let currentStart = first;
      const previous = segments[segments.length - 1];
      if (previous && currentStart <= previous.last) {
        if (previous.child !== segment.child) {
          // Raw segments from apply() are disjoint; this only guards accidental overlap.
          currentStart = previous.last + 1;
        } else {
          previous.last = Math.max(previous.last, last);
          continue;
        }
      }
      append({ first: currentStart, last, child: segment.child });
    }

    if (segments.length === 0) return defaultChild;
    if (segments.length === 1 && segments[0].first === 0 && segments[0].last === valueCount - 1) {
      return segments[0].child;
    }

    const key = `${level}:${defaultChild}:${segments.map((segment) => `${segment.first}-${segment.last}-${segment.child}`).join(',')}`;
    const existing = this.uniqueNodes.get(key);
    if (existing !== undefined) return existing;

    if (this.nextId - 2 >= this.nodeBudget) throw new MddBudgetExceeded();
    const id = this.nextId++;
    this.nodes.set(id, { id, level, defaultChild, segments });
    this.uniqueNodes.set(key, id);
    return id;
  }

  private count(node: number, level: number): number {
    if (node === RuleDiagram.ZERO) return 0;
    if (node === RuleDiagram.ONE) return this.suffixCounts[level];
    const key = `${node}:${level}`;
    const cached = this.countCache.get(key);
    if (cached !== undefined) return cached;

    const current = this.nodes.get(node);
    if (!current) throw new Error('Unknown MDD node');
    let result: number;
    if (current.level > level) {
      return this.suffixCounts[level] / this.suffixCounts[current.level] * this.count(node, current.level);
    } else {
      let covered = 0;
      result = 0;
      for (const segment of current.segments) {
        const length = segment.last - segment.first + 1;
        covered += length;
        result += length * this.count(segment.child, level + 1);
      }
      result += (this.counts[level] - covered) * this.count(current.defaultChild, level + 1);
    }
    this.countCache.set(key, result);
    return result;
  }

  private writeWitness(node: number, level: number, digits: number[]): boolean {
    if (node === RuleDiagram.ZERO) return false;
    if (node === RuleDiagram.ONE) {
      for (let index = level; index < this.counts.length; index += 1) digits[index] = 0;
      return true;
    }

    const current = this.nodes.get(node);
    if (!current) throw new Error('Unknown MDD node');
    if (current.level > level) {
      digits[level] = 0;
      return this.writeWitness(node, level + 1, digits);
    }

    let cursor = 0;
    for (const segment of current.segments) {
      if (current.defaultChild !== RuleDiagram.ZERO && cursor < segment.first) {
        digits[level] = cursor;
        return this.writeWitness(current.defaultChild, level + 1, digits);
      }
      if (segment.child !== RuleDiagram.ZERO) {
        digits[level] = segment.first;
        return this.writeWitness(segment.child, level + 1, digits);
      }
      cursor = Math.max(cursor, segment.last + 1);
    }
    if (current.defaultChild !== RuleDiagram.ZERO && cursor < this.counts[level]) {
      digits[level] = cursor;
      return this.writeWitness(current.defaultChild, level + 1, digits);
    }
    return false;
  }

  private collectWitnesses(
    node: number,
    level: number,
    digits: number[],
    witnesses: number[][],
    limit: number,
  ): void {
    if (witnesses.length >= limit || node === RuleDiagram.ZERO) return;
    if (level === this.counts.length) {
      if (node === RuleDiagram.ONE) witnesses.push([...digits]);
      return;
    }
    if (node === RuleDiagram.ONE) {
      for (let value = 0; value < this.counts[level]; value += 1) {
        digits[level] = value;
        this.collectWitnesses(RuleDiagram.ONE, level + 1, digits, witnesses, limit);
        if (witnesses.length >= limit) return;
      }
      return;
    }

    const current = this.nodes.get(node);
    if (!current) throw new Error('Unknown MDD node');
    if (current.level > level) {
      for (let value = 0; value < this.counts[level]; value += 1) {
        digits[level] = value;
        this.collectWitnesses(node, level + 1, digits, witnesses, limit);
        if (witnesses.length >= limit) return;
      }
      return;
    }

    const visitRange = (first: number, last: number, child: number): void => {
      if (child === RuleDiagram.ZERO) return;
      for (let value = first; value <= last; value += 1) {
        digits[level] = value;
        this.collectWitnesses(child, level + 1, digits, witnesses, limit);
        if (witnesses.length >= limit) return;
      }
    };

    let cursor = 0;
    for (const segment of current.segments) {
      visitRange(cursor, segment.first - 1, current.defaultChild);
      if (witnesses.length >= limit) return;
      visitRange(segment.first, segment.last, segment.child);
      if (witnesses.length >= limit) return;
      cursor = segment.last + 1;
    }
    visitRange(cursor, this.counts[level] - 1, current.defaultChild);
  }
}
