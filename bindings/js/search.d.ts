export type SearchStatus =
  | "sat"
  | "unsat"
  | "unknown"
  | "error"
  | "optimal"
  | "feasible"
  | "complete"
  | "capped";
export type SearchValue = number | boolean | string;
export type Expression = string | number | Variable;

export interface SolveOptions {
  timeoutMs?: number;
}

export interface SearchSpec {
  version: 1;
  name?: string;
  variables: Array<{
    name: string;
    domain: { min: number; max: number } | { values: number[] };
    labels?: Record<string, string>;
  }>;
  constraints: Array<Record<string, unknown>>;
  objective?: { sense: "minimize" | "maximize"; expression: string };
  limits?: { timeout_ms?: number; max_solutions?: number };
}

export class SearchError extends Error {}
export class NativeSearchError extends Error {}

export class Variable {
  readonly name: string;
  toString(): string;
}

export class IntVar extends Variable {
  readonly lower: number;
  readonly upper: number;
}

export class BoolVar extends IntVar {}

export class ChoiceVar extends IntVar {
  readonly choices: readonly string[];
}

export class Solution {
  readonly values: Readonly<Record<string, SearchValue>>;
  readonly rawValues: Readonly<Record<string, number>>;
  get(variable: Variable | string): SearchValue | undefined;
}

export class SolveResult {
  readonly status: SearchStatus;
  readonly solution?: Solution;
  readonly solutions: readonly Solution[];
  readonly objective?: number;
  readonly optimal?: boolean;
  readonly complete?: boolean;
  readonly reason?: string;
  readonly error?: string;
  readonly raw: Readonly<Record<string, unknown>>;
  readonly isSat: boolean;
  requireSolution(): Solution;
}

export class Model {
  constructor(name?: string);
  readonly name?: string;
  int(name: string, lower: number, upper: number): IntVar;
  bool(name: string): BoolVar;
  choice(name: string, choices: readonly string[]): ChoiceVar;
  intGrid(
    name: string,
    rows: number,
    columns: number,
    lower: number,
    upper: number,
  ): IntVar[][];
  add(equation: string): this;
  allDifferent(variables: Iterable<Variable>): this;
  table(
    variables: readonly Variable[],
    rows: Iterable<readonly SearchValue[]>,
  ): this;
  element(index: Variable, array: readonly Variable[], result: Variable): this;
  minimize(expression: Expression): this;
  maximize(expression: Expression): this;
  solve(options?: SolveOptions): SolveResult;
  enumerate(limit?: number, options?: SolveOptions): SolveResult;
  toSMT2(): string;
  toSpec(): SearchSpec;
}

export function equationPrompt(
  variableNames: Iterable<string | Variable>,
  request: string,
): string;
