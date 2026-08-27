export type SearchStatus =
  | "sat"
  | "unsat"
  | "unknown"
  | "error"
  | "optimal"
  | "feasible"
  | "complete"
  | "capped";
/** Decoded values; the numeric alternative is always a safe integer. */
export type SearchValue = number | boolean | string;
/** Restricted expression text, a safe integer, or a variable handle. */
export type Expression = string | number | Variable;

export interface SolveOptions {
  /** Positive wall-clock budget in milliseconds, as a safe integer. */
  timeoutMs?: number;
}

/** JSON-safe finite-domain shape; every number must be a safe integer. */
export type SearchDomainSpec =
  | { min: number; max: number; values?: never }
  | { values: number[]; min?: never; max?: never };

export interface SearchVariableSpec {
  name: string;
  domain: SearchDomainSpec;
  /** Signed-decimal integer keys mapped to display labels. */
  labels?: Record<string, string>;
}

/** Strictly one v1 constraint shape; tuple numbers must be safe integers. */
export type SearchConstraintSpec =
  | {
      expression: string;
      all_different?: never;
      table?: never;
      element?: never;
    }
  | {
      all_different: string[];
      expression?: never;
      table?: never;
      element?: never;
    }
  | {
      table: { variables: string[]; tuples: number[][] };
      expression?: never;
      all_different?: never;
      element?: never;
    }
  | {
      element: { index: string; array: string[]; result: string };
      expression?: never;
      all_different?: never;
      table?: never;
    };

export interface SearchObjectiveSpec {
  sense: "minimize" | "maximize";
  expression: string;
}

export interface SearchLimitsSpec {
  /** Positive wall-clock budget in milliseconds, as a safe integer. */
  timeout_ms?: number;
  /** Positive retained-solution cap, as a safe integer. */
  max_solutions?: number;
}

/** Version-1 wire document emitted by Model.toSpec(). */
export interface SearchSpec {
  version: 1;
  name?: string;
  variables: SearchVariableSpec[];
  constraints?: SearchConstraintSpec[];
  objective?: SearchObjectiveSpec;
  limits?: SearchLimitsSpec;
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
  /** Declare an inclusive safe-integer interval. */
  int(name: string, lower: number, upper: number): IntVar;
  bool(name: string): BoolVar;
  choice(name: string, choices: readonly string[]): ChoiceVar;
  /** Declare a grid with positive safe-integer dimensions and safe bounds. */
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
  /** Enumerate up to a positive safe-integer solution cap. */
  enumerate(limit?: number, options?: SolveOptions): SolveResult;
  toSMT2(): string;
  toSpec(): SearchSpec;
}

export function equationPrompt(
  variableNames: Iterable<string | Variable>,
  request: string,
): string;
