// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/** Declarative finite-domain search powered by AY. No host-language eval. */

import { koffi, lib } from "./_lib.mjs";

const NAME = /^[A-Za-z_][A-Za-z0-9_]*$/;
const MODEL = Symbol("ay-search model");
const SOLUTION_VARIABLES = Symbol("ay-search solution variables");

export class SearchError extends Error {
  constructor(message) {
    super(message);
    this.name = "SearchError";
  }
}

export class NativeSearchError extends Error {
  constructor(message) {
    super(message);
    this.name = "NativeSearchError";
  }
}

export class Variable {
  constructor(name, model) {
    this.name = name;
    this[MODEL] = model;
    if (new.target === Variable) Object.freeze(this);
  }

  toString() {
    return this.name;
  }
}

export class IntVar extends Variable {
  constructor(name, model, lower, upper) {
    super(name, model);
    this.lower = lower;
    this.upper = upper;
    if (new.target === IntVar) Object.freeze(this);
  }
}

export class BoolVar extends IntVar {
  constructor(name, model, lower, upper) {
    super(name, model, lower, upper);
    Object.freeze(this);
  }
}

export class ChoiceVar extends IntVar {
  constructor(name, model, choices) {
    super(name, model, 0, choices.length - 1);
    this.choices = Object.freeze([...choices]);
    Object.freeze(this);
  }
}

export class Solution {
  constructor(values, rawValues, model) {
    // A model variable may legally be named `__proto__`.  Null-prototype
    // records keep every solver-provided name as ordinary data instead of
    // invoking Object.prototype's legacy setter or shadowing inherited keys.
    this.values = Object.freeze(Object.assign(Object.create(null), values));
    this.rawValues = Object.freeze(
      Object.assign(Object.create(null), rawValues),
    );
    this[MODEL] = model;
    const variables = Object.create(null);
    for (const [name, variable] of model?._variables ?? []) {
      variables[name] = variable;
    }
    this[SOLUTION_VARIABLES] = Object.freeze(variables);
    Object.freeze(this);
  }

  get(variable) {
    let name = variable;
    if (variable instanceof Variable) {
      if (
        variable[MODEL] !== this[MODEL] ||
        this[SOLUTION_VARIABLES][variable.name] !== variable
      ) {
        throw new SearchError(
          `variable ${variable.name} belongs to another model or solve epoch`,
        );
      }
      name = variable.name;
    }
    return this.values[name];
  }
}

export class SolveResult {
  constructor(fields) {
    Object.assign(this, fields);
    Object.freeze(this.solutions);
    Object.freeze(this);
  }

  get isSat() {
    return this.solution !== undefined;
  }

  requireSolution() {
    if (!this.solution) {
      throw new SearchError(
        `search has no solution: ${this.error ?? this.reason ?? this.status}`,
      );
    }
    return this.solution;
  }
}

function callJson(fn, document) {
  const pointer = fn(JSON.stringify(document));
  if (!pointer)
    throw new NativeSearchError("AY search returned a null response");
  let text;
  try {
    text = koffi.decode(pointer, "char", -1);
  } finally {
    lib.ay_string_free(pointer);
  }
  let response;
  try {
    response = JSON.parse(text);
  } catch (error) {
    throw new NativeSearchError("AY search returned malformed JSON", {
      cause: error,
    });
  }
  if (!response || Array.isArray(response) || typeof response !== "object") {
    throw new NativeSearchError(
      "AY search returned a non-object JSON response",
    );
  }
  return response;
}

function integer(value, what) {
  if (!Number.isSafeInteger(value))
    throw new TypeError(`${what} must be a safe integer`);
  return value;
}

export class Model {
  constructor(name = undefined) {
    if (name !== undefined && typeof name !== "string") {
      throw new TypeError("model name must be a string or undefined");
    }
    this.name = name;
    this._variables = new Map();
    this._constraints = [];
    this._objective = undefined;
  }

  int(name, lower, upper) {
    this._checkNewName(name);
    integer(lower, "lower bound");
    integer(upper, "upper bound");
    if (lower > upper)
      throw new SearchError(`empty domain for ${JSON.stringify(name)}`);
    const variable = new IntVar(name, this, lower, upper);
    this._variables.set(name, variable);
    return variable;
  }

  bool(name) {
    this._checkNewName(name);
    const variable = new BoolVar(name, this, 0, 1);
    this._variables.set(name, variable);
    return variable;
  }

  choice(name, choices) {
    this._checkNewName(name);
    if (typeof choices === "string") {
      throw new TypeError(
        "choices must be an iterable of labels, not one string",
      );
    }
    const labels = [...choices];
    if (!labels.length)
      throw new SearchError("choice requires at least one label");
    if (labels.some((label) => typeof label !== "string" || !label)) {
      throw new SearchError("choice labels must be non-empty strings");
    }
    if (new Set(labels).size !== labels.length) {
      throw new SearchError("choice labels must be unique");
    }
    const variable = new ChoiceVar(name, this, labels);
    this._variables.set(name, variable);
    return variable;
  }

  intGrid(name, rows, columns, lower, upper) {
    if (!NAME.test(name))
      throw new SearchError(`invalid grid name ${JSON.stringify(name)}`);
    integer(rows, "row count");
    integer(columns, "column count");
    if (rows <= 0 || columns <= 0)
      throw new SearchError("grid dimensions must be positive");
    return Array.from({ length: rows }, (_, row) =>
      Array.from({ length: columns }, (_, column) =>
        this.int(`${name}_${row}_${column}`, lower, upper),
      ),
    );
  }

  add(equation) {
    if (typeof equation !== "string")
      throw new TypeError("add() expects an equation string");
    if (!equation.trim()) throw new SearchError("equation must not be empty");
    this._constraints.push({ expression: equation });
    return this;
  }

  allDifferent(variables) {
    const names = [...variables].map((variable) =>
      this._variableName(variable),
    );
    if (!names.length)
      throw new SearchError("allDifferent requires at least one variable");
    this._constraints.push({ all_different: names });
    return this;
  }

  table(variables, rows) {
    const vars = [...variables];
    const names = vars.map((variable) => this._variableName(variable));
    if (!names.length)
      throw new SearchError("table requires at least one variable");
    const encodedRows = [...rows].map((row, rowNumber) => {
      const values = [...row];
      if (values.length !== vars.length) {
        throw new SearchError(
          `table row ${rowNumber} has ${values.length} values; expected ${vars.length}`,
        );
      }
      return values.map((value, index) =>
        this._encodeValue(vars[index], value),
      );
    });
    if (!encodedRows.length) {
      throw new SearchError("table requires at least one allowed tuple");
    }
    this._constraints.push({
      table: { variables: names, tuples: encodedRows },
    });
    return this;
  }

  element(index, array, result) {
    const indexName = this._variableName(index);
    const arrayNames = [...array].map((variable) =>
      this._variableName(variable),
    );
    if (!arrayNames.length) {
      throw new SearchError("element requires a non-empty variable array");
    }
    const resultName = this._variableName(result);
    this._constraints.push({
      element: { index: indexName, array: arrayNames, result: resultName },
    });
    return this;
  }

  minimize(expression) {
    this._objective = {
      sense: "minimize",
      expression: this._expression(expression),
    };
    return this;
  }

  maximize(expression) {
    this._objective = {
      sense: "maximize",
      expression: this._expression(expression),
    };
    return this;
  }

  solve({ timeoutMs } = {}) {
    return this._result(
      callJson(lib.ay_search_solve_json, this._spec(timeoutMs)),
    );
  }

  enumerate(limit = 100, { timeoutMs } = {}) {
    if (this._objective !== undefined) {
      throw new SearchError(
        "enumerate() is unavailable on a model with an objective",
      );
    }
    integer(limit, "enumeration limit");
    if (limit <= 0) throw new SearchError("enumeration limit must be positive");
    return this._result(
      callJson(lib.ay_search_solve_json, this._spec(timeoutMs, limit)),
    );
  }

  toSMT2() {
    const response = callJson(
      lib.ay_search_compile_json,
      this._spec(undefined),
    );
    if (response.status === "error" || response.error) {
      throw new SearchError(String(response.error ?? response.message));
    }
    if (typeof response.smt2 !== "string") {
      throw new NativeSearchError(
        "AY search compile response has no SMT-LIB string",
      );
    }
    return response.smt2;
  }

  toSpec() {
    return this._spec(undefined);
  }

  _checkNewName(name) {
    if (typeof name !== "string" || !NAME.test(name)) {
      throw new SearchError(
        `invalid variable name ${JSON.stringify(name)}; use [A-Za-z_][A-Za-z0-9_]*`,
      );
    }
    if (this._variables.has(name))
      throw new SearchError(`duplicate variable name ${name}`);
  }

  _variableName(variable) {
    if (!(variable instanceof Variable))
      throw new TypeError("expected an AY search variable");
    if (
      variable[MODEL] !== this ||
      this._variables.get(variable.name) !== variable
    ) {
      throw new SearchError(
        `variable ${variable.name} belongs to another model`,
      );
    }
    return variable.name;
  }

  _expression(expression) {
    if (expression instanceof Variable) return this._variableName(expression);
    if (typeof expression !== "string" && !Number.isSafeInteger(expression)) {
      throw new TypeError(
        "expression must be a string, safe integer, or model variable",
      );
    }
    const rendered = String(expression).trim();
    if (!rendered) throw new SearchError("expression must not be empty");
    return rendered;
  }

  _encodeValue(variable, value) {
    this._variableName(variable);
    let encoded = value;
    if (variable instanceof ChoiceVar && typeof value === "string") {
      encoded = variable.choices.indexOf(value);
      if (encoded < 0)
        throw new SearchError(
          `unknown label ${value} for choice ${variable.name}`,
        );
    } else if (typeof value === "boolean") {
      encoded = Number(value);
    }
    integer(encoded, `table value for ${variable.name}`);
    if (encoded < variable.lower || encoded > variable.upper) {
      throw new SearchError(
        `value ${encoded} is outside ${variable.name}'s domain`,
      );
    }
    return encoded;
  }

  _spec(timeoutMs, maxSolutions = undefined) {
    const variables = [...this._variables.values()].map((variable) => {
      const item = {
        name: variable.name,
        domain: { min: variable.lower, max: variable.upper },
      };
      if (variable instanceof ChoiceVar) {
        item.labels = Object.fromEntries(
          variable.choices.map((label, index) => [index, label]),
        );
      }
      return item;
    });
    const limits = {};
    if (timeoutMs !== undefined) {
      integer(timeoutMs, "timeout_ms");
      if (timeoutMs <= 0) throw new SearchError("timeout_ms must be positive");
      limits.timeout_ms = timeoutMs;
    }
    if (maxSolutions !== undefined) limits.max_solutions = maxSolutions;
    const spec = {
      version: 1,
      variables,
      constraints: this._constraints.map((constraint) =>
        structuredClone(constraint),
      ),
    };
    if (this.name !== undefined) spec.name = this.name;
    if (this._objective !== undefined) spec.objective = { ...this._objective };
    if (Object.keys(limits).length) spec.limits = limits;
    return spec;
  }

  _solution(raw) {
    const values = Object.create(null);
    const rawValues = Object.create(null);
    for (const [name, value] of Object.entries(raw)) {
      if (!Number.isSafeInteger(value)) {
        throw new NativeSearchError(
          `AY returned a non-integer value for ${name}`,
        );
      }
      rawValues[name] = value;
      const variable = this._variables.get(name);
      if (
        variable instanceof ChoiceVar &&
        value >= 0 &&
        value < variable.choices.length
      ) {
        values[name] = variable.choices[value];
      } else if (variable instanceof BoolVar) {
        values[name] = Boolean(value);
      } else {
        values[name] = value;
      }
    }
    return new Solution(values, rawValues, this);
  }

  _result(response) {
    const status = [
      "sat",
      "unsat",
      "unknown",
      "error",
      "optimal",
      "feasible",
      "complete",
      "capped",
    ].includes(response.status)
      ? response.status
      : "error";
    const solutions = Array.isArray(response.solutions)
      ? response.solutions
          .filter((item) => item && typeof item === "object")
          .map((item) => this._solution(item.assignments ?? item))
      : [];
    const assignments = response.assignments ?? response.solution;
    let solution =
      assignments && typeof assignments === "object"
        ? this._solution(assignments)
        : undefined;
    solution ??= solutions[0];
    const objective =
      response.objective && typeof response.objective === "object"
        ? response.objective.value
        : response.objective;
    if (objective != null && !Number.isSafeInteger(objective)) {
      throw new NativeSearchError(
        "AY returned an objective outside JavaScript's safe integer range",
      );
    }
    return new SolveResult({
      status,
      solution,
      solutions,
      objective: objective == null ? undefined : objective,
      optimal:
        status === "optimal"
          ? true
          : status === "feasible"
            ? false
            : typeof response.optimal === "boolean"
              ? response.optimal
              : undefined,
      complete:
        status === "complete"
          ? true
          : status === "capped"
            ? false
            : typeof response.complete === "boolean"
              ? response.complete
              : undefined,
      reason: response.reason == null ? undefined : String(response.reason),
      error:
        status === "error"
          ? String(response.error ?? response.message ?? "search error")
          : undefined,
      raw: response,
    });
  }
}

export function equationPrompt(variableNames, request) {
  const names = [...variableNames].map((item) =>
    item instanceof Variable ? item.name : String(item),
  );
  return (
    'Translate the requirement below into AY Search equations. Return JSON as {"equations":["..."]} ' +
    "and nothing else. Use only integer literals, the listed variables, parentheses, +, -, " +
    "constant multiplication, and exactly one of ==, !=, <=, >= per equation. Do not emit code " +
    `or SMT-LIB.\nVariables: ${names.join(", ")}\nRequirement: ${request}`
  );
}
