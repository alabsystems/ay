# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Declarative finite-domain search and optimization powered by AY.

The host-language API only builds a versioned JSON SearchSpec. Equation strings
cross the C ABI as data and are parsed by AY's restricted linear-expression
parser; this module never calls ``eval``.
"""

from __future__ import annotations

import builtins
import re
from copy import deepcopy
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import (
    Any,
    Dict,
    Iterable,
    Iterator,
    List,
    Literal,
    Mapping,
    Optional,
    Sequence,
    Tuple,
    Union,
)

from . import _native
from ._native import NativeSearchError


Status = Literal[
    "sat",
    "unsat",
    "unknown",
    "error",
    "optimal",
    "feasible",
    "complete",
    "capped",
]
Scalar = Union[int, bool, str]
Expression = Union[str, int, "Variable"]
_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class SearchError(ValueError):
    """A model is malformed or AY reports a search error."""


@dataclass(frozen=True)
class Variable:
    """A model-scoped variable reference accepted by constraints/results."""

    name: str
    _model_token: object = field(repr=False)

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class IntVar(Variable):
    lower: int
    upper: int


@dataclass(frozen=True)
class BoolVar(IntVar):
    pass


@dataclass(frozen=True)
class ChoiceVar(IntVar):
    choices: Tuple[str, ...]


@dataclass(frozen=True)
class Solution:
    """An immutable assignment; index it by a variable or by its name."""

    values: Mapping[str, Scalar]
    raw_values: Mapping[str, int]
    _model_token: object = field(repr=False, compare=False)
    _variables: Mapping[str, Variable] = field(repr=False, compare=False)

    def __getitem__(self, key: Union[str, Variable]) -> Scalar:
        if isinstance(key, Variable):
            if (
                key._model_token is not self._model_token
                or self._variables.get(key.name) is not key
            ):
                raise SearchError(f"variable {key.name!r} belongs to another model")
            return self.values[key.name]
        return self.values[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self.values)

    def __len__(self) -> int:
        return len(self.values)


@dataclass(frozen=True)
class SolveResult:
    """A faithful AY result: unknown and error are never collapsed to unsat."""

    status: Status
    solution: Optional[Solution] = None
    solutions: Tuple[Solution, ...] = ()
    objective: Optional[int] = None
    optimal: Optional[bool] = None
    complete: Optional[bool] = None
    reason: Optional[str] = None
    error: Optional[str] = None
    raw: Optional[Mapping[str, Any]] = None

    @property
    def is_sat(self) -> bool:
        return self.solution is not None

    def require_solution(self) -> Solution:
        if self.solution is None:
            detail = self.error or self.reason or self.status
            raise SearchError(f"search has no solution: {detail}")
        return self.solution


class Model:
    """A declarative finite-domain search model.

    Use :meth:`int`, :meth:`bool`, :meth:`choice`, and :meth:`int_grid` to
    declare decisions. Constraints are linear equation strings or safe global
    constraints. Calling :meth:`solve` is the only operation that invokes AY.
    """

    def __init__(self, name: Optional[str] = None):
        if name is not None and not isinstance(name, str):
            raise TypeError("model name must be a string or None")
        self.name = name
        self._model_token = object()
        self._variables: Dict[str, IntVar] = {}
        self._constraints: List[Dict[str, Any]] = []
        self._objective: Optional[Dict[str, str]] = None

    def int(self, name: str, lower: builtins.int, upper: builtins.int) -> IntVar:
        self._check_new_name(name)
        if isinstance(lower, bool) or isinstance(upper, bool):
            raise TypeError("integer bounds must be integers, not bool")
        if not isinstance(lower, int) or not isinstance(upper, int):
            raise TypeError("integer bounds must be integers")
        if lower > upper:
            raise SearchError(f"empty domain for {name!r}: {lower}..{upper}")
        if lower < -(2**63) or upper > 2**63 - 1:
            raise SearchError("integer bounds must fit in signed 64-bit values")
        variable = IntVar(name, self._model_token, lower, upper)
        self._variables[name] = variable
        return variable

    def bool(self, name: str) -> BoolVar:
        self._check_new_name(name)
        variable = BoolVar(name, self._model_token, 0, 1)
        self._variables[name] = variable
        return variable

    def choice(self, name: str, choices: Sequence[str]) -> ChoiceVar:
        self._check_new_name(name)
        if isinstance(choices, str):
            raise TypeError("choices must be a sequence of labels, not one string")
        labels = tuple(choices)
        if not labels:
            raise SearchError("choice requires at least one label")
        if any(not isinstance(label, str) or not label for label in labels):
            raise SearchError("choice labels must be non-empty strings")
        if len(set(labels)) != len(labels):
            raise SearchError("choice labels must be unique")
        variable = ChoiceVar(name, self._model_token, 0, len(labels) - 1, labels)
        self._variables[name] = variable
        return variable

    def int_grid(
        self,
        name: str,
        rows: builtins.int,
        columns: builtins.int,
        lower: builtins.int,
        upper: builtins.int,
    ) -> List[List[IntVar]]:
        if not _NAME.fullmatch(name):
            raise SearchError(f"invalid grid name {name!r}")
        if (
            isinstance(rows, bool)
            or isinstance(columns, bool)
            or not isinstance(rows, int)
            or not isinstance(columns, int)
        ):
            raise TypeError("grid dimensions must be integers")
        if rows <= 0 or columns <= 0:
            raise SearchError("grid dimensions must be positive")
        return [
            [
                self.int(f"{name}_{row}_{column}", lower, upper)
                for column in range(columns)
            ]
            for row in range(rows)
        ]

    def add(self, equation: str) -> "Model":
        if not isinstance(equation, str):
            raise TypeError("add() expects an equation string")
        if not equation.strip():
            raise SearchError("equation must not be empty")
        self._constraints.append({"expression": equation})
        return self

    def all_different(self, variables: Iterable[Variable]) -> "Model":
        names = self._variable_names(variables)
        if not names:
            raise SearchError("all_different requires at least one variable")
        self._constraints.append({"all_different": names})
        return self

    def table(
        self,
        variables: Sequence[Variable],
        rows: Iterable[Sequence[Scalar]],
    ) -> "Model":
        variables_tuple = tuple(variables)
        names = self._variable_names(variables_tuple)
        if not names:
            raise SearchError("table requires at least one variable")
        encoded_rows: List[List[int]] = []
        for row_number, row in enumerate(rows):
            values = tuple(row)
            if len(values) != len(variables_tuple):
                raise SearchError(
                    f"table row {row_number} has {len(values)} values; expected {len(names)}"
                )
            encoded_rows.append(
                [
                    self._encode_value(var, value)
                    for var, value in zip(variables_tuple, values)
                ]
            )
        self._constraints.append(
            {"table": {"variables": names, "tuples": encoded_rows}}
        )
        return self

    def element(
        self,
        index: Variable,
        array: Sequence[Variable],
        result: Variable,
    ) -> "Model":
        """Constrain ``result`` to equal ``array[index]``."""
        index_name = self._variable_names((index,))[0]
        array_names = self._variable_names(array)
        if not array_names:
            raise SearchError("element requires a non-empty variable array")
        result_name = self._variable_names((result,))[0]
        self._constraints.append(
            {
                "element": {
                    "index": index_name,
                    "array": array_names,
                    "result": result_name,
                }
            }
        )
        return self

    def minimize(self, expression: Expression) -> "Model":
        self._objective = {
            "sense": "minimize",
            "expression": self._expression(expression),
        }
        return self

    def maximize(self, expression: Expression) -> "Model":
        self._objective = {
            "sense": "maximize",
            "expression": self._expression(expression),
        }
        return self

    def solve(
        self,
        *,
        timeout_ms: Optional[builtins.int] = None,
    ) -> SolveResult:
        document = self._spec(timeout_ms, None)
        return self._result(_native.solve(document))

    def enumerate(
        self,
        limit: builtins.int = 100,
        *,
        timeout_ms: Optional[builtins.int] = None,
    ) -> SolveResult:
        if self._objective is not None:
            raise SearchError("enumerate() is unavailable on a model with an objective")
        if not isinstance(limit, int) or isinstance(limit, bool) or limit <= 0:
            raise SearchError("enumeration limit must be a positive integer")
        document = self._spec(timeout_ms, limit)
        return self._result(_native.solve(document))

    def to_smt2(self) -> str:
        response = _native.compile_smt2(self._spec(None, None))
        if response.get("status") == "error" or "error" in response:
            raise SearchError(str(response.get("error") or response.get("message")))
        smt2 = response.get("smt2")
        if not isinstance(smt2, str):
            raise NativeSearchError("AY search compile response has no SMT-LIB string")
        return smt2

    def to_spec(self) -> Dict[str, Any]:
        """Return a detached, JSON-serializable SearchSpec document."""
        return self._spec(None, None)

    def _check_new_name(self, name: str) -> None:
        if not isinstance(name, str) or not _NAME.fullmatch(name):
            raise SearchError(
                f"invalid variable name {name!r}; use [A-Za-z_][A-Za-z0-9_]*"
            )
        if name in self._variables:
            raise SearchError(f"duplicate variable name {name!r}")

    def _require_ours(self, variable: Variable) -> None:
        if not isinstance(variable, Variable):
            raise TypeError("expected an aysearch variable")
        if (
            variable._model_token is not self._model_token
            or self._variables.get(variable.name) is not variable
        ):
            raise SearchError(f"variable {variable.name!r} belongs to another model")

    def _variable_names(self, variables: Iterable[Variable]) -> List[str]:
        result = []
        for variable in variables:
            self._require_ours(variable)
            result.append(variable.name)
        return result

    def _expression(self, expression: Expression) -> str:
        if isinstance(expression, Variable):
            self._require_ours(expression)
            return expression.name
        if isinstance(expression, bool) or not isinstance(expression, (str, int)):
            raise TypeError("expression must be a string, integer, or model variable")
        if isinstance(expression, int) and not -(2**63) <= expression <= 2**63 - 1:
            raise SearchError("integer expression must fit in a signed 64-bit value")
        rendered = str(expression).strip()
        if not rendered:
            raise SearchError("expression must not be empty")
        return rendered

    def _encode_value(self, variable: Variable, value: Scalar) -> builtins.int:
        self._require_ours(variable)
        if isinstance(variable, ChoiceVar) and isinstance(value, str):
            try:
                return variable.choices.index(value)
            except ValueError as error:
                raise SearchError(
                    f"unknown label {value!r} for choice {variable.name!r}"
                ) from error
        if isinstance(value, bool):
            encoded = int(value)
        elif isinstance(value, int):
            encoded = value
        else:
            raise SearchError(f"table value for {variable.name!r} must be an integer")
        if isinstance(variable, IntVar) and not (
            variable.lower <= encoded <= variable.upper
        ):
            raise SearchError(f"value {encoded} is outside {variable.name!r}'s domain")
        return encoded

    def _spec(
        self,
        timeout_ms: Optional[builtins.int],
        max_solutions: Optional[builtins.int],
    ) -> Dict[str, Any]:
        variables = []
        for variable in self._variables.values():
            item: Dict[str, Any] = {
                "name": variable.name,
                "domain": {"min": variable.lower, "max": variable.upper},
            }
            if isinstance(variable, ChoiceVar):
                item["labels"] = {
                    str(index): label for index, label in enumerate(variable.choices)
                }
            variables.append(item)
        limits: Dict[str, int] = {}
        if timeout_ms is not None:
            if (
                not isinstance(timeout_ms, int)
                or isinstance(timeout_ms, bool)
                or not 0 < timeout_ms <= 2**64 - 1
            ):
                raise SearchError("timeout_ms must be a positive integer")
            limits["timeout_ms"] = timeout_ms
        if max_solutions is not None:
            limits["max_solutions"] = max_solutions
        result: Dict[str, Any] = {
            "version": 1,
            "variables": variables,
            "constraints": deepcopy(self._constraints),
        }
        if self.name is not None:
            result["name"] = self.name
        if self._objective is not None:
            result["objective"] = dict(self._objective)
        if limits:
            result["limits"] = limits
        return result

    def _solution(self, raw: Mapping[str, Any]) -> Solution:
        integer_values: Dict[str, int] = {}
        display_values: Dict[str, Scalar] = {}
        for name, value in raw.items():
            if isinstance(value, bool):
                integer = int(value)
            elif isinstance(value, int):
                integer = value
            else:
                raise NativeSearchError(f"AY returned a non-integer value for {name!r}")
            integer_values[name] = integer
            variable = self._variables.get(name)
            if isinstance(variable, ChoiceVar) and 0 <= integer < len(variable.choices):
                display_values[name] = variable.choices[integer]
            elif isinstance(variable, BoolVar):
                display_values[name] = bool(integer)
            else:
                display_values[name] = integer
        return Solution(
            MappingProxyType(display_values),
            MappingProxyType(integer_values),
            self._model_token,
            MappingProxyType(dict(self._variables)),
        )

    def _result(self, response: Mapping[str, Any]) -> SolveResult:
        status_value = response.get("status", "error")
        status: Status
        if status_value in (
            "sat",
            "unsat",
            "unknown",
            "error",
            "optimal",
            "feasible",
            "complete",
            "capped",
        ):
            status = status_value
        else:
            status = "error"
        raw_solutions = response.get("solutions")
        solutions: Tuple[Solution, ...] = ()
        if isinstance(raw_solutions, list):
            decoded_solutions = []
            for item in raw_solutions:
                if not isinstance(item, Mapping):
                    continue
                assignments = item.get("assignments", item)
                if not isinstance(assignments, Mapping):
                    raise NativeSearchError(
                        "AY returned malformed enumeration assignments"
                    )
                decoded_solutions.append(self._solution(assignments))
            solutions = tuple(decoded_solutions)
        raw_solution = response.get("assignments", response.get("solution"))
        solution = (
            self._solution(raw_solution) if isinstance(raw_solution, Mapping) else None
        )
        if solution is None and solutions:
            solution = solutions[0]
        objective = response.get("objective")
        if isinstance(objective, Mapping):
            objective = objective.get("value")
        optimal = response.get("optimal")
        if status in ("optimal", "feasible"):
            optimal = status == "optimal"
        elif not isinstance(optimal, bool):
            optimal = None
        complete = response.get("complete")
        if status in ("complete", "capped"):
            complete = status == "complete"
        elif not isinstance(complete, bool):
            complete = None
        return SolveResult(
            status=status,
            solution=solution,
            solutions=solutions,
            objective=objective
            if isinstance(objective, int) and not isinstance(objective, bool)
            else None,
            optimal=optimal,
            complete=complete,
            reason=str(response["reason"])
            if response.get("reason") is not None
            else None,
            error=str(response.get("error") or response.get("message"))
            if status == "error"
            else None,
            raw=dict(response),
        )


def equation_prompt(
    variable_names: Iterable[Union[str, Variable]], request: str
) -> str:
    """Build a prompt for an LLM that returns only AY's safe equation strings."""
    names = [
        item.name if isinstance(item, Variable) else str(item)
        for item in variable_names
    ]
    return (
        "Translate the requirement below into AY Search equations. Return JSON as "
        '{"equations":["..."]} and nothing else. Use only integer literals, the '
        "listed variables, parentheses, +, -, constant multiplication, and exactly "
        "one of ==, !=, <=, >= per equation. Do not emit code or SMT-LIB.\n"
        f"Variables: {', '.join(names)}\nRequirement: {request}"
    )


__all__ = [
    "BoolVar",
    "ChoiceVar",
    "IntVar",
    "Model",
    "NativeSearchError",
    "SearchError",
    "Solution",
    "SolveResult",
    "Status",
    "Variable",
    "equation_prompt",
]
