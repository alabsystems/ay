// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer-valued string function classification and range helpers for effort 1.

use super::super::*;

impl CoreSolver {
    /// Whether `t` is a reducible integer-valued string function application.
    pub(in super::super) fn is_reducible_int_app(terms: &TermStore, t: TermId) -> bool {
        let TermData::App(sym, args) = terms.get(t) else {
            return false;
        };
        matches!(sym.name(), "str.to_int" | "str.to.int" if args.len() == 1)
            || matches!(sym.name(), "str.indexof" if args.len() == 3)
            || matches!(sym.name(), "str.to_code" if args.len() == 1)
    }

    /// Whether `t` is a range-restricted integer-valued string function.
    ///
    /// All functions in `is_reducible_int_app` have restricted ranges under
    /// SMT-LIB 2.6 semantics:
    /// - `str.to_int`: {-1} ∪ ℤ≥0
    /// - `str.indexof`: {-1} ∪ ℤ≥0
    /// - `str.to_code`: {-1} ∪ [0, 196607]
    ///
    /// The LIA solver treats these as uninterpreted and cannot enforce range
    /// constraints. When the function argument is unresolved and a positive
    /// equality asserts a specific value, this classification determines
    /// whether the solver must remain incomplete.
    pub(in super::super) fn is_range_restricted_int_app(terms: &TermStore, t: TermId) -> bool {
        Self::is_reducible_int_app(terms, t)
    }

    /// Whether `val` is in the valid output range of the function `t`.
    ///
    /// Returns `false` if the value is provably outside the function's range,
    /// meaning the equality `t = val` is unsatisfiable regardless of arguments.
    /// When `state` is available, uses length information to narrow str.to_code
    /// range (#6353).
    pub(in super::super) fn is_in_valid_range(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        val: &BigInt,
    ) -> bool {
        let Some((min, max)) = Self::int_app_bounds_with_state(terms, Some(state), t) else {
            return true;
        };
        *val >= min && max.is_none_or(|m| *val <= m)
    }

    pub(in super::super) fn relation_for_int_app(
        op: &str,
        func_on_left: bool,
        expected_truth: bool,
    ) -> Option<IntRelation> {
        match (op, func_on_left, expected_truth) {
            ("<", true, true) => Some(IntRelation::Lt),
            ("<", true, false) => Some(IntRelation::Ge),
            ("<", false, true) => Some(IntRelation::Gt),
            ("<", false, false) => Some(IntRelation::Le),
            ("<=", true, true) => Some(IntRelation::Le),
            ("<=", true, false) => Some(IntRelation::Gt),
            ("<=", false, true) => Some(IntRelation::Ge),
            ("<=", false, false) => Some(IntRelation::Lt),
            _ => None,
        }
    }

    pub(in super::super) fn relation_holds(
        relation: IntRelation,
        lhs: &BigInt,
        rhs: &BigInt,
    ) -> bool {
        match relation {
            IntRelation::Lt => lhs < rhs,
            IntRelation::Le => lhs <= rhs,
            IntRelation::Gt => lhs > rhs,
            IntRelation::Ge => lhs >= rhs,
        }
    }

    pub(in super::super) fn range_has_witness_for_relation(
        terms: &TermStore,
        state: &SolverState,
        func_term: TermId,
        relation: IntRelation,
        bound: &BigInt,
    ) -> bool {
        let Some((min, max)) = Self::int_app_bounds_with_state(terms, Some(state), func_term)
        else {
            return true;
        };
        match relation {
            IntRelation::Lt => &min < bound,
            IntRelation::Le => &min <= bound,
            IntRelation::Gt => max.is_none_or(|m| &m > bound),
            IntRelation::Ge => max.is_none_or(|m| &m >= bound),
        }
    }

    /// State-aware integer function bounds.
    ///
    /// When `state` is provided and the function is `str.to_code(x)` with
    /// `len(x) = 1` known, the range narrows from `{-1} ∪ [0, 196607]` to
    /// `[0, 196607]`. The `-1` return value only occurs when `len(x) != 1`,
    /// so the length constraint eliminates it.
    ///
    /// This prevents false SAT on assertions like `(< (str.to_code x) 0)`
    /// when `(= (str.len x) 1)` is asserted (#6353).
    pub(in super::super) fn int_app_bounds_with_state(
        terms: &TermStore,
        state: Option<&SolverState>,
        t: TermId,
    ) -> Option<(BigInt, Option<BigInt>)> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.to_int" | "str.to.int" | "str.indexof" => Some((BigInt::from(-1), None)),
            "str.to_code" if args.len() == 1 => {
                // str.to_code(x) returns -1 when len(x) != 1, and a value
                // in [0, 196607] when len(x) = 1. If len(x) = 1 is known
                // via the solver state, tighten the lower bound to 0.
                let len_is_one = state
                    .is_some_and(|s| s.known_length_full(terms, args[0]).is_some_and(|n| n == 1));
                let min = if len_is_one {
                    BigInt::from(0)
                } else {
                    BigInt::from(-1)
                };
                Some((min, Some(BigInt::from(196_607))))
            }
            "str.to_code" => Some((BigInt::from(-1), Some(BigInt::from(196_607)))),
            _ => None,
        }
    }
}
