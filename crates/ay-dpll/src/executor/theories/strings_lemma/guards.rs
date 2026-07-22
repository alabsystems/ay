// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reason-guard helpers for string lemma clause creation.

use ay_core::term::{Constant, TermData};
use ay_core::{TermId, TheoryLit};

/// Build a reason-guard clause prefix from theory literal reasons.
///
/// Converts each `TheoryLit { term, value }` into a guard literal:
/// - If `value` is true, the guard is `¬term` (negated)
/// - If `value` is false, the guard is `term` (already negated in the reason)
///
/// Returns a `Vec<TermId>` with capacity for `extra_capacity` additional elements
/// so the caller can push conclusion literals without reallocation.
pub(in crate::executor) fn build_reason_guard(
    terms: &mut ay_core::TermStore,
    reason: &[TheoryLit],
    extra_capacity: usize,
) -> Vec<TermId> {
    let mut clause = Vec::with_capacity(reason.len() + extra_capacity);
    for lit in reason {
        let guard = if lit.value {
            terms.mk_not(lit.term)
        } else {
            lit.term
        };
        clause.push(guard);
    }
    clause
}

/// Emit companion EmptySplit clauses for variables referenced in reason guards.
///
/// When a guarded clause (ConstSplit, VarSplit) has a reason guard like
/// `var=""`, the SAT solver needs an explicit decision clause `var="" ∨ var!=""`
/// to be able to flip the guard literal. Without this, the SAT solver may not
/// have the propositional atom for `var=""` in any clause except the guarded
/// one, preventing backtracking from `var=""` to `var!=""` (#6273).
///
/// Scans reason guards for `(= x "")` or `(= "" x)` patterns with
/// `value=true` and emits EmptySplit `[x="", ¬(x="")]` tautology clauses.
pub(in crate::executor) fn emit_guard_empty_splits(
    terms: &mut ay_core::TermStore,
    reason: &[TheoryLit],
) -> Vec<Vec<TermId>> {
    let empty = terms.mk_string(String::new());
    let mut splits = Vec::new();
    for lit in reason {
        if !lit.value {
            continue;
        }
        // Check if lit.term is (= x "") or (= "" x) where one side is empty.
        let (lhs, rhs) = match terms.get(lit.term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => (args[0], args[1]),
            _ => continue,
        };
        let var = if rhs == empty {
            lhs
        } else if lhs == empty {
            rhs
        } else {
            // Also check if either side is a string constant that is empty.
            let lhs_is_empty =
                matches!(terms.get(lhs), TermData::Const(Constant::String(s)) if s.is_empty());
            let rhs_is_empty =
                matches!(terms.get(rhs), TermData::Const(Constant::String(s)) if s.is_empty());
            if rhs_is_empty {
                lhs
            } else if lhs_is_empty {
                rhs
            } else {
                continue;
            }
        };
        // Skip if the variable is itself the empty string constant.
        if matches!(terms.get(var), TermData::Const(Constant::String(s)) if s.is_empty()) {
            continue;
        }
        // Emit EmptySplit: [var="", ¬(var="")]
        let eq = terms.mk_eq(var, empty);
        let neq = terms.mk_not(eq);
        splits.push(vec![eq, neq]);
    }
    splits
}
