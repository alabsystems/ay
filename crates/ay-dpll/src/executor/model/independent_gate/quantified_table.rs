// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded normalization for quantified integer point tables.

use ay_core::{Sort, TermData, TermId, TermStore};

/// Return the integer variable selected by a point equality such as `x = 7`.
fn quantified_gate_int_point_variable(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(equality, args) = terms.get(term) else {
        return None;
    };
    if equality.name() != "=" || args.len() != 2 {
        return None;
    }
    for (variable, point) in [(args[0], args[1]), (args[1], args[0])] {
        if matches!(terms.get(variable), TermData::Var(..))
            && terms.sort(variable) == &Sort::Int
            && matches!(terms.get(point), TermData::Const(ay_core::Constant::Int(_)))
        {
            return Some(variable);
        }
    }
    None
}

/// Normalize the large integer-point Boolean-table residue emitted by a
/// printer-table quantified-model check:
///
/// ```text
/// !((x = k) = ((x = k) /\ (x != k_1) /\ ...))
///     <=> (x = k) /\ !((x != k_1) /\ ...)
/// ```
///
/// This exact, linear grammar was used by the former isolated gate solver.
/// Keep it at the checked-solve boundary so migrating to proof-carrying nested
/// decisions does not reintroduce the table-enumeration timeout. Unrecognized
/// shapes remain byte-for-byte unchanged.
fn quantified_gate_simplify_negated_absorbed_bool_eq(
    terms: &mut TermStore,
    assertion: TermId,
) -> TermId {
    const MIN_TABLE_FANOUT: usize = 256;

    let TermData::Not(inner) = terms.get(assertion).clone() else {
        return assertion;
    };
    let TermData::App(equality, equality_args) = terms.get(inner).clone() else {
        return assertion;
    };
    if equality.name() != "="
        || equality_args.len() != 2
        || terms.sort(equality_args[0]) != &Sort::Bool
    {
        return assertion;
    }

    for (pivot, compound) in [
        (equality_args[0], equality_args[1]),
        (equality_args[1], equality_args[0]),
    ] {
        let TermData::App(connective, args) = terms.get(compound).clone() else {
            continue;
        };
        if connective.name() != "and" || args.len() < MIN_TABLE_FANOUT {
            continue;
        }
        let Some(pivot_index) = args.iter().position(|&argument| argument == pivot) else {
            continue;
        };
        let Some(table_variable) = quantified_gate_int_point_variable(terms, pivot) else {
            continue;
        };
        let mut rest = args;
        let _ = rest.remove(pivot_index);
        if !rest.iter().all(|&entry| {
            let TermData::Not(point) = terms.get(entry) else {
                return false;
            };
            quantified_gate_int_point_variable(terms, *point) == Some(table_variable)
        }) {
            continue;
        }
        let residue = terms.mk_and(rest);
        let not_residue = terms.mk_not(residue);
        return terms.mk_and(vec![pivot, not_residue]);
    }

    assertion
}

pub(super) fn simplify(terms: &mut TermStore, assertions: &mut [TermId], enabled: bool) {
    if !enabled {
        return;
    }
    for assertion in assertions {
        *assertion = quantified_gate_simplify_negated_absorbed_bool_eq(terms, *assertion);
    }
}
