// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::quantifier_loop::result_mapping to preserve item paths.

/// #unit-conjunctive: a top-level assertion counts as a unit FACT only when it
/// is a plain ATOM — no Boolean structure, no quantifier. Restricting it this
/// way is what keeps the unit simplification from smuggling in an obligation:
/// only something unconditionally true may be used to simplify.
fn is_unit_atom(terms: &ay_core::TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Forall(..) | TermData::Exists(..) | TermData::Not(..) => false,
        TermData::App(ay_core::Symbol::Named(name), _) => {
            !matches!(name.as_str(), "and" | "or" | "=>" | "not" | "ite" | "xor")
        }
        _ => true,
    }
}

/// Truth of `t` under the top-level unit facts, if determined: `Some(true)` /
/// `Some(false)`, or `None` when the units say nothing about it. Handles a
/// negated atom by flipping its atom's unit value.
fn unit_value(
    terms: &ay_core::TermStore,
    units: &ay_core::kani_compat::DetHashMap<TermId, bool>,
    t: TermId,
) -> Option<bool> {
    if let Some(&v) = units.get(&t) {
        return Some(v);
    }
    if let TermData::Not(inner) = terms.get(t) {
        if let Some(&v) = units.get(inner) {
            return Some(!v);
        }
    }
    None
}

/// Rebuild an evaluated scalar as a constant of exactly `sort`.
///
/// `EvalValue::Rational` represents both SMT `Int` and `Real` values, so the
/// expected term sort is load-bearing: integral Reals must remain Real, Ints
/// must be integral, and bit-vector widths must agree. Any incompatible pair
/// fails closed instead of relying on `mk_eq` to discover a sort mismatch.
fn pin_eval_const_for_sort(
    terms: &mut ay_core::TermStore,
    sort: &ay_core::Sort,
    value: &EvalValue,
) -> Option<TermId> {
    match (sort, value) {
        (ay_core::Sort::Bool, EvalValue::Bool(value)) => Some(terms.mk_bool(*value)),
        (ay_core::Sort::Int, EvalValue::Rational(value)) if value.is_integer() => {
            Some(terms.mk_int(value.numer().clone()))
        }
        (ay_core::Sort::Real, EvalValue::Rational(value)) => Some(terms.mk_rational(value.clone())),
        (ay_core::Sort::BitVec(sort), EvalValue::BitVec { value, width })
            if sort.width == *width =>
        {
            Some(terms.mk_bitvec(value.clone(), *width))
        }
        _ => None,
    }
}
