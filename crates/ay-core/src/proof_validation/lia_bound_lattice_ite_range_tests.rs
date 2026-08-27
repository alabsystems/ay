// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the `ite`-of-integer-constants RANGE sub-check.
//!
//! Same three layers as the parent module. The independent evaluator here is a
//! plain `i64` interpreter written in this file: it walks the term directly and
//! shares no code with the recognizer — no `parse_int_comparison_row`, no
//! coefficient map, no canonicalisation.

use super::*;
use crate::term::{Symbol, TermData};

/// Which guard the ITE-range sub-check owes to which test. Every entry was
/// checked by DELETING or WEAKENING the guard, running the named test,
/// observing the failure, and restoring the guard.
const ITE_RANGE_GUARD_LEDGER: &[(&str, &str)] = &[
    (
        "BOTH branches must be integer constants",
        "rejects_an_ite_with_a_symbolic_branch",
    ),
    (
        "the range is [min, max] of the branches, not one of them",
        "rejects_a_bound_inside_the_branch_range",
    ),
    (
        "the bound DIRECTION is honoured (upper vs lower)",
        "sweep_ite_range_family_never_accepts_a_falsifiable_clause",
    ),
    (
        "negation PARITY, so a double negation is not read as a single one",
        "sweep_ite_range_family_never_accepts_a_falsifiable_clause",
    ),
    (
        "the form must be a SINGLE atom at coefficient exactly 1 (SOUNDNESS)",
        "rejects_a_scaled_ite_lower_bound_outside_the_unscaled_range",
    ),
    (
        "the ITE condition is never read, so no branch is assumed",
        "accepts_the_measured_dillig32_shapes",
    ),
    (
        "the form must be a SINGLE atom, not the first of several (SOUNDNESS)",
        "rejects_a_two_atom_form_containing_an_ite",
    ),
    (
        "SCOPE: the literal cap. Honestly GREEN under mutation - a work bound \
         whose dropped rows only weaken the hypothesis being refuted",
        "(none)",
    ),
];

// ===== the independent evaluator =====

/// Evaluate an `Int`-sorted term under `assignment` (variable name -> value).
fn eval_int(terms: &TermStore, term: TermId, assignment: &[(&str, i64)]) -> i64 {
    match terms.get(term) {
        TermData::Const(crate::Constant::Int(n)) => {
            use num_traits::ToPrimitive;
            n.to_i64().expect("test constants fit in i64")
        }
        TermData::Var(name, _) => {
            assignment
                .iter()
                .find(|(key, _)| key == name)
                .expect("every variable of a test fixture is assigned")
                .1
        }
        TermData::Ite(condition, then_branch, else_branch) => {
            let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
            if eval_bool(terms, condition, assignment) {
                eval_int(terms, then_branch, assignment)
            } else {
                eval_int(terms, else_branch, assignment)
            }
        }
        TermData::App(Symbol::Named(name), args) => {
            let (name, args) = (name.clone(), args.clone());
            let values: Vec<i64> = args
                .iter()
                .map(|&arg| eval_int(terms, arg, assignment))
                .collect();
            match name.as_str() {
                "+" => values.iter().sum(),
                "*" => values.iter().product(),
                "-" if values.len() == 1 => -values[0],
                "-" => values[0] - values[1..].iter().sum::<i64>(),
                other => panic!("the independent evaluator does not model `{other}`"),
            }
        }
        other => panic!("the independent evaluator does not model {other:?}"),
    }
}

/// Evaluate a `Bool`-sorted term under `assignment`.
fn eval_bool(terms: &TermStore, term: TermId, assignment: &[(&str, i64)]) -> bool {
    match terms.get(term) {
        TermData::Const(crate::Constant::Bool(value)) => *value,
        TermData::Not(inner) => !eval_bool(terms, *inner, assignment),
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let (name, left, right) = (name.clone(), args[0], args[1]);
            let (l, r) = (
                eval_int(terms, left, assignment),
                eval_int(terms, right, assignment),
            );
            match name.as_str() {
                "<=" => l <= r,
                "<" => l < r,
                ">=" => l >= r,
                ">" => l > r,
                "=" => l == r,
                other => panic!("the independent evaluator does not model `{other}`"),
            }
        }
        other => panic!("the independent evaluator does not model {other:?}"),
    }
}

/// The first assignment in the box falsifying EVERY literal, or `None`.
fn falsifying_point(
    terms: &TermStore,
    clause: &[TermId],
    names: &[&'static str],
    range: std::ops::RangeInclusive<i64>,
) -> Option<Vec<(&'static str, i64)>> {
    let values: Vec<i64> = range.collect();
    let mut point: Vec<(&str, i64)> = names.iter().map(|&name| (name, 0)).collect();
    let total = values.len().pow(u32::try_from(names.len()).unwrap());
    for index in 0..total {
        let mut rest = index;
        for slot in 0..names.len() {
            point[slot].1 = values[rest % values.len()];
            rest /= values.len();
        }
        if clause
            .iter()
            .all(|&literal| !eval_bool(terms, literal, &point))
        {
            return Some(point.iter().map(|&(n, v)| (n, v)).collect());
        }
    }
    None
}

// ===== fixture helpers =====

fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn int_const(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

/// `(ite (= C 0) 1 0)` — the measured atom.
fn measured_ite(terms: &mut TermStore, c: TermId) -> TermId {
    let zero = int_const(terms, 0);
    let one = int_const(terms, 1);
    let condition = app(terms, "=", vec![c, zero], Sort::Bool);
    terms.mk_ite(condition, one, zero)
}

// ===== the measured population =====

/// All four `dillig32_000` conflict shapes and the `half_true_modif_m_000` one,
/// each valid from the single ITE literal alone, each with the rest of the
/// clause present exactly as recorded.
#[test]
fn accepts_the_measured_dillig32_shapes() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let d = terms.mk_var("D", Sort::Int);
    let e = terms.mk_var("E", Sort::Int);
    let ite = measured_ite(&mut terms, c);
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let hundred = int_const(&mut terms, 100);
    let two = int_const(&mut terms, 2);
    let two_e = app(&mut terms, "*", vec![e, two], Sort::Int);
    let two_e_le_d = app(&mut terms, "<=", vec![two_e, d], Sort::Bool);
    let not_two_e_le_d = terms.mk_not_raw(two_e_le_d);
    let padding = terms.mk_not_raw(not_two_e_le_d);
    let zero_le_c = app(&mut terms, "<=", vec![zero, c], Sort::Bool);
    let not_zero_le_c = terms.mk_not_raw(zero_le_c);
    let c_le_one = app(&mut terms, "<=", vec![c, one], Sort::Bool);
    let not_c_le_one = terms.mk_not_raw(c_le_one);
    let hundred_le_e = app(&mut terms, "<=", vec![hundred, e], Sort::Bool);
    let not_hundred_le_e = terms.mk_not_raw(hundred_le_e);
    let zero_le_d = app(&mut terms, "<=", vec![zero, d], Sort::Bool);
    let not_zero_le_d = terms.mk_not_raw(zero_le_d);

    // 1. `(not (not (<= 0 ITE)))`
    let zero_le_ite = app(&mut terms, "<=", vec![zero, ite], Sort::Bool);
    let not_zero_le_ite = terms.mk_not_raw(zero_le_ite);
    let double_negated_lower = terms.mk_not_raw(not_zero_le_ite);
    // 2. `(not (not (<= ITE 1)))`
    let ite_le_one = app(&mut terms, "<=", vec![ite, one], Sort::Bool);
    let not_ite_le_one = terms.mk_not_raw(ite_le_one);
    let double_negated_upper = terms.mk_not_raw(not_ite_le_one);
    // 3/5. `(not (< ITE 0))`
    let ite_lt_zero = app(&mut terms, "<", vec![ite, zero], Sort::Bool);
    let not_ite_lt_zero = terms.mk_not_raw(ite_lt_zero);
    // 4. `(not (< 1 ITE))`
    let one_lt_ite = app(&mut terms, "<", vec![one, ite], Sort::Bool);
    let not_one_lt_ite = terms.mk_not_raw(one_lt_ite);

    for clause in [
        vec![not_zero_le_c, padding, double_negated_lower],
        vec![not_c_le_one, padding, double_negated_upper],
        vec![
            padding,
            not_zero_le_c,
            not_hundred_le_e,
            not_zero_le_d,
            not_ite_lt_zero,
        ],
        vec![
            padding,
            not_c_le_one,
            not_hundred_le_e,
            not_zero_le_d,
            not_one_lt_ite,
        ],
    ] {
        assert!(
            recognize_int_bound_lattice_gap(&terms, &clause),
            "the measured shape must be accepted: {clause:?}"
        );
        assert!(
            falsifying_point(&terms, &clause, &["C", "D", "E"], -3..=3).is_none(),
            "an accepted clause must be a tautology over the box"
        );
    }
    assert_eq!(ITE_RANGE_GUARD_LEDGER.len(), 8);
}

// ===== adversarial negatives =====

/// A bound INSIDE the branch range proves nothing. `(not (< (ite (= C 0) 1 0) 1))`
/// is falsified at `C = 1`: the else-branch `0` is `< 1`, so the literal is
/// false and the clause has nothing else.
#[test]
fn rejects_a_bound_inside_the_branch_range() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let ite = measured_ite(&mut terms, c);
    let one = int_const(&mut terms, 1);
    let ite_lt_one = app(&mut terms, "<", vec![ite, one], Sort::Bool);
    let literal = terms.mk_not_raw(ite_lt_one);
    let zero = int_const(&mut terms, 0);
    let zero_le_c = app(&mut terms, "<=", vec![zero, c], Sort::Bool);
    let clause = vec![terms.mk_not_raw(zero_le_c), literal];
    let point = falsifying_point(&terms, &clause, &["C"], -3..=3)
        .expect("this negative's clause must be falsifiable");
    assert!(point.iter().any(|&(name, value)| name == "C" && value >= 0));
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

/// A SYMBOLIC branch leaves the atom unbounded. Falsified at `C = 1, S = -5`.
#[test]
fn rejects_an_ite_with_a_symbolic_branch() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let s = terms.mk_var("S", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let condition = app(&mut terms, "=", vec![c, zero], Sort::Bool);
    let one = int_const(&mut terms, 1);
    let ite = terms.mk_ite(condition, one, s);
    let ite_lt_zero = app(&mut terms, "<", vec![ite, zero], Sort::Bool);
    let clause = vec![terms.mk_not_raw(ite_lt_zero)];
    let point = falsifying_point(&terms, &clause, &["C", "S"], -3..=3)
        .expect("this negative's clause must be falsifiable");
    assert!(point.iter().any(|&(name, value)| name == "S" && value < 0));
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

/// A SCALED form is out of scope: the rule computes the range of the atom, not
/// of `2 * atom`. The clause here is valid, so the decline is a deliberate
/// boundary and is recorded as SCOPE.
#[test]
fn rejects_a_scaled_ite_form() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let ite = measured_ite(&mut terms, c);
    let two = int_const(&mut terms, 2);
    let zero = int_const(&mut terms, 0);
    let scaled = app(&mut terms, "*", vec![ite, two], Sort::Int);
    let scaled_lt_zero = app(&mut terms, "<", vec![scaled, zero], Sort::Bool);
    let clause = vec![terms.mk_not_raw(scaled_lt_zero)];
    assert!(falsifying_point(&terms, &clause, &["C"], -3..=3).is_none());
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

/// The coefficient guard is a SOUNDNESS guard, not only a scope one. Reading
/// `2 * ITE` against the UNSCALED range `[0, 1]` would accept
/// `(cl (not (<= 2 (* 2 ITE))))`, which is FALSE at `C = 0`: the then-branch
/// makes `ITE = 1`, so `2 * ITE = 2` and the literal is false.
#[test]
fn rejects_a_scaled_ite_lower_bound_outside_the_unscaled_range() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let ite = measured_ite(&mut terms, c);
    let two = int_const(&mut terms, 2);
    let scaled = app(&mut terms, "*", vec![ite, two], Sort::Int);
    let two_le_scaled = app(&mut terms, "<=", vec![two, scaled], Sort::Bool);
    let clause = vec![terms.mk_not_raw(two_le_scaled)];
    let point = falsifying_point(&terms, &clause, &["C"], -3..=3)
        .expect("this negative's clause must be falsifiable");
    assert!(point.iter().any(|&(name, value)| name == "C" && value == 0));
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

/// The SINGLE-atom guard is a soundness guard too: reading only the FIRST
/// entry of a two-atom form would compare a bound on `ITE + X` against `ITE`'s
/// own range. `(cl (not (< (+ ITE X) 0)))` is FALSE at `C = 1, X = -5` — the
/// else-branch makes `ITE = 0`, so `ITE + X = -5 < 0` and the literal is false.
/// Both operand orders are covered, so the `BTreeMap` iteration order cannot
/// make the test pass by accident.
#[test]
fn rejects_a_two_atom_form_containing_an_ite() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let ite = measured_ite(&mut terms, c);
    let x = terms.mk_var("X", Sort::Int);
    let zero = int_const(&mut terms, 0);
    for operands in [vec![ite, x], vec![x, ite]] {
        let sum = app(&mut terms, "+", operands, Sort::Int);
        let sum_lt_zero = app(&mut terms, "<", vec![sum, zero], Sort::Bool);
        let clause = vec![terms.mk_not_raw(sum_lt_zero)];
        let point = falsifying_point(&terms, &clause, &["C", "X"], -5..=5)
            .expect("this negative's clause must be falsifiable");
        assert!(point.iter().any(|&(name, value)| name == "X" && value < 0));
        assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    }
}

/// A non-`Int` `ite` never reaches the rule: `parse_int_comparison_row` fails
/// closed on a `Real` form, and the range argument is integral.
#[test]
fn rejects_a_real_sorted_ite() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("Cr", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let condition = app(&mut terms, "=", vec![c, zero], Sort::Bool);
    let ite = terms.mk_ite(condition, one, zero);
    let ite_lt_zero = app(&mut terms, "<", vec![ite, zero], Sort::Bool);
    let clause = vec![terms.mk_not_raw(ite_lt_zero)];
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

// ===== the exhaustive sweep =====

/// EXHAUSTIVE over every `(k1, k2, operator, bound, negation parity, side)`
/// combination, with an irrelevant padding literal: no accepted clause is
/// falsifiable anywhere in a `[-4, 4]^2` box, and the sweep accepts enough
/// clauses that it cannot pass vacuously.
#[test]
fn sweep_ite_range_family_never_accepts_a_falsifiable_clause() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let e = terms.mk_var("E", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let padding = {
        let bound = app(&mut terms, "<=", vec![zero, e], Sort::Bool);
        terms.mk_not_raw(bound)
    };
    let mut clauses = 0usize;
    let mut accepted = 0usize;
    for k1 in -2i64..=2 {
        for k2 in -2i64..=2 {
            let then_branch = int_const(&mut terms, k1);
            let else_branch = int_const(&mut terms, k2);
            let condition = app(&mut terms, "=", vec![c, zero], Sort::Bool);
            let ite = terms.mk_ite(condition, then_branch, else_branch);
            for operator in ["<=", "<", ">=", ">"] {
                for bound in -3i64..=3 {
                    let bound_term = int_const(&mut terms, bound);
                    for swapped in [false, true] {
                        let args = if swapped {
                            vec![bound_term, ite]
                        } else {
                            vec![ite, bound_term]
                        };
                        let atom = app(&mut terms, operator, args, Sort::Bool);
                        let mut literal = atom;
                        for nots in 0..3 {
                            if nots > 0 {
                                literal = terms.mk_not_raw(literal);
                            }
                            let clause = vec![padding, literal];
                            clauses += 1;
                            if recognize_int_bound_lattice_gap(&terms, &clause) {
                                accepted += 1;
                                assert!(
                                    falsifying_point(&terms, &clause, &["C", "E"], -4..=4)
                                        .is_none(),
                                    "accepted a FALSIFIABLE clause: k1={k1} k2={k2} \
                                     op={operator} bound={bound} swapped={swapped} nots={nots}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(
        clauses >= 4000,
        "the sweep must cover a real box: {clauses}"
    );
    assert!(
        accepted >= 200,
        "the sweep must not pass vacuously: {accepted} accepts of {clauses}"
    );
}
