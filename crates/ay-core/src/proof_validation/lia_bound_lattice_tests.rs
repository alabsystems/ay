// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the integer bound-lattice recognizer.
//!
//! The tests are organized as the soundness argument itself is:
//!
//! * the `accepts` child module pins the shapes the rule is FOR, each with the
//!   reason it has no rational Farkas certificate;
//! * `rejects_*` are adversarial negatives, and EVERY ONE names the concrete
//!   integer (or rational) assignment that falsifies the clause, so a future
//!   loosening cannot be argued to be harmless;
//! * the `sweeps` child module enumerates a bounded coefficient/bound box
//!   exhaustively and re-evaluates every ACCEPT at every point of an integer
//!   box using a plain-`i64` evaluator that shares no code with the recognizer;
//! * `mutation_*` document, for each guard, the test that fails when the guard
//!   is removed (the removal itself is performed by hand — see the module
//!   comment on `GUARD_MUTATION_LEDGER`).

use num_bigint::BigInt;

use super::lia_bound_lattice::{int_bound_lattice_gap_core, recognize_int_bound_lattice_gap};
use crate::{Sort, TermId, TermStore};

#[path = "lia_bound_lattice_accept_tests.rs"]
mod accepts;
#[path = "lia_bound_lattice_sweep_tests.rs"]
mod sweeps;

/// Which guard in `int_bound_lattice_gap_core` (or in the `parse_int_bound`
/// chain it depends on) each adversarial test defends. Every entry was checked
/// by DELETING the guard, running the named test, observing the failure, and
/// restoring the guard.
const GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "int_linear_diff: `Sort::Int` check on every variable",
        "rejects_real_sorted_form_satisfied_at_one_half",
    ),
    (
        "int_bound_lattice_gap_core: group key is the canonical coefficient map",
        "rejects_bounds_on_overlapping_but_different_linear_forms",
    ),
    (
        "int_bound_lattice_gap_core: both a lower AND an upper bound required",
        "rejects_lower_bound_without_an_upper_bound",
    ),
    (
        "int_bound_lattice_gap_core: `gcd.is_positive()`",
        "rejects_variable_free_form_without_panicking",
    ),
    (
        "int_bound_lattice_gap_core: strict `>` in the attainability test",
        "rejects_range_whose_endpoint_is_attainable",
    ),
    (
        "int_bound_lattice_gap_core: `div_ceil` rounding (not a bare lower > upper)",
        "accepts_scaled_singleton_range_with_no_attainable_point",
    ),
    (
        "int_bound_lattice_gap_core: tightest-bound selection per group",
        "accepts_when_only_the_tightest_pair_of_many_bounds_conflicts",
    ),
];

#[test]
fn guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        GUARD_MUTATION_LEDGER.len(),
        7,
        "every guard in the recognizer must name the test that defends it",
    );
    for (guard, test) in GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

// ---------------------------------------------------------------------------
// A tiny independent literal model.
//
// `LitSpec` is evaluated with plain `i64` arithmetic and shares NO code with
// the recognizer (no `TermStore`, no `parse_linear_expr`, no `BigInt`), so
// agreement between the two is real evidence rather than a tautology.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cmp {
    Le,
    Lt,
}

/// `negated ? not(coeff_x*x + coeff_y*y + constant CMP rhs) : (...)`.
#[derive(Clone, Copy, Debug)]
struct LitSpec {
    coeff_x: i64,
    coeff_y: i64,
    constant: i64,
    cmp: Cmp,
    rhs: i64,
    negated: bool,
}

impl LitSpec {
    fn holds(self, x: i64, y: i64) -> bool {
        let lhs = self.coeff_x * x + self.coeff_y * y + self.constant;
        let atom = match self.cmp {
            Cmp::Le => lhs <= self.rhs,
            Cmp::Lt => lhs < self.rhs,
        };
        atom != self.negated
    }

    fn build(self, terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
        let mut summands = Vec::new();
        if self.coeff_x != 0 {
            let c = terms.mk_int(BigInt::from(self.coeff_x));
            summands.push(terms.mk_mul(vec![c, x]));
        }
        if self.coeff_y != 0 {
            let c = terms.mk_int(BigInt::from(self.coeff_y));
            summands.push(terms.mk_mul(vec![c, y]));
        }
        if self.constant != 0 || summands.is_empty() {
            summands.push(terms.mk_int(BigInt::from(self.constant)));
        }
        let lhs = if summands.len() == 1 {
            summands[0]
        } else {
            terms.mk_add(summands)
        };
        let rhs = terms.mk_int(BigInt::from(self.rhs));
        let atom = match self.cmp {
            Cmp::Le => terms.mk_le(lhs, rhs),
            Cmp::Lt => terms.mk_lt(lhs, rhs),
        };
        if self.negated {
            terms.mk_not(atom)
        } else {
            atom
        }
    }
}

/// True when `spec`'s clause is FALSE at `(x, y)` — i.e. every literal is
/// false there, so the named point refutes the clause's validity.
fn falsified_at(spec: &[LitSpec], x: i64, y: i64) -> bool {
    spec.iter().all(|lit| !lit.holds(x, y))
}

/// Search a box for an integer point falsifying EVERY literal of `spec`.
fn falsifying_point(spec: &[LitSpec], radius: i64) -> Option<(i64, i64)> {
    for x in -radius..=radius {
        for y in -radius..=radius {
            if spec.iter().all(|lit| !lit.holds(x, y)) {
                return Some((x, y));
            }
        }
    }
    None
}

fn build_clause(terms: &mut TermStore, spec: &[LitSpec]) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    spec.iter().map(|lit| lit.build(terms, x, y)).collect()
}

/// `L >= value` for `L = coeff·x`, spelled as the POSITIVE literal `L < value`
/// (whose falsity is the bound). Exercises the positive-literal arm of
/// `parse_int_bound`.
fn lower_bound_on_x(coeff: i64, value: i64) -> LitSpec {
    LitSpec {
        coeff_x: coeff,
        coeff_y: 0,
        constant: 0,
        cmp: Cmp::Lt,
        rhs: value,
        negated: false,
    }
}

/// `L <= value`, spelled as the NEGATED literal `(not (L <= value))`.
fn upper_bound_on_x(coeff: i64, value: i64) -> LitSpec {
    LitSpec {
        coeff_x: coeff,
        coeff_y: 0,
        constant: 0,
        cmp: Cmp::Le,
        rhs: value,
        negated: true,
    }
}

// ---------------------------------------------------------------------------
// Adversarial negatives. Each names the assignment that falsifies the clause.
// ---------------------------------------------------------------------------

#[test]
fn rejects_real_sorted_form_satisfied_at_one_half() {
    // FALSIFYING ASSIGNMENT: r = 1/2 gives 2r = 1, satisfying `2r >= 1` and
    // `2r <= 1` simultaneously, so the clause is NOT valid over the reals.
    // Guard: `int_linear_diff` rejects any non-`Int`-sorted variable.
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));
    let scaled = terms.mk_mul(vec![two, r]);
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let lower = terms.mk_lt(scaled, one);
    let one2 = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let upper = terms.mk_le(scaled, one2);
    let not_upper = terms.mk_not(upper);
    let clause = vec![lower, not_upper];
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

#[test]
fn rejects_bounds_on_two_different_linear_forms() {
    // FALSIFYING ASSIGNMENT: x = 1, y = 0 gives 2x = 2 >= 1 and 3y = 0 <= 0,
    // so both literals are false. Guard: the group key is the coefficient map,
    // so bounds on different forms are never combined.
    let mut terms = TermStore::new();
    let spec = [
        lower_bound_on_x(2, 1),
        LitSpec {
            coeff_x: 0,
            coeff_y: 3,
            constant: 0,
            cmp: Cmp::Le,
            rhs: 0,
            negated: true,
        },
    ];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, 1, 0));
}

#[test]
fn rejects_lower_bound_without_an_upper_bound() {
    // FALSIFYING ASSIGNMENT: x = 5 gives 2x = 10 >= 1 and y = 0 keeps the
    // Boolean-shaped literal false. Guard: a group needs BOTH directions.
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(2, 1), lower_bound_on_x(2, -100)];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsifying_point(&spec, 60).is_some());
}

#[test]
fn rejects_range_whose_endpoint_is_attainable() {
    // FALSIFYING ASSIGNMENT: q = 0 gives 2q = 0, satisfying `2q >= 0` and
    // `2q <= 0`. Guard: the attainability test is STRICT (`>`), so an
    // attainable endpoint rejects.
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(2, 0), upper_bound_on_x(2, 0)];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, 0, 0));
}

#[test]
fn rejects_range_wide_enough_to_contain_a_multiple() {
    // FALSIFYING ASSIGNMENT: q = 1 gives 6q = 6 ∈ [5, 7].
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(6, 5), upper_bound_on_x(6, 7)];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, 1, 0));
}

#[test]
fn rejects_unit_coefficient_singleton_range() {
    // FALSIFYING ASSIGNMENT: x = 3 gives x ∈ [3,3]; gcd 1 divides everything.
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(1, 3), upper_bound_on_x(1, 3)];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, 3, 0));
}

#[test]
fn rejects_coprime_two_variable_form_pinned_to_one() {
    // FALSIFYING ASSIGNMENT: x = -1, y = 1 gives 2x + 3y = 1. gcd(2,3) = 1,
    // so the lattice is all of ℤ and nothing is excluded.
    let mut terms = TermStore::new();
    let spec = [
        LitSpec {
            coeff_x: 2,
            coeff_y: 3,
            constant: 0,
            cmp: Cmp::Lt,
            rhs: 1,
            negated: false,
        },
        LitSpec {
            coeff_x: 2,
            coeff_y: 3,
            constant: 0,
            cmp: Cmp::Le,
            rhs: 1,
            negated: true,
        },
    ];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, -1, 1));
}

#[test]
fn rejects_variable_free_form_without_panicking() {
    // FALSIFYING ASSIGNMENT: EVERY integer x. `(<= (+ x 5) (+ x 1))` is false
    // for all x, and so is `(not (<= (+ x 1) (+ x 5)))` — this clause is a
    // CONTRADICTION, not a tautology.
    //
    // Both literals nevertheless parse as bounds on the same DIFFERENCE form,
    // whose `x` cancels: the coefficient map is EMPTY, so `g = 0`. The term
    // store folds `x - x` to the constant `0` and then folds the comparison to
    // a Boolean, so this cancelling-operand spelling is the only way to reach
    // the empty-coefficient case. Guard: `gcd.is_positive()` — without it
    // `lower.div_ceil(&gcd)` divides by zero and the CHECKER PANICS on
    // attacker-shaped input.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let five = terms.mk_int(BigInt::from(5));
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let x_plus_5 = terms.mk_add(vec![x, five]);
    let lower = terms.mk_le(x_plus_5, x_plus_1);
    let upper = terms.mk_le(x_plus_1, x_plus_5);
    let not_upper = terms.mk_not(upper);
    let clause = vec![lower, not_upper];
    assert!(
        !recognize_int_bound_lattice_gap(&terms, &clause),
        "a variable-free difference form carries no lattice and must be rejected",
    );
    for x in -20..=20i64 {
        assert!(
            !(x + 5 <= x + 1) && (x + 1 <= x + 5),
            "clause is false at x={x}"
        );
    }
}

#[test]
fn rejects_bounds_on_overlapping_but_different_linear_forms() {
    // FALSIFYING ASSIGNMENT: x = 0, y = 1 gives 2x + 3y = 3 >= 1 and 2x = 0
    // <= 1, so both literals are false. The two forms SHARE the variable `x`
    // and even share its coefficient; only the `y` column separates them.
    // Guard: the group key is the WHOLE canonical coefficient map, so a bound
    // on `2x + 3y` is never combined with a bound on `2x`.
    let mut terms = TermStore::new();
    let spec = [
        LitSpec {
            coeff_x: 2,
            coeff_y: 3,
            constant: 0,
            cmp: Cmp::Lt,
            rhs: 1,
            negated: false,
        },
        LitSpec {
            coeff_x: 2,
            coeff_y: 0,
            constant: 0,
            cmp: Cmp::Le,
            rhs: 1,
            negated: true,
        },
    ];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
    assert!(falsified_at(&spec, 0, 1));
}

#[test]
fn rejects_empty_and_single_literal_clauses() {
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(2, 1)];
    let clause = build_clause(&mut terms, &spec);
    assert!(!recognize_int_bound_lattice_gap(&terms, &[]));
    assert!(!recognize_int_bound_lattice_gap(&terms, &clause));
}

#[test]
fn rejects_clause_of_boolean_literals_only() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    assert!(!recognize_int_bound_lattice_gap(&terms, &[p, not_p]));
}
