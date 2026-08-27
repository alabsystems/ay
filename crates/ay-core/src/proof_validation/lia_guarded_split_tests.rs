// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the guarded-split lattice recognizer.
//!
//! * `accepts_*` pin the shape the rule is FOR — the #4751 guarded
//!   mod-witness closer head, distilled to its mechanism: a negated goal
//!   disjunction whose strictly-integer branch needs equality substitution
//!   plus the attainable-value gap, next to a rationally-refutable branch;
//! * `rejects_*` are adversarial negatives, and EVERY ONE names the concrete
//!   assignment that falsifies the clause (or the exact fail-closed guard it
//!   defends), so a future loosening cannot be argued to be harmless.

use num_bigint::BigInt;

use super::recognize_int_guarded_split_gap;
use crate::{Sort, TermId, TermStore};

/// `2q2 + r3 = 2q0 + 2A + 2` as a negated clause literal (the equality HOLDS
/// in the clause's negation).
fn witness_equality(
    terms: &mut TermStore,
    q2: TermId,
    r3: TermId,
    q0: TermId,
    a: TermId,
) -> TermId {
    let two = terms.mk_int(BigInt::from(2));
    let two_q2 = terms.mk_mul(vec![two, q2]);
    let lhs = terms.mk_add(vec![two_q2, r3]);
    let two_b = terms.mk_int(BigInt::from(2));
    let two_q0 = terms.mk_mul(vec![two_b, q0]);
    let two_c = terms.mk_int(BigInt::from(2));
    let two_a = terms.mk_mul(vec![two_c, a]);
    let two_const = terms.mk_int(BigInt::from(2));
    let rhs = terms.mk_add(vec![two_q0, two_a, two_const]);
    let eq = terms.mk_eq(lhs, rhs);
    terms.mk_not_raw(eq)
}

/// The distilled #4751 closer head:
///
/// ```text
/// (cl (not (<= 0 r3)) (not (< r3 2)) (not (<= 0 A))
///     (not (= (+ (* 2 q2) r3) (+ (* 2 q0) (* 2 A) 2)))
///     (not (or (not (= r3 0)) (not (<= 0 A)))))
/// ```
///
/// Its negation asserts `0 ≤ r3 < 2`, `A ≥ 0`, the Euclidean witness
/// equality, and the goal disjunction. The `(not (= r3 0))` branch is the
/// strictly-integer one: substituting the equality (pivot `r3`, coefficient
/// one) squeezes the all-even form `2q0 + 2A − 2q2` into `[-1, -1]`, which
/// holds no multiple of 2 — rationally that branch is satisfiable at
/// `q2 = q0 + A + 1/2`, so no Farkas certificate exists and every
/// Farkas-based validator must decline it. The `(not (<= 0 A))` branch is
/// refuted by the plain bounds gap `0 ≤ A ≤ −1`.
fn distilled_head(terms: &mut TermStore) -> Vec<TermId> {
    let a = terms.mk_var("A", Sort::Int);
    let q0 = terms.mk_var("q0", Sort::Int);
    let q2 = terms.mk_var("q2", Sort::Int);
    let r3 = terms.mk_var("r3", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));

    let r3_lower = terms.mk_le(zero, r3);
    let l0 = terms.mk_not_raw(r3_lower);
    let r3_upper = terms.mk_lt(r3, two);
    let l1 = terms.mk_not_raw(r3_upper);
    let a_lower = terms.mk_le(zero, a);
    let l2 = terms.mk_not_raw(a_lower);
    let l3 = witness_equality(terms, q2, r3, q0, a);

    let zero_again = terms.mk_int(BigInt::from(0));
    let r3_zero = terms.mk_eq(r3, zero_again);
    let d1 = terms.mk_not_raw(r3_zero);
    let d2 = terms.mk_not_raw(a_lower);
    let goal = terms.mk_or(vec![d1, d2]);
    let l4 = terms.mk_not_raw(goal);

    vec![l0, l1, l2, l3, l4]
}

#[test]
fn accepts_the_distilled_guarded_mod_witness_head() {
    let mut terms = TermStore::new();
    let clause = distilled_head(&mut terms);
    assert!(
        !super::recognize_int_cut_lattice_gap(&terms, &clause),
        "precondition: the shipped cut rule must decline this head (its \
         linear literals alone are satisfiable, e.g. A=0, r3=0, q2=q0+1), \
         otherwise the guarded-split rule would be unnecessary"
    );
    assert!(
        recognize_int_guarded_split_gap(&terms, &clause),
        "the guarded split must certify the distilled closer head"
    );
}

/// Dropping `(not (<= 0 A))` from the clause leaves the `A ≤ −1` branch
/// unrefuted, and the clause really is falsified at
/// `A = −1, r3 = 0, q0 = 0, q2 = 0`: the bounds and the equality
/// (`0 + 0 = 0 − 2 + 2`) all hold, and the goal disjunction holds through
/// its `(not (<= 0 A))` disjunct, so every clause literal is false.
#[test]
fn rejects_head_without_the_branch_refuting_bound() {
    let mut terms = TermStore::new();
    let clause = distilled_head(&mut terms);
    let without_a_bound: Vec<TermId> = clause
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, literal)| (index != 2).then_some(literal))
        .collect();
    assert!(
        !recognize_int_guarded_split_gap(&terms, &without_a_bound),
        "a clause falsified at A=-1, r3=0, q0=q2=0 must be rejected"
    );
}

/// A `true` disjunct makes the case analysis unclosable — the branch has no
/// constraint to refute — and the clause really is falsifiable (the same
/// linear literals as the accept, with the disjunction satisfied through
/// `true` at `A = 0, r3 = 0, q0 = 0, q2 = 1`).
#[test]
fn rejects_head_whose_disjunction_carries_a_true_disjunct() {
    let mut terms = TermStore::new();
    let mut clause = distilled_head(&mut terms);
    let truth = terms.mk_bool(true);
    let zero = terms.mk_int(BigInt::from(0));
    let r3 = terms.mk_var("r3", Sort::Int);
    let r3_zero = terms.mk_eq(r3, zero);
    let d1 = terms.mk_not_raw(r3_zero);
    // Raw application: `mk_or` would fold the `true` disjunct away, and the
    // closer heads carry exactly such raw rebuilt disjunctions.
    let goal = terms.mk_app(crate::term::Symbol::named("or"), [d1, truth], Sort::Bool);
    let last = clause.len() - 1;
    clause[last] = terms.mk_not_raw(goal);
    assert!(
        !recognize_int_guarded_split_gap(&terms, &clause),
        "an or-literal with a `true` disjunct can never close the case split"
    );
}

/// Without any negated-disjunction literal there is nothing to split on;
/// the rule's whole license is the case analysis, so it must decline even
/// though other rules may accept such clauses.
#[test]
fn rejects_clause_without_a_negated_disjunction() {
    let mut terms = TermStore::new();
    let clause = distilled_head(&mut terms);
    let without_or: Vec<TermId> = clause[..clause.len() - 1].to_vec();
    assert!(
        !recognize_int_guarded_split_gap(&terms, &without_or),
        "no split literal: the base facts alone are satisfiable \
         (A=0, r3=0, q2=q0+1) and the rule must not invent a refutation"
    );
}

/// The lattice step is licensed by integrality, so `Real`-sorted quotient
/// witnesses in the branch equality must fail the candidate. With
/// `q0, q2 : Real`, the parity branch is satisfiable at
/// `q2 = q0 + A + 1/2` and `r3 = 1`, so accepting would be a false
/// certificate. `int_linear_diff` fails closed on the real-sorted equality,
/// leaving that branch unrefuted.
#[test]
fn rejects_real_sorted_witness() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let q0 = terms.mk_var("q0", Sort::Real);
    let q2 = terms.mk_var("q2", Sort::Real);
    let r3 = terms.mk_var("r3", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));

    let r3_lower = terms.mk_le(zero, r3);
    let l0 = terms.mk_not_raw(r3_lower);
    let r3_upper = terms.mk_lt(r3, two);
    let l1 = terms.mk_not_raw(r3_upper);
    let a_lower = terms.mk_le(zero, a);
    let l2 = terms.mk_not_raw(a_lower);
    let real_two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));
    let two_q2 = terms.mk_mul(vec![real_two, q2]);
    let real_r3 = terms.mk_to_real(r3);
    let lhs = terms.mk_add(vec![two_q2, real_r3]);
    let two_q0 = terms.mk_mul(vec![real_two, q0]);
    let real_a = terms.mk_to_real(a);
    let two_a = terms.mk_mul(vec![real_two, real_a]);
    let rhs = terms.mk_add(vec![two_q0, two_a, real_two]);
    let witness = terms.mk_eq(lhs, rhs);
    let l3 = terms.mk_not_raw(witness);

    let zero_again = terms.mk_int(BigInt::from(0));
    let r3_zero = terms.mk_eq(r3, zero_again);
    let d1 = terms.mk_not_raw(r3_zero);
    let d2 = terms.mk_not_raw(a_lower);
    let goal = terms.mk_or(vec![d1, d2]);
    let l4 = terms.mk_not_raw(goal);

    let clause = vec![l0, l1, l2, l3, l4];
    assert!(
        !recognize_int_guarded_split_gap(&terms, &clause),
        "with rational quotients the parity branch is satisfiable, so the \
         clause must be rejected"
    );
}
