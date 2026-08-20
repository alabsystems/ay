// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial audit for the Fourier–Motzkin `Generic` lemma validator.
//!
//! The tests come in DISCRIMINATING PAIRS wherever a single bit decides
//! soundness: the same geometry with a strict bound and with a non-strict one,
//! the same interval closed at zero-width and open at unit width, the same
//! disequality with and without a bound that closes both split branches. A
//! validator that mishandles strictness, that combines same-sign rows, or that
//! smuggles integrality into a rational decision fails at least one member of
//! each pair.

use super::*;
use ay_core::{Proof, Sort, TheoryLemmaKind};

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn int_const(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(n.into())
}

/// The checker must DERIVE the refutation itself.
fn accept(terms: &TermStore, clause: &[TermId], why: &str) {
    if let Err(error) = validate_fourier_motzkin_refutation(terms, ProofId(0), clause) {
        panic!("{why}: unexpected refusal: {error}");
    }
}

/// The negated clause has a rational model (or is out of fragment): accepting
/// it would be a fabricated proof. Returns the refusal for message assertions.
fn refuse(terms: &TermStore, clause: &[TermId], why: &str) -> ProofCheckError {
    let error = validate_fourier_motzkin_refutation(terms, ProofId(0), clause).expect_err(why);
    assert_ne!(
        error,
        ProofCheckError::ResourceLimit,
        "{why}: must refuse on the merits, not by tripping the caller envelope"
    );
    error
}

fn assert_reports_rational_model(error: &ProofCheckError, why: &str) {
    assert!(
        error.to_string().contains("rational model"),
        "{why}: the refusal must come from DECIDING the relaxation satisfiable, \
         not from an incidental cap trip: {error}"
    );
}

// ===========================================================================
// Strictness: the bit that decides whether a proof can be fabricated
// ===========================================================================

/// `x > 0 AND x < 0` is infeasible over any ordered field.
#[test]
fn accepts_opposing_strict_bounds() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_strict_x");
    let zero = int_const(&mut terms, 0);
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    accept(&terms, &clause, "x > 0 and x < 0 have no common solution");
}

/// `x > 0 AND x <= 0` is infeasible only because ONE side is strict. The
/// combined row is `0 < 0`; a validator that forgot to propagate strictness
/// would derive `0 <= 0` and refuse, and one that manufactured strictness
/// would break the companion test below.
#[test]
fn accepts_strict_bound_against_touching_nonstrict_bound() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_touch_strict_x");
    let zero = int_const(&mut terms, 0);
    let gt = terms.mk_gt(x, zero);
    let le = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(le)];

    accept(&terms, &clause, "x > 0 and x <= 0 have no common solution");
}

/// COMPANION NEGATIVE: `x >= 0 AND x <= 0` is SATISFIABLE (x = 0). The
/// elimination derives `0 <= 0`, which is true. Reporting this infeasible is
/// exactly the strictness bug that fabricates proofs.
#[test]
fn refuses_touching_nonstrict_bounds() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_touch_loose_x");
    let zero = int_const(&mut terms, 0);
    let ge = terms.mk_ge(x, zero);
    let le = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not_raw(ge), terms.mk_not_raw(le)];

    let error = refuse(&terms, &clause, "x = 0 satisfies x >= 0 and x <= 0");
    assert_reports_rational_model(&error, "touching non-strict bounds");
}

/// THE INTEGRALITY TRAP. `x > 0 AND x < 1` over the INTEGERS is infeasible,
/// and `x` here is `Int`-sorted — but this kernel decides over the RATIONALS,
/// where `x = 1/2` is a model. Claiming infeasibility would import an
/// integrality argument the elimination never made.
#[test]
fn refuses_open_unit_interval_that_is_only_integer_infeasible() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_unit_x");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, one);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    let error = refuse(
        &terms,
        &clause,
        "x = 1/2 satisfies x > 0 and x < 1 over the rationals",
    );
    assert_reports_rational_model(&error, "open unit interval");

    // The equality-span fast path must not accept it either.
    super::super::nia_linear_ideal::validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect_err("the span rule has no order content and must also refuse");
}

/// A second integrality trap without any inequality: `2x = 1` has the rational
/// model `x = 1/2`, so the clause `(not (= (* 2 x) 1))` — VALID over the
/// integers — must be refused here.
#[test]
fn refuses_integer_only_equation_with_a_rational_solution() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_halfint_x");
    let one = int_const(&mut terms, 1);
    let two = int_const(&mut terms, 2);
    let two_x = terms.mk_mul(vec![two, x]);
    let equation = terms.mk_eq(two_x, one);
    let clause = vec![terms.mk_not_raw(equation)];

    let error = refuse(&terms, &clause, "2x = 1 is solvable over the rationals");
    assert_reports_rational_model(&error, "2x = 1");
}

// ===========================================================================
// Multi-round elimination
// ===========================================================================

/// `x < y AND y < z AND x >= z` is infeasible: two elimination rounds.
#[test]
fn accepts_strict_transitivity_chain() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_chain_x");
    let y = int_var(&mut terms, "fm_chain_y");
    let z = int_var(&mut terms, "fm_chain_z");
    let xy = terms.mk_lt(x, y);
    let yz = terms.mk_lt(y, z);
    let xz = terms.mk_lt(x, z);
    let clause = vec![terms.mk_not_raw(xy), terms.mk_not_raw(yz), xz];

    accept(&terms, &clause, "x < y < z contradicts x >= z");
}

/// Same three-variable geometry with ONE strict link relaxed. `x <= y AND
/// y <= z AND x >= z` is satisfiable (x = y = z), so the chain must be refused.
/// Paired with the test above this pins strictness propagation across two
/// elimination rounds, not just one.
#[test]
fn refuses_nonstrict_transitivity_chain() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_loose_chain_x");
    let y = int_var(&mut terms, "fm_loose_chain_y");
    let z = int_var(&mut terms, "fm_loose_chain_z");
    let xy = terms.mk_le(x, y);
    let yz = terms.mk_le(y, z);
    let xz = terms.mk_lt(x, z);
    let clause = vec![terms.mk_not_raw(xy), terms.mk_not_raw(yz), xz];

    let error = refuse(&terms, &clause, "x = y = z satisfies the relaxed chain");
    assert_reports_rational_model(&error, "non-strict chain");
}

/// A chain with one strict link IS infeasible: `x <= y AND y < z AND x >= z`.
#[test]
fn accepts_mixed_strictness_transitivity_chain() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_mixed_chain_x");
    let y = int_var(&mut terms, "fm_mixed_chain_y");
    let z = int_var(&mut terms, "fm_mixed_chain_z");
    let xy = terms.mk_le(x, y);
    let yz = terms.mk_lt(y, z);
    let xz = terms.mk_lt(x, z);
    let clause = vec![terms.mk_not_raw(xy), terms.mk_not_raw(yz), xz];

    accept(
        &terms,
        &clause,
        "one strict link suffices to refute the chain",
    );
}

/// Same-sign rows must NEVER be combined: `x <= 0 AND y <= 0` is satisfiable,
/// and every coordinate here has only one sign, so both rows are simply
/// dropped.
#[test]
fn refuses_independent_upper_bounds() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_indep_x");
    let y = int_var(&mut terms, "fm_indep_y");
    let zero = int_const(&mut terms, 0);
    let bx = terms.mk_le(x, zero);
    let by = terms.mk_le(y, zero);
    let clause = vec![terms.mk_not_raw(bx), terms.mk_not_raw(by)];

    let error = refuse(&terms, &clause, "x = y = 0 satisfies both bounds");
    assert_reports_rational_model(&error, "independent upper bounds");
}

// ===========================================================================
// Exact rational scaling
// ===========================================================================

/// `2x <= -1 AND 3x >= 0` needs the multipliers 1/2 and 1/3 to derive
/// `1/2 <= 0`. Floating point or integer-only scaling would miss it.
#[test]
fn accepts_conflict_requiring_exact_rational_multipliers() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_scale_x");
    let zero = int_const(&mut terms, 0);
    let two = int_const(&mut terms, 2);
    let three = int_const(&mut terms, 3);
    let minus_one = int_const(&mut terms, -1);
    let two_x = terms.mk_mul(vec![two, x]);
    let three_x = terms.mk_mul(vec![three, x]);
    let upper = terms.mk_le(two_x, minus_one);
    let lower = terms.mk_ge(three_x, zero);
    let clause = vec![terms.mk_not_raw(upper), terms.mk_not_raw(lower)];

    accept(&terms, &clause, "x <= -1/2 contradicts x >= 0");
}

/// COMPANION NEGATIVE: flipping the constant makes the same scaled system
/// satisfiable (`0 <= x <= 1/2`).
#[test]
fn refuses_scaled_bounds_that_still_overlap() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_scale_ok_x");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let two = int_const(&mut terms, 2);
    let three = int_const(&mut terms, 3);
    let two_x = terms.mk_mul(vec![two, x]);
    let three_x = terms.mk_mul(vec![three, x]);
    let upper = terms.mk_le(two_x, one);
    let lower = terms.mk_ge(three_x, zero);
    let clause = vec![terms.mk_not_raw(upper), terms.mk_not_raw(lower)];

    let error = refuse(&terms, &clause, "x = 0 satisfies 2x <= 1 and 3x >= 0");
    assert_reports_rational_model(&error, "overlapping scaled bounds");
}

// ===========================================================================
// Monomial abstraction stays a RELAXATION
// ===========================================================================

/// A nonlinear product is one opaque coordinate: `x*y > 3 AND x*y < 2` is
/// refuted purely by the order facts about that coordinate.
#[test]
fn accepts_bound_conflict_on_a_nonlinear_monomial() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_mono_x");
    let y = int_var(&mut terms, "fm_mono_y");
    let two = int_const(&mut terms, 2);
    let three = int_const(&mut terms, 3);
    let xy = terms.mk_mul(vec![x, y]);
    let gt = terms.mk_gt(xy, three);
    let lt = terms.mk_lt(xy, two);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    accept(&terms, &clause, "x*y cannot exceed 3 and stay below 2");
}

/// The abstraction must never USE a nonlinear fact. `(>= (* x x) 0)` is a
/// VALID clause over the reals, but its negation `x*x < 0` is satisfiable once
/// `x*x` is an independent coordinate — so this validator must decline. Losing
/// a valid lemma is the safe direction; the unsound direction would be to
/// teach the relaxation that squares are non-negative.
#[test]
fn refuses_square_nonnegativity_it_cannot_see() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_square_x");
    let zero = int_const(&mut terms, 0);
    let square = terms.mk_mul(vec![x, x]);
    let ge = terms.mk_ge(square, zero);

    let error = refuse(
        &terms,
        &[ge],
        "the monomial relaxation has no access to x*x >= 0",
    );
    assert_reports_rational_model(&error, "square non-negativity");
}

/// Distinct monomials stay distinct coordinates: `x*y > 3 AND y*z < 2` says
/// nothing at all.
#[test]
fn refuses_bounds_on_unrelated_monomials() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_unrelated_x");
    let y = int_var(&mut terms, "fm_unrelated_y");
    let z = int_var(&mut terms, "fm_unrelated_z");
    let two = int_const(&mut terms, 2);
    let three = int_const(&mut terms, 3);
    let xy = terms.mk_mul(vec![x, y]);
    let yz = terms.mk_mul(vec![y, z]);
    let gt = terms.mk_gt(xy, three);
    let lt = terms.mk_lt(yz, two);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    let error = refuse(&terms, &clause, "x*y and y*z are unrelated coordinates");
    assert_reports_rational_model(&error, "unrelated monomials");
}

// ===========================================================================
// Bounded disequality case split
// ===========================================================================

/// Antisymmetry: `x <= y AND y <= x AND x != y`. Both split branches close,
/// each against the OPPOSITE bound — the shape the span rule cannot reach.
#[test]
fn accepts_antisymmetry_through_the_disequality_split() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_anti_x");
    let y = int_var(&mut terms, "fm_anti_y");
    let xy = terms.mk_le(x, y);
    let yx = terms.mk_le(y, x);
    let equal = terms.mk_eq(x, y);
    let clause = vec![terms.mk_not_raw(xy), terms.mk_not_raw(yx), equal];

    accept(&terms, &clause, "antisymmetry is a valid order lemma");
    super::super::nia_linear_ideal::validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect_err("antisymmetry needs ORDER reasoning the span rule does not have");
}

/// Drop one bound and antisymmetry becomes satisfiable (`x < y`).
#[test]
fn refuses_antisymmetry_missing_one_bound() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_half_anti_x");
    let y = int_var(&mut terms, "fm_half_anti_y");
    let xy = terms.mk_le(x, y);
    let equal = terms.mk_eq(x, y);
    let clause = vec![terms.mk_not_raw(xy), equal];

    let error = refuse(&terms, &clause, "x < y satisfies x <= y and x != y");
    assert_reports_rational_model(&error, "one-sided antisymmetry");
}

/// BOTH branches must close. `x >= 0 AND x != 0` closes the `x < 0` branch
/// only; `x = 1` is a model, so the lemma must be refused. A validator that
/// accepted after the first infeasible branch fails here.
#[test]
fn refuses_when_only_one_split_branch_closes() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_one_branch_x");
    let zero = int_const(&mut terms, 0);
    let ge = terms.mk_ge(x, zero);
    let equal = terms.mk_eq(x, zero);
    let clause = vec![terms.mk_not_raw(ge), equal];

    let error = refuse(&terms, &clause, "x = 1 satisfies x >= 0 and x != 0");
    assert_reports_rational_model(&error, "single closing branch");
}

/// COMPANION POSITIVE: add the opposite bound and both branches close.
#[test]
fn accepts_when_both_split_branches_close() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_both_branch_x");
    let zero = int_const(&mut terms, 0);
    let ge = terms.mk_ge(x, zero);
    let le = terms.mk_le(x, zero);
    let equal = terms.mk_eq(x, zero);
    let clause = vec![terms.mk_not_raw(ge), terms.mk_not_raw(le), equal];

    accept(&terms, &clause, "0 <= x <= 0 leaves no room for x != 0");
}

/// Two disequalities exercise all four branches.
#[test]
fn accepts_two_way_disequality_split() {
    let mut terms = TermStore::new();
    let zero = int_const(&mut terms, 0);
    let mut clause = Vec::new();
    for name in ["fm_two_split_x", "fm_two_split_y"] {
        let variable = int_var(&mut terms, name);
        let ge = terms.mk_ge(variable, zero);
        let le = terms.mk_le(variable, zero);
        let equal = terms.mk_eq(variable, zero);
        clause.push(terms.mk_not_raw(ge));
        clause.push(terms.mk_not_raw(le));
        clause.push(equal);
    }

    accept(
        &terms,
        &clause,
        "each pinned variable closes both of its branches",
    );
}

/// Surplus disequalities beyond the split cap are DROPPED, which is
/// conservative: the retained order conflict still refutes every branch.
#[test]
fn accepts_order_conflict_alongside_surplus_disequalities() {
    let mut terms = TermStore::new();
    let zero = int_const(&mut terms, 0);
    let mut clause = Vec::new();
    for index in 0..=MAX_NE_CASE_SPLIT {
        let variable = int_var(&mut terms, &format!("fm_surplus_{index}"));
        let equal = terms.mk_eq(variable, zero);
        clause.push(equal);
    }
    let pivot = int_var(&mut terms, "fm_surplus_pivot");
    let gt = terms.mk_gt(pivot, zero);
    let lt = terms.mk_lt(pivot, zero);
    clause.push(terms.mk_not_raw(gt));
    clause.push(terms.mk_not_raw(lt));

    accept(
        &terms,
        &clause,
        "dropping surplus disequalities cannot create a refutation, and the \
         retained order pair already refutes",
    );
}

/// ...and dropping them never manufactures one: the same surplus
/// disequalities WITHOUT the order conflict are satisfiable.
#[test]
fn refuses_surplus_disequalities_on_their_own() {
    let mut terms = TermStore::new();
    let zero = int_const(&mut terms, 0);
    let mut clause = Vec::new();
    for index in 0..=MAX_NE_CASE_SPLIT {
        let variable = int_var(&mut terms, &format!("fm_surplus_only_{index}"));
        let equal = terms.mk_eq(variable, zero);
        clause.push(equal);
    }

    let error = refuse(&terms, &clause, "every variable may simply be nonzero");
    assert_reports_rational_model(&error, "surplus disequalities alone");
}

// ===========================================================================
// Overlap with the equality-span fast path
// ===========================================================================

/// The loop-invariant consecution shape that motivated the span rule is also
/// decided here (its equalities plus the split disequality close both
/// branches), so the span rule really is a FAST PATH and not the only lane.
#[test]
fn accepts_invariant_consecution_through_elimination() {
    let mut terms = TermStore::new();
    let n = int_var(&mut terms, "fm_cons_n");
    let sum = int_var(&mut terms, "fm_cons_sum");
    let counter = int_var(&mut terms, "fm_cons_counter");
    let one = int_const(&mut terms, 1);

    let counter_n = terms.mk_mul(vec![counter, n]);
    let n_n = terms.mk_mul(vec![n, n]);
    let inv_lhs = terms.mk_add(vec![sum, counter_n]);
    let inv = terms.mk_eq(inv_lhs, n_n);

    let sum_next = terms.mk_add(vec![sum, n]);
    let counter_next = terms.mk_sub(vec![counter, one]);
    let counter_next_n = terms.mk_mul(vec![counter_next, n]);
    let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
    let inv_next = terms.mk_eq(inv_next_lhs, n_n);

    let clause = vec![terms.mk_not_raw(inv), inv_next];
    accept(&terms, &clause, "consecution is a polynomial identity");
}

/// The off-by-one consecution variant stays refused on this lane too.
#[test]
fn refuses_broken_invariant_consecution() {
    let mut terms = TermStore::new();
    let n = int_var(&mut terms, "fm_broken_n");
    let sum = int_var(&mut terms, "fm_broken_sum");
    let counter = int_var(&mut terms, "fm_broken_counter");
    let one = int_const(&mut terms, 1);

    let counter_n = terms.mk_mul(vec![counter, n]);
    let n_n = terms.mk_mul(vec![n, n]);
    let inv_lhs = terms.mk_add(vec![sum, counter_n]);
    let inv = terms.mk_eq(inv_lhs, n_n);

    // WRONG update: sum + 1 instead of sum + n.
    let sum_next = terms.mk_add(vec![sum, one]);
    let counter_next = terms.mk_sub(vec![counter, one]);
    let counter_next_n = terms.mk_mul(vec![counter_next, n]);
    let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
    let inv_next = terms.mk_eq(inv_next_lhs, n_n);

    let clause = vec![terms.mk_not_raw(inv), inv_next];
    let error = refuse(&terms, &clause, "the off-by-one update is not implied");
    assert_reports_rational_model(&error, "broken consecution");
}

// ===========================================================================
// Fail-closed boundaries
// ===========================================================================

#[test]
fn refuses_non_arithmetic_clause() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("fm_bool_p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);

    refuse(
        &terms,
        &[p, not_p],
        "a propositional tautology is outside this fragment",
    );
}

#[test]
fn refuses_mixed_sort_relation() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_mixed_int");
    let y = terms.mk_var("fm_mixed_real", Sort::Real);
    let malformed = terms.mk_app(ay_core::Symbol::named("<="), vec![x, y], Sort::Bool);
    let not_malformed = terms.mk_not_raw(malformed);

    refuse(
        &terms,
        &[not_malformed, malformed],
        "a forged mixed-sort relation must fail closed",
    );
}

#[test]
fn refuses_more_coordinates_than_the_cap() {
    let mut terms = TermStore::new();
    let zero = int_const(&mut terms, 0);
    let mut summands = Vec::new();
    for index in 0..=MAX_FM_VARIABLES {
        summands.push(int_var(&mut terms, &format!("fm_cap_{index}")));
    }
    let sum = terms.mk_add(summands);
    let bound = terms.mk_le(sum, zero);
    let literal = terms.mk_not_raw(bound);

    let error = decide_fourier_motzkin_refutation(&terms, &[literal])
        .expect_err("more coordinates than the cap must fail closed");
    assert!(
        error.contains("coordinate cap"),
        "unexpected refusal: {error}"
    );
}

#[test]
fn caller_envelope_refusal_is_typed_as_resource_limit() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_envelope_x");
    let zero = int_const(&mut terms, 0);
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    let error = validate_fourier_motzkin_refutation_with_progress(
        &terms,
        ProofId(0),
        &clause,
        &mut |_, _| false,
    )
    .expect_err("a refusing caller envelope must stop the validator");
    assert_eq!(error, ProofCheckError::ResourceLimit);
}

/// An empty clause carries nothing to refute and must not be accepted.
#[test]
fn refuses_empty_clause() {
    let terms = TermStore::new();
    refuse(&terms, &[], "an empty clause has no negation to refute");
}

// ===========================================================================
// Integration with strict checking
// ===========================================================================

/// End-to-end: a `Generic` lemma that ONLY order reasoning can discharge is
/// accepted by the strict checker, while the authored-assumption authentication
/// still fails closed.
#[test]
fn strict_checker_accepts_an_order_only_generic_lemma() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_strict_order_x");
    let y = int_var(&mut terms, "fm_strict_order_y");
    let xy = terms.mk_le(x, y);
    let yx = terms.mk_le(y, x);
    let equal = terms.mk_eq(x, y);
    let not_xy = terms.mk_not_raw(xy);
    let not_yx = terms.mk_not_raw(yx);
    let not_equal = terms.mk_not_raw(equal);

    let mut proof = Proof::new();
    let h_xy = proof.add_assume(xy, None);
    let h_yx = proof.add_assume(yx, None);
    let h_not_equal = proof.add_assume(not_equal, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "LIA",
        vec![not_xy, not_yx, equal],
        TheoryLemmaKind::Generic,
    );
    let after_first = proof.add_resolution(vec![not_yx, equal], xy, lemma, h_xy);
    let after_second = proof.add_resolution(vec![equal], yx, after_first, h_yx);
    proof.add_resolution(vec![], equal, after_second, h_not_equal);

    crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[xy, yx, not_equal]))
        .expect("antisymmetry is semantically revalidated, so strict checking must pass");

    crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[xy, yx]))
        .expect_err("omitting an authored assumption must still fail closed");
}

/// The companion NEGATIVE at the integration boundary: a `Generic` lemma whose
/// negation is satisfiable stays a hard strict-mode rejection.
#[test]
fn strict_checker_still_rejects_an_unrefutable_generic_lemma() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "fm_strict_bad_x");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, one);
    let not_gt = terms.mk_not_raw(gt);
    let not_lt = terms.mk_not_raw(lt);

    let mut proof = Proof::new();
    let h_gt = proof.add_assume(gt, None);
    let h_lt = proof.add_assume(lt, None);
    let lemma =
        proof.add_theory_lemma_with_kind("LIA", vec![not_gt, not_lt], TheoryLemmaKind::Generic);
    let after_first = proof.add_resolution(vec![not_lt], gt, lemma, h_gt);
    proof.add_resolution(vec![], lt, after_first, h_lt);

    let error = crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[gt, lt]))
        .expect_err("0 < x < 1 has a rational model, so the lemma must stay rejected");
    assert!(
        matches!(error, ProofCheckError::UnsupportedTheoryLemmaKind { .. }),
        "unexpected strict-mode outcome: {error}"
    );
}
