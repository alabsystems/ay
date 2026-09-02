// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for minimal-core affine conflict narrowing (#23 Stage 2).
//!
//! The general problem: on Bool-guarded equality networks the affine
//! implication check produced FAT conflicts containing EVERY live equation's
//! reasons, so learned clauses did not generalize across the guard space.
//! These tests pin the multiplier-tracking core extraction, the trusted
//! re-verification gate, the fuel fallback, and the kill-switch parser.

use super::*;
use num_rational::BigRational;

/// Build a rational row from integer cells (last cell = constant column).
fn row(cells: &[i64]) -> Vec<BigRational> {
    cells
        .iter()
        .map(|&c| BigRational::from(BigInt::from(c)))
        .collect()
}

// ========================================================================
// Multiplier-tracking candidate extraction
// ========================================================================

/// The candidate core is exactly the participating rows: a chain
/// `x - y = 0`, `y - z = 0` implies `x - z = 0`; unrelated rows about
/// `w`, `u` must NOT appear in the core.
#[test]
fn test_min_core_candidate_is_exactly_participating_rows() {
    // Columns: x, y, z, w, u, constant.
    let rows = vec![
        row(&[1, -1, 0, 0, 0, 0]), // x - y = 0   (participates)
        row(&[0, 1, -1, 0, 0, 0]), // y - z = 0   (participates)
        row(&[0, 0, 0, 1, -1, 5]), // w - u = 5   (irrelevant)
        row(&[0, 0, 0, 1, 0, 7]),  // w = 7       (irrelevant)
    ];
    let target = row(&[1, 0, -1, 0, 0, 0]); // x - z = 0

    let mut fuel = 1_000_000;
    let core = LiaSolver::affine_core_candidate(&rows, &target, &mut fuel)
        .expect("target is in the row span");
    assert_eq!(core, vec![0, 1], "core must be exactly the chain rows");
    assert!(
        LiaSolver::affine_core_verified(&rows, &target, &core),
        "trusted re-verification must accept the true core"
    );
}

/// Rational multipliers: `2x = 4` and `3y = 3` imply `x + y = 3` via
/// multipliers 1/2 and 1/3. Both rows participate; the padding row does not.
#[test]
fn test_min_core_candidate_with_rational_multipliers() {
    // Columns: x, y, z, constant.
    let rows = vec![
        row(&[2, 0, 0, 4]),  // 2x = 4       (multiplier 1/2)
        row(&[0, 0, 5, 10]), // 5z = 10      (irrelevant)
        row(&[0, 3, 0, 3]),  // 3y = 3       (multiplier 1/3)
    ];
    let target = row(&[1, 1, 0, 3]); // x + y = 3

    let mut fuel = 1_000_000;
    let core = LiaSolver::affine_core_candidate(&rows, &target, &mut fuel)
        .expect("target is in the row span");
    assert_eq!(core, vec![0, 2]);
    assert!(LiaSolver::affine_core_verified(&rows, &target, &core));
}

/// A target OUTSIDE the row span must return None (defensive path — the
/// caller only invokes extraction after the trusted test said "implied").
#[test]
fn test_min_core_candidate_rejects_unimplied_target() {
    let rows = vec![
        row(&[1, -1, 0, 0]), // x - y = 0
    ];
    let target = row(&[1, 0, -1, 0]); // x - z = 0: not implied

    let mut fuel = 1_000_000;
    assert!(
        LiaSolver::affine_core_candidate(&rows, &target, &mut fuel).is_none(),
        "target outside the row span must not produce a core"
    );
}

/// Linearly dependent equation sets: whatever combination the elimination
/// picks, the returned candidate must pass the trusted re-verification.
#[test]
fn test_min_core_candidate_on_dependent_rows_still_verifies() {
    // Columns: x, y, constant. Rows 0 and 1 are scalar multiples.
    let rows = vec![
        row(&[1, -1, 0, 0]), // x - y = 0
        row(&[2, -2, 0, 0]), // 2x - 2y = 0 (dependent duplicate)
        row(&[0, 1, -1, 0]), // y - z = 0
    ];
    let target = row(&[1, 0, -1, 0]); // x - z = 0

    let mut fuel = 1_000_000;
    let core = LiaSolver::affine_core_candidate(&rows, &target, &mut fuel)
        .expect("target is in the row span");
    assert!(LiaSolver::affine_core_verified(&rows, &target, &core));
    assert!(
        core.len() <= 2,
        "a 2-row combination suffices, got {core:?}"
    );
}

// ========================================================================
// Trusted re-verification gate
// ========================================================================

/// Re-verification rejects an artificially corrupted core (a strict subset
/// of the true core that no longer implies the target).
#[test]
fn test_min_core_reverification_rejects_corrupted_core() {
    let rows = vec![
        row(&[1, -1, 0, 0, 0, 0]), // x - y = 0
        row(&[0, 1, -1, 0, 0, 0]), // y - z = 0
        row(&[0, 0, 0, 1, -1, 5]), // w - u = 5
    ];
    let target = row(&[1, 0, -1, 0, 0, 0]); // x - z = 0

    // Corrupted: drop the second chain link.
    assert!(
        !LiaSolver::affine_core_verified(&rows, &target, &[0]),
        "x - y = 0 alone must NOT verify x - z = 0"
    );
    // Corrupted: swap in an irrelevant row.
    assert!(
        !LiaSolver::affine_core_verified(&rows, &target, &[0, 2]),
        "an irrelevant row must not substitute for the chain link"
    );
    // Corrupted: out-of-range index must be rejected, not panic.
    assert!(!LiaSolver::affine_core_verified(&rows, &target, &[0, 99]));
    // Empty core cannot imply a nonzero target.
    assert!(!LiaSolver::affine_core_verified(&rows, &target, &[]));
    // Sanity: the true core verifies.
    assert!(LiaSolver::affine_core_verified(&rows, &target, &[0, 1]));
}

// ========================================================================
// Fuel fallback
// ========================================================================

/// Exhausting the fuel budget mid-elimination returns None (the caller then
/// falls back to the fat conflict) instead of producing a partial core.
#[test]
fn test_min_core_fuel_exhaustion_returns_none() {
    let rows = vec![
        row(&[1, -1, 0, 0]), // x - y = 0
        row(&[0, 1, -1, 0]), // y - z = 0
    ];
    let target = row(&[1, 0, -1, 0]); // x - z = 0

    // Generous fuel succeeds.
    let mut fuel = 1_000_000;
    assert!(LiaSolver::affine_core_candidate(&rows, &target, &mut fuel).is_some());

    // Tiny fuel fails closed.
    let mut fuel = 3;
    assert!(
        LiaSolver::affine_core_candidate(&rows, &target, &mut fuel).is_none(),
        "fuel exhaustion must fall back, never return a partial core"
    );
}

/// A bounded-rank abort is "not proved", not a numeric rank. In particular,
/// two coefficient-bound aborts must not compare equal and accidentally
/// validate a core.
#[test]
fn test_rank_coefficient_abort_is_not_rank_zero() {
    let oversized = BigRational::from(BigInt::one() << 256usize);
    let rows = vec![vec![oversized.clone(), BigRational::zero()]];
    let target = vec![oversized, BigRational::zero()];

    assert!(
        !LiaSolver::affine_core_verified(&rows, &target, &[0]),
        "aborted base and augmented ranks must never validate a core"
    );
}

/// Inputs at the coefficient limit can still create an oversized exact
/// intermediate. The pre-operation bound makes that one operation finite,
/// and the post-operation bound declines the partial core.
#[test]
fn test_min_core_intermediate_coefficient_explosion_returns_none() {
    let max_width = (BigInt::one() << 256usize) - BigInt::one();
    let inverse = BigRational::new(BigInt::one(), max_width.clone());
    let rows = vec![vec![inverse.clone(), BigRational::from(max_width.clone())]];
    let target = rows[0].clone();

    let mut fuel = 1_000_000;
    assert!(
        LiaSolver::affine_core_candidate(&rows, &target, &mut fuel).is_none(),
        "normalizing by 1/M creates M^2 and must fail closed"
    );
}

// ========================================================================
// End-to-end through the LIA solver
// ========================================================================

/// Equality chain + irrelevant equalities: the published conflict must
/// contain the chain literals and the disequality, and must NOT contain the
/// irrelevant equality literals (this is the whole point of Stage 2 — the
/// learned clause generalizes across the guard space).
#[test]
fn test_min_core_narrows_solver_conflict_to_chain() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let p = terms.mk_var("p", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    let b_plus_one = terms.mk_add(vec![b, one]);
    let c_minus_one = terms.mk_sub(vec![c, one]);
    let eq_ab = terms.mk_eq(a, b_plus_one); // a = b + 1   (chain)
    let eq_bc = terms.mk_eq(b, c_minus_one); // b = c - 1  (chain)
    let q_plus_one = terms.mk_add(vec![q, one]);
    let eq_pq = terms.mk_eq(p, q_plus_one); // p = q + 1   (irrelevant)
    let eq_ac = terms.mk_eq(a, c); // a != c              (target)

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);
    solver.assert_literal(eq_pq, true);
    solver.assert_literal(eq_ac, false);

    let conflict = solver
        .check_affine_disequality_implication(false)
        .expect("a = b+1, b = c-1, a != c is an affine contradiction");

    assert!(
        conflict.literals.iter().any(|l| l.term == eq_ab && l.value),
        "conflict must keep the first chain link: {conflict:?}"
    );
    assert!(
        conflict.literals.iter().any(|l| l.term == eq_bc && l.value),
        "conflict must keep the second chain link: {conflict:?}"
    );
    assert!(
        conflict
            .literals
            .iter()
            .any(|l| l.term == eq_ac && !l.value),
        "conflict must keep the disequality: {conflict:?}"
    );
    // Min-core narrowing is always on (former `AY_AFFINE_MIN_CORE`
    // kill-switch removed; enabled was the default).
    assert!(
        !conflict.literals.iter().any(|l| l.term == eq_pq),
        "min-core conflict must DROP the irrelevant equality: {conflict:?}"
    );
    assert_eq!(solver.affine_min_core_successes, 1);
    assert_eq!(solver.affine_min_core_attempts, 1);

    // #rank-4 increment 2: the min-core path emits the Gaussian
    // multipliers as a Farkas certificate, and it must pass the shared
    // semantic validator (equality-implication case split).
    let farkas = conflict
        .farkas
        .as_ref()
        .expect("min-core affine conflict must carry a Farkas certificate");
    assert_eq!(farkas.coefficients.len(), conflict.literals.len());
    assert!(farkas.is_valid(), "coefficients must be non-negative");
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &conflict.literals, farkas)
        .expect("affine min-core Farkas certificate must verify semantically");

    // The narrowed conflict is still a real theory contradiction.
    let result = TheoryResult::Unsat(conflict.literals);
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

/// The affine accelerator must decline an otherwise valid implication when a
/// source coefficient exceeds its exact-arithmetic bound. Declining cannot be
/// turned into an affine conflict.
#[test]
fn test_affine_oversized_source_coefficient_returns_no_conflict() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let oversized = terms.mk_int(BigInt::one() << 256usize);
    let scaled_x = terms.mk_mul(vec![oversized, x]);
    let scaled_eq_zero = terms.mk_eq(scaled_x, zero);
    let x_eq_zero = terms.mk_eq(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(scaled_eq_zero, true);
    solver.assert_literal(x_eq_zero, false);

    assert!(
        solver.check_affine_disequality_implication(false).is_none(),
        "coefficient-bound abort must return no implication, never a conflict"
    );
}

/// An armed cooperative timeout is observed by the affine accelerator itself,
/// before it can publish an implication conflict.
#[test]
fn test_affine_immediate_timeout_returns_no_conflict() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let two_x_eq_zero = terms.mk_eq(two_x, zero);
    let x_eq_zero = terms.mk_eq(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(two_x_eq_zero, true);
    solver.assert_literal(x_eq_zero, false);
    solver.set_timeout_callback(|| true);

    assert!(
        solver.check_affine_disequality_implication(false).is_none(),
        "cancelled affine elimination must not publish a conflict"
    );
}

// ========================================================================
// Disequality-attribution regression tests (adversarial-review fix)
// ========================================================================

/// REGRESSION (adversarial review on #rank-4 increment 2):
/// `affine_conflict_farkas` re-parses every CORE EQUATION's reason literal
/// against its row, but used to give the DISEQUALITY reason literal weight 1
/// with NO check that it denotes the target row. A shared disequality whose
/// single propagated reason is a wrong/unrelated literal (simulating a
/// combiner partial-explanation bug) got a shape-valid certificate with
/// weight 1 on that unrelated literal — and the release-mode dispatch arms
/// only ran the shape check. The fix re-parses the diseq reason against the
/// target row and DROPS the certificate on mismatch; the conflict verdict
/// is unchanged.
#[test]
fn test_poisoned_shared_diseq_reason_drops_certificate() {
    use ay_core::TheoryLit;
    use ay_core::TheorySolver;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let ninety_nine = terms.mk_int(BigInt::from(99));
    let eq_ab = terms.mk_eq(a, b); // genuine equation a = b
    let eq_z99 = terms.mk_eq(z, ninety_nine); // unrelated atom, asserted false

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_z99, false);
    // Poisoned propagation: a != b "because" not(z = 99). This simulates a
    // combiner bug producing a wrong single-literal reason for a shared
    // disequality. The conflict set {a=b, not(z=99)} is SATISFIABLE
    // (a=b=0, z=0), so a weight-1 certificate on not(z=99) would be wrong.
    solver.assert_shared_disequality(a, b, &[TheoryLit::new(eq_z99, false)]);

    let conflict = solver
        .check_affine_disequality_implication(false)
        .expect("affine path fires on the poisoned shared diseq");

    // The verdict is unchanged (reasons are trusted for the conflict under
    // the combiner contract), but the certificate must be DROPPED: weight 1
    // on a literal that does not denote the target row certifies the wrong
    // combination, and only the shape check runs on some release arms.
    assert!(
        conflict.farkas.is_none(),
        "certificate must be dropped when the diseq reason literal does not \
         denote the target row: {conflict:?}"
    );
}

/// REGRESSION: the same attribution hole existed in the single-literal
/// `t != t` branch — a shared disequality between syntactically equal sides
/// whose propagated reason is an unrelated literal used to get the weight-1
/// case-split certificate. The certificate must be dropped; the conflict
/// (trusted propagated reasons) is unchanged.
#[test]
fn test_poisoned_trivial_diseq_reason_drops_certificate() {
    use ay_core::TheoryLit;
    use ay_core::TheorySolver;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let ninety_nine = terms.mk_int(BigInt::from(99));
    let eq_ab = terms.mk_eq(a, b); // keeps the equation set non-empty
    let eq_z99 = terms.mk_eq(z, ninety_nine); // unrelated atom, asserted false

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_z99, false);
    // Poisoned propagation: a != a "because" not(z = 99). The target row is
    // empty (a - a = 0), so the branch fires on the reasons alone.
    solver.assert_shared_disequality(a, a, &[TheoryLit::new(eq_z99, false)]);

    let conflict = solver
        .check_affine_disequality_implication(false)
        .expect("trivial t != t branch fires on the poisoned shared diseq");

    assert!(
        conflict.farkas.is_none(),
        "weight-1 certificate must be dropped when the single reason literal \
         does not denote the empty target row: {conflict:?}"
    );
}

/// CONTROL for the attribution fix: a shared disequality whose reason IS the
/// genuine `(= lhs rhs)` atom asserted false still yields a certificate, and
/// it passes the full semantic validator.
#[test]
fn test_genuine_shared_diseq_reason_keeps_certificate() {
    use ay_core::TheoryLit;
    use ay_core::TheorySolver;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = terms.mk_eq(a, b); // equation a = b
    let eq_ba = terms.mk_eq(b, a); // the SAME disequality, operands swapped

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_ba, false);
    // Genuine propagation: b != a because not(b = a); operand order swapped
    // relative to the shared pair to exercise negation-up-to-sign matching.
    solver.assert_shared_disequality(a, b, &[TheoryLit::new(eq_ba, false)]);

    let conflict = solver
        .check_affine_disequality_implication(false)
        .expect("affine path fires on the genuine shared diseq");

    let farkas = conflict
        .farkas
        .as_ref()
        .expect("genuine diseq attribution must keep the certificate");
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &conflict.literals, farkas)
        .expect("the kept certificate must pass the full semantic validator");
}
