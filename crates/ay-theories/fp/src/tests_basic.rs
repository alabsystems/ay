// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

#[test]
fn test_fp_precision() {
    assert_eq!(FpPrecision::Float32.exponent_bits(), 8);
    assert_eq!(FpPrecision::Float32.significand_bits(), 24);
    assert_eq!(FpPrecision::Float32.total_bits(), 32);
    assert_eq!(FpPrecision::Float32.bias(), 127);

    assert_eq!(FpPrecision::Float64.exponent_bits(), 11);
    assert_eq!(FpPrecision::Float64.significand_bits(), 53);
    assert_eq!(FpPrecision::Float64.total_bits(), 64);
    assert_eq!(FpPrecision::Float64.bias(), 1023);
}

#[test]
fn test_rounding_modes() {
    assert_eq!(RoundingMode::from_name("RNE"), Some(RoundingMode::RNE));
    assert_eq!(
        RoundingMode::from_name("roundNearestTiesToEven"),
        Some(RoundingMode::RNE)
    );
    assert_eq!(RoundingMode::from_name("RTZ"), Some(RoundingMode::RTZ));
    assert_eq!(RoundingMode::from_name("invalid"), None);
}

#[test]
fn test_make_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let pos_zero = solver.make_zero(FpPrecision::Float32, false);
    assert_eq!(pos_zero.exponent.len(), 8);
    assert_eq!(pos_zero.significand.len(), 23);

    let neg_zero = solver.make_zero(FpPrecision::Float32, true);
    assert_eq!(neg_zero.exponent.len(), 8);
}

#[test]
fn test_make_infinity() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let pos_inf = solver.make_infinity(FpPrecision::Float64, false);
    assert_eq!(pos_inf.exponent.len(), 11);
    assert_eq!(pos_inf.significand.len(), 52);
}

#[test]
fn test_make_nan() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let nan = solver.make_nan_value(FpPrecision::Float32);
    assert_eq!(nan.exponent.len(), 8);
    assert_eq!(nan.significand.len(), 23);
}

#[test]
fn test_classification_predicates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let is_nan = solver.bitblast_is_nan(x);
    assert!(is_nan != 0);

    let is_inf = solver.bitblast_is_infinite(x);
    assert!(is_inf != 0);

    let is_zero = solver.bitblast_is_zero(x);
    assert!(is_zero != 0);
}

#[test]
fn test_comparison_predicates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let eq = solver.bitblast_fp_eq(x, y);
    assert!(eq != 0);

    let lt = solver.bitblast_fp_lt(x, y);
    assert!(lt != 0);
}

#[test]
fn test_cnf_generation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let _ = solver.bitblast_is_nan(x);

    let clauses = solver.clauses();
    assert!(!clauses.is_empty());
}

#[test]
fn test_arithmetic_special_cases() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let fp_x = solver.get_fp(x);
    let fp_y = solver.get_fp(y);

    let _ = solver.make_add(&fp_x, &fp_y, RoundingMode::RNE);
    assert!(!solver.clauses().is_empty());

    let _ = solver.make_mul(&fp_x, &fp_y, RoundingMode::RTZ);
    let _ = solver.make_div(&fp_x, &fp_y, RoundingMode::RTP);
    let _ = solver.make_sqrt(&fp_x, RoundingMode::RTN);
}

#[test]
fn test_negation_and_abs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let fp_x = solver.get_fp(x);

    let neg_x = solver.make_neg(&fp_x);
    assert_eq!(neg_x.precision, FpPrecision::Float32);

    let abs_x = solver.make_abs(&fp_x);
    assert_eq!(abs_x.precision, FpPrecision::Float32);
}

#[test]
fn test_min_max() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let fp_x = solver.get_fp(x);
    let fp_y = solver.get_fp(y);

    let min_xy = solver.make_min(&fp_x, &fp_y);
    assert_eq!(min_xy.precision, FpPrecision::Float32);

    let max_xy = solver.make_max(&fp_x, &fp_y);
    assert_eq!(max_xy.precision, FpPrecision::Float32);
}

#[test]
fn test_float16() {
    assert_eq!(FpPrecision::Float16.exponent_bits(), 5);
    assert_eq!(FpPrecision::Float16.significand_bits(), 11);
    assert_eq!(FpPrecision::Float16.total_bits(), 16);
    assert_eq!(FpPrecision::Float16.bias(), 15);
}

#[test]
fn test_float128() {
    assert_eq!(FpPrecision::Float128.exponent_bits(), 15);
    assert_eq!(FpPrecision::Float128.significand_bits(), 113);
    assert_eq!(FpPrecision::Float128.total_bits(), 128);
    assert_eq!(FpPrecision::Float128.bias(), 16383);
}

#[test]
fn test_custom_precision() {
    let custom = FpPrecision::Custom { eb: 6, sb: 10 };
    assert_eq!(custom.exponent_bits(), 6);
    assert_eq!(custom.significand_bits(), 10);
    assert_eq!(custom.total_bits(), 16);
    assert_eq!(custom.bias(), 31);

    assert_eq!(FpPrecision::from_eb_sb(8, 24), FpPrecision::Float32);
    assert_eq!(FpPrecision::from_eb_sb(11, 53), FpPrecision::Float64);
    assert!(matches!(
        FpPrecision::from_eb_sb(6, 10),
        FpPrecision::Custom { .. }
    ));
}

// ---------- Push/pop / reset cache hygiene (#8714) ----------
//
// Ported from Z3 PR #9028 (FP push/pop soundness). These tests pin the
// invariant that ay's FP theory does not leak stale conversion / bit-blast
// state across scope or solver lifetime boundaries.
//
// Background: Z3's `theory_fpa` keeps an `m_conversions` cache mapping
// FP expressions to their BV-lowered form. Entries are inserted at the
// current DPLL scope, but the side-condition clauses linking FP UFs to BV
// counterparts are scoped theory axioms that DPLL deletes on backtrack.
// If a conversion was cached at a base scope (after a user `push`) and the
// side conditions were asserted at a deeper scope that later got popped,
// re-converting the same FP expression hit the cache and short-circuited
// the rewriter — never re-asserting the side conditions. Result: unsound
// UNSAT after pop.
//
// ay is not affected by this bug because:
//   1. `FpSolver` is constructed fresh by `solve_fp()` on every `check-sat`;
//      there is no cross-call cache that could leak state.
//   2. `FpSolver`'s `TheorySolver::push`/`pop` are no-ops by design: the
//      solver owns no scope-dependent cache.
//   3. `FpSolver::reset()` (called from `IncrementalTheoryState::reset`) does
//      clear `term_to_fp` AND `bv_term_bits` — this was fixed in #8619 after
//      a similar bug class (stale BV-to-CNF mappings).
//   4. `FpSolverStandalone` implements a trail-based push/pop that truncates
//      the trail on pop.
//
// The tests below act as regression guards: if someone ever adds a
// persistent FP-expr cache that survives push/pop/reset (the Z3 bug
// shape), these assertions will fail.

#[test]
fn test_fp_reset_clears_term_to_fp_cache_pr_9028_regression() {
    // Ported from Z3 PR #9028 (FP push/pop soundness).
    // Pins that reset() fully clears term_to_fp (FP-term -> decomposed bits)
    // so re-encoding after reset regenerates bit-blast output.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(5, 11));
    let y = terms.mk_var("y", Sort::FloatingPoint(5, 11));

    let mut solver = FpSolver::new(&terms);
    // Force bit-blast of x and y (populates term_to_fp).
    let _ = solver.bitblast_is_nan(x);
    let _ = solver.bitblast_is_nan(y);
    assert!(
        !solver.term_to_fp().is_empty(),
        "term_to_fp must have entries before reset"
    );

    <FpSolver<'_> as ay_core::TheorySolver>::reset(&mut solver);

    assert!(
        solver.term_to_fp().is_empty(),
        "reset() must clear term_to_fp — otherwise stale FP decompositions would \
         leak across incremental calls (Z3 PR #9028 bug class)"
    );
    assert!(
        solver.bv_term_bits().is_empty(),
        "reset() must clear bv_term_bits (fixed in #8619) — otherwise stale \
         BV-to-CNF mappings would leak (Z3 PR #9028 bug class)"
    );
    assert_eq!(
        solver.clauses().len(),
        0,
        "reset() must clear generated clauses"
    );
}

#[test]
fn test_fp_standalone_push_pop_restores_trail() {
    // Ported from Z3 PR #9028 (FP push/pop soundness).
    // Verifies FpSolverStandalone::pop() restores trail state. Under the
    // Z3 bug pattern, scope state survived across pop; ay's trail-based
    // approach truncates correctly.
    use ay_core::TheorySolver;
    let mut solver = FpSolverStandalone::new();
    <FpSolverStandalone as TheorySolver>::push(&mut solver);
    // The standalone impl records trail.len() on push and truncates on pop;
    // with an empty trail, both length and stack should return to 0.
    <FpSolverStandalone as TheorySolver>::pop(&mut solver);
    // Trail should be empty (it was empty before push) and the scope stack
    // should have been drained by the pop.
    // Doing a second pop with no scope to pop is a no-op and must not panic.
    <FpSolverStandalone as TheorySolver>::pop(&mut solver);
}

/// `set_next_var` must actually move the allocator, because an incremental FP
/// lane will use it to make a variable name mean the same SAT variable across
/// check-sats.
///
/// Both `FpSolver` constructors hard-code `next_var: 1`. That is safe today only
/// because nothing is retained between solves — `solve_fp` builds a fresh solver
/// every check-sat. Once any FP clause outlives a solve, a counter that restarts
/// makes the same FP variable denote a DIFFERENT SAT variable and silently
/// mis-wires the retained clause: a wrong-`sat` generator, and the failure
/// `IncrementalBvState`'s `bv_var_offset` / `sync_next_bv_var` pair exists to
/// prevent (#7892).
///
/// This pins the allocator contract only. It does NOT claim the lane is
/// incremental — `solve_fp` does not call the setter.
#[test]
fn set_next_var_moves_the_allocator_so_names_can_survive_a_solve() {
    let terms = TermStore::new();

    let mut fresh = FpSolver::new(&terms);
    assert_eq!(fresh.num_vars(), 0, "a new solver has issued no names");
    let first = fresh.fresh_var();

    // Restore to a frontier as an incremental caller would, then allocate.
    let mut restored = FpSolver::new(&terms);
    restored.set_next_var(500);
    let after_restore = restored.fresh_var();

    assert_ne!(
        after_restore, first,
        "set_next_var did not move the allocator: a restored solver re-issued the \
         SAME name as a fresh one, so a retained clause would be mis-wired"
    );
    assert_eq!(
        after_restore, 500,
        "the restored frontier must be honoured exactly"
    );
    assert_eq!(
        restored.fresh_var(),
        501,
        "allocation must continue forward from the restored frontier"
    );
    assert_eq!(
        restored.num_vars(),
        501,
        "num_vars is next_var - 1 and must reflect the restored frontier"
    );

    // A stale snapshot must not rewind the allocator. Rewinding here would
    // re-issue 500 and 501, silently changing what retained clauses mean.
    restored.set_next_var(1);
    assert_eq!(
        restored.fresh_var(),
        502,
        "a stale restore rewound the allocator and re-issued an existing name"
    );
}
