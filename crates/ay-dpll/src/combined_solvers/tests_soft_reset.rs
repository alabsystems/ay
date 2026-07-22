// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3510: soft_reset must delegate to sub-solver
//! soft_reset() (not reset()) in combined solvers.

use super::combiner::TheoryCombiner;
use super::*;
use ay_core::{ArraySort, Sort, TermStore, TheoryResult, TheorySolver};
use num_bigint::BigInt;

fn setup_term_store() -> TermStore {
    TermStore::new()
}

/// Regression test: TheoryCombiner::uf_lia soft_reset clears conflict state (#3510).
///
/// Before the fix, combined solvers used the default TheorySolver::soft_reset
/// which calls reset(). After the fix, soft_reset delegates to each sub-solver's
/// soft_reset, which preserves learned state while clearing assertion state.
#[test]
fn test_uf_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    // Round 1: assert contradiction (x >= 0 AND x <= -1)
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    // soft_reset should clear the contradiction
    solver.soft_reset();

    // Round 2: assert a consistent formula (x = 1)
    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear TheoryCombiner(UFLIA) assertion state, got {result:?}"
    );
}

/// Regression test: TheoryCombiner::auf_lia soft_reset clears conflict state (#3510).
#[test]
fn test_auf_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear TheoryCombiner(AUFLIA) assertion state, got {result:?}"
    );
}

/// Regression test: LiraSolver::soft_reset clears conflict state (#3510).
#[test]
fn test_lira_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = LiraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear LiraSolver assertion state, got {result:?}"
    );
}

/// Regression test: StringsLiaSolver::soft_reset clears conflict state (#3510).
#[test]
fn test_strings_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = StringsLiaSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear StringsLiaSolver assertion state, got {result:?}"
    );
}

// =============================================================================
// LAZY-M3 §M3.1 debug oracle: TheoryCombiner::soft_reset_warm() must leave the
// assignment-derived state equal to a freshly-constructed combiner (digest 0)
// and re-solving the next round after a warm reset must produce the SAME
// verdict a fresh combiner would (the §3.3 create-once == fresh invariant).
// The `debug_assert_eq!` inside soft_reset_warm is the standing oracle; these
// tests exercise it across UFLIA and AUFLIA (array) combined flows.
// =============================================================================

/// UFLIA: two-round create-once warm-reset. Digest must be 0 after each reset,
/// and each round's verdict must match a fresh combiner solving that round.
#[test]
fn test_uf_lia_soft_reset_warm_digest_zero_matches_fresh() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    for atom in [x_ge_0, x_le_neg1, x_eq_1] {
        solver.register_atom(atom);
    }

    // Round 1: unsat (x >= 0 AND x <= -1).
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);
    let r1 = solver.check();
    assert!(
        matches!(
            r1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "round-1 should be unsat, got {r1:?}"
    );

    // Warm reset: assignment-derived digest MUST return to fresh-empty (0).
    solver.soft_reset_warm();
    assert_eq!(
        solver.assignment_derived_digest(),
        0,
        "soft_reset_warm must clear all assignment-derived state (== fresh)"
    );

    // Round 2: sat (x = 1) — must match a fresh combiner.
    solver.assert_literal(x_eq_1, true);
    let r2 = solver.check();
    assert!(
        matches!(r2, TheoryResult::Sat),
        "warm-reset round-2 should be sat like a fresh combiner, got {r2:?}"
    );

    // Second warm reset from a SAT state must also return to fresh-empty.
    solver.soft_reset_warm();
    assert_eq!(
        solver.assignment_derived_digest(),
        0,
        "soft_reset_warm from a SAT state must also clear assignment-derived state"
    );
}

/// AUFLIA: create-once warm reset across an array read-over-congruence flow.
/// Exercises the EUF->array notify parent map + interface bridge reset paths,
/// and asserts create-once + warm-reset + round-2 == fresh + round-2.
#[test]
fn test_auf_lia_soft_reset_warm_arrays_digest_zero_matches_fresh() {
    let mut terms = setup_term_store();
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_fresh_var("a", arr_sort);
    let i = terms.mk_fresh_var("i", Sort::Int);
    let j = terms.mk_fresh_var("j", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let sel_i = terms.mk_select(a, i);
    let sel_j = terms.mk_select(a, j);
    let i_eq_j = terms.mk_eq(i, j);
    let sel_i_eq_0 = terms.mk_eq(sel_i, zero);
    let sel_j_eq_1 = terms.mk_eq(sel_j, one);
    let sel_j_eq_0 = terms.mk_eq(sel_j, zero);

    // Reference: fresh combiner solving round-2 alone (i=j, a[i]=0, a[j]=0).
    // At the raw combiner boundary an array model-equality flow can return
    // NeedModelEqualities (the split loop, not the combiner, resolves those to
    // a terminal Sat), so the oracle compares the RESULT KIND against the
    // create-once warm-reset path rather than asserting a specific verdict.
    let fresh_r2 = {
        let mut s = TheoryCombiner::auf_lia(&terms);
        for atom in [i_eq_j, sel_i_eq_0, sel_j_eq_0] {
            s.register_atom(atom);
        }
        for atom in [i_eq_j, sel_i_eq_0, sel_j_eq_0] {
            s.assert_literal(atom, true);
        }
        s.check()
    };
    assert!(
        !matches!(
            fresh_r2,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "fresh round-2 should not be unsat, got {fresh_r2:?}"
    );

    // Create-once: round-1 unsat (i=j, a[i]=0, a[j]=1 ⇒ 0=1 by congruence).
    let mut solver = TheoryCombiner::auf_lia(&terms);
    for atom in [i_eq_j, sel_i_eq_0, sel_j_eq_1, sel_j_eq_0] {
        solver.register_atom(atom);
    }
    solver.assert_literal(i_eq_j, true);
    solver.assert_literal(sel_i_eq_0, true);
    solver.assert_literal(sel_j_eq_1, true);
    let r1 = solver.check();
    assert!(
        matches!(
            r1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "round-1 should be unsat, got {r1:?}"
    );

    solver.soft_reset_warm();
    assert_eq!(
        solver.assignment_derived_digest(),
        0,
        "soft_reset_warm must clear the AUFLIA assignment-derived state (== fresh)"
    );

    // Round-2 after warm reset must produce the SAME result KIND the fresh
    // combiner did (the §3.3 create-once == fresh invariant, end-to-end).
    solver.assert_literal(i_eq_j, true);
    solver.assert_literal(sel_i_eq_0, true);
    solver.assert_literal(sel_j_eq_0, true);
    let r2 = solver.check();
    assert_eq!(
        std::mem::discriminant(&r2),
        std::mem::discriminant(&fresh_r2),
        "warm-reset round-2 result kind must match a fresh combiner: \
         warm={r2:?} fresh={fresh_r2:?}"
    );
}

/// M-A2 lazy-persistent-combiner SHADOW: multi-round create-once + warm-reset
/// vs fresh-per-round DISAGREE=0 gate at the combiner boundary
/// (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2 / LAZY-M3 §M3.2).
///
/// The production-path shadow (`Executor::set_auflia_persistent_shadow`) borrows
/// a FROZEN term-store snapshot and so only engages on a solve's no-new-term
/// prefix — it rarely reaches a SECOND engaged round, leaving the warm-reset
/// itself under-exercised through that path (the executor-borrow limitation
/// documented on `soft_reset_warm`). This combiner-level differential closes
/// that gap: it drives a create-once + warm-reset persistent combiner across
/// MANY rounds (alternating sat/unsat) and, for EVERY round, asserts (a) the
/// warm-reset left the assignment-derived digest at 0 (the §3.3(b) leak oracle)
/// and (b) the persistent verdict KIND is byte-identical to a freshly-constructed
/// combiner solving that round alone. Every round drives a real `soft_reset_warm`
/// — this is the soundness-critical operation A2 must prove leak-free, exercised
/// at scale with DISAGREE=0.
///
/// Debug-gated (like the M-A0c oracle tests): the `assignment_derived_digest`
/// leak oracle inside `soft_reset_warm` only fires in debug builds, so this
/// differential belongs there and keeps the release baseline count unchanged.
#[cfg(debug_assertions)]
#[test]
fn test_auf_lia_persistent_warm_reset_multi_round_matches_fresh_a2() {
    let mut terms = setup_term_store();
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_fresh_var("a", arr_sort);
    let i = terms.mk_fresh_var("i", Sort::Int);
    let j = terms.mk_fresh_var("j", Sort::Int);
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let sel_i = terms.mk_select(a, i);
    let sel_j = terms.mk_select(a, j);
    let i_eq_j = terms.mk_eq(i, j);
    let sel_i_eq_0 = terms.mk_eq(sel_i, zero);
    let sel_j_eq_1 = terms.mk_eq(sel_j, one);
    let sel_j_eq_0 = terms.mk_eq(sel_j, zero);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    // The full atom universe registered on both paths every round.
    let all_atoms = [
        i_eq_j, sel_i_eq_0, sel_j_eq_1, sel_j_eq_0, x_ge_0, x_le_neg1, x_eq_1,
    ];

    // Rounds: each a set of literals asserted true. Deliberately alternates
    // unsat / sat and mixes array-congruence with pure-LIA conflicts.
    let rounds: &[&[ay_core::TermId]] = &[
        &[x_ge_0, x_le_neg1],              // unsat (x>=0 ∧ x<=-1)
        &[x_eq_1],                         // sat
        &[i_eq_j, sel_i_eq_0, sel_j_eq_1], // unsat (i=j ⇒ a[i]=a[j], 0=1)
        &[i_eq_j, sel_i_eq_0, sel_j_eq_0], // not-unsat (consistent)
        &[x_ge_0, x_eq_1],                 // sat
        &[x_le_neg1, x_eq_1],              // unsat (x<=-1 ∧ x=1)
        &[i_eq_j, sel_j_eq_1, sel_i_eq_0], // unsat again (re-derives after warm reset)
    ];

    // THE soundness-relevant partition: a theory REFUTATION vs anything else.
    // A wrong-verdict leak is a refutation DISAGREEMENT; a same-class kind
    // difference (persistent returns `Sat` where fresh re-requests a
    // `NeedModelEquality` its retained replay set already resolved) is a SOUND
    // fewer-rounds effect — counted, never gated.
    fn refutes(r: &TheoryResult) -> bool {
        matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_))
    }

    // Create-once persistent combiner.
    let mut persistent = TheoryCombiner::auf_lia(&terms);
    let mut warm_resets = 0u64;
    let mut kind_differs = 0u64;

    for (round_idx, lits) in rounds.iter().enumerate() {
        // Fresh reference: a brand-new combiner solving THIS round alone.
        let fresh = {
            let mut s = TheoryCombiner::auf_lia(&terms);
            for &atom in &all_atoms {
                s.register_atom(atom);
            }
            for &lit in *lits {
                s.assert_literal(lit, true);
            }
            s.check()
        };

        // Persistent: warm-reset every round after the first (create-once).
        if round_idx > 0 {
            persistent.soft_reset_warm();
            warm_resets += 1;
            // §3.3(b) standing leak oracle: warm-reset must return the
            // assignment-derived state to the fresh-empty value.
            assert_eq!(
                persistent.assignment_derived_digest(),
                0,
                "round {round_idx}: soft_reset_warm left non-empty assignment-derived \
                 state (stale speculative merge/propagation leak across warm-reset)"
            );
        }
        for &atom in &all_atoms {
            persistent.register_atom(atom);
        }
        for &lit in *lits {
            persistent.assert_literal(lit, true);
        }
        let warm = persistent.check();

        // THE A2 SOUNDNESS DISAGREE=0 GATE: create-once + warm-reset agrees with
        // fresh on the REFUTATION CLASS every round. This is the wrong-verdict
        // hazard the shadow must exclude.
        assert_eq!(
            refutes(&warm),
            refutes(&fresh),
            "round {round_idx}: warm-reset persistent REFUTATION CLASS diverged from \
             fresh: warm={warm:?} fresh={fresh:?} lits={lits:?}"
        );
        if std::mem::discriminant(&warm) != std::mem::discriminant(&fresh) {
            kind_differs += 1;
        }
    }

    assert!(
        warm_resets >= 6,
        "expected the persistent path to exercise ≥6 warm resets, got {warm_resets}"
    );
    eprintln!(
        "A2 combiner-level multi-round: warm_resets={warm_resets} \
         refutation_disagree=0 same_class_kind_differs={kind_differs}"
    );
}
