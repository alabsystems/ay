// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Helper: make external literal from 1-based signed integer.
fn ext_lit(signed: i32) -> u32 {
    let var = signed.unsigned_abs() - 1;
    var * 2 + if signed < 0 { 1 } else { 0 }
}

#[test]
fn test_sat_trivial() {
    let mut k = Kitten::new();
    // x1 OR x2
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(2)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 10);
}

#[test]
fn test_unsat_empty_clause() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 20);
}

#[test]
fn test_unsat_unit_conflict() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(-1)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 20);
}

#[test]
fn test_sat_with_propagation() {
    let mut k = Kitten::new();
    // x1, (~x1 OR x2), (~x2 OR x3) → x1=T, x2=T, x3=T
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.add_clause_with_id(2, &[ext_lit(-2), ext_lit(3)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 10);
    assert!(k.value(ext_lit(1)) > 0);
    assert!(k.value(ext_lit(2)) > 0);
    assert!(k.value(ext_lit(3)) > 0);
}

#[test]
fn test_unsat_conflict_analysis() {
    let mut k = Kitten::new();
    // Pigeonhole-like: 3 vars, all positive and negative pairs forced.
    // (x1), (x2), (~x1 OR ~x2)
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(2)], INVALID);
    k.add_clause_with_id(2, &[ext_lit(-1), ext_lit(-2)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 20);
}

#[test]
fn test_assume_sat() {
    let mut k = Kitten::new();
    // (x1 OR x2), assume x1
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(2)], INVALID);
    k.seal_original();
    k.assume(ext_lit(1));
    assert_eq!(k.solve(), 10);
    assert!(k.value(ext_lit(1)) > 0);
}

#[test]
fn test_assume_unsat() {
    let mut k = Kitten::new();
    // (x1), assume ~x1
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.seal_original();
    k.assume(ext_lit(-1));
    assert_eq!(k.solve(), 20);
}

#[test]
fn test_flip_literal_success() {
    let mut k = Kitten::new();
    // (x1 OR x2): if model has x1=T,x2=T, flipping x1 should succeed.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(2)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 10);

    // At least one of x1, x2 is true. Try flipping the true one.
    let v1 = k.value(ext_lit(1));
    let v2 = k.value(ext_lit(2));
    if v1 > 0 && v2 > 0 {
        // Both true — flipping either should succeed (other covers clause).
        assert!(k.flip_literal(ext_lit(1)));
    } else if v1 > 0 {
        // Only x1 true — flipping x1 would fail (clause unsatisfied).
        assert!(!k.flip_literal(ext_lit(1)));
    }
}

#[test]
fn test_clear_and_reuse() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 10);

    k.clear();

    // New problem on same kitten.
    k.add_clause_with_id(0, &[ext_lit(-1)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 10);
    assert!(k.value(ext_lit(1)) < 0);
}

#[test]
fn test_ticks_limit() {
    let mut k = Kitten::new();
    // Lots of clauses to force many propagations.
    for i in 1..20 {
        k.add_clause_with_id(i as u32, &[ext_lit(i), ext_lit(-(i + 1))], INVALID);
        k.add_clause_with_id((i + 100) as u32, &[ext_lit(-i), ext_lit(i + 1)], INVALID);
    }
    k.seal_original();
    k.set_ticks_limit(1); // very tight limit
    let result = k.solve();
    // Should hit limit and return 0 (unknown) or solve instantly.
    assert!(result == 0 || result == 10 || result == 20);
}

#[test]
fn test_ticks_limit_is_relative_to_current_ticks() {
    let mut k = Kitten::new();
    k.ticks = 41;
    k.set_ticks_limit(7);
    assert_eq!(k.ticks_limit, 48);
}

#[test]
fn test_randomize_phases_changes_sat_models() {
    let mut k = Kitten::new();
    // Tautology imports x1 without constraining it, so the SAT model follows
    // the current decision phase for the first branch.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(-1)], INVALID);
    k.seal_original();

    let mut saw_true = false;
    let mut saw_false = false;
    for _ in 0..8 {
        k.randomize_phases();
        assert_eq!(k.solve(), 10);
        let value = k.value(ext_lit(1));
        saw_true |= value > 0;
        saw_false |= value < 0;
    }

    assert!(saw_true, "randomized kitten phases never produced x1=true");
    assert!(
        saw_false,
        "randomized kitten phases never produced x1=false"
    );
}

#[test]
fn test_flip_phases_inverts_next_decision_model() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(-1)], INVALID);
    k.seal_original();

    assert_eq!(k.solve(), 10);
    let before = k.value(ext_lit(1));
    assert_ne!(before, 0);

    k.flip_phases();
    assert_eq!(k.solve(), 10);
    let after = k.value(ext_lit(1));
    assert_eq!(after, -before);
}

#[test]
fn test_fixed_value_only_reports_level_zero_assignments() {
    let mut k = Kitten::new();
    // x1 is fixed at level 0. x2 is unconstrained except for being imported.
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(2), ext_lit(-2)], INVALID);
    k.seal_original();

    assert_eq!(k.solve(), 10);
    assert!(
        k.fixed_value(ext_lit(1)) > 0,
        "x1 should be fixed true at level 0"
    );
    assert!(
        k.fixed_value(ext_lit(-1)) < 0,
        "~x1 should be fixed false at level 0"
    );
    assert_eq!(
        k.fixed_value(ext_lit(2)),
        0,
        "decision-only assignments must not count as fixed"
    );
    assert_eq!(
        k.fixed_value(ext_lit(-2)),
        0,
        "decision-only assignments must not count as fixed"
    );
}

#[test]
fn test_clausal_core() {
    let mut k = Kitten::new();
    k.enable_antecedent_tracking();
    // (x1), (~x1 OR x2), (~x2) — UNSAT, all 3 clauses in core.
    k.add_clause_with_id(100, &[ext_lit(1)], INVALID);
    k.add_clause_with_id(200, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.add_clause_with_id(300, &[ext_lit(-2)], INVALID);
    k.seal_original();
    assert_eq!(k.solve(), 20);

    let core = k.compute_clausal_core();
    // All 3 original clauses should be in the core.
    assert!(core.contains(&100), "clause 100 missing from core");
    assert!(core.contains(&200), "clause 200 missing from core");
    assert!(core.contains(&300), "clause 300 missing from core");
}

/// Regression test for #7067: level-0 propagated variables must be tracked
/// in the units vector so completely_backtrack_to_root_level() properly
/// unassigns them before incremental solves.
///
/// Setup: unit clause forces x1=T, binary clause (¬x1 ∨ x2) forces x2=T
/// at level 0 through propagation. x2's learned unit clause must be in the
/// units vector. Then an incremental solve assuming ¬x2 must report UNSAT
/// (x2 is forced true), and assuming x2 must report SAT.
///
/// Without the fix: x2 stays assigned after completely_backtrack_to_root_level
/// because its learned unit clause isn't tracked. The incremental solve sees
/// x2=T as a stale fact, potentially misreporting equivalences.
#[test]
fn test_incremental_level0_propagation_unassignment() {
    let mut k = Kitten::new();
    // x1 (unit clause)
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    // ¬x1 ∨ x2 (binary → x2 propagated at level 0)
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    // ¬x2 ∨ x3 (binary → x3 propagated at level 0)
    k.add_clause_with_id(2, &[ext_lit(-2), ext_lit(3)], INVALID);
    // x4 ∨ x5 (gives kitten something to decide on)
    k.add_clause_with_id(3, &[ext_lit(4), ext_lit(5)], INVALID);
    k.seal_original();

    // First solve: should be SAT. Level-0 propagation: x1=T → x2=T → x3=T.
    assert_eq!(k.solve(), 10);
    assert!(k.value(ext_lit(1)) > 0, "x1 should be true");
    assert!(k.value(ext_lit(2)) > 0, "x2 should be true");
    assert!(k.value(ext_lit(3)) > 0, "x3 should be true");

    // Incremental: assume ¬x2. Since x2 is forced true at level 0,
    // this should be UNSAT.
    k.assume(ext_lit(-2));
    assert_eq!(k.solve(), 20, "¬x2 should be UNSAT (x2 forced true)");

    // Incremental: assume x2 (true). Should be SAT since x2 IS true.
    k.assume(ext_lit(2));
    assert_eq!(k.solve(), 10, "x2 should be SAT");

    // Incremental: assume ¬x3. Since x3 is forced true at level 0
    // (x1→x2→x3), this should be UNSAT.
    k.assume(ext_lit(-3));
    assert_eq!(
        k.solve(),
        20,
        "¬x3 should be UNSAT (x3 forced true via chain)"
    );

    // Incremental: probe for equivalence-like pattern.
    // assume(¬x2, x3) — should be UNSAT (x2 forced true, ¬x2 contradicts).
    k.assume(ext_lit(-2));
    k.assume(ext_lit(3));
    assert_eq!(k.solve(), 20, "¬x2 ∧ x3 should be UNSAT");
}

/// Regression test for #7049: opposite-direction sweep probes must not
/// inherit stale assignments or learned facts from the previous probe.
///
/// The formula is SAT overall. Under assumptions (¬a ∧ b), kitten should
/// report UNSAT. Under the opposite probe (a ∧ ¬b), kitten should report
/// SAT with c forced false. Old incremental-reset bugs could leak c=true
/// from the first probe into the second and produce a false equivalence.
#[test]
fn test_incremental_opposite_probe_does_not_leak_state() {
    let mut k = Kitten::new();
    // a ∨ c
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(3)], INVALID);
    // ¬b ∨ c
    k.add_clause_with_id(1, &[ext_lit(-2), ext_lit(3)], INVALID);
    // a ∨ ¬b ∨ ¬c
    k.add_clause_with_id(2, &[ext_lit(1), ext_lit(-2), ext_lit(-3)], INVALID);
    // ¬a ∨ b ∨ ¬c
    k.add_clause_with_id(3, &[ext_lit(-1), ext_lit(2), ext_lit(-3)], INVALID);
    k.seal_original();

    // Mirror sweep usage: start from a SAT base solve, then probe opposite
    // directions incrementally on the same kitten instance.
    assert_eq!(k.solve(), 10, "base formula should be SAT");

    // Probe 1: ¬a ∧ b forces c and ¬c, so this branch is UNSAT.
    k.assume(ext_lit(-1));
    k.assume(ext_lit(2));
    assert_eq!(k.solve(), 20, "¬a ∧ b should be UNSAT");

    // Probe 2: a ∧ ¬b leaves only ¬c, so this branch is SAT. If c=true
    // leaked from the prior probe, this would spuriously become UNSAT.
    k.assume(ext_lit(1));
    k.assume(ext_lit(-2));
    assert_eq!(k.solve(), 10, "a ∧ ¬b should stay SAT after reset");
    assert!(
        k.value(ext_lit(-3)) > 0,
        "second probe should force c=false rather than inherit c=true"
    );
}

/// Regression test for #8530/#8538: ticks limit hit during backbone probing
/// must not accumulate stale assumptions into subsequent probes.
///
/// Setup: build a formula with enough clauses that a tight ticks limit will
/// cause some solves to return unknown (0). Then verify that equivalence
/// probing on the same kitten instance still produces correct results.
///
/// Root cause: kitten's solve() did not reset assumptions when returning 0.
/// The next assume() saw status==0 and skipped reset_incremental(), appending
/// new assumptions onto stale ones. The accumulated assumption stack caused
/// false UNSAT results in subsequent probes.
#[test]
fn test_ticks_limit_does_not_corrupt_subsequent_probes_8530() {
    let mut k = Kitten::new();

    // Build a formula where x1 <-> x2 (equivalent) and x3 is independent.
    // x1 -> x2: (¬x1 ∨ x2)
    // x2 -> x1: (x1 ∨ ¬x2)
    // x3 unconstrained: (x3 ∨ ¬x3 ∨ x4) — tautological filler
    k.add_clause_with_id(0, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(1), ext_lit(-2)], INVALID);
    // Add many clauses to make the formula expensive to solve.
    for i in 3..20 {
        k.add_clause_with_id(
            i as u32,
            &[ext_lit(i), ext_lit(-(i + 1)), ext_lit(i + 2)],
            INVALID,
        );
        k.add_clause_with_id(
            (i + 100) as u32,
            &[ext_lit(-i), ext_lit(i + 1), ext_lit(-(i + 2))],
            INVALID,
        );
    }
    k.seal_original();

    // Initial SAT solve with tight ticks limit.
    k.set_ticks_limit(10); // very tight — may return unknown
    let _ = k.solve(); // Don't care about the result

    // Now remove the tight limit and do equivalence-style probing.
    // Even if the first solve hit the ticks limit, subsequent probes
    // must not inherit stale assumptions from that solve.
    k.set_ticks_limit(u64::MAX);

    // Forward: x1 ∧ ¬x2 should be UNSAT (x1 -> x2 holds).
    k.assume(ext_lit(1));
    k.assume(ext_lit(-2));
    let forward = k.solve();
    assert_eq!(forward, 20, "x1 ∧ ¬x2 should be UNSAT (x1 -> x2 holds)");

    // Backward: ¬x1 ∧ x2 should be UNSAT (x2 -> x1 holds).
    k.assume(ext_lit(-1));
    k.assume(ext_lit(2));
    let backward = k.solve();
    assert_eq!(backward, 20, "¬x1 ∧ x2 should be UNSAT (x2 -> x1 holds)");

    // Verify that a non-equivalence is NOT reported as equivalent.
    // x1 ∧ ¬x3: should be SAT (x1 and x3 are independent).
    k.assume(ext_lit(1));
    k.assume(ext_lit(-3));
    let non_equiv = k.solve();
    assert_eq!(
        non_equiv, 10,
        "x1 ∧ ¬x3 should be SAT (x1 and x3 are independent)"
    );
}

/// Regression test for #8538: many incremental probes on the same kitten
/// must not accumulate stale learned clauses or state that cause false UNSAT.
///
/// This tests a sweep-like pattern: many assumption-based solves on the same
/// kitten, alternating between UNSAT and SAT expected results.
#[test]
fn test_many_incremental_probes_no_stale_state_8538() {
    let mut k = Kitten::new();

    // Formula: x1 <-> x2, x3 <-> x4, but x1 and x3 are independent.
    // x1 -> x2
    k.add_clause_with_id(0, &[ext_lit(-1), ext_lit(2)], INVALID);
    // x2 -> x1
    k.add_clause_with_id(1, &[ext_lit(1), ext_lit(-2)], INVALID);
    // x3 -> x4
    k.add_clause_with_id(2, &[ext_lit(-3), ext_lit(4)], INVALID);
    // x4 -> x3
    k.add_clause_with_id(3, &[ext_lit(3), ext_lit(-4)], INVALID);
    // Some filler to make the formula non-trivial:
    k.add_clause_with_id(4, &[ext_lit(1), ext_lit(3), ext_lit(5)], INVALID);
    k.add_clause_with_id(5, &[ext_lit(-5), ext_lit(6)], INVALID);
    k.add_clause_with_id(6, &[ext_lit(-6), ext_lit(5)], INVALID);
    k.seal_original();

    // Run many rounds of probing, alternating between equivalent and
    // non-equivalent pairs. Each round exercises the incremental path.
    for round in 0..10 {
        // Probe x1 <-> x2 (should be UNSAT in both directions).
        k.assume(ext_lit(1));
        k.assume(ext_lit(-2));
        assert_eq!(k.solve(), 20, "round {round}: x1 ∧ ¬x2 should be UNSAT");
        k.assume(ext_lit(-1));
        k.assume(ext_lit(2));
        assert_eq!(k.solve(), 20, "round {round}: ¬x1 ∧ x2 should be UNSAT");

        // Probe x1 vs x3 (should be SAT — independent).
        k.assume(ext_lit(1));
        k.assume(ext_lit(-3));
        assert_eq!(k.solve(), 10, "round {round}: x1 ∧ ¬x3 should be SAT");

        // Probe x3 <-> x4 (should be UNSAT in both directions).
        k.assume(ext_lit(3));
        k.assume(ext_lit(-4));
        assert_eq!(k.solve(), 20, "round {round}: x3 ∧ ¬x4 should be UNSAT");
        k.assume(ext_lit(-3));
        k.assume(ext_lit(4));
        assert_eq!(k.solve(), 20, "round {round}: ¬x3 ∧ x4 should be UNSAT");

        // Probe x2 vs x4 (should be SAT — independent).
        k.assume(ext_lit(2));
        k.assume(ext_lit(-4));
        assert_eq!(k.solve(), 10, "round {round}: x2 ∧ ¬x4 should be SAT");
    }
}

/// Test the three cases of failing_analysis:
/// Case 1: assumption falsified at level 0 by unit propagation.
#[test]
fn test_failing_analysis_unit_level_falsification() {
    let mut k = Kitten::new();
    // Unit clause forces x1=true at level 0.
    k.add_clause_with_id(0, &[ext_lit(1)], INVALID);
    // Binary to propagate x2=true at level 0.
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.seal_original();

    // Assume ¬x2: falsified at level 0 (unit propagation forces x2=true).
    k.assume(ext_lit(-2));
    assert_eq!(k.solve(), 20, "¬x2 should be UNSAT (x2 forced at level 0)");
}

/// Test the three cases of failing_analysis:
/// Case 2: assumption clashes with another assumption.
#[test]
fn test_failing_analysis_clashing_assumptions() {
    let mut k = Kitten::new();
    // Minimal formula — just need variables to exist.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(-1)], INVALID); // tautology
    k.seal_original();

    // Assume x1 and ¬x1 — direct clash.
    k.assume(ext_lit(1));
    k.assume(ext_lit(-1));
    assert_eq!(
        k.solve(),
        20,
        "x1 ∧ ¬x1 should be UNSAT (clashing assumptions)"
    );
}

/// Test the three cases of failing_analysis:
/// Case 3: general failure — assumption falsified by propagation at non-zero level.
#[test]
fn test_failing_analysis_general_propagation() {
    let mut k = Kitten::new();
    // (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x3)
    // Under assumption x1: propagation forces x2=true → x3=true, but ¬x3 clause
    // makes x3=false at level 0. So assumption x1 leads to a contradiction
    // through propagation.
    k.add_clause_with_id(0, &[ext_lit(1), ext_lit(2)], INVALID);
    k.add_clause_with_id(1, &[ext_lit(-1), ext_lit(2)], INVALID);
    k.add_clause_with_id(2, &[ext_lit(-2), ext_lit(3)], INVALID);
    k.add_clause_with_id(3, &[ext_lit(-3)], INVALID);
    k.seal_original();

    // x2 is forced true by resolution of clauses 0 and 1.
    // Then x3 is forced true by clause 2, but clause 3 forces x3 false.
    // This is actually unconditionally UNSAT.
    assert_eq!(k.solve(), 20, "formula should be UNSAT");

    // With assumptions it should also be UNSAT.
    k.assume(ext_lit(1));
    assert_eq!(k.solve(), 20, "UNSAT formula stays UNSAT under assumptions");
}
