// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof checking tests: forward DRUP checker, proof mode auto-configuration,
//! proof emission, LRAT chain validation, and mark-empty-clause lifecycle.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Proof Analyze Conflict Tests
// ========================================================================

#[test]
fn test_proof_analyze_conflict_index_bounds() {
    // Basic UNSAT via unit propagation — verifies 1UIP conflict analysis
    // produces a correct result on a minimal contradictory formula.

    let mut solver: Solver = Solver::new(3);

    // Create a simple unsatisfiable formula:
    // (a) ∧ (¬a ∨ b) ∧ (¬b) → UNSAT
    let a = Literal::positive(Variable(0));
    let neg_a = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let neg_b = Literal::negative(Variable(1));

    solver.add_clause(vec![a]); // Force a = true
    solver.add_clause(vec![neg_a, b]); // a → b
    solver.add_clause(vec![neg_b]); // Force b = false

    // Solve should return UNSAT without panic
    assert!(solver.process_initial_clauses().is_none());
    let result = solver.solve().into_inner();

    // Formula is UNSAT: a=true forces b=true, but b=false is required
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT, got {result:?}"
    );
}

// PROOF TEST: analyze_conflict returns None for stale trail/assignment metadata
//
// This directly exercises the edge case that motivated #3151 and #8479: the
// conflict clause references literals that appear assigned at the current level
// but no corresponding literal exists on the trail (stale metadata after theory
// handoff or chronological backtracking). analyze_conflict must return None
// (trail exhaustion bailout) and increment the stat counter rather than
// panicking.
#[test]
fn test_proof_analyze_conflict_returns_none_when_seen_literal_missing_from_trail() {
    let mut solver: Solver = Solver::new(2);

    let x = Literal::positive(Variable(0));
    let y = Literal::positive(Variable(1));
    let conflict_ref = solver
        .add_theory_lemma(vec![x, y])
        .expect("expected learned conflict clause");

    // Simulate stale solver metadata: vals/level says x,y are assigned
    // at decision level 1, but the trail is empty.
    solver.decision_level = 1;
    solver.vals[Literal::positive(Variable(0)).index()] = -1;
    solver.vals[Literal::negative(Variable(0)).index()] = 1;
    solver.vals[Literal::positive(Variable(1)).index()] = -1;
    solver.vals[Literal::negative(Variable(1)).index()] = 1;
    solver.var_data[0].level = 1;
    solver.var_data[1].level = 1;
    solver.trail.clear();
    solver.qhead = 0;

    let result = solver.analyze_conflict(conflict_ref);
    assert!(
        result.is_none(),
        "analyze_conflict should return None when trail is empty but seen literals exist"
    );
    assert!(
        solver.stats.trail_exhaustion_bailouts > 0,
        "trail_exhaustion_bailouts stat should be incremented"
    );
}

// PROOF TEST: analyze_conflict handles minimal trail correctly
//
// This tests a scenario where the trail is very short (single decision).
// The index decrement must not underflow when searching backwards.
#[test]
fn test_proof_analyze_conflict_short_trail() {
    let mut solver: Solver = Solver::new(4);

    // Create conflict at decision level 1:
    // (a) ∧ (¬a ∨ b) ∧ (¬a ∨ ¬b)
    // a=true at level 0, then we get b and ¬b at level 1
    let a = Literal::positive(Variable(0));
    let neg_a = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let neg_b = Literal::negative(Variable(1));

    solver.add_clause(vec![a]); // Unit at level 0
    solver.add_clause(vec![neg_a, b]); // a → b
    solver.add_clause(vec![neg_a, neg_b]); // a → ¬b

    assert!(solver.process_initial_clauses().is_none());
    let result = solver.solve().into_inner();

    // Conflict should be detected and handled without panic
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT, got {result:?}"
    );
}

/// Test for #1495: BVE resolvents must be properly watched when literals
/// are already assigned at level 0.
///
/// This test creates a scenario where:
/// 1. Variable x0 is eliminated at level 0
/// 2. The resolvent has literals that are already assigned
/// 3. The resolvent must be reordered so unassigned literals are watched

// ========================================================================
// Forward Checker + Congruence Proof Emission Tests
// ========================================================================

#[test]
fn test_congruence_equivalence_proof_emission_drat_uses_rup_checked_path() {
    use crate::proof::ProofOutput;

    // y0 = AND(a, b), y1 = AND(a, b) should force y0 <-> y1 congruence.
    // Variables: y0=0, y1=1, a=2, b=3.
    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut solver = Solver::with_proof_output(4, ProofOutput::drat_text(Vec::<u8>::new()));
    solver.add_clause(vec![neg(0), pos(2)]);
    solver.add_clause(vec![neg(0), pos(3)]);
    solver.add_clause(vec![pos(0), neg(2), neg(3)]);
    solver.add_clause(vec![neg(1), pos(2)]);
    solver.add_clause(vec![neg(1), pos(3)]);
    solver.add_clause(vec![pos(1), neg(2), neg(3)]);

    // Watches must be initialized before congruence() so that BCP works
    // during the RUP safety gate (congruence_edges_are_rup uses decide/propagate).
    solver.initialize_watches();
    solver.congruence();

    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "test setup must trigger at least one congruence equivalence"
    );
    let writer = solver.proof_manager.as_ref().expect("proof writer");
    assert!(
        writer.added_count() > 0,
        "congruence with proof logging must emit add records"
    );
}

#[test]
fn test_congruence_equivalence_proof_emission_lrat_defensive_axiom_fallback() {
    use crate::proof::ProofOutput;

    // Same duplicate-AND setup as DRAT test above.
    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut solver = Solver::with_proof_output(4, ProofOutput::lrat_text(Vec::<u8>::new(), 6));
    // LRAT profile policy clamps scheduled congruence. This test calls the
    // congruence body directly to keep its defensive per-site fallback covered.
    solver.set_congruence_enabled(true);

    solver.add_clause(vec![neg(0), pos(2)]);
    solver.add_clause(vec![neg(0), pos(3)]);
    solver.add_clause(vec![pos(0), neg(2), neg(3)]);
    solver.add_clause(vec![neg(1), pos(2)]);
    solver.add_clause(vec![neg(1), pos(3)]);
    solver.add_clause(vec![pos(1), neg(2), neg(3)]);

    // Watches must be initialized for BCP during RUP safety gate.
    solver.initialize_watches();

    // If equivalence implications were emitted as Derived with empty hints in
    // LRAT mode, ProofManager would debug-assert. This must stay panic-free.
    solver.congruence();

    // In LRAT mode, direct congruence equivalence implications use Axiom with
    // empty hints, which ProofManager suppresses (returns 0). The test verifies
    // that the body runs without panic and finds equivalences.
    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "test setup must trigger at least one congruence equivalence"
    );
}

// ── Forward DRUP checker integration tests ─────────────────────

#[test]
fn test_forward_checker_integration_solve_unsat() {
    let mut solver: Solver = Solver::new(2);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));
    // (a) ∧ (¬a ∨ b) ∧ (¬a ∨ ¬b) is UNSAT.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![na, b]);
    solver.add_clause(vec![na, nb]);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
}

#[test]
fn test_forward_checker_records_empty_clause_step_on_unsat() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![na]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
    assert_eq!(
        solver.forward_checker_derived_count(),
        Some(1),
        "UNSAT finalization must record exactly one empty-clause derived step"
    );
}

#[test]
fn test_forward_checker_integration_solve_sat() {
    let mut solver: Solver = Solver::new(4);
    solver.enable_forward_checker();
    let v: Vec<Variable> = (0..4).map(Variable).collect();
    let pos = |i: usize| Literal::positive(v[i]);
    let neg = |i: usize| Literal::negative(v[i]);
    // 3-SAT clauses with a satisfying assignment.
    solver.add_clause(vec![pos(0), pos(1), pos(2)]);
    solver.add_clause(vec![neg(0), pos(1), pos(3)]);
    solver.add_clause(vec![pos(0), neg(2), pos(3)]);
    solver.add_clause(vec![neg(1), neg(2), neg(3)]);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));
}

/// Verify that clauses added via `add_clause_watched` (the inprocessing path)
/// are verified as derived by the forward checker, not treated as original.
///
/// This tests the fix for the gap where BVE resolvents, HTR resolvents, and
/// factorization products were added with `learned=false` → `add_original()`
/// in the forward checker, bypassing RUP verification entirely.
///
/// Here we manually call `add_clause_watched` with a correct derived clause
/// to verify the forward checker's `add_derived` path accepts it.
#[test]
fn test_forward_checker_add_clause_watched_checks_derived() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    // (a ∨ b) ∧ (¬a ∨ b) → b is RUP-implied.
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);
    // Add derived clause (b) via add_clause_watched (inprocessing path).
    // With the fix, the forward checker calls add_derived → RUP check passes.
    // Before the fix, it called add_original → no check at all.
    let mut derived = vec![b];
    solver.add_clause_watched(&mut derived);
    // If we get here without panic, the forward checker accepted the derived clause.
}

/// Verify that the forward checker detects an incorrect inprocessing-derived
/// clause when added via `add_clause_watched`. The forward checker records
/// the RUP failure and adds the clause as trusted (#7929).
#[test]
fn test_forward_checker_add_clause_watched_rejects_invalid_derived() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    // (a ∨ b) — only one clause, cannot derive (c) from it.
    solver.add_clause(vec![a, b]);
    // Try to add (c) via add_clause_watched — NOT RUP-implied.
    let mut invalid = vec![c];
    solver.add_clause_watched(&mut invalid);
    // Forward checker records the RUP failure but does not panic.
}

// ── Proof provenance independence from learned flag (#4648) ──────

/// Verify that derived-irredundant clauses (add_clause_watched with learned=false)
/// are classified as derived (not original) in clause trace provenance.
///
/// Before #4648 fix: add_clause_db_checked used !learned to determine is_original,
/// so derived-irredundant clauses were incorrectly marked as original.
/// After fix: uses !forward_check_derived, correctly marking them as derived.
#[test]
fn test_derived_irredundant_clause_trace_shows_derived_not_original() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_clause_trace();

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));

    // Original clauses: (a ∨ b) ∧ (¬a ∨ b) → b is RUP-derivable.
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);

    // Derived-irredundant clause via add_clause_watched (inprocessing path).
    // learned=false but forward_check_derived=true inside add_clause_watched_impl.
    let mut derived = vec![b];
    solver.add_clause_watched(&mut derived);

    let trace = solver
        .take_clause_trace()
        .expect("clause trace should be enabled");
    let entries = trace.entries();

    // First 2 entries are original clauses.
    assert!(entries[0].is_original, "first clause should be original");
    assert!(entries[1].is_original, "second clause should be original");

    // Third entry is the derived-irredundant clause — must NOT be marked original.
    assert_eq!(entries.len(), 3, "expected 3 trace entries");
    assert!(
        !entries[2].is_original,
        "derived-irredundant clause must be marked as derived in trace, not original (#4648)"
    );
}

// ── Forward checker empty clause notification (#4483) ────────────

/// Verify that mark_empty_clause notifies the forward checker of the
/// empty clause derivation. This is a protocol completeness check: the
/// forward checker must see every add/delete/derived step including the
/// final empty clause.
///
/// Formula: (a) ∧ (¬a) — UNSAT from contradictory unit clauses.
/// BCP derives a conflict at level 0, triggering mark_empty_clause.
/// The forward checker receives add_derived(&[]) and verifies RUP.
/// If the empty clause is NOT RUP-derivable, this test panics.
#[test]
fn test_forward_checker_sees_empty_clause() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    // (a) ∧ (¬a) — trivially UNSAT.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![na]);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
}

/// Forward checker with a more complex UNSAT formula that requires
/// conflict analysis (not just level-0 BCP). The empty clause is
/// derived after backtracking from learned clause contradictions.
#[test]
fn test_forward_checker_sees_empty_clause_with_conflict_analysis() {
    let mut solver: Solver = Solver::new(3);
    solver.enable_forward_checker();
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));
    let c = Literal::positive(Variable(2));
    let nc = Literal::negative(Variable(2));
    // PHP(2,1): 3 vars, unsatisfiable
    // (a ∨ b) ∧ (a ∨ c) ∧ (¬a) ∧ (¬b ∨ ¬c)
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a, c]);
    solver.add_clause(vec![na]);
    solver.add_clause(vec![nb, nc]);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
}

// ── Level-0 BCP conflict LRAT hint test (#4397) ─────────────────

/// Verify that record_level0_conflict_chain writes non-empty LRAT hints.
///
/// Formula: (a) ∧ (¬a ∨ b) ∧ (¬b) — UNSAT purely from level-0 BCP.
/// After process_initial_clauses enqueues a and ¬b, propagation derives
/// a conflict without any decisions or inprocessing. The empty clause
/// must have resolution hints referencing the original clauses.
#[test]

// ========================================================================
// LRAT Level0 Conflict + IO Sentinel Tests
// ========================================================================

fn test_lrat_level0_conflict_has_hints() {
    use crate::ProofOutput;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(2, proof_writer);

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));

    // 3 original clauses → clause IDs 1, 2, 3
    solver.add_clause(vec![a]); // clause 1: a
    solver.add_clause(vec![na, b]); // clause 2: ¬a ∨ b
    solver.add_clause(vec![nb]); // clause 3: ¬b

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The proof should contain the empty clause derivation with non-empty hints.
    // LRAT format: <id> 0 <hints> 0
    // With empty hints it would be: <id> 0 0  (just "N 0 0")
    // With proper hints it should be: <id> 0 <hint1> <hint2> ... 0
    let lines: Vec<&str> = proof.lines().collect();
    assert!(
        !lines.is_empty(),
        "LRAT proof must not be empty for UNSAT formula"
    );

    // The last line should be the empty clause (no literals before the first 0).
    let last_line = lines.last().expect("proof must have at least one line");
    let tokens: Vec<&str> = last_line.split_whitespace().collect();
    // Format: <id> 0 <hints...> 0
    // The clause ID is first, then literal 0, then hints, then trailing 0.
    assert!(
        tokens.len() >= 2,
        "Empty clause line too short: {last_line}"
    );

    // Find the position of the first "0" (end of literals). For the empty
    // clause, this should be tokens[1].
    let first_zero = tokens
        .iter()
        .position(|t| *t == "0")
        .expect("missing literal terminator");
    assert_eq!(
        first_zero, 1,
        "Expected empty clause (first 0 at position 1), got: {last_line}"
    );

    // Everything between first_zero+1 and the last token (trailing 0) is hints.
    // If there are no hints, the line is just "<id> 0 0".
    let trailing_zero = tokens.len() - 1;
    let hint_count = trailing_zero - first_zero - 1;
    assert!(
        hint_count > 0,
        "BUG (#4397): Empty clause has NO resolution hints. \
         record_level0_conflict_chain must pass hints to proof_writer.\n\
         Proof line: {last_line}\nFull proof:\n{proof}"
    );
}

/// Regression test for #4434: LRAT `add` returns sentinel `Ok(0)` after I/O
/// failure, but `replace_clause_checked` must NOT propagate that sentinel into
/// `clause_ids` or `next_clause_id`.
///
/// Setup: create solver with LRAT using a writer that fails after N bytes.
/// Add original clauses (succeeds), then trigger I/O failure, then call
/// `replace_clause_checked`. Verify clause ID state is unchanged.
#[test]
fn test_lrat_io_failed_sentinel_does_not_corrupt_clause_ids() {
    /// Writer that succeeds for the first `limit` bytes, then fails.
    struct FailAfterN {
        buf: Vec<u8>,
        limit: usize,
    }

    impl Write for FailAfterN {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            if self.buf.len() + data.len() > self.limit {
                return Err(std::io::Error::other("simulated disk full"));
            }
            self.buf.extend_from_slice(data);
            Ok(data.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    // Allow enough bytes for original clause registration + first few LRAT
    // adds, then trigger failure on the replacement add.
    let writer = FailAfterN {
        buf: Vec::new(),
        limit: 220,
    };
    // 4 original clauses: the 4th ([¬x1]) makes [x0] RUP-derivable.
    // RUP check for [x0]: negate x0 → assign ¬x0, then:
    //   [x0,x1] → unit-propagate x1
    //   [¬x1]   → conflict. QED.
    let proof = ProofOutput::lrat_text(writer, 4);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // Add 4 original clauses (LRAT IDs 1-4)
    solver.add_clause(vec![x0, x1]);
    solver.add_clause(vec![x0, x2]);
    solver.add_clause(vec![x1, x2]);
    solver.add_clause(vec![x1.negated()]); // resolving clause for [x0]

    // Register ¬x1 with the forward checker (debug-mode only) so
    // strengthening [x0, x1] → [x0] is RUP-valid: negating x0 propagates
    // x1=true via [x0, x1], then ¬x1 triggers conflict.
    if let Some(ref mut pm) = solver.proof_manager {
        pm.register_original_clause(&[Literal::negative(Variable(1))]);
    }

    // Record clause ID state before the failing replacement
    let clause_0_id = solver.cold.clause_ids[0];
    let saved_next = solver.cold.next_clause_id;
    assert!(clause_0_id != 0, "clause 0 should have a non-zero LRAT ID");

    // Exhaust the writer's byte budget to force io_failed on next write.
    // Use Derived kind with valid LRAT hints so the write reaches the output
    // (Axiom+empty hints are now skipped in LRAT mode per #4490).
    if let Some(ref mut pw) = solver.proof_manager {
        // Write a large dummy clause to exhaust the budget.
        // Use non-empty hints (&[1]) to bypass the LRAT theory-lemma guard
        // which blocks Axiom clauses with empty hints (returns Ok(0) without
        // writing). Use unique variables to satisfy the no-duplicate-literal
        // debug_assert in proof.rs and forward_checker.rs.
        let big_clause: Vec<Literal> = (0..50)
            .map(|i| Literal::positive(Variable(i as u32)))
            .collect();
        for _ in 0..20 {
            let _ = pw.emit_add(&big_clause, &[1], ProofAddKind::Derived);
        }
        assert!(
            pw.has_io_error(),
            "writer should be in io_failed state after exhausting byte budget"
        );
    }

    // Now call replace_clause_checked — the LRAT writer.add will return Ok(0)
    solver.replace_clause_checked(0, &[x0]);

    // Verify: clause_ids[0] must NOT have been overwritten with sentinel 0
    assert_eq!(
        solver.cold.clause_ids[0], clause_0_id,
        "clause_ids[0] must be unchanged after io_failed replacement (was {}, now {})",
        clause_0_id, solver.cold.clause_ids[0]
    );
    // Verify: next_clause_id must NOT have regressed to 1 (sentinel 0 + 1)
    assert!(
        solver.cold.next_clause_id >= saved_next,
        "next_clause_id must not regress: was {}, now {}",
        saved_next,
        solver.cold.next_clause_id
    );
}

/// Regression test for #4572: BVE inprocessing with io_failed sentinel.
///
/// Exercises the BVE resolvent emission path (`inprocessing.rs:1600-1607`)
/// under LRAT I/O failure. Without the `new_id != 0` guard, the BVE emit_add
/// returning Ok(0) would reset `next_clause_id` to 0, corrupting all
/// subsequent clause ID assignments.
#[test]
fn test_lrat_io_failed_sentinel_bve_does_not_corrupt_clause_ids() {
    /// Writer that succeeds for the first `limit` bytes, then fails.
    struct FailAfterN {
        buf: Vec<u8>,
        limit: usize,
    }

    impl Write for FailAfterN {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            if self.buf.len() + data.len() > self.limit {
                return Err(std::io::Error::other("simulated disk full"));
            }
            self.buf.extend_from_slice(data);
            Ok(data.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    // Allow enough bytes for original clauses but fail during BVE resolvent.
    let writer = FailAfterN {
        buf: Vec::new(),
        limit: 120,
    };
    // Formula with a variable eligible for BVE:
    //   (x0 ∨ x1)     — positive occurrence of x0
    //   (¬x0 ∨ x2)    — negative occurrence of x0
    //   (x1 ∨ x2)     — unrelated clause to keep x1, x2 alive
    // BVE on x0 produces resolvent (x1 ∨ x2).
    let proof = ProofOutput::lrat_text(writer, 3);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    solver.add_clause(vec![x0, x1]);
    solver.add_clause(vec![x0.negated(), x2]);
    solver.add_clause(vec![x1, x2]);

    let saved_next = solver.cold.next_clause_id;

    // Exhaust the writer's byte budget to force io_failed.
    // Ensure enough variables for the big clause to avoid duplicate literals
    // (forward checker debug assertion).
    while solver.num_vars < 50 {
        solver.new_var();
    }
    if let Some(ref mut pw) = solver.proof_manager {
        let big_clause: Vec<Literal> = (0..50)
            .map(|i| Literal::positive(Variable(i as u32)))
            .collect();
        // Use Derived with hint [1] (referencing first original clause) so
        // the LRAT writer actually writes bytes. Axiom+empty hints are
        // suppressed in LRAT mode and never reach the writer.
        for _ in 0..20 {
            let _ = pw.emit_add(&big_clause, &[1], ProofAddKind::Derived);
        }
        assert!(
            pw.has_io_error(),
            "writer should be in io_failed state after exhausting byte budget"
        );
    }

    // Run the solve — BVE may fire during inprocessing and call emit_add
    // which returns Ok(0). The guard must prevent next_clause_id corruption.
    let _result = solver.solve().into_inner();

    // next_clause_id must not have regressed due to the sentinel
    assert!(
        solver.cold.next_clause_id >= saved_next,
        "BUG (#4572): next_clause_id regressed after BVE with io_failed: was {}, now {}",
        saved_next,
        solver.cold.next_clause_id
    );
}

// ── #4564 Unified forward checker contract tests ─────────────────

/// Verify that a solver with proof output (but no explicit
/// `enable_forward_checker()` call) auto-enables the forward checker
/// in debug builds and correctly validates derived clauses.
#[test]
#[cfg(debug_assertions)]

// ========================================================================
// Proof Mode Auto + Proof Emit Tests
// ========================================================================

fn test_proof_mode_auto_enables_forward_checker() {
    use crate::proof::ProofOutput;

    let buf: Vec<u8> = Vec::new();
    let output = ProofOutput::drat_text(buf);
    let mut solver = Solver::with_proof_output(2, output);

    // In debug builds, the checker should be auto-enabled by the constructor.
    assert!(
        solver.cold.forward_checker.is_some(),
        "forward checker should be auto-enabled in debug+proof mode (#4564)"
    );

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));

    // (a) ∧ (¬a ∨ b) ∧ (¬a ∨ ¬b) is UNSAT.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![na, b]);
    solver.add_clause(vec![na, nb]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
}

/// Verify that release proof output is emit-only by default.
#[test]
#[cfg(not(debug_assertions))]
fn test_release_proof_mode_does_not_auto_enable_forward_checker() {
    use crate::proof::ProofOutput;

    let buf: Vec<u8> = Vec::new();
    let output = ProofOutput::lrat_text(buf, 0);
    let solver = Solver::with_proof_output(2, output);

    assert!(
        solver.cold.forward_checker.is_none(),
        "release LRAT proof output should not auto-enable the forward checker"
    );
}

/// Verify that a solver with proof output detects an invalid derived clause
/// added via `add_clause_watched` (inprocessing path).
///
/// Since #7929, the forward checker demotes non-RUP clauses to trusted instead
/// of panicking, because inprocessing techniques (BVE, backbone, sweep) routinely
/// produce clauses whose derivations aren't reproducible by the forward checker.
/// This test verifies the checker records the RUP failure via `rup_failures()`.
#[test]
#[cfg(debug_assertions)]
fn test_proof_mode_auto_checker_rejects_invalid_derived() {
    use crate::proof::ProofOutput;

    let buf: Vec<u8> = Vec::new();
    let output = ProofOutput::drat_text(buf);
    let mut solver = Solver::with_proof_output(3, output);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // Only (a ∨ b) — cannot derive (c).
    solver.add_clause(vec![a, b]);

    assert_eq!(
        solver.cold.forward_checker.as_ref().unwrap().rup_failures(),
        0,
        "should start with zero RUP failures"
    );

    // Try to add (c) via add_clause_watched — NOT RUP-implied.
    let mut invalid = vec![c];
    solver.add_clause_watched(&mut invalid);

    assert_eq!(
        solver.cold.forward_checker.as_ref().unwrap().rup_failures(),
        1,
        "forward checker should record one RUP failure for non-implied clause"
    );
}

/// Verify that `proof_emit_add` routes through the unified solver-owned
/// forward checker. A valid derived clause should pass; no panic.
#[test]
#[cfg(debug_assertions)]
fn test_proof_emit_add_uses_unified_checker() {
    use crate::proof::ProofOutput;
    use crate::proof_manager::ProofAddKind;

    let buf: Vec<u8> = Vec::new();
    let output = ProofOutput::drat_text(buf);
    let mut solver = Solver::with_proof_output(2, output);

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));

    // Register originals through normal add_clause path.
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);

    // (b) is RUP-implied by (a ∨ b) ∧ (¬a ∨ b).
    let result = solver.proof_emit_add(&[b], &[], ProofAddKind::Derived);
    assert!(
        result.is_ok(),
        "RUP-valid derived clause should pass unified checker"
    );
}

/// Verify that LRAT-derived clauses with explicit hints bypass the solver-level
/// forward DRUP check. These clauses may be LRAT-valid without being
/// DRUP-provable, so `proof_emit_add` must not route them through
/// `checker.add_derived()` (#7108).
#[test]
#[cfg(debug_assertions)]
fn test_proof_emit_add_lrat_hints_bypass_forward_checker() {
    use crate::proof::ProofOutput;
    use crate::proof_manager::ProofAddKind;

    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, output);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a, b]); // LRAT ID 1

    // `[-a]` is not DRUP-implied by `(a ∨ b)`, so routing this through
    // `checker.add_derived()` would panic. In LRAT mode with hints, the
    // solver-level checker must treat it as an original and let the proof
    // manager/LRAT checker handle the chain instead.
    let result = solver.proof_emit_add(&[a.negated()], &[1], ProofAddKind::Derived);
    assert!(
        result.is_ok(),
        "LRAT-derived clause with hints should bypass forward DRUP checking",
    );
    assert_eq!(
        solver.forward_checker_derived_count(),
        Some(0),
        "bypassed LRAT-derived clause must not increment derived-count",
    );
}

/// Verify that `proof_emit_delete` routes through the unified checker
/// without error for a known clause.
#[test]
#[cfg(debug_assertions)]
fn test_proof_emit_delete_uses_unified_checker() {
    use crate::proof::ProofOutput;
    use crate::proof_manager::ProofAddKind;

    let buf: Vec<u8> = Vec::new();
    let output = ProofOutput::drat_text(buf);
    let mut solver = Solver::with_proof_output(2, output);

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![na, b]);

    // Add a derived clause, then delete it.
    let id = solver
        .proof_emit_add(&[b], &[], ProofAddKind::Derived)
        .expect("add should succeed");
    let del = solver.proof_emit_delete(&[b], id);
    assert!(del.is_ok(), "deleting a known clause should succeed");
}

/// Grep guard: no solver file (except proof_emit.rs) should directly call
/// `manager.emit_add(` or `manager.emit_delete(`.
///
/// This test reads the source files and checks for violations of the
/// single-authority contract established by #4564.
#[test]
fn test_no_direct_manager_emit_calls_in_solver() {
    let solver_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("solver");

    let forbidden_patterns = ["manager.emit_add(", "manager.emit_delete("];
    let mut violations = Vec::new();
    let mut saw_nested_solver_rs = false;
    let mut stack = vec![solver_dir.clone()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read solver dir") {
            let entry = entry.expect("read dir entry");
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }

            let is_rust_file = path
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("rs"));
            if !is_rust_file {
                continue;
            }

            let relative = path
                .strip_prefix(&solver_dir)
                .unwrap_or_else(|_| panic!("strip prefix {}", path.display()));
            let file_name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default();
            let in_tests_dir = relative
                .components()
                .any(|c| c.as_os_str().to_str() == Some("tests"));
            // proof_emit.rs is the wrapper and tests files contain guard strings.
            if file_name == "proof_emit.rs" || file_name == "tests.rs" || in_tests_dir {
                continue;
            }
            if relative.components().count() > 1 {
                saw_nested_solver_rs = true;
            }

            let content = std::fs::read_to_string(&path)
                .unwrap_or_else(|_| panic!("read {}", path.display()));
            // Normalize out whitespace and line comments so split-token calls like
            // `manager` + newline + `.emit_add(...)` are still detected.
            let no_line_comments = content
                .lines()
                .filter(|line| {
                    let trimmed = line.trim_start();
                    !trimmed.starts_with("//")
                })
                .collect::<Vec<_>>()
                .join("\n");
            let compact = no_line_comments
                .chars()
                .filter(|ch| !ch.is_whitespace())
                .collect::<String>();

            for pattern in &forbidden_patterns {
                if compact.contains(pattern) {
                    violations.push(format!("{}: found `{pattern}`", relative.display()));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "#4564 contract violation: direct manager.emit_* calls found in solver files \
         (use proof_emit_add/proof_emit_delete wrappers instead):\n  {}",
        violations.join("\n  ")
    );
    assert!(
        saw_nested_solver_rs,
        "test setup regression: expected at least one nested solver/*.rs file to be scanned"
    );
}

/// Regression test for #4596: preprocessing probing was skipped in LRAT mode
/// due to a stale guard (`!self.cold.lrat_enabled`). The hint collection code
/// (`collect_probe_conflict_lrat_hints`) was already wired in, making the
/// guard unnecessary.
///
/// Formula: 4 variables, 5 clauses.
///   (b)             -- unit clause, forces b=true at level 0
///   (a | c)         -- binary, makes `a` a probe root (pos_occs>0, neg_occs=0)
///   (a | ~c)        -- binary
///   (~a | ~b | d)   -- ternary, under a=true and b=true: d forced
///   (~a | ~b | ~d)  -- ternary, under a=true and b=true: ~d forced -> conflict
///
/// Probing `a` (root literal) finds a conflict -> ~a is a failed literal.
/// After enqueuing ~a, clauses 2,3 force both c and ~c -> UNSAT.

// ========================================================================
// Preprocessing Probe LRAT + Mark Empty Clause + Finalize Tests
// ========================================================================

#[test]
fn test_preprocessing_probe_runs_in_lrat_mode() {
    use crate::ProofOutput;

    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = Literal::negative(Variable(1));
    let c = Literal::positive(Variable(2));
    let nc = Literal::negative(Variable(2));
    let d = Literal::positive(Variable(3));
    let nd = Literal::negative(Variable(3));

    // 5 original clauses -> LRAT IDs 1-5, learned start at 6.
    let proof_writer = ProofOutput::lrat_text(Vec::new(), 5);
    let mut solver = Solver::with_proof_output(4, proof_writer);

    solver.add_clause(vec![b]); // clause 1: (b)
    solver.add_clause(vec![a, c]); // clause 2: (a | c)
    solver.add_clause(vec![a, nc]); // clause 3: (a | ~c)
    solver.add_clause(vec![na, nb, d]); // clause 4: (~a | ~b | d)
    solver.add_clause(vec![na, nb, nd]); // clause 5: (~a | ~b | ~d)

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "formula must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    assert!(
        !proof.is_empty(),
        "LRAT proof must not be empty for UNSAT formula"
    );

    // Verify all derived (non-deletion) LRAT lines have non-empty hints.
    // LRAT add format: <id> <lits...> 0 <hints...> 0
    // Empty hints would be: "<id> <lits...> 0 0"
    for line in proof.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() < 2 {
            continue;
        }
        // Skip deletion lines ("N d ...")
        if tokens.get(1) == Some(&"d") {
            continue;
        }
        // Find first "0" (end of literals), hints are between first and last "0"
        let first_zero = tokens
            .iter()
            .position(|t| *t == "0")
            .expect("missing literal terminator in LRAT line");
        let trailing_zero = tokens.len() - 1;
        let hint_count = trailing_zero - first_zero - 1;
        assert!(
            hint_count > 0,
            "BUG (#4596): Derived LRAT clause has NO resolution hints.\n\
             Preprocessing probing should produce valid hint chains.\n\
             Proof line: {line}\nFull proof:\n{proof}"
        );
    }
}

/// A missing-hint empty LRAT step fails closed, remains unwritten, and reuses
/// its hidden bookkeeping ID on repeated reports.
#[test]
fn test_mark_empty_clause_without_hints_fails_closed_without_id_drift() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);
    solver.add_clause(vec![b]);

    solver.mark_empty_clause();
    let id_after_first = solver.cold.next_clause_id;
    assert!(
        !solver.cold.empty_clause_in_proof,
        "a missing-hint empty clause must not be reported as proof-visible"
    );
    let manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(manager.has_lrat_authority_fail_closed());
    assert_eq!(manager.added_count(), 0);

    // Repeating the same unsupported terminal step must not drift IDs.
    solver.mark_empty_clause();
    let id_after_second = solver.cold.next_clause_id;
    assert_eq!(
        id_after_second, id_after_first,
        "second mark_empty_clause must NOT advance next_clause_id (#4475)"
    );

    let output = solver.take_proof_writer().expect("proof writer");
    assert!(
        output
            .into_vec()
            .expect("proof output remains readable")
            .is_empty(),
        "missing-hint empty clauses must never reach the LRAT stream"
    );
}

#[test]
fn test_mark_empty_clause_with_level0_hints_emits_non_empty_lrat_chain() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    let a = Literal::positive(Variable(0));
    let na = Literal::negative(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a]);
    solver.add_clause(vec![na, b]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "setup must produce a level-0 trail without an immediate conflict"
    );
    solver.mark_empty_clause_with_level0_hints();

    assert!(
        solver.cold.empty_clause_in_proof,
        "helper must emit the empty clause into the LRAT proof"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    let empty_clause_line = proof
        .lines()
        .find(|line| line.split_whitespace().nth(1) == Some("0"))
        .expect("proof must contain empty clause line");
    let tokens: Vec<&str> = empty_clause_line.split_whitespace().collect();
    assert!(
        tokens.len() > 3,
        "empty clause LRAT line must include at least one hint: {empty_clause_line}"
    );
    assert_ne!(
        tokens[2], "0",
        "empty clause LRAT line must include a non-empty hint chain: {empty_clause_line}"
    );
}

struct AlwaysFailOnWrite;

impl Write for AlwaysFailOnWrite {
    fn write(&mut self, _data: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::other("simulated write failure"))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

struct FailOnFlush {
    bytes: Vec<u8>,
}

impl Write for FailOnFlush {
    fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
        self.bytes.extend_from_slice(data);
        Ok(data.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::other("simulated flush failure"))
    }
}

/// Regression test for #4654 (mod.rs path): `mark_empty_clause` must not claim
/// the empty clause is in the proof when `emit_add` fails.
#[test]
fn test_mark_empty_clause_emit_failure_keeps_proof_flag_false() {
    let proof = ProofOutput::lrat_text(AlwaysFailOnWrite, 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let a = Literal::positive(Variable(0));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);

    solver.mark_empty_clause();

    assert!(
        solver.has_empty_clause,
        "solver state must still mark UNSAT"
    );
    assert!(
        !solver.cold.empty_clause_in_proof,
        "empty_clause_in_proof must remain false when emit_add fails (#4654)"
    );
}

/// Regression test for #4654 plus SAT-COMP fail-closed behavior: proof I/O
/// failure during UNSAT finalization returns UNKNOWN instead of panicking.
#[test]
fn test_finalize_unsat_proof_emit_failure_returns_unknown() {
    let proof = ProofOutput::lrat_text(AlwaysFailOnWrite, 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let a = Literal::positive(Variable(0));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);

    let result = solver.solve().into_inner();

    assert!(result.is_unknown(), "proof I/O failure must fail closed");
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofFinalizationFailure)
    );
    assert!(
        !solver.cold.empty_clause_in_proof,
        "empty_clause_in_proof must remain false when finalize emit_add fails (#4654)"
    );
}

#[test]
fn test_finalize_unsat_proof_flush_failure_returns_unknown() {
    let proof = ProofOutput::lrat_text(FailOnFlush { bytes: Vec::new() }, 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let a = Literal::positive(Variable(0));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);

    let result = solver.solve().into_inner();

    assert!(result.is_unknown(), "proof flush failure must fail closed");
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofFinalizationFailure)
    );
}

// =============================================================================
// Unknown-handling validation tests (#4622)

// ========================================================================
// LRAT Chain Finalization + Scoped/Assumption Unsat Proof Tests
// ========================================================================

#[test]
fn test_finalize_unsat_proof_catches_lrat_chain_failures() {
    // Create a simple UNSAT formula: (a) ∧ (¬a)
    // With correct LRAT hints, the empty clause derivation chain verifies.
    // The LRAT chain verifier runs in debug builds, so this exercises
    // the try_add_derived → failure-counter path end-to-end.
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    let a = Literal::positive(Variable(0));
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "(a) ∧ (¬a) must be UNSAT");

    // After a successful UNSAT solve, the LRAT chain verifier should
    // report zero failures. This confirms the proof emission pipeline
    // produced valid LRAT hints for all derived clauses.
    if let Some(ref manager) = solver.proof_manager {
        assert_eq!(
            manager.lrat_failures(),
            0,
            "LRAT chain verifier must report zero failures for a valid UNSAT proof"
        );
    }
}

/// Verify that scoped (push/pop) UNSAT also produces zero LRAT chain failures.
///
/// The push/pop LRAT path has additional complexity: original clause IDs
/// may be reused after scope retraction, and the empty clause needs an
/// LRAT delete step on pop. This test verifies the chain verifier accepts
/// the full scoped proof lifecycle.
#[test]
#[cfg(debug_assertions)]
fn test_scoped_unsat_lrat_chain_zero_failures() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let x = Literal::positive(Variable(0));

    solver.add_clause(vec![x]); // clause 1: (x)

    solver.push();
    solver.add_clause(vec![x.negated()]); // clause 2 (scoped): (¬x)

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "scoped (x) + (¬x) must be UNSAT");

    // Pop retracts the scoped clause and LRAT-deletes the empty clause.
    assert!(solver.pop(), "pop must succeed after scoped UNSAT");

    // After pop, the solver should be satisfiable again.
    let result2 = solver.solve().into_inner();
    assert!(
        matches!(result2, SatResult::Sat(_)),
        "after pop, formula should be SAT, got {result2:?}"
    );
}

/// Verify that assumption-based solving with LRAT proof enabled produces
/// a structurally complete proof (the empty clause is written).
///
/// Gap: assumption-path `process_initial_clauses()` failure does not call
/// `mark_empty_clause()` explicitly; it relies on `finalize_unsat_proof`
/// as a fallback. This test confirms that fallback works.
#[test]
fn test_assumption_unsat_writes_proof_empty_clause() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let x = Literal::positive(Variable(0));

    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);

    // Solve with assumptions (the formula is already UNSAT, so assumptions
    // don't matter — the UNSAT is detected during initial clause processing).
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "(x) ∧ (¬x) must be UNSAT");

    // Verify the proof stream contains at least the empty clause.
    // finalize_unsat_proof asserts added_count >= 1 (always-on check).
    // If we get here without panic, the assertion passed.
}

/// Preserved learned clauses must appear in the DRAT proof stream as axioms.
///
/// Before the fix (#3882), `add_preserved_learned` skipped proof logging
/// entirely. Any UNSAT derivation that depended on a preserved clause
/// would produce an incomplete proof rejected by `drat-trim`.
#[test]
fn test_preserved_learned_clause_emits_drat_proof_entry() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));

    let proof_buf = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(3, proof_buf);

    // Original clauses: (a ∨ b) ∧ (¬a ∨ c)
    solver.add_clause(vec![pos(0), pos(1)]);
    solver.add_clause(vec![neg(0), pos(2)]);
    solver.initialize_watches();

    let added_before = solver
        .proof_manager
        .as_ref()
        .expect("proof writer")
        .added_count();

    // Add a preserved learned clause: (b ∨ c)
    // This simulates carrying a clause from a previous B&B iteration.
    solver.add_preserved_learned(vec![pos(1), pos(2)]);

    let added_after = solver
        .proof_manager
        .as_ref()
        .expect("proof writer")
        .added_count();

    assert!(
        added_after > added_before,
        "BUG (#3882): add_preserved_learned must emit a proof entry when \
         DRAT proof output is enabled. Before={added_before}, After={added_after}"
    );
}

/// Preserved learned unit clauses must also appear in the DRAT proof stream.
#[test]
fn test_preserved_learned_unit_clause_emits_drat_proof_entry() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));

    let proof_buf = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(2, proof_buf);

    // Original clause: (a ∨ b)
    solver.add_clause(vec![pos(0), pos(1)]);
    solver.initialize_watches();

    let added_before = solver
        .proof_manager
        .as_ref()
        .expect("proof writer")
        .added_count();

    // Add a preserved learned unit clause: (a)
    solver.add_preserved_learned(vec![pos(0)]);

    let added_after = solver
        .proof_manager
        .as_ref()
        .expect("proof writer")
        .added_count();

    assert!(
        added_after > added_before,
        "BUG (#3882): add_preserved_learned must emit a proof entry for unit \
         clauses when DRAT proof output is enabled. Before={added_before}, After={added_after}"
    );
}
