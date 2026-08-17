// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::search` to preserve test FQNs.

// ========================================================================
// Chronological Backtracking Tests
// ========================================================================

#[test]
fn test_chrono_backtrack_decision() {
    // Test that chrono backtracking is used when jump distance is large
    let mut solver = Solver::new(10);
    solver.decision_level = 150;
    solver.chrono_enabled = true;

    // Jump of 140 levels exceeds CHRONO_LEVEL_LIMIT (100), should use chrono BT
    let actual = solver.compute_chrono_backtrack_level(10);
    assert_eq!(actual, 149); // Should backtrack to level - 1
    assert_eq!(solver.stats.chrono_backtracks, 1);

    // Jump of 50 levels is within limit, should use NCB
    solver.decision_level = 60;
    let actual = solver.compute_chrono_backtrack_level(10);
    assert_eq!(actual, 10); // Should use the original jump level
}

#[test]
fn test_chrono_backtrack_disabled() {
    // Test that chrono backtracking can be disabled
    let mut solver = Solver::new(10);
    solver.decision_level = 150;
    solver.chrono_enabled = false;

    // Even with large jump, should use NCB when disabled
    let actual = solver.compute_chrono_backtrack_level(10);
    assert_eq!(actual, 10);
    assert_eq!(solver.stats.chrono_backtracks, 0);
}

#[test]
fn test_chrono_backtrack_unit_clause_always_level_0() {
    // Test that unit clauses (jump_level == 0) ALWAYS backtrack to level 0,
    // regardless of chrono BT settings. This is the fix for #1696.
    let mut solver = Solver::new(10);
    solver.chrono_enabled = true;

    // At level 150, a unit clause would normally trigger chrono BT
    // (150 > CHRONO_LEVEL_LIMIT of 100), returning level 149.
    // But unit clauses MUST return level 0.
    solver.decision_level = 150;
    let actual = solver.compute_chrono_backtrack_level(0);
    assert_eq!(actual, 0, "Unit clauses must always backtrack to level 0");

    // Verify chrono_backtracks counter is NOT incremented for unit clauses
    // (we bypass chrono BT entirely)
    assert_eq!(solver.stats.chrono_backtracks, 0);

    // Also test at a level just above CHRONO_LEVEL_LIMIT
    solver.decision_level = 105;
    let actual = solver.compute_chrono_backtrack_level(0);
    assert_eq!(actual, 0, "Unit clauses must always backtrack to level 0");

    // Also verify unit clauses work correctly when chrono is disabled
    solver.chrono_enabled = false;
    solver.decision_level = 150;
    let actual = solver.compute_chrono_backtrack_level(0);
    assert_eq!(
        actual, 0,
        "Unit clauses return level 0 even with chrono disabled"
    );
}

#[test]
fn test_chrono_backtrack_preserves_correctness() {
    // Verify that chronological backtracking doesn't break correctness
    let mut solver = Solver::new(5);
    solver.chrono_enabled = true;

    // Create a formula that requires some backtracking
    // (a OR b) AND (a OR NOT b) AND (NOT a OR c) AND (NOT a OR NOT c)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    // This formula is UNSAT
    assert!(result.is_unsat());
}

#[test]
fn test_chrono_reuse_trail_correctness() {
    // Test that chrono_reuse_trail doesn't break correctness
    // Issue #112: "causes regression on some instances"

    // Generate a random 3-SAT formula at phase transition
    fn generate_random_3sat(num_vars: u32, num_clauses: usize, seed: u64) -> Vec<Vec<i32>> {
        let mut clauses = Vec::with_capacity(num_clauses);
        let mut state = seed;
        let lcg_next = |s: &mut u64| {
            *s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
            *s
        };

        for _ in 0..num_clauses {
            let mut clause = Vec::with_capacity(3);
            for _ in 0..3 {
                let var = ((lcg_next(&mut state) % u64::from(num_vars)) + 1) as i32;
                let sign = if lcg_next(&mut state) % 2 == 0 { 1 } else { -1 };
                clause.push(var * sign);
            }
            clauses.push(clause);
        }
        clauses
    }

    // Test on multiple random formulas
    for seed in 0..10 {
        let clauses = generate_random_3sat(50, 215, seed); // 50 vars, ~4.3 ratio

        // Solve with reuse disabled
        let mut solver_disabled = Solver::new(50);
        solver_disabled.set_chrono_reuse_trail(false);
        for clause in &clauses {
            let lits: Vec<_> = clause
                .iter()
                .map(|&lit| {
                    if lit > 0 {
                        Literal::positive(Variable((lit - 1) as u32))
                    } else {
                        Literal::negative(Variable((-lit - 1) as u32))
                    }
                })
                .collect();
            solver_disabled.add_clause(lits);
        }
        let result_disabled = solver_disabled.solve().into_inner();

        // Solve with reuse enabled
        let mut solver_enabled = Solver::new(50);
        solver_enabled.set_chrono_reuse_trail(true);
        for clause in &clauses {
            let lits: Vec<_> = clause
                .iter()
                .map(|&lit| {
                    if lit > 0 {
                        Literal::positive(Variable((lit - 1) as u32))
                    } else {
                        Literal::negative(Variable((-lit - 1) as u32))
                    }
                })
                .collect();
            solver_enabled.add_clause(lits);
        }
        let result_enabled = solver_enabled.solve().into_inner();

        // Both should give same answer
        match (&result_disabled, &result_enabled) {
            (SatResult::Sat(_), SatResult::Sat(_)) | (SatResult::Unsat(_), SatResult::Unsat(_)) => {
            }
            _ => panic!(
                "Seed {seed}: disabled={result_disabled:?}, enabled={result_enabled:?} - MISMATCH!"
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Phase saving behavioral tests
// ---------------------------------------------------------------------------

/// Verify that phase saving records the polarity on every assignment.
///
/// CaDiCaL propagate.cpp:151: phase is saved in enqueue(), not just at backtrack.
/// Decides v0=TRUE at level 1, v1=FALSE at level 2. Phases are saved immediately
/// at assignment time, not deferred to backtrack.
#[test]
fn test_phase_saving_records_polarity_at_backtrack() {
    let mut solver = Solver::new(4);

    // Initially, no phase is saved (0 = unset)
    assert_eq!(
        solver.phase[0], 0,
        "phase[0] should be 0 (unset) before any assignment"
    );
    assert_eq!(
        solver.phase[1], 0,
        "phase[1] should be 0 (unset) before any assignment"
    );

    // Decide v0=TRUE at level 1, propagate to advance qhead
    solver.decide(Literal::positive(Variable(0)));
    assert!(solver.propagate().is_none(), "no conflict expected");
    // Decide v1=FALSE at level 2
    solver.decide(Literal::negative(Variable(1)));
    assert!(solver.propagate().is_none(), "no conflict expected");

    // CaDiCaL propagate.cpp:151: phases saved eagerly in enqueue()
    assert_eq!(
        solver.phase[0], 1,
        "phase[0] should be saved immediately on assignment"
    );
    assert_eq!(
        solver.phase[1], -1,
        "phase[1] should be saved immediately on assignment"
    );

    // Backtrack to level 0 — phases already saved, backtrack also saves
    solver.backtrack(0);

    assert_eq!(
        solver.phase[0], 1,
        "phase[0] should record TRUE (last assigned polarity)"
    );
    assert_eq!(
        solver.phase[1], -1,
        "phase[1] should record FALSE (last assigned polarity)"
    );
}

/// Verify that suppress_phase_saving + backtrack_without_phase_saving
/// does NOT corrupt phases.
///
/// This is the vivification safety contract: artificial decisions during
/// vivification must not overwrite real phase data. Both enqueue() and
/// backtrack must be guarded.
#[test]
fn test_backtrack_without_phase_saving_preserves_phases() {
    let mut solver = Solver::new(4);

    // First, establish real phases via normal decisions and backtrack
    solver.decide(Literal::positive(Variable(0)));
    assert!(solver.propagate().is_none());
    solver.decide(Literal::negative(Variable(1)));
    assert!(solver.propagate().is_none());
    solver.backtrack(0);

    assert_eq!(solver.phase[0], 1);
    assert_eq!(solver.phase[1], -1);

    // Now simulate vivification: suppress phase saving during artificial
    // decisions and backtrack WITHOUT phase saving.
    solver.suppress_phase_saving = true;
    solver.decide(Literal::negative(Variable(0))); // opposite polarity
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(Variable(1))); // opposite polarity
    assert!(solver.propagate().is_none());
    solver.backtrack_without_phase_saving(0);
    solver.suppress_phase_saving = false;

    assert_eq!(
        solver.phase[0], 1,
        "phase[0] must stay TRUE after vivification-style backtrack"
    );
    assert_eq!(
        solver.phase[1], -1,
        "phase[1] must stay FALSE after vivification-style backtrack"
    );
}

/// Verify that re-assigning a variable updates the saved phase on backtrack.
///
/// If v0 is first assigned TRUE, backtracked, then assigned FALSE and backtracked
/// again, phase[0] should reflect the most recent polarity (FALSE).
#[test]
fn test_phase_saving_updates_on_reassignment() {
    let mut solver = Solver::new(4);

    // First assignment: v0=TRUE
    solver.decide(Literal::positive(Variable(0)));
    assert!(solver.propagate().is_none());
    solver.backtrack(0);
    assert_eq!(solver.phase[0], 1);

    // Second assignment: v0=FALSE (opposite polarity)
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate().is_none());
    solver.backtrack(0);
    assert_eq!(
        solver.phase[0], -1,
        "phase[0] should update to FALSE after reassignment"
    );
}

/// (#8482, #8496) Backtrack gracefully handles removed variables on the trail.
///
/// BVE marks variables as eliminated without removing them from the trail
/// (matching CaDiCaL flags.cpp:34). When backtracking encounters such a
/// variable, it unassigns it but does NOT push it back onto the VSIDS heap
/// or VMTF queue -- it must never be re-decided. The primary fix is
/// `flush_learned_with_eliminated_vars()` in config_preprocess_bve.rs;
/// this tests the defense-in-depth guard.
#[test]
fn test_backtrack_skips_removed_variable_on_trail() {
    let mut solver = Solver::new(2);

    solver.decide(Literal::positive(Variable(0)));
    solver.var_lifecycle.mark_eliminated(0);

    // Should not panic; the removed variable is skipped during unassignment.
    solver.backtrack(0);

    // After backtrack, the trail should be empty (backtrack to level 0).
    assert_eq!(
        solver.trail.len(),
        0,
        "trail should be empty after backtrack(0)"
    );
    // Variable 0 should be unassigned (vals cleared).
    assert_eq!(
        solver.vals[0], 0,
        "eliminated variable should be unassigned after backtrack"
    );
}

#[test]
fn test_backtrack_zero_preserves_lrat_cursor_for_unchanged_root_prefix() {
    let mut solver = Solver::new(4);
    solver.enable_lrat();

    let root_a = Literal::positive(Variable(0));
    let root_b = Literal::negative(Variable(1));
    solver.enqueue(root_a, None);
    solver.record_unit_proof_id_for_lit(root_a, 1);
    solver.enqueue(root_b, None);
    solver.record_unit_proof_id_for_lit(root_b, 2);
    assert!(solver.propagate().is_none());

    solver.materialize_level0_unit_proofs();
    assert_eq!(solver.stats.lrat_materialize_root_trail_entries, 2);
    assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 2);

    solver.decide(Literal::positive(Variable(2)));
    assert!(solver.propagate().is_none());
    solver.backtrack(0);

    assert_eq!(solver.trail, vec![root_a, root_b]);
    assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 2);

    solver.materialize_level0_unit_proofs();
    assert_eq!(
        solver.stats.lrat_materialize_root_trail_entries, 2,
        "unchanged root prefix should not be rescanned after backtrack(0)"
    );
}

// --- Random variable frequency tests (#4919 Phase 4) ---

#[test]
fn test_random_var_freq_clamps_to_valid_range() {
    let mut solver = Solver::new(1);

    solver.set_random_var_freq(0.5);
    assert!((solver.random_var_freq() - 0.5).abs() < f64::EPSILON);

    solver.set_random_var_freq(-1.0);
    assert!(
        (solver.random_var_freq() - 0.0).abs() < f64::EPSILON,
        "negative should clamp to 0"
    );

    solver.set_random_var_freq(2.0);
    assert!(
        (solver.random_var_freq() - 1.0).abs() < f64::EPSILON,
        "above 1 should clamp to 1"
    );

    solver.set_random_var_freq(0.0);
    assert!(
        (solver.random_var_freq() - 0.0).abs() < f64::EPSILON,
        "0.0 should stay 0.0"
    );

    solver.set_random_var_freq(1.0);
    assert!(
        (solver.random_var_freq() - 1.0).abs() < f64::EPSILON,
        "1.0 should stay 1.0"
    );
}
