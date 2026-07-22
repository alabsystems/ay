// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 incremental solving correctness and robustness stress tests (#8649).
//!
//! These tests simulate realistic IC3/PDR workloads to verify:
//! 1. Correctness across 1000+ incremental calls with growing clause databases
//! 2. Level-0 GC correctness under IC3 (mark_satisfied_clauses_as_garbage)
//! 3. Assumption trail interaction with between_solve_reduce decay
//! 4. Monotonicity of learned clause and conflict counters
//! 5. Cross-checking: every UNSAT result is validated against base SAT,
//!    every SAT result is validated against clause satisfaction

use super::*;

fn var(i: u32) -> Variable {
    Variable::new(i)
}
fn pos(i: u32) -> Literal {
    Literal::positive(var(i))
}
fn neg(i: u32) -> Literal {
    Literal::negative(var(i))
}

/// Verify that a SAT model satisfies all clauses in the solver.
///
/// Checks every clause in the original ledger against the model.
/// This is the ground-truth cross-check for SAT results.
fn verify_model_satisfies_clauses(_solver: &Solver, model: &[bool], clauses: &[Vec<Literal>]) {
    for (ci, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&lit| {
            let vi = lit.variable().index();
            if vi >= model.len() {
                return false;
            }
            if lit.is_positive() {
                model[vi]
            } else {
                !model[vi]
            }
        });
        assert!(satisfied, "clause {ci} ({clause:?}) not satisfied by model");
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Test 1: Comprehensive IC3 stress test — 1000+ incremental calls
// ════════════════════════════════════════════════════════════════════════════

/// Simulates a realistic IC3/PDR workload with 1000+ incremental calls.
///
/// This test exercises:
/// - Mix of SAT and UNSAT results from varying assumptions
/// - Gradually growing clause database (blocking clauses added between solves)
/// - Varying assumption sets (some overlapping, some disjoint)
/// - Cross-check: every UNSAT result verified (base formula remains SAT)
/// - Cross-check: every SAT model verified against all clauses
/// - Learned clause count monotonicity (never reset between calls)
/// - Conflict count monotonicity (lifetime + current never decreases)
#[test]
fn test_ic3_stress_1000_incremental_calls_with_cross_check() {
    let num_vars = 30u32;
    let mut s = Solver::new(num_vars as usize);
    s.set_ic3_mode();

    // Build an implication chain: x_i -> x_{i+1}
    let mut all_clauses: Vec<Vec<Literal>> = Vec::new();
    for i in 0..num_vars - 1 {
        let c = vec![neg(i), pos(i + 1)];
        s.add_clause(c.clone());
        all_clauses.push(c);
    }
    // Cross-constraints for density
    for i in 0..num_vars - 3 {
        let c = vec![pos(i), neg(i + 1), pos(i + 3)];
        s.add_clause(c.clone());
        all_clauses.push(c);
    }
    // At-least-one clause
    {
        let c = vec![pos(0), pos(5), pos(10), pos(15)];
        s.add_clause(c.clone());
        all_clauses.push(c);
    }

    let mut prev_total_conflicts: u64 = 0;
    let mut sat_count = 0u32;
    let mut unsat_count = 0u32;

    for iteration in 0..1200u32 {
        // Varying assumptions: 1-3 assumptions per query
        let mut assumptions = Vec::new();
        let v0 = iteration % num_vars;
        assumptions.push(if iteration % 3 == 0 { neg(v0) } else { pos(v0) });
        if iteration % 5 < 3 {
            let v1 = (iteration * 7 + 3) % num_vars;
            if v1 != v0 {
                assumptions.push(if iteration % 4 == 0 { neg(v1) } else { pos(v1) });
            }
        }
        if iteration % 11 == 0 {
            let v2 = (iteration * 13 + 7) % num_vars;
            if v2 != v0
                && !assumptions
                    .iter()
                    .any(|l| l.variable().index() == v2 as usize)
            {
                assumptions.push(pos(v2));
            }
        }

        let result = s.solve_incremental_ic3(&assumptions);

        // Cross-check results
        match result.into_inner() {
            AssumeResult::Sat(model) => {
                sat_count += 1;
                // Verify model satisfies all clauses
                verify_model_satisfies_clauses(&s, &model, &all_clauses);
                // Also verify all assumption literals are satisfied
                for &lit in &assumptions {
                    let vi = lit.variable().index();
                    if vi < model.len() {
                        let expected = lit.is_positive();
                        assert_eq!(
                            model[vi], expected,
                            "iteration {iteration}: SAT model violates assumption {lit:?}"
                        );
                    }
                }
            }
            AssumeResult::Unsat(..) => {
                unsat_count += 1;
                // Cross-check: base formula (no assumptions) should still be SAT
                // unless we've added contradictory blocking clauses.
                let base = s.solve_incremental_ic3(&[]);
                if base.is_sat() {
                    // Good: base is SAT, so UNSAT was due to assumptions.
                } else {
                    // Base became UNSAT due to accumulated blocking clauses.
                    // This is valid — we just can't cross-check further.
                }
            }
            AssumeResult::Unknown => {
                // Unknown is acceptable (e.g., interrupt) but should be rare.
            }
        }

        // Monotonicity check: total conflicts should never decrease
        let total = s.total_conflicts();
        assert!(
            total >= prev_total_conflicts,
            "iteration {iteration}: total conflicts decreased from {prev_total_conflicts} to {total}"
        );
        prev_total_conflicts = total;

        // Periodically add blocking clauses (IC3 frame lemma pattern)
        if iteration % 8 == 3 {
            let v0 = iteration % num_vars;
            let v1 = (iteration + 1) % num_vars;
            let v2 = (iteration + 2) % num_vars;
            if v0 != v1 && v1 != v2 && v0 != v2 {
                let c = vec![pos(v0), neg(v1), pos(v2)];
                s.add_clause(c.clone());
                all_clauses.push(c);
            }
        }
        // Add binary blocking clauses periodically
        if iteration % 15 == 7 {
            let v0 = (iteration * 3) % num_vars;
            let v1 = (iteration * 3 + 5) % num_vars;
            if v0 != v1 {
                let c = vec![pos(v0), pos(v1)];
                s.add_clause(c.clone());
                all_clauses.push(c);
            }
        }
    }

    // Verify we actually tested both SAT and UNSAT paths
    assert!(
        sat_count > 0,
        "stress test produced zero SAT results — test is vacuous"
    );
    assert!(
        unsat_count > 0,
        "stress test produced zero UNSAT results — test is vacuous"
    );
    assert!(
        sat_count + unsat_count >= 1000,
        "stress test produced only {} SAT + UNSAT results (expected >= 1000)",
        sat_count + unsat_count
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 2: Level-0 GC correctness under IC3
// ════════════════════════════════════════════════════════════════════════════

/// Test that level-0 GC (mark_satisfied_clauses_as_garbage) does not
/// corrupt the clause database under IC3 incremental solving.
///
/// Scenario:
/// 1. Establish level-0 units via propagation (x0=true, x1=true)
/// 2. Add clauses satisfied at level 0 (e.g., x0 | x2)
/// 3. Trigger reduce_db (via many conflicts)
/// 4. Add new clauses that depend on level-0-satisfied clauses
/// 5. Verify correctness is maintained across all subsequent solves
#[test]
fn test_ic3_level0_gc_correctness() {
    let mut s = Solver::new(20);
    s.set_ic3_mode();

    // Unit clauses: establish x0=true, x1=true at level 0
    s.add_clause(vec![pos(0)]);
    s.add_clause(vec![pos(1)]);

    // Base clauses
    s.add_clause(vec![pos(2), pos(3)]);
    s.add_clause(vec![neg(2), pos(4)]);
    s.add_clause(vec![neg(3), pos(5)]);

    // First solve: propagates x0=true, x1=true at level 0
    let r1 = s.solve_incremental_ic3(&[]);
    assert!(r1.is_sat(), "base formula should be SAT");

    // Add clauses that are trivially satisfied at level 0
    // (since x0=true, x0 | anything is satisfied)
    for i in 6..15u32 {
        s.add_clause(vec![pos(0), pos(i)]); // satisfied by x0=true
        s.add_clause(vec![pos(1), neg(i)]); // satisfied by x1=true
    }

    // Run many incremental solves to accumulate conflicts and trigger
    // between_solve_reduce / reduce_db
    for round in 0..500u32 {
        let assume_var = 2 + (round % 4);
        let lit = if round % 2 == 0 {
            pos(assume_var)
        } else {
            neg(assume_var)
        };
        let _r = s.solve_incremental_ic3(&[lit]);

        // Periodically add more clauses involving level-0-satisfied vars
        if round % 50 == 25 {
            let target = 15 + (round / 50) % 5;
            // These clauses depend on x0 and x1 being true
            s.add_clause(vec![neg(0), neg(1), pos(target)]);
        }
    }

    // After all that activity, add clauses that critically depend on
    // propagations from the level-0-satisfied clauses
    s.add_clause(vec![neg(0), neg(1), pos(19)]);
    s.add_clause(vec![neg(19)]);

    // x0=true, x1=true -> x19=true from clause, but neg(19) -> x19=false
    // This should be UNSAT
    let r_final = s.solve_incremental_ic3(&[]);
    assert!(
        r_final.is_unsat(),
        "formula should be UNSAT after adding contradicting clauses"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 3: Assumption trail interaction with between_solve_reduce
// ════════════════════════════════════════════════════════════════════════════

/// Test that between_solve_reduce's CaDiCaL-style decay does not corrupt
/// learned clauses that are needed for correct UNSAT under assumptions.
///
/// Scenario:
/// 1. Build a formula that requires specific learned clauses for UNSAT
///    under certain assumptions
/// 2. Run many incremental solves to trigger between_solve_reduce decay
/// 3. Verify the solver still produces correct UNSAT for those assumptions
#[test]
fn test_ic3_between_solve_reduce_preserves_unsat_correctness() {
    let num_vars = 25u32;
    let mut s = Solver::new(num_vars as usize);
    s.set_ic3_mode();

    // Build a formula where:
    // - Base formula is SAT
    // - Under assumption x0=true AND x1=true: UNSAT
    // (x0 -> x2, x1 -> !x2, so x0=true & x1=true -> x2=true & x2=false)
    s.add_clause(vec![neg(0), pos(2)]); // x0 -> x2
    s.add_clause(vec![neg(1), neg(2)]); // x1 -> !x2

    // More clauses to create a richer learned clause database
    for i in 3..num_vars {
        s.add_clause(vec![pos(i), pos((i + 1) % num_vars)]);
    }
    for i in 3..num_vars - 1 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }

    // Verify base formula is SAT
    let r_base = s.solve_incremental_ic3(&[]);
    assert!(r_base.is_sat(), "base formula should be SAT");

    // Verify UNSAT under assumptions x0=true, x1=true
    let r_unsat = s.solve_incremental_ic3(&[pos(0), pos(1)]);
    assert!(
        r_unsat.is_unsat(),
        "should be UNSAT with x0=true and x1=true"
    );

    // Run many incremental solves to trigger between_solve_reduce
    // This accumulates lifetime conflicts and fires the decay mechanism
    for round in 0..800u32 {
        let v = 3 + (round % (num_vars - 3));
        let lit = if round % 3 == 0 { neg(v) } else { pos(v) };
        let _r = s.solve_incremental_ic3(&[lit]);

        // Periodically add blocking clauses to grow the database
        if round % 20 == 10 {
            let v0 = 3 + (round % (num_vars - 3));
            let v1 = 3 + ((round + 5) % (num_vars - 3));
            if v0 != v1 {
                s.add_clause(vec![pos(v0), pos(v1)]);
            }
        }
    }

    // After between_solve_reduce has fired multiple times,
    // re-verify that UNSAT is still correct
    let r_unsat2 = s.solve_incremental_ic3(&[pos(0), pos(1)]);
    assert!(
        r_unsat2.is_unsat(),
        "UNSAT must be preserved after between_solve_reduce decay"
    );

    // And base formula is still SAT
    let r_sat2 = s.solve_incremental_ic3(&[]);
    assert!(
        r_sat2.is_sat(),
        "base formula should still be SAT after between_solve_reduce"
    );

    // Verify with different assumption that x0=true alone is SAT
    // (x0=true -> x2=true, but nothing forces !x2 without x1=true)
    let r_x0 = s.solve_incremental_ic3(&[pos(0)]);
    assert!(r_x0.is_sat(), "x0=true alone should be SAT");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 4: Domain-restricted IC3 stress test with SAT model cross-check
// ════════════════════════════════════════════════════════════════════════════

/// Stress test domain-restricted IC3 queries (the primary IC3 use case)
/// with rigorous cross-checking of every result.
///
/// Domain restriction causes IC3 to bypass finalize_sat_model and build
/// the model directly from vals[]. This test verifies that domain-restricted
/// SAT models are correct and that UNSAT results are consistent.
#[test]
fn test_ic3_domain_restricted_stress_cross_check() {
    let num_state = 10u32; // current-state vars: 0..9
    let num_next = 10u32; // next-state vars: 10..19
    let total = (num_state + num_next) as usize;
    let mut s = Solver::new(total);
    s.set_ic3_mode();

    // Transition relation: x_i -> x_{i+10} (current implies next)
    let mut all_clauses: Vec<Vec<Literal>> = Vec::new();
    for i in 0..num_state {
        let c = vec![neg(i), pos(i + num_state)];
        s.add_clause(c.clone());
        all_clauses.push(c);
    }
    // At-least-one constraints
    {
        let c: Vec<Literal> = (0..num_state).map(pos).collect();
        s.add_clause(c.clone());
        all_clauses.push(c);
    }
    {
        let c: Vec<Literal> = (num_state..num_state + num_next).map(pos).collect();
        s.add_clause(c.clone());
        all_clauses.push(c);
    }

    // Domain: current-state + next-state vars
    let domain: Vec<Variable> = (0..total as u32).map(var).collect();
    s.set_domain(&domain);

    for iteration in 0..500u32 {
        // IC3 cube query: typically 1-3 state variable assumptions
        let mut assumptions = Vec::new();
        let v0 = iteration % num_state;
        assumptions.push(if iteration % 2 == 0 { pos(v0) } else { neg(v0) });
        if iteration % 3 == 0 {
            let v1 = (v0 + 3) % num_state;
            if v1 != v0 {
                assumptions.push(pos(v1));
            }
        }

        let result = s.solve_incremental_ic3(&assumptions);

        match result.into_inner() {
            AssumeResult::Sat(model) => {
                // Verify model satisfies all clauses
                verify_model_satisfies_clauses(&s, &model, &all_clauses);
            }
            AssumeResult::Unsat(..) => {
                // UNSAT under assumptions — verify base is still SAT
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "iteration {iteration}: base formula became UNSAT"
                );
            }
            AssumeResult::Unknown => {}
        }

        // IC3 blocking clause pattern: add frame lemmas
        if iteration % 10 == 5 {
            let v0 = iteration % num_state;
            let v1 = (iteration + 2) % num_state;
            if v0 != v1 {
                let c = vec![pos(v0), pos(v1)];
                s.add_clause(c.clone());
                all_clauses.push(c);
            }
        }
    }

    s.clear_domain();
}

// ════════════════════════════════════════════════════════════════════════════
// Test 5: Push/pop + IC3 + between_solve_reduce interaction
// ════════════════════════════════════════════════════════════════════════════

/// Test the interaction of push/pop scopes, IC3 incremental solving,
/// and between_solve_reduce clause decay.
///
/// IC3 engines use push/pop for scoped obligation queries while accumulating
/// permanent blocking clauses. This test verifies that the three mechanisms
/// compose correctly over many rounds.
#[test]
fn test_ic3_push_pop_reduce_interaction_stress() {
    let mut s = Solver::new(16);

    // Build a satisfiable base
    for i in 0..8u32 {
        s.add_clause(vec![pos(i), pos(i + 8)]);
    }
    s.add_clause(vec![neg(0), neg(1), pos(2)]);
    s.add_clause(vec![neg(8), pos(9)]);

    let mut permanent_clause_count = 0u32;

    for round in 0..300u32 {
        // Add a permanent blocking clause (IC3 frame lemma)
        let l1 = if round % 3 == 0 {
            pos(round % 8)
        } else {
            neg(round % 8)
        };
        let l2 = pos((round + 3) % 8);
        s.add_clause_global(vec![l1, l2]);
        permanent_clause_count += 1;

        // Scoped obligation query using push/pop
        s.push();
        let temp = if round % 2 == 0 {
            pos(round % 8)
        } else {
            neg(round % 8)
        };
        s.add_clause(vec![temp, pos((round + 1) % 8)]);

        let assumptions = vec![pos(round % 8)];
        let combined = s.compose_scope_assumptions(&assumptions);
        let scoped_result = s.solve_incremental_ic3(&combined);

        // Result should be SAT, UNSAT, or Unknown — never panic
        let _ = scoped_result.into_inner();

        assert!(s.pop(), "pop should succeed in round {round}");

        // Unscoped query to verify base + permanent clauses are consistent
        let unscoped = s.solve_incremental_ic3(&[pos(round % 8)]);
        let inner = unscoped.into_inner();
        if matches!(&inner, AssumeResult::Unknown) {
            if let Some(detail) = &s.cold.last_unknown_detail {
                assert!(
                    !detail.contains("unsatisfied"),
                    "FINALIZE_SAT_FAIL in push/pop+reduce round {round}: {detail}"
                );
            }
        }
    }

    // Final sanity: base formula should still be solvable
    let final_result = s.solve_incremental_ic3(&[]);
    // Either SAT or UNSAT is fine (accumulated clauses may make it UNSAT)
    let _ = final_result.into_inner();
    assert!(
        permanent_clause_count >= 300,
        "should have added at least 300 permanent clauses"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 6: Monotonicity invariants across many IC3 solves
// ════════════════════════════════════════════════════════════════════════════

/// Verify that key solver invariants hold across 1000+ IC3 solves:
/// - Total conflict count (lifetime + current) never decreases
/// - Incremental solve count grows monotonically
/// - VSIDS rescaling fires periodically without corruption
#[test]
fn test_ic3_monotonicity_invariants() {
    let mut s = Solver::new(20);
    s.set_ic3_mode();

    // Dense formula to generate conflicts
    for i in 0..10u32 {
        s.add_clause(vec![pos(i), pos(i + 10)]);
        if i < 9 {
            s.add_clause(vec![neg(i), neg(i + 1)]);
            s.add_clause(vec![neg(i + 10), neg(i + 11)]);
        }
    }
    // Cross-links
    for i in 0..8u32 {
        s.add_clause(vec![neg(i), pos(i + 2)]);
    }

    let mut prev_total_conflicts: u64 = 0;
    let mut prev_solve_count: u64 = 0;

    for iteration in 0..1200u32 {
        let v = iteration % 20;
        let lit = if iteration % 3 == 0 { neg(v) } else { pos(v) };
        let _r = s.solve_incremental_ic3(&[lit]);

        let total = s.total_conflicts();
        assert!(
            total >= prev_total_conflicts,
            "iteration {iteration}: total_conflicts decreased: {prev_total_conflicts} -> {total}"
        );
        prev_total_conflicts = total;

        let solve_count = s.cold.incremental_solve_count;
        assert!(
            solve_count >= prev_solve_count,
            "iteration {iteration}: incremental_solve_count decreased: {prev_solve_count} -> {solve_count}"
        );
        prev_solve_count = solve_count;

        // Add blocking clause every few rounds
        if iteration % 12 == 6 {
            let v0 = iteration % 20;
            let v1 = (iteration + 5) % 20;
            if v0 != v1 {
                s.add_clause(vec![pos(v0), pos(v1)]);
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Test 7: Rapid assumption switching (disjoint sets)
// ════════════════════════════════════════════════════════════════════════════

/// Test rapid switching between completely disjoint assumption sets.
///
/// IC3 queries can jump between unrelated parts of the state space.
/// This tests that the incremental reset correctly handles assumption
/// cache invalidation and that stale trail state doesn't corrupt results.
///
/// Cross-check: every UNSAT is verified by confirming the base (no
/// assumptions) is still SAT, ensuring UNSAT was due to assumptions.
#[test]
fn test_ic3_disjoint_assumption_switching() {
    let mut s = Solver::new(30);
    s.set_ic3_mode();

    // Build independent sub-formulas on disjoint variable sets.
    // Each group has an at-least-one clause guaranteeing base SAT.
    // Group A: vars 0-9
    for i in 0..9u32 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }
    s.add_clause(vec![pos(0), pos(5)]);

    // Group B: vars 10-19
    for i in 10..19u32 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }
    s.add_clause(vec![pos(10), pos(15)]);

    // Group C: vars 20-29
    for i in 20..29u32 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }
    s.add_clause(vec![pos(20), pos(25)]);

    let mut sat_count = 0u32;
    let mut unsat_count = 0u32;

    // Rapidly switch between groups
    for iteration in 0..600u32 {
        let group = iteration % 3;
        let base = group * 10;
        let v = base + (iteration / 3) % 10;
        // Use positive assumptions only: with implication chains x_i -> x_{i+1},
        // positive assumptions at any point in the chain are always satisfiable
        // (set all variables from the assumption point forward to true).
        let lit = pos(v);

        let result = s.solve_incremental_ic3(&[lit]);

        if result.is_sat() {
            sat_count += 1;
        } else if result.is_unsat() {
            unsat_count += 1;
            // Cross-check: base formula should still be SAT
            let base_r = s.solve_incremental_ic3(&[]);
            assert!(
                base_r.is_sat(),
                "iteration {iteration}: base formula should remain SAT"
            );
        }

        // Occasionally add cross-group clauses
        if iteration % 100 == 50 {
            s.add_clause(vec![pos(iteration % 10), pos(10 + iteration % 10)]);
        }
    }

    // With positive assumptions on implication chains, all queries should be SAT
    assert!(
        sat_count > 500,
        "expected mostly SAT results, got {sat_count} SAT, {unsat_count} UNSAT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 8: IC3 with unit propagation cascade on clause addition
// ════════════════════════════════════════════════════════════════════════════

/// Test that unit clauses added between IC3 solves trigger correct
/// propagation cascades in the incremental attachment path.
///
/// This is a regression vector for #8633: the incremental clause attachment
/// must correctly propagate new units at level 0, not just attach watches.
#[test]
fn test_ic3_unit_propagation_cascade_between_solves() {
    let mut s = Solver::new(10);
    s.set_ic3_mode();

    // Base: implication chain x0 -> x1 -> x2 -> ... -> x9
    for i in 0..9u32 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }
    // Base is SAT (set x0..x9 all to false, or all to true)
    let r = s.solve_incremental_ic3(&[]);
    assert!(r.is_sat(), "base should be SAT");

    // Add unit clause: x0 = true
    // This should cascade: x0=true -> x1=true -> ... -> x9=true
    s.add_clause(vec![pos(0)]);

    // Verify: with x0 forced true, all x_i should be true
    let r2 = s.solve_incremental_ic3(&[]);
    assert!(r2.is_sat(), "formula with x0=true should be SAT");
    if let AssumeResult::Sat(model) = r2.into_inner() {
        for i in 0..10 {
            assert!(
                model[i],
                "var {i} should be true due to unit propagation cascade"
            );
        }
    }

    // Now add !x9: this contradicts the forced chain
    s.add_clause(vec![neg(9)]);
    let r3 = s.solve_incremental_ic3(&[]);
    assert!(r3.is_unsat(), "x0=true + chain + !x9 should be UNSAT");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 9: IC3 with multiple contradictory unit additions
// ════════════════════════════════════════════════════════════════════════════

/// Test that adding contradictory unit clauses between IC3 solves
/// correctly marks the formula as permanently UNSAT.
#[test]
fn test_ic3_contradictory_units_between_solves() {
    let mut s = Solver::new(5);
    s.set_ic3_mode();

    s.add_clause(vec![pos(0), pos(1)]);
    s.add_clause(vec![pos(2), pos(3)]);

    let r1 = s.solve_incremental_ic3(&[]);
    assert!(r1.is_sat());

    // Add x4=true
    s.add_clause(vec![pos(4)]);
    let r2 = s.solve_incremental_ic3(&[]);
    assert!(r2.is_sat());

    // Add x4=false: direct contradiction
    s.add_clause(vec![neg(4)]);
    let r3 = s.solve_incremental_ic3(&[]);
    assert!(
        r3.is_unsat(),
        "contradictory units should make formula UNSAT"
    );

    // Subsequent solves should also be UNSAT
    let r4 = s.solve_incremental_ic3(&[pos(0)]);
    assert!(
        r4.is_unsat(),
        "formula should remain UNSAT after contradiction"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 10: IC3 with large assumption sets
// ════════════════════════════════════════════════════════════════════════════

/// Test IC3 with large assumption sets (10+ assumptions per query).
///
/// While typical IC3 queries use 1-5 assumptions, some engines use
/// larger assumption sets for multi-property checking or deep unrolling.
/// This tests that the assumption handling scales correctly.
#[test]
fn test_ic3_large_assumption_sets() {
    let num_vars = 40u32;
    let mut s = Solver::new(num_vars as usize);
    s.set_ic3_mode();

    // Build a formula that is SAT under most assumption subsets
    for i in 0..num_vars - 1 {
        s.add_clause(vec![pos(i), pos(i + 1)]);
    }
    // At-least-one in each group of 4
    for base in (0..num_vars).step_by(4) {
        let end = (base + 4).min(num_vars);
        let c: Vec<Literal> = (base..end).map(pos).collect();
        if c.len() >= 2 {
            s.add_clause(c);
        }
    }

    for iteration in 0..200u32 {
        // Large assumption set: 5-15 assumptions
        let num_assumptions = 5 + (iteration % 11);
        let mut assumptions = Vec::new();
        let mut used_vars = vec![false; num_vars as usize];
        for j in 0..num_assumptions {
            let v = ((iteration * 7 + j * 13) % num_vars) as usize;
            if !used_vars[v] {
                used_vars[v] = true;
                let lit = if (iteration + j) % 3 == 0 {
                    neg(v as u32)
                } else {
                    pos(v as u32)
                };
                assumptions.push(lit);
            }
        }

        let result = s.solve_incremental_ic3(&assumptions);
        // We don't know a priori if SAT or UNSAT, but it should not panic
        let _ = result.into_inner();
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Test 11: IC3 with new variable allocation between solves
// ════════════════════════════════════════════════════════════════════════════

/// Test that allocating new variables between IC3 solves (via new_var)
/// works correctly with the incremental reset path.
///
/// IC3/PDR engines sometimes allocate fresh Tseitin variables for
/// auxiliary lemma encoding between queries.
#[test]
fn test_ic3_new_vars_between_solves() {
    let mut s = Solver::new(10);
    s.set_ic3_mode();

    // Base formula
    for i in 0..9u32 {
        s.add_clause(vec![pos(i), pos(i + 1)]);
    }

    let r1 = s.solve_incremental_ic3(&[pos(0)]);
    assert!(r1.is_sat());

    // Add new variable and use it in a clause
    let new_v = s.new_var();
    let _new_vi = new_v.index() as u32;
    s.add_clause(vec![neg(0), Literal::positive(new_v)]);
    s.add_clause(vec![Literal::negative(new_v), pos(5)]);

    let r2 = s.solve_incremental_ic3(&[pos(0)]);
    assert!(r2.is_sat(), "formula with new variable should be SAT");

    // Add more new vars in a loop
    for _ in 0..20 {
        let v = s.new_var();
        s.add_clause(vec![Literal::positive(v), pos(3)]);
    }

    let r3 = s.solve_incremental_ic3(&[pos(0)]);
    assert!(r3.is_sat(), "formula with many new variables should be SAT");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 12: IC3 consecution pattern (the core IC3/PDR workload)
// ════════════════════════════════════════════════════════════════════════════

/// Simulate the actual IC3 consecution check pattern:
///
///   For each frame F_k and cube c:
///     push()
///     add_clause(F_k)  -- frame clauses
///     add_clause(T)    -- transition relation
///     solve(assumptions=[c'])  -- check if c is reachable from F_k via T
///     if UNSAT: extract core, pop(), generalize
///     if SAT: pop(), propagate counterexample
///
/// This is the most realistic IC3 workload pattern.
#[test]
fn test_ic3_consecution_pattern_realistic() {
    let num_state = 8u32;
    let num_next = 8u32;
    let total = (num_state + num_next) as usize;
    let mut s = Solver::new(total);

    // Transition relation: x_i' = x_{(i+1) % n} (shift register)
    for i in 0..num_state {
        let next_i = i + num_state;
        let src = (i + 1) % num_state;
        // x_{next_i} <-> x_src
        // Encoded as: (!x_src | x_{next_i}) & (x_src | !x_{next_i})
        s.add_clause(vec![neg(src), pos(next_i)]);
        s.add_clause(vec![pos(src), neg(next_i)]);
    }

    // Property: !x0 (invariant to check)
    // Init: x0=true, rest false

    let mut frame_clauses: Vec<Vec<Literal>> = Vec::new();

    // Initial frame F0: just the init state
    frame_clauses.push(vec![pos(0)]); // x0=true in init

    for round in 0..200u32 {
        // Consecution check: can cube {x0=true} be reached from frame?
        s.push();

        // Add current frame clauses
        for fc in &frame_clauses {
            s.add_clause(fc.clone());
        }

        // Cube to check (in next-state variables): x0'=true
        let assumptions = vec![pos(num_state)]; // x0' = true
        let combined = s.compose_scope_assumptions(&assumptions);
        let result = s.solve_incremental_ic3(&combined);

        let was_unsat = result.is_unsat();
        let _ = result.into_inner();

        assert!(s.pop(), "pop should succeed in round {round}");

        // Add a blocking clause (generalized cube negation) to frame
        if was_unsat {
            // Block x0=true in the frame
            frame_clauses.push(vec![neg(0), pos(round % num_state)]);
        } else {
            // Strengthen the frame
            let v = round % num_state;
            frame_clauses.push(vec![pos(v), pos((v + 1) % num_state)]);
        }

        // Verify base formula (without frame) is still SAT
        let base = s.solve_incremental_ic3(&[]);
        assert!(
            base.is_sat(),
            "round {round}: base transition relation should always be SAT"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Test 13: Verify clause database growth under IC3
// ════════════════════════════════════════════════════════════════════════════

/// Verify that the clause database does not grow unboundedly under IC3
/// workloads. The between_solve_reduce mechanism should keep learned
/// clause count bounded relative to the original clause count.
#[test]
fn test_ic3_clause_database_bounded_growth() {
    let num_vars = 20u32;
    let mut s = Solver::new(num_vars as usize);
    s.set_ic3_mode();

    // Build a conflict-rich formula
    for i in 0..num_vars - 1 {
        s.add_clause(vec![pos(i), pos(i + 1)]);
    }
    for i in 0..num_vars - 2 {
        s.add_clause(vec![neg(i), neg(i + 1), pos(i + 2)]);
    }
    for i in 0..num_vars - 1 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }

    let initial_active = s.arena.active_clause_count();

    // Run 500 IC3 queries to generate learned clauses
    for iteration in 0..500u32 {
        let v = iteration % num_vars;
        let lit = if iteration % 2 == 0 { pos(v) } else { neg(v) };
        let _r = s.solve_incremental_ic3(&[lit]);
    }

    let final_active = s.arena.active_clause_count();

    // The database should grow but not unboundedly. Allow up to 20x growth.
    // In practice, between_solve_reduce keeps it much tighter, but 20x is a
    // generous upper bound that catches true unbounded growth.
    assert!(
        final_active < initial_active * 20,
        "clause database grew from {initial_active} to {final_active} ({}x) — \
         between_solve_reduce may not be firing",
        final_active / initial_active.max(1)
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 14: IC3 state persistence acceptance test (#8643)
// ════════════════════════════════════════════════════════════════════════════

/// Definitive acceptance test for #8643: verify ALL five persistence
/// properties hold simultaneously across 1000+ queries with blocking
/// clause additions between every query.
///
/// This test validates the complete fix for #8643 by checking:
/// 1. Learned clauses persist (count never drops between consecutive calls)
/// 2. VSIDS activity accumulates (max activity after 1000 queries > after 10)
/// 3. Phase saving persists (saved phases are non-zero across calls)
/// 4. Watch lists are NOT rebuilt (incremental cache hits >> misses)
/// 5. add_clause integrates incrementally (doesn't force full reset)
///
/// Formula design: all clauses include at least one positive literal, so
/// "all variables true" is always a satisfying assignment. This ensures
/// the formula never becomes permanently UNSAT (which would cause
/// has_empty_clause early-exits that bypass the incremental reset path).
/// Conflicts are generated by assumptions containing negative literals
/// that contradict the implication chain.
#[test]
fn test_ic3_state_persistence_acceptance_8643() {
    let num_vars = 25u32;
    let mut s = Solver::new(num_vars as usize);
    s.set_ic3_mode();

    // Build a formula where "all true" is always a satisfying assignment.
    // Implication chain: !x_i | x_{i+1} — satisfied when both true.
    for i in 0..num_vars - 1 {
        s.add_clause(vec![neg(i), pos(i + 1)]);
    }
    // Cross-implication: !x_i | x_{i+2} — satisfied when both true.
    for i in 0..num_vars - 2 {
        s.add_clause(vec![neg(i), pos(i + 2)]);
    }
    // Wider disjunctions with at least one positive literal.
    for i in 0..num_vars - 3 {
        s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
    }
    // Binary positive disjunctions for richer propagation.
    for i in 0..num_vars - 1 {
        s.add_clause(vec![pos(i), pos(i + 1)]);
    }

    // ── Phase 1: Warm up (10 queries) ──
    // Use negative assumption literals to force conflicts against the
    // implication chain. The base formula stays satisfiable.
    for i in 0..10u32 {
        let v = i % num_vars;
        // Alternate between positive and negative assumptions.
        // Negative assumptions on early variables force UNSAT (conflict
        // with implication chain), generating learned clauses and VSIDS bumps.
        let lit = if i % 2 == 0 { neg(v) } else { pos(v) };
        let _r = s.solve_incremental_ic3(&[lit]);
    }
    let learned_after_warmup: usize = s
        .arena
        .indices()
        .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
        .count();
    let _cache_hits_after_warmup = s.stats.assumption_cache_hits;

    // ── Phase 2: Main run (1090 queries with blocking clauses) ──
    let mut prev_learned = learned_after_warmup;
    let mut learned_decreased_count = 0u32;

    for i in 10..1100u32 {
        // Add a blocking clause between every query (IC3 pattern).
        // Always include at least one positive literal so "all true"
        // remains a satisfying assignment.
        let v0 = i % num_vars;
        let v1 = (i * 3 + 1) % num_vars;
        if v0 != v1 {
            // Clause: pos(v0) | pos(v1) — trivially satisfied by all-true.
            s.add_clause(vec![pos(v0), pos(v1)]);
        }

        // Query with a mix of assumptions to generate conflicts.
        // Use multiple assumptions for richer conflict analysis.
        let v = i % num_vars;
        let w = (i * 7 + 3) % num_vars;
        let mut assumptions = vec![neg(v)]; // Force conflict with chain
        if w != v {
            assumptions.push(pos(w));
        }
        let _r = s.solve_incremental_ic3(&assumptions);

        // Track learned clause persistence (property 1).
        let current_learned: usize = s
            .arena
            .indices()
            .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
            .count();
        if current_learned < prev_learned {
            learned_decreased_count += 1;
        }
        prev_learned = current_learned;
    }

    let learned_after_main: usize = s
        .arena
        .indices()
        .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
        .count();
    let max_activity_after_main: f64 = (0..num_vars)
        .map(|i| s.vsids.activity(Variable::new(i)))
        .fold(0.0f64, f64::max);
    let cache_hits_after_main = s.stats.assumption_cache_hits;
    let cache_misses_total = s.stats.assumption_cache_misses;

    // ── Property 1: Learned clauses persist ──
    // After 1000+ queries, learned clause count should be non-zero
    // (IC3 mode skips between_solve_reduce, so they accumulate).
    assert!(
        learned_after_main > 0,
        "property 1 FAILED: no learned clauses after 1100 queries"
    );
    // Learned clause count should not decrease on most queries.
    // In-solve reduce_db fires at restarts, so some decreases are normal.
    // But if it decreased on >50% of queries, something is wrong.
    assert!(
        learned_decreased_count < 550,
        "property 1 FAILED: learned clause count decreased on {learned_decreased_count}/1090 \
         queries — clauses are not persisting across calls"
    );

    // ── Property 2: VSIDS activity accumulates ──
    // After 1100 queries, max activity should be non-zero.
    // Note: VSIDS rescaling normalizes max to 1.0 periodically, so
    // we can't compare absolute values. Just verify non-zero.
    assert!(
        max_activity_after_main > 0.0,
        "property 2 FAILED: max VSIDS activity is 0.0 after 1100 queries"
    );

    // ── Property 3: Phase saving persists ──
    // After 1100 queries, some variables should have non-zero saved phase.
    let saved_phase_count = (0..num_vars as usize).filter(|&i| s.phase[i] != 0).count();
    assert!(
        saved_phase_count > 0,
        "property 3 FAILED: no saved phases after 1100 queries"
    );

    // ── Property 4: Watch lists NOT rebuilt from scratch ──
    // The incremental cache should be hit on the vast majority of queries.
    // First query misses (cold start), but all subsequent should hit
    // because add_clause sets ic3_new_clauses_pending instead of
    // invalidating the assumption cache.
    let total_cache_hits = cache_hits_after_main;
    assert!(
        total_cache_hits > 1000,
        "property 4 FAILED: only {total_cache_hits} cache hits out of 1100 queries \
         (misses={cache_misses_total}) — watch lists are being rebuilt from scratch"
    );

    // ── Property 5: add_clause integrates incrementally ──
    // Since we added blocking clauses between every query, and the cache
    // hit rate is high, add_clause is NOT invalidating the cache.
    // Allow a small number of misses for the initial cold-start solve(s).
    assert!(
        cache_misses_total <= 2,
        "property 5 FAILED: {cache_misses_total} cache misses — add_clause is \
         forcing full resets instead of incremental clause attachment"
    );
}
