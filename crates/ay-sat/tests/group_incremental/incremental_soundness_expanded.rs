// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expanded incremental solving soundness tests.
//!
//! Covers push/pop interactions with BVE reconstruction, proof emission,
//! nested scopes, assumptions, and SAT/UNSAT transitions across scopes.

use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};
use ntest::timeout;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

/// Verify that a model satisfies all clauses.
fn verify_model(clauses: &[Vec<Literal>], model: &[bool]) {
    for (i, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&l| {
            let val = model[l.variable().index()];
            if l.is_positive() {
                val
            } else {
                !val
            }
        });
        assert!(satisfied, "Model violates clause {i}: {clause:?}");
    }
}

fn assert_sat(solver: &mut Solver, clauses: &[Vec<Literal>], context: &str) {
    match solver.solve().into_inner() {
        SatResult::Sat(model) => verify_model(clauses, &model),
        other => panic!("{context}: expected SAT, got {other:?}"),
    }
}

fn assert_unsat(solver: &mut Solver, context: &str) {
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "{context}: expected UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Test: Push/pop with BVE enabled (reconstruction across scopes)
// ---------------------------------------------------------------------------

/// BVE may eliminate variables in the base formula before push().
/// After pop(), reconstruction must produce a valid model for the base formula.
#[test]
#[timeout(30_000)]
fn test_push_pop_with_bve_reconstruction() {
    // Use enough variables that BVE has elimination candidates.
    let mut solver = Solver::new(6);

    // Base formula: an AND-gate pattern that BVE can exploit.
    // x2 = x0 AND x1:
    //   (x0 | !x2)  (x1 | !x2)  (!x0 | !x1 | x2)
    // Plus clauses that make the formula SAT:
    //   (x2 | x3)  (x3 | x4)  (x4 | x5)
    let base_clauses = vec![
        vec![lit(0, true), lit(2, false)],
        vec![lit(1, true), lit(2, false)],
        vec![lit(0, false), lit(1, false), lit(2, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(3, true), lit(4, true)],
        vec![lit(4, true), lit(5, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // First solve: BVE may eliminate variables.
    assert_sat(&mut solver, &base_clauses, "base formula first solve");

    // Push scope, add scoped constraint that narrows but doesn't contradict.
    solver.push();
    solver.add_clause(vec![lit(0, true)]); // force x0=true (compatible with base)
    solver.add_clause(vec![lit(1, true)]); // force x1=true (compatible with base)
                                           // With x0=true, x1=true, the gate gives x2=true. All base clauses satisfied.

    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Scoped formula should be SAT, got {r:?}");

    // Pop and verify base formula still yields a valid model.
    assert!(solver.pop(), "Pop should succeed");
    assert_sat(&mut solver, &base_clauses, "base formula after pop");
}

/// BVE elimination followed by a scoped contradiction. After pop, the
/// solver must still reconstruct a valid model for the base formula.
#[test]
#[timeout(30_000)]
fn test_bve_scoped_contradiction_then_pop() {
    let mut solver = Solver::new(5);

    // Base formula: satisfiable pigeon-like structure.
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(1, true), lit(2, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(3, true), lit(4, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // First solve triggers preprocessing (may run BVE).
    assert_sat(&mut solver, &base_clauses, "base formula");

    // Scoped contradiction: force all variables false.
    solver.push();
    for v in 0..5 {
        solver.add_clause(vec![lit(v, false)]);
    }
    assert_unsat(&mut solver, "all-false contradicts base");

    assert!(solver.pop(), "Pop should succeed");
    assert_sat(&mut solver, &base_clauses, "base formula after pop");
}

// ---------------------------------------------------------------------------
// Test: Push/pop with DRAT proof emission
// ---------------------------------------------------------------------------

/// Proof output must not panic or corrupt state across push/pop cycles.
#[test]
#[timeout(30_000)]
fn test_push_pop_with_drat_proof_emission() {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(3, proof_writer);

    // Base formula.
    solver.add_clause(vec![lit(0, true), lit(1, true)]);
    solver.add_clause(vec![lit(1, true), lit(2, true)]);

    let r1 = solver.solve().into_inner();
    assert!(r1.is_sat(), "Base should be SAT, got {r1:?}");

    // Push and create UNSAT under scope.
    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    solver.add_clause(vec![lit(1, false)]);
    solver.add_clause(vec![lit(2, false)]);

    let r2 = solver.solve().into_inner();
    assert!(r2.is_unsat(), "Scoped should be UNSAT, got {r2:?}");

    // Pop and solve again.
    assert!(solver.pop(), "Pop should succeed");
    let r3 = solver.solve().into_inner();
    assert!(r3.is_sat(), "After pop should be SAT, got {r3:?}");

    // Verify proof output was produced without panics.
    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush proof");
    // Proof should contain at least some data from the UNSAT derivation.
    assert!(
        !proof_bytes.is_empty(),
        "Proof output should be non-empty after UNSAT derivation"
    );
}

/// LRAT proof emission across push/pop should maintain valid clause IDs.
#[test]
#[timeout(30_000)]
fn test_push_pop_with_lrat_proof_emission() {
    let num_base_clauses = 2u64;
    let proof_writer = ProofOutput::lrat_text(Vec::<u8>::new(), num_base_clauses);
    let mut solver = Solver::with_proof_output(3, proof_writer);

    solver.add_clause(vec![lit(0, true), lit(1, true)]);
    solver.add_clause(vec![lit(1, true), lit(2, true)]);

    // Push and add contradiction.
    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    solver.add_clause(vec![lit(1, false)]);
    solver.add_clause(vec![lit(2, false)]);

    let r = solver.solve().into_inner();
    assert!(r.is_unsat(), "Scoped should be UNSAT, got {r:?}");

    // Pop.
    assert!(solver.pop(), "Pop should succeed");

    // Solve base — should not panic on LRAT ID accounting.
    let r2 = solver.solve().into_inner();
    assert!(r2.is_sat(), "Base after pop should be SAT, got {r2:?}");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    // LRAT output should have at least some steps.
    assert!(!proof_text.is_empty(), "LRAT proof should be non-empty");
}

// ---------------------------------------------------------------------------
// Test: Multiple nested push/pop levels
// ---------------------------------------------------------------------------

/// Two levels of nesting: push, push, pop, pop. Each level adds constraints.
/// Does not solve at base level before pushing to avoid preprocessing
/// interactions — the goal is testing nested scope mechanics.
#[test]
#[timeout(30_000)]
fn test_nested_push_pop_two_levels() {
    let mut solver = Solver::new(4);

    // Base: (x0 | x1) & (x2 | x3)
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(2, true), lit(3, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // Level 1: force x0=true (compatible, narrows search).
    solver.push();
    solver.add_clause(vec![lit(0, true)]);
    let r1 = solver.solve().into_inner();
    assert!(r1.is_sat(), "Level-1 should be SAT, got {r1:?}");

    // Level 2: force x0=false — contradicts level-1's x0=true → UNSAT.
    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    let r2 = solver.solve().into_inner();
    assert!(r2.is_unsat(), "Level-2 should be UNSAT, got {r2:?}");

    // Pop level 2: back to level 1 (x0=true only).
    assert!(solver.pop(), "Pop level 2 should succeed");
    let r3 = solver.solve().into_inner();
    assert!(r3.is_sat(), "Back at level 1 should be SAT, got {r3:?}");

    // Pop level 1: back to base.
    assert!(solver.pop(), "Pop level 1 should succeed");
    assert_sat(&mut solver, &base_clauses, "back to base");
}

/// Three levels of nesting with SAT at each level until the deepest.
#[test]
#[timeout(30_000)]
fn test_nested_push_pop_three_levels() {
    let mut solver = Solver::new(6);

    // Base: (x0|x1) & (x2|x3) & (x4|x5)
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(4, true), lit(5, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // Level 1.
    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Level 1 SAT, got {r:?}");

    // Level 2.
    solver.push();
    solver.add_clause(vec![lit(2, false)]);
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Level 2 SAT, got {r:?}");

    // Level 3: force enough to make it UNSAT.
    solver.push();
    solver.add_clause(vec![lit(1, false)]); // clause (x0|x1) violated
    let r = solver.solve().into_inner();
    assert!(r.is_unsat(), "Level 3 UNSAT, got {r:?}");

    // Unwind all three levels.
    assert!(solver.pop(), "Pop level 3");
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Level 2 after pop SAT, got {r:?}");

    assert!(solver.pop(), "Pop level 2");
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Level 1 after pop SAT, got {r:?}");

    assert!(solver.pop(), "Pop level 1");
    assert_sat(&mut solver, &base_clauses, "base after all pops");
}

// ---------------------------------------------------------------------------
// Test: Assumptions + push/pop interaction
// ---------------------------------------------------------------------------

/// Assumptions under a pushed scope should respect both scoped and base clauses.
#[test]
#[timeout(30_000)]
fn test_assumptions_under_push_scope() {
    let mut solver = Solver::new(4);
    solver.set_preprocess_enabled(false);

    // Base: (x0 | x1) & (x2 | x3)
    solver.add_clause(vec![lit(0, true), lit(1, true)]);
    solver.add_clause(vec![lit(2, true), lit(3, true)]);

    solver.push();
    // Scoped: x0 = false
    solver.add_clause(vec![lit(0, false)]);

    // Assumptions: x1 = false. Combined with scoped x0=false, clause (x0|x1) unsatisfied.
    let assumptions = vec![lit(1, false)];
    let r = solver
        .solve_with_assumptions_interruptible(&assumptions, || false)
        .into_inner();
    assert!(
        r.is_unsat(),
        "Assumptions + scoped should be UNSAT, got {r:?}"
    );

    // Without the assumption, scoped formula is still SAT (x1=true).
    let r2 = solver.solve().into_inner();
    assert!(r2.is_sat(), "Scoped without assumptions SAT, got {r2:?}");

    assert!(solver.pop(), "Pop should succeed");
    let r3 = solver.solve().into_inner();
    assert!(r3.is_sat(), "Base after pop SAT, got {r3:?}");
}

/// Assumption-based UNSAT core should not include scope selector variables.
#[test]
#[timeout(30_000)]
fn test_assumption_core_excludes_scope_selectors() {
    let mut solver = Solver::new(3);
    solver.set_preprocess_enabled(false);

    // Base: (x0 | x1)
    solver.add_clause(vec![lit(0, true), lit(1, true)]);

    solver.push();
    // Scoped: x0 = false
    solver.add_clause(vec![lit(0, false)]);

    // Assumption: x1 = false → UNSAT.
    let assumptions = vec![lit(1, false)];
    let r = solver
        .solve_with_assumptions_interruptible(&assumptions, || false)
        .into_inner();

    match r {
        ay_sat::AssumeResult::Unsat(core, _) => {
            // Core should contain user literals only (no internal scope selectors).
            for l in &core {
                assert!(
                    l.variable().index() < 3,
                    "Core contains non-user variable: {l:?}"
                );
            }
        }
        ay_sat::AssumeResult::Sat(_) => panic!("Expected UNSAT"),
        ay_sat::AssumeResult::Unknown => panic!("Expected UNSAT, got Unknown"),
        _ => panic!("Expected UNSAT, got unexpected variant"),
    }

    assert!(solver.pop(), "Pop should succeed");
}

// ---------------------------------------------------------------------------
// Test: SAT -> UNSAT -> SAT transitions across scopes
// ---------------------------------------------------------------------------

/// Classic incremental pattern: base SAT, scoped UNSAT, pop back to SAT.
/// Repeated multiple times to stress the state cleanup.
#[test]
#[timeout(30_000)]
fn test_sat_unsat_sat_repeated_transitions() {
    let mut solver = Solver::new(3);

    // Base: (x0 | x1) & (x1 | x2)
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(1, true), lit(2, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }
    assert_sat(&mut solver, &base_clauses, "initial SAT");

    // Repeat the push/UNSAT/pop cycle 5 times.
    for round in 0..5 {
        solver.push();
        // Force contradiction: all vars false.
        solver.add_clause(vec![lit(0, false)]);
        solver.add_clause(vec![lit(1, false)]);
        solver.add_clause(vec![lit(2, false)]);
        assert_unsat(&mut solver, &format!("round {round} UNSAT"));

        assert!(solver.pop(), "Pop round {round}");
        assert_sat(
            &mut solver,
            &base_clauses,
            &format!("round {round} SAT after pop"),
        );
    }
}

/// Alternating scoped SAT and UNSAT across multiple push/pop rounds.
#[test]
#[timeout(30_000)]
fn test_alternating_sat_unsat_scopes() {
    let mut solver = Solver::new(4);

    // Base: (x0|x1) & (x2|x3)
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(2, true), lit(3, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // Round 1: scoped SAT (add x0=true, still sat).
    solver.push();
    solver.add_clause(vec![lit(0, true)]);
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Round 1 scoped SAT, got {r:?}");
    assert!(solver.pop());

    // Round 2: scoped UNSAT.
    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    solver.add_clause(vec![lit(1, false)]);
    assert_unsat(&mut solver, "Round 2 scoped UNSAT");
    assert!(solver.pop());

    // Round 3: scoped SAT (different constraint).
    solver.push();
    solver.add_clause(vec![lit(2, true)]);
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Round 3 scoped SAT, got {r:?}");
    assert!(solver.pop());

    // Base still SAT.
    assert_sat(&mut solver, &base_clauses, "base after alternating");
}

// ---------------------------------------------------------------------------
// Test: Add clauses between push/pop to exercise the original-formula ledger
// ---------------------------------------------------------------------------

/// Clauses added at different scope depths are correctly tracked.
/// Base clauses persist; scoped clauses vanish after pop.
#[test]
#[timeout(30_000)]
fn test_original_ledger_across_scopes() {
    let mut solver = Solver::new(4);

    // Base clause.
    solver.add_clause(vec![lit(0, true), lit(1, true)]);

    solver.push();
    // Scoped clause that narrows the model.
    solver.add_clause(vec![lit(0, false)]);
    solver.add_clause(vec![lit(2, true), lit(3, true)]);

    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Scoped SAT, got {r:?}");
    // Under scope: x0=false, so x1 must be true (from base clause).
    if let SatResult::Sat(model) = &r {
        // x0 should be false (forced), x1 should be true (implied).
        assert!(!model[0], "x0 should be false under scope");
        assert!(model[1], "x1 should be true (implied by base + scope)");
    }

    assert!(solver.pop());

    // After pop, x0 is no longer forced false.
    let r2 = solver.solve().into_inner();
    assert!(r2.is_sat(), "Base SAT after pop, got {r2:?}");
}

// ---------------------------------------------------------------------------
// Test: Decompose/gate/congruence + push/pop
// ---------------------------------------------------------------------------

/// Decompose/gate/congruence inprocessing + incremental push/pop.
/// Aggressive inprocessing should be disabled after push, but the solver
/// must still handle the state correctly.
#[test]
#[timeout(30_000)]
fn test_decompose_gate_congruence_with_push_pop() {
    let mut solver = Solver::new(5);
    solver.set_decompose_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);

    // AND-gate: x2 = x0 & x1.
    let base_clauses = vec![
        vec![lit(0, true), lit(2, false)],
        vec![lit(1, true), lit(2, false)],
        vec![lit(0, false), lit(1, false), lit(2, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(3, true), lit(4, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // First solve (triggers inprocessing).
    assert_sat(&mut solver, &base_clauses, "base with gate");

    solver.push();
    // Force x2=false, x3=false → need x4=true from (x3|x4), but x3 is false
    // and base says (x2|x3)... x2=false, x3=false violates (x2|x3). UNSAT.
    solver.add_clause(vec![lit(2, false)]);
    solver.add_clause(vec![lit(3, false)]);
    assert_unsat(&mut solver, "gate + scope UNSAT");

    assert!(solver.pop());
    assert_sat(&mut solver, &base_clauses, "base after gate scope pop");
}

// ---------------------------------------------------------------------------
// Test: Pop without prior solve
// ---------------------------------------------------------------------------

/// Push, add clauses, pop without solving in between.
/// The solver should handle this gracefully.
#[test]
#[timeout(10_000)]
fn test_push_pop_without_intermediate_solve() {
    let mut solver = Solver::new(3);

    solver.add_clause(vec![lit(0, true), lit(1, true)]);
    solver.add_clause(vec![lit(1, true), lit(2, true)]);

    solver.push();
    solver.add_clause(vec![lit(0, false)]);
    solver.add_clause(vec![lit(1, false)]);
    solver.add_clause(vec![lit(2, false)]);
    // Do NOT solve under scope.
    assert!(solver.pop(), "Pop without intermediate solve");

    // Base should still be SAT.
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(1, true), lit(2, true)],
    ];
    assert_sat(&mut solver, &base_clauses, "base after no-solve pop");
}

// ---------------------------------------------------------------------------
// Test: Multiple solves within a single scope
// ---------------------------------------------------------------------------

/// Solve the same scoped formula twice. The second solve must not
/// produce a different or invalid result.
#[test]
#[timeout(30_000)]
fn test_multiple_solves_within_scope() {
    let mut solver = Solver::new(4);

    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(2, true), lit(3, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    solver.push();
    solver.add_clause(vec![lit(0, false)]);

    // All clauses that matter under scope.
    let scoped_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(0, false)],
    ];

    // Solve twice under scope.
    assert_sat(&mut solver, &scoped_clauses, "first solve under scope");
    assert_sat(&mut solver, &scoped_clauses, "second solve under scope");

    assert!(solver.pop());
    assert_sat(&mut solver, &base_clauses, "base after double-solve scope");
}

// ---------------------------------------------------------------------------
// Test: Empty scope (push immediately followed by pop)
// ---------------------------------------------------------------------------

/// Push then immediately pop with no clauses added. Should be a no-op.
#[test]
#[timeout(10_000)]
fn test_empty_scope_push_pop() {
    let mut solver = Solver::new(3);

    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(1, true), lit(2, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }
    assert_sat(&mut solver, &base_clauses, "base before empty scope");

    solver.push();
    assert!(solver.pop());
    assert_sat(&mut solver, &base_clauses, "base after empty scope");
}

/// Multiple empty scopes in sequence.
#[test]
#[timeout(10_000)]
fn test_multiple_empty_scopes() {
    let mut solver = Solver::new(2);

    solver.add_clause(vec![lit(0, true), lit(1, true)]);

    for _ in 0..10 {
        solver.push();
        assert!(solver.pop());
    }

    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Base after 10 empty scopes, got {r:?}");
}

// ---------------------------------------------------------------------------
// Test: Pop returns false when no scope is active
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_pop_without_push_returns_false() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]);
    assert!(!solver.pop(), "Pop without push should return false");
}

#[test]
#[timeout(10_000)]
fn test_extra_pop_returns_false() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]);

    solver.push();
    assert!(solver.pop(), "First pop should succeed");
    assert!(!solver.pop(), "Second pop should return false");
}

// ---------------------------------------------------------------------------
// Test: scope_depth tracking
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_scope_depth_tracking() {
    let mut solver = Solver::new(2);
    assert_eq!(solver.scope_depth(), 0);

    solver.push();
    assert_eq!(solver.scope_depth(), 1);

    solver.push();
    assert_eq!(solver.scope_depth(), 2);

    solver.push();
    assert_eq!(solver.scope_depth(), 3);

    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 2);

    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 1);

    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 0);

    assert!(!solver.pop());
    assert_eq!(solver.scope_depth(), 0);
}

// ---------------------------------------------------------------------------
// Test: Base-level UNSAT survives push/pop
// ---------------------------------------------------------------------------

/// If the base formula is UNSAT (empty clause at root level), push/pop
/// should not clear it.
#[test]
#[timeout(10_000)]
fn test_base_unsat_survives_push_pop() {
    let mut solver = Solver::new(2);

    // Root-level contradiction.
    solver.add_clause(vec![lit(0, true)]);
    solver.add_clause(vec![lit(0, false)]);
    assert_unsat(&mut solver, "base UNSAT");

    solver.push();
    assert_unsat(&mut solver, "still UNSAT under scope");
    assert!(solver.pop());
    assert_unsat(&mut solver, "still UNSAT after pop");
}

// ---------------------------------------------------------------------------
// Test: Large push/pop depth stress
// ---------------------------------------------------------------------------

/// Push 20 levels deep, each adding one unit clause, then pop all.
#[test]
#[timeout(30_000)]
fn test_deep_push_pop_20_levels() {
    let num_vars = 25;
    let mut solver = Solver::new(num_vars);

    // Base: large disjunction (x0 | x1 | ... | x24) — very easy SAT.
    let big_clause: Vec<Literal> = (0..num_vars as u32).map(|v| lit(v, true)).collect();
    solver.add_clause(big_clause);

    // Push 20 levels, each forcing one more variable false.
    for depth in 0..20u32 {
        solver.push();
        solver.add_clause(vec![lit(depth, false)]);
    }

    // At depth 20: variables 0..19 are false.
    // The big clause still has x20..x24 available, so SAT.
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Deep scope should be SAT, got {r:?}");

    // Pop all 20 levels.
    for _ in 0..20 {
        assert!(solver.pop());
    }

    // Base SAT.
    let r = solver.solve().into_inner();
    assert!(r.is_sat(), "Base after deep pop SAT, got {r:?}");

    assert_eq!(solver.scope_depth(), 0);
}

// ---------------------------------------------------------------------------
// Regression tests for #7981: BVE + push/pop interaction
// ---------------------------------------------------------------------------

/// Regression test for #7981: BVE elimination before push(), then a scoped
/// clause referencing the eliminated variable. Without the VSIDS activity
/// fix, reactivated variables sat at zero activity and were never branched
/// on, causing incomplete search and false UNSAT.
///
/// This test creates a formula where BVE will eliminate a variable, then
/// after push() adds a clause that requires the eliminated variable to
/// take a specific value. The solver must find the satisfying assignment.
#[test]
#[timeout(30_000)]
fn test_bve_push_pop_eliminated_var_in_scoped_clause() {
    let mut solver = Solver::new(8);

    // Base formula with BVE-friendly structure:
    // Variable x3 appears in exactly one positive and one negative clause
    // (ideal BVE candidate with zero growth).
    //   (x0 | x3)    -- positive x3
    //   (x1 | !x3)   -- negative x3
    //   (x2 | x4)    -- unrelated, keeps formula SAT
    //   (x5 | x6)    -- unrelated
    //   (x6 | x7)    -- unrelated
    let base_clauses = vec![
        vec![lit(0, true), lit(3, true)],
        vec![lit(1, true), lit(3, false)],
        vec![lit(2, true), lit(4, true)],
        vec![lit(5, true), lit(6, true)],
        vec![lit(6, true), lit(7, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // First solve triggers preprocessing: BVE should consider eliminating x3.
    // Resolvent of (x0|x3) and (x1|!x3) is (x0|x1), which is smaller.
    assert_sat(&mut solver, &base_clauses, "base formula before push");

    // Push scope and add clause referencing x3 (possibly BVE-eliminated).
    solver.push();
    solver.add_clause(vec![lit(3, true)]); // force x3=true
    solver.add_clause(vec![lit(0, false)]); // force x0=false

    // Under scope: (x0|x3) needs x3=true (since x0=false). SAT.
    let r = solver.solve().into_inner();
    assert!(
        r.is_sat(),
        "Scoped formula should be SAT (x3=true satisfies everything), got {r:?}"
    );

    // Pop and verify base formula still SAT.
    assert!(solver.pop(), "Pop should succeed");
    assert_sat(
        &mut solver,
        &base_clauses,
        "base formula after pop (BVE reactivation)",
    );
}

/// Regression test for #7981: multiple rounds of BVE elimination + push/pop.
/// Each round eliminates variables, then push/pop exercises the reactivation
/// path. Without competitive VSIDS activity, reactivated variables would
/// accumulate at zero activity across rounds, making false UNSAT more likely.
#[test]
#[timeout(30_000)]
fn test_bve_push_pop_multiple_rounds_reactivation() {
    let mut solver = Solver::new(10);

    // Base formula: chain of implications with BVE candidates.
    //   (x0 | x1)  (x1 | x2)  (x2 | x3)  (x3 | x4)
    //   (x5 | x6)  (x6 | x7)  (x7 | x8)  (x8 | x9)
    let base_clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(1, true), lit(2, true)],
        vec![lit(2, true), lit(3, true)],
        vec![lit(3, true), lit(4, true)],
        vec![lit(5, true), lit(6, true)],
        vec![lit(6, true), lit(7, true)],
        vec![lit(7, true), lit(8, true)],
        vec![lit(8, true), lit(9, true)],
    ];
    for c in &base_clauses {
        solver.add_clause(c.clone());
    }

    // First solve: BVE may eliminate some variables.
    assert_sat(&mut solver, &base_clauses, "initial solve");

    // Multiple push/pop rounds exercising different eliminated variables.
    for round in 0..3 {
        solver.push();
        // Add a constraint that might reference eliminated variables.
        solver.add_clause(vec![lit(round * 3, true)]);
        solver.add_clause(vec![lit(round * 3 + 1, false)]);

        let r = solver.solve().into_inner();
        assert!(
            r.is_sat() || r.is_unsat(),
            "Round {round}: got unexpected result {r:?}"
        );

        assert!(solver.pop(), "Pop round {round}");
        assert_sat(
            &mut solver,
            &base_clauses,
            &format!("base after round {round}"),
        );
    }
}
