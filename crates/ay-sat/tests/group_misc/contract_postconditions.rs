// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Contract postcondition tests for CDCL hot path.
//!
//! Part of Epic #4172 (sat-debuggability), proof_coverage phase.
//! These tests exercise the 4 contract postconditions identified in
//! [m7sat-P1]3 audit as HIGH/MEDIUM priority gaps:
//!
//! 1. pick_next_decision_variable: returned var is unassigned + not eliminated
//! 2. ConflictAnalyzer::clear(): all seen marks cleared after sparse clear
//! 3. backtrack: every kept trail reason points to active clause
//! 4. add_learned_clause: UIP is unassigned at learning time
//!
//! These tests verify the contracts don't fire on valid solver states.
//! In debug builds, the debug_asserts in the production code catch violations.
//! These tests complement by exercising the paths through the public API.

use ay_sat::{parse_dimacs, Literal, Solver, Variable};

// ========================================================================
// Contract 1: pick_next_decision_variable postcondition
// ========================================================================

/// Force many decisions to stress the decision variable selection path.
/// This 50-variable satisfiable formula requires the solver to make many
/// decisions, each of which must return an unassigned, non-eliminated variable.
///
/// In debug builds, the postcondition in pick_next_decision_variable fires
/// if the VSIDS heap or VMTF returns a bad variable.
#[test]
fn test_decision_variable_postcondition_many_decisions() {
    let n = 50;
    let mut solver = Solver::new(n);

    // Create a chain of implications that forces many decision variables:
    // (x0 ∨ x1) ∧ (x1 ∨ x2) ∧ ... ∧ (x_{n-2} ∨ x_{n-1})
    // This is satisfiable (all true) but requires decisions at each level.
    for i in 0..(n - 1) {
        solver.add_clause(vec![
            Literal::positive(Variable::new(i as u32)),
            Literal::positive(Variable::new((i + 1) as u32)),
        ]);
    }
    // Add some negative implications to force conflicts and backtracking:
    // (¬x0 ∨ ¬x_{n/2}) forces conflict when both are decided true
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new((n / 2) as u32)),
    ]);

    let result = solver.solve().into_inner();
    assert!(result.is_sat(), "formula is satisfiable");
}

/// Decision variable postcondition under BVE (bounded variable elimination).
/// After preprocessing eliminates variables, the decision heuristic must
/// never select eliminated variables.
///
/// This formula has an AND-gate structure that BVE can eliminate (x8), while
/// the remaining variables form an independent SAT problem requiring many
/// decisions. The solver must decide all non-eliminated variables without
/// selecting the eliminated gate variable.
#[test]
fn test_decision_variable_skips_eliminated_after_bve() {
    let n = 20;
    let mut solver = Solver::new(n);
    let v = |i: u32| Variable::new(i);

    // AND-gate: x8 = AND(x0, x1). BVE can eliminate x8.
    // (¬x8 ∨ x0) ∧ (¬x8 ∨ x1) ∧ (x8 ∨ ¬x0 ∨ ¬x1)
    solver.add_clause(vec![Literal::negative(v(8)), Literal::positive(v(0))]);
    solver.add_clause(vec![Literal::negative(v(8)), Literal::positive(v(1))]);
    solver.add_clause(vec![
        Literal::positive(v(8)),
        Literal::negative(v(0)),
        Literal::negative(v(1)),
    ]);

    // Gate variable x8 interacts with the rest of the formula
    solver.add_clause(vec![Literal::positive(v(8)), Literal::positive(v(9))]);
    solver.add_clause(vec![Literal::negative(v(8)), Literal::positive(v(10))]);

    // Independent SAT subproblem on x2-x19 (excluding x8) that requires
    // many decisions. Chain + cross-links create a loosely constrained SAT
    // instance. Every non-eliminated variable must be decided.
    for i in 2..18 {
        if i == 8 {
            continue;
        }
        let next = if i + 1 == 8 { i + 2 } else { i + 1 };
        if next < n as u32 {
            solver.add_clause(vec![Literal::positive(v(i)), Literal::positive(v(next))]);
        }
    }
    // Cross-links to force some backtracking
    solver.add_clause(vec![Literal::negative(v(3)), Literal::negative(v(15))]);
    solver.add_clause(vec![Literal::negative(v(5)), Literal::negative(v(17))]);

    let result = solver.solve().into_inner();
    assert!(
        result.is_sat(),
        "formula is satisfiable — decisions must skip eliminated vars"
    );
}

// ========================================================================
// Contract 2: seen marks cleared after conflict analysis
// ========================================================================

/// Multiple conflicts exercise the seen-mark clear/reuse cycle.
/// Each conflict analysis marks variables as "seen", and the sparse clear
/// must reset all marks before the next analysis. Stale marks would cause
/// the next conflict to incorrectly skip resolution steps.
#[test]
fn test_seen_marks_cleared_across_multiple_conflicts() {
    // PHP (Pigeonhole Principle) 4→3: forces many conflicts with overlapping
    // variable sets, stressing the seen-mark clear path.
    let mut solver = Solver::new(12);

    // p_{i,j} = pigeon i goes to hole j (i=0..3, j=0..2)
    // Variable encoding: p_{i,j} = i * 3 + j
    let p = |i: u32, j: u32| -> Literal { Literal::positive(Variable::new(i * 3 + j)) };

    // Each pigeon must go to some hole
    for i in 0..4 {
        solver.add_clause(vec![p(i, 0), p(i, 1), p(i, 2)]);
    }

    // No two pigeons in the same hole
    for j in 0..3 {
        for i1 in 0..4 {
            for i2 in (i1 + 1)..4 {
                solver.add_clause(vec![
                    Literal::negative(Variable::new(i1 * 3 + j)),
                    Literal::negative(Variable::new(i2 * 3 + j)),
                ]);
            }
        }
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(4,3) is unsatisfiable");
}

// ========================================================================
// Contract 3: backtrack reason-clause validity
// ========================================================================

/// Deep backtracking after conflict: every kept trail literal must have
/// a valid (active) reason clause. This test creates a formula that forces
/// long implication chains and deep backjumps.
#[test]
fn test_backtrack_reason_validity_deep_backjump() {
    let n = 20;
    let mut solver = Solver::new(n);

    // Create a formula that forces deep implication chains:
    // Level 0: x0 is unit
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);

    // Long implication chain at level 0: x0 → x1 → x2 → ... → x9
    for i in 0..9 {
        solver.add_clause(vec![
            Literal::negative(Variable::new(i as u32)),
            Literal::positive(Variable::new((i + 1) as u32)),
        ]);
    }

    // Force conflict at deep level requiring backjump to level 0:
    // The remaining variables (x10-x19) create a conflict tree
    for i in 10..18 {
        solver.add_clause(vec![
            Literal::positive(Variable::new(i as u32)),
            Literal::positive(Variable::new((i + 1) as u32)),
        ]);
    }
    // Contradiction involving deeply implied literals
    solver.add_clause(vec![
        Literal::negative(Variable::new(9)),
        Literal::positive(Variable::new(10)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(9)),
        Literal::negative(Variable::new(10)),
        Literal::positive(Variable::new(19)),
    ]);
    solver.add_clause(vec![Literal::negative(Variable::new(19))]);

    let result = solver.solve().into_inner();
    // Result doesn't matter — the test verifies debug_asserts don't fire
    // during the backtracking that must occur
    let _ = result;
}

/// Clause reduction (reduce_db) followed by continued solving.
/// After learned clauses are garbage-collected, reason references must
/// not point to deleted clauses.
///
/// Uses random 3-SAT generated via DIMACS format and parsed through the
/// standard pipeline. The formula is generated above the phase transition
/// to guarantee UNSAT, and is large enough to force ≥2000 CDCL conflicts
/// that trigger reduce_db.
///
/// Why not PHP? PHP(10,9) generates 2000+ conflicts but takes >60s in
/// debug mode due to exponential resolution complexity. Random 3-SAT
/// above the transition is hard for CDCL but not exponential — each
/// conflict is cheap, so debug overhead stays manageable.
///
/// Preprocessing is disabled to prevent AY's conditioning pass from
/// trivializing the formula before CDCL starts.
///
/// Part of #4629: PHP(10,9) infeasible in debug mode.
/// Ported from m7arch commit 49b602615.
#[test]
fn test_backtrack_reason_after_clause_reduction() {
    let num_vars: u32 = 120;
    let num_clauses: usize = 540; // ratio 4.5, above phase transition ~4.26

    for base_seed in 1u64..51 {
        let mut dimacs = format!("p cnf {num_vars} {num_clauses}\n");

        // Xorshift64 RNG: uniform distribution across all bits.
        // LCG low bit alternates deterministically, so xorshift is used instead.
        let mut state = base_seed;
        let xorshift = |s: &mut u64| -> u64 {
            let mut x = *s;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *s = x;
            x
        };

        for _ in 0..num_clauses {
            let v0 = (xorshift(&mut state) % u64::from(num_vars)) as i32 + 1;
            let mut v1 = (xorshift(&mut state) % u64::from(num_vars - 1)) as i32 + 1;
            if v1 >= v0 {
                v1 += 1;
            }
            let mut v2 = (xorshift(&mut state) % u64::from(num_vars - 2)) as i32 + 1;
            if v2 >= v0.min(v1) {
                v2 += 1;
            }
            if v2 >= v0.max(v1) {
                v2 += 1;
            }

            let l0 = if xorshift(&mut state) & 1 == 0 {
                v0
            } else {
                -v0
            };
            let l1 = if xorshift(&mut state) & 1 == 0 {
                v1
            } else {
                -v1
            };
            let l2 = if xorshift(&mut state) & 1 == 0 {
                v2
            } else {
                -v2
            };
            dimacs.push_str(&format!("{l0} {l1} {l2} 0\n"));
        }

        let formula = parse_dimacs(&dimacs).expect("valid DIMACS");
        let mut solver = formula.into_solver();
        solver.set_preprocess_enabled(false);

        let result = solver.solve().into_inner();
        let conflicts = solver.num_conflicts();
        if result.is_unsat() && conflicts >= 2000 {
            return;
        }
    }

    panic!(
        "no suitable UNSAT instance found in seeds 1..51 for \
         random 3-SAT({num_vars}, {num_clauses}). \
         Need UNSAT with >=2000 conflicts."
    );
}

// ========================================================================
// Contract 4: UIP unassigned at add_learned_clause
// ========================================================================

/// Conflict analysis must produce a UIP that is unassigned after backtracking.
/// This test exercises the CDCL loop: conflict → analyze → backtrack → learn.
/// The UIP-unassigned assert fires if backtracking doesn't clear the UIP.
#[test]
fn test_uip_unassigned_at_learning_time() {
    let mut solver = Solver::new(8);

    // Formula that forces a specific conflict structure:
    // x0 = true (unit)
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // x0 → x1
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    // Conflict: decide x2=true, then (¬x1 ∨ ¬x2 ∨ x3) propagates x3,
    // then (¬x3 ∨ x4) propagates x4, then (¬x2 ∨ ¬x4) conflicts.
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::positive(Variable::new(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(4)),
    ]);
    // Additional clauses using x5-x7 to keep the formula satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable::new(5)),
        Literal::positive(Variable::new(6)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(6)),
        Literal::positive(Variable::new(7)),
    ]);

    let result = solver.solve().into_inner();
    assert!(result.is_sat(), "formula is satisfiable");
}

/// Push/pop scoped solving exercises the UIP contract under incremental mode.
/// Each scope creates independent conflict analyses, and the UIP must be
/// unassigned in each scope's backtracking context.
#[test]
fn test_uip_unassigned_with_push_pop() {
    let mut solver = Solver::new(6);

    // Base formula
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);

    // Scope 1: add conflict
    solver.push();
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ]);
    solver.add_clause(vec![Literal::positive(Variable::new(1))]);
    solver.add_clause(vec![Literal::positive(Variable::new(2))]);
    // This might be unsat or sat depending on propagation
    let _ = solver.solve().into_inner();
    let _ = solver.pop();

    // Scope 2: different formula
    solver.push();
    solver.add_clause(vec![
        Literal::positive(Variable::new(3)),
        Literal::negative(Variable::new(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::positive(Variable::new(5)),
    ]);
    let result = solver.solve().into_inner();
    assert!(result.is_sat());
    let _ = solver.pop();
}
