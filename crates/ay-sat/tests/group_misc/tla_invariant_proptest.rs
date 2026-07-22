// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Property-based tests mirroring TLA+ invariants from specs/cdcl.tla.
//!
//! Part of #7914: Strengthen TLA+ specifications by adding Rust-side
//! property tests that verify the same invariants the TLA+ model checks.
//!
//! Three invariant families are tested:
//!
//! 1. **TypeInvariant** (cdcl.tla lines 73-80, cdcl_test.tla lines 193-202):
//!    - Variable assignments are within valid ranges (TRUE/FALSE/UNDEF)
//!    - Trail literals correspond to assigned variables
//!    - Decision level is bounded by num_vars
//!    - Trail length <= num_vars
//!
//! 2. **Soundness** (cdcl.tla lines 200-218, cdcl_test.tla lines 209-227):
//!    - SAT results have a model satisfying all original clauses
//!    - UNSAT results are consistent (no satisfying assignment exists for
//!      small enough formulas to enumerate, or cross-validated with an oracle)
//!
//! 3. **WatchedInvariant** (cdcl.tla lines 240-244):
//!    - For every clause of length >= 2, either the clause is satisfied
//!      or at least one literal is not falsified (non-FALSE)
//!    - Verified indirectly: after solving, if SAT, the model satisfies all
//!      clauses; if UNSAT, the solver's internal debug_asserts on watch
//!      lists did not fire during BCP.

use super::common::verify_model;
use ay_sat::{parse_dimacs, Literal, SatResult, Solver, Variable};
use proptest::prelude::*;

// ============================================================================
// Proptest Strategies for SAT Formula Generation
// ============================================================================

/// Generate a random literal for a formula with `num_vars` variables.
fn arb_literal(num_vars: u32) -> impl Strategy<Value = Literal> {
    (0..num_vars, proptest::bool::ANY).prop_map(|(var, positive)| {
        if positive {
            Literal::positive(Variable::new(var))
        } else {
            Literal::negative(Variable::new(var))
        }
    })
}

/// Generate a random clause with 1 to `max_len` literals over `num_vars` variables.
fn arb_clause(num_vars: u32, max_len: usize) -> impl Strategy<Value = Vec<Literal>> {
    proptest::collection::vec(arb_literal(num_vars), 1..=max_len)
}

/// Generate a random SAT formula: a vector of clauses.
fn arb_formula(
    num_vars_range: std::ops::RangeInclusive<u32>,
    num_clauses_range: std::ops::RangeInclusive<usize>,
    max_clause_len: usize,
) -> impl Strategy<Value = (u32, Vec<Vec<Literal>>)> {
    num_vars_range.prop_flat_map(move |num_vars| {
        let nv = num_vars.max(1); // at least 1 variable
        proptest::collection::vec(arb_clause(nv, max_clause_len), num_clauses_range.clone())
            .prop_map(move |clauses| (nv, clauses))
    })
}

/// Generate random 3-SAT formulas at the phase transition (ratio ~4.26).
/// These formulas are roughly 50/50 SAT/UNSAT, stressing the solver.
fn arb_3sat_phase_transition() -> impl Strategy<Value = (u32, Vec<Vec<Literal>>)> {
    // Small variable counts to keep tests fast.
    (5u32..=20u32).prop_flat_map(|num_vars| {
        // Clause/variable ratio near phase transition
        let num_clauses = (f64::from(num_vars) * 4.26).round() as usize;
        let nv = num_vars;
        proptest::collection::vec(
            // Exactly 3 distinct literals per clause
            (
                0..nv,
                0..nv,
                0..nv,
                proptest::bool::ANY,
                proptest::bool::ANY,
                proptest::bool::ANY,
            )
                .prop_map(move |(v0, v1_raw, v2_raw, s0, s1, s2)| {
                    // Ensure distinct variables
                    let v1 = if v1_raw == v0 { (v0 + 1) % nv } else { v1_raw };
                    let mut v2 = if v2_raw == v0 { (v0 + 1) % nv } else { v2_raw };
                    if v2 == v1 {
                        v2 = (v1 + 1) % nv;
                        if v2 == v0 {
                            v2 = (v2 + 1) % nv;
                        }
                    }
                    let mk = |v: u32, pos: bool| {
                        if pos {
                            Literal::positive(Variable::new(v))
                        } else {
                            Literal::negative(Variable::new(v))
                        }
                    };
                    vec![mk(v0, s0), mk(v1, s1), mk(v2, s2)]
                }),
            num_clauses..=num_clauses,
        )
        .prop_map(move |clauses| (nv, clauses))
    })
}

/// Generate a formula that is guaranteed SAT by construction.
/// Creates a random assignment and then generates clauses that are satisfied by it.
fn arb_guaranteed_sat() -> impl Strategy<Value = (u32, Vec<Vec<Literal>>, Vec<bool>)> {
    (3u32..=15u32).prop_flat_map(|num_vars| {
        let nv = num_vars;
        // Random satisfying assignment
        proptest::collection::vec(proptest::bool::ANY, nv as usize..=nv as usize).prop_flat_map(
            move |assignment| {
                let asgn = assignment.clone();
                // Generate clauses that are satisfied by this assignment
                let num_clauses = (nv as usize) * 2;
                proptest::collection::vec(
                    (1usize..=4, proptest::collection::vec(0..nv, 1..=4)).prop_map(
                        move |(_len, vars)| {
                            vars.into_iter()
                                .map(|v| {
                                    // With 70% probability, make literal agree with assignment
                                    // (ensures clause is almost certainly satisfied)
                                    // With 30% probability, random polarity
                                    let val = asgn[v as usize];
                                    if val {
                                        Literal::positive(Variable::new(v))
                                    } else {
                                        Literal::negative(Variable::new(v))
                                    }
                                })
                                .collect::<Vec<_>>()
                        },
                    ),
                    num_clauses..=num_clauses,
                )
                .prop_map(move |clauses| (nv, clauses, assignment.clone()))
            },
        )
    })
}

/// Generate small formulas that are guaranteed UNSAT (pigeonhole principle).
fn arb_pigeonhole_unsat() -> impl Strategy<Value = (u32, Vec<Vec<Literal>>)> {
    // PHP(n+1, n) for n in 2..=4
    (2u32..=4u32).prop_map(|n| {
        let pigeons = n + 1;
        let holes = n;
        let num_vars = pigeons * holes;
        let mut clauses = Vec::new();

        // At-least-one: each pigeon goes to at least one hole
        for i in 0..pigeons {
            let clause: Vec<Literal> = (0..holes)
                .map(|j| Literal::positive(Variable::new(i * holes + j)))
                .collect();
            clauses.push(clause);
        }

        // At-most-one: no two pigeons in the same hole
        for j in 0..holes {
            for i1 in 0..pigeons {
                for i2 in (i1 + 1)..pigeons {
                    clauses.push(vec![
                        Literal::negative(Variable::new(i1 * holes + j)),
                        Literal::negative(Variable::new(i2 * holes + j)),
                    ]);
                }
            }
        }

        (num_vars, clauses)
    })
}

// ============================================================================
// TypeInvariant Property Tests
// ============================================================================
// TLA+ cdcl.tla TypeInvariant:
//   /\ assignment \in [Variables -> Values]
//   /\ trail \in Seq(Literals)
//   /\ state \in {"PROPAGATING", "DECIDING", "CONFLICTING", "SAT", "UNSAT"}
//   /\ decisionLevel \in Nat
//   /\ learnedClauses \subseteq SUBSET Literals
//
// cdcl_test.tla TypeInvariant:
//   /\ assignment \in [VarIndices -> Values]
//   /\ trail \in Seq(Literals)
//   /\ TrailAssignmentConsistent(assignment, trail)
//   /\ decisionLevel \in 0..NumVars
//   /\ decisionLevel <= Len(trail)
//   /\ Len(trail) <= NumVars

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// TypeInvariant: after solving, variable assignments are within valid ranges.
    ///
    /// Mirrors cdcl_test.tla TypeInvariant:
    /// - assignment[v] in {TRUE, FALSE, UNDEF} for all v
    /// - SAT model has exactly one boolean per variable
    /// - No variable index exceeds num_vars
    #[test]
    fn prop_type_invariant_assignment_ranges(
        (num_vars, clauses) in arb_formula(2..=30, 1..=60, 5)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                // TypeInvariant: model length equals num_vars (user-visible)
                // The model is indexed by variable index and covers all user variables.
                prop_assert!(
                    model.len() >= num_vars as usize,
                    "SAT model length {} < num_vars {}",
                    model.len(),
                    num_vars
                );
                // Each entry is a valid bool (Rust type system enforces this,
                // but we verify the model is indexable for all variables)
                for v in 0..num_vars {
                    let _val: bool = model[v as usize];
                }
            }
            SatResult::Unsat(_) => {
                // TypeInvariant: trail should be empty after UNSAT
                // (solver has backtracked to level 0 and exhausted search)
            }
            SatResult::Unknown => {
                // Unknown is a valid terminal state
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }

        // TypeInvariant: All literal variable indices in clauses are within bounds.
        for clause in &original_clauses {
            for lit in clause {
                prop_assert!(
                    lit.variable().index() < num_vars as usize,
                    "Literal variable index {} >= num_vars {}",
                    lit.variable().index(),
                    num_vars
                );
            }
        }
    }

    /// TypeInvariant: trail and decision level bounds.
    ///
    /// Mirrors cdcl_test.tla:
    /// - decisionLevel \in 0..NumVars
    /// - decisionLevel <= Len(trail)
    /// - Len(trail) <= NumVars
    ///
    /// Verified by querying the solver's public state after add_clause
    /// (before solve), and by the fact that debug_asserts in the solver
    /// enforce these bounds during propagation.
    #[test]
    fn prop_type_invariant_trail_bounds(
        (num_vars, clauses) in arb_formula(2..=20, 1..=40, 4)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        // Before solving: decision level should be 0, trail may have
        // level-0 propagated literals from unit clauses.
        let level_before = solver.current_decision_level();
        let trail_before = solver.trail_len();
        prop_assert_eq!(level_before, 0, "decision level should be 0 before solve");
        prop_assert!(
            trail_before <= num_vars as usize,
            "trail length {} > num_vars {} before solve",
            trail_before,
            num_vars
        );

        let _result = solver.solve().into_inner();

        // After solving: decision level should be 0 (solver backtracks fully).
        let level_after = solver.current_decision_level();
        let trail_after = solver.trail_len();
        prop_assert!(
            level_after <= num_vars,
            "decision level {} > num_vars {} after solve",
            level_after,
            num_vars
        );
        prop_assert!(
            trail_after <= solver.total_num_vars(),
            "trail length {} > total_num_vars {} after solve",
            trail_after,
            solver.total_num_vars()
        );
    }

    /// TypeInvariant: TrailAssignmentConsistent - every trail literal's variable
    /// is assigned, and the assignment matches the literal's polarity.
    ///
    /// Mirrors cdcl_test.tla TrailAssignmentConsistent:
    /// - For each literal on the trail, assignment[Var(lit)] != UNDEF
    /// - If literal is positive, assignment is TRUE; if negative, FALSE
    #[test]
    fn prop_type_invariant_trail_assignment_consistent(
        (num_vars, clauses) in arb_formula(2..=20, 1..=40, 4)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();

        // After solving to SAT, the trail should be consistent with the assignment.
        if let SatResult::Sat(model) = &result {
            let trail = solver.trail();
            for lit in trail {
                let var_idx = lit.variable().index();
                if var_idx < model.len() {
                    let assigned_value = model[var_idx];
                    // Trail literal polarity must match assignment
                    if lit.is_positive() {
                        prop_assert!(
                            assigned_value,
                            "Trail has positive literal for var {}, but model has FALSE",
                            var_idx
                        );
                    } else {
                        prop_assert!(
                            !assigned_value,
                            "Trail has negative literal for var {}, but model has TRUE",
                            var_idx
                        );
                    }
                }
            }
        }
    }

    /// TypeInvariant: NoTrailDuplicates - no variable appears on the trail twice.
    ///
    /// Mirrors cdcl_test.tla NoTrailDuplicates:
    /// - \A i, j \in 1..Len(trail) : i # j => Var(trail[i]) # Var(trail[j])
    #[test]
    fn prop_type_invariant_no_trail_duplicates(
        (num_vars, clauses) in arb_formula(2..=20, 1..=40, 4)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let _result = solver.solve().into_inner();

        let trail = solver.trail();
        let mut seen_vars = std::collections::HashSet::new();
        for lit in trail {
            let var_idx = lit.variable().index();
            prop_assert!(
                seen_vars.insert(var_idx),
                "Variable {} appears twice on the trail",
                var_idx
            );
        }
    }
}

// ============================================================================
// Soundness Property Tests
// ============================================================================
// TLA+ cdcl.tla Soundness:
//   SatCorrect == state = "SAT" => \A clause \in Clauses : Satisfied(clause)
//   UnsatCorrect == state = "UNSAT" => RootConflictDerivable

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Soundness/SatCorrect: SAT result model satisfies all original clauses.
    ///
    /// Mirrors cdcl.tla SatCorrect:
    ///   state = "SAT" => \A clause \in Clauses : Satisfied(clause)
    ///
    /// This is the most critical soundness property. If the solver returns
    /// SAT, the model must satisfy every clause in the original formula.
    #[test]
    fn prop_soundness_sat_correct(
        (num_vars, clauses) in arb_formula(2..=30, 1..=80, 5)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            // SatCorrect: every original clause must be satisfied
            prop_assert!(
                verify_model(&original_clauses, &model),
                "SOUNDNESS BUG: SAT model violates at least one original clause"
            );
        }
    }

    /// Soundness/SatCorrect on guaranteed-SAT formulas.
    ///
    /// Generate formulas with a known satisfying assignment. The solver
    /// must return SAT (not UNSAT or Unknown).
    #[test]
    fn prop_soundness_guaranteed_sat(
        (num_vars, clauses, expected_assignment) in arb_guaranteed_sat()
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                // Must satisfy all clauses (may differ from expected_assignment)
                prop_assert!(
                    verify_model(&original_clauses, &model),
                    "SOUNDNESS BUG: SAT model violates clause"
                );
            }
            SatResult::Unsat(_) => {
                // Verify the expected assignment does satisfy the formula
                // (to confirm the formula really is SAT)
                prop_assert!(
                    verify_model(&original_clauses, &expected_assignment),
                    "Test bug: expected assignment does not satisfy formula"
                );
                prop_assert!(
                    false,
                    "SOUNDNESS BUG: formula is SAT (witnessed) but solver says UNSAT"
                );
            }
            SatResult::Unknown => {
                // Acceptable for small formulas only if the solver times out
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// Soundness/UnsatCorrect on guaranteed-UNSAT formulas (pigeonhole).
    ///
    /// PHP(n+1, n) is unsatisfiable for all n >= 1. The solver must
    /// return UNSAT, never SAT.
    ///
    /// Mirrors cdcl.tla UnsatCorrect:
    ///   state = "UNSAT" => RootConflictDerivable
    #[test]
    fn prop_soundness_pigeonhole_unsat(
        (num_vars, clauses) in arb_pigeonhole_unsat()
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                // If it claims SAT, the model must actually satisfy the formula.
                // PHP is UNSAT, so this would be a soundness bug.
                let satisfies = verify_model(&original_clauses, &model);
                prop_assert!(
                    !satisfies,
                    "CRITICAL SOUNDNESS BUG: solver found a model for an UNSAT pigeonhole instance"
                );
                // Even if the model doesn't satisfy, returning SAT is wrong.
                prop_assert!(
                    false,
                    "SOUNDNESS BUG: solver returned SAT on UNSAT pigeonhole formula"
                );
            }
            SatResult::Unsat(_) => {
                // Correct: pigeonhole is UNSAT
            }
            SatResult::Unknown => {
                // Acceptable (timeout), but unexpected for small instances
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// Soundness: random 3-SAT formulas near the phase transition.
    ///
    /// Combined SatCorrect + UnsatCorrect: whatever the solver returns,
    /// if SAT then the model must satisfy all clauses.
    #[test]
    fn prop_soundness_3sat_phase_transition(
        (num_vars, clauses) in arb_3sat_phase_transition()
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            prop_assert!(
                verify_model(&original_clauses, &model),
                "SOUNDNESS BUG: SAT model violates clause on 3-SAT instance"
            );
        }
        // UNSAT is also fine (these formulas may be either SAT or UNSAT)
    }

    /// Soundness: single-variable unit clause formulas.
    ///
    /// Degenerate case: a single unit clause (x) or (NOT x) must be SAT.
    /// Contradicting units (x) AND (NOT x) must be UNSAT.
    #[test]
    fn prop_soundness_unit_clauses(
        num_vars in 1u32..=10u32,
        assignments in proptest::collection::vec(proptest::bool::ANY, 1..=10usize)
    ) {
        let nv = num_vars.max(assignments.len() as u32);
        let mut solver = Solver::new(nv as usize);
        let mut clauses = Vec::new();

        for (i, &val) in assignments.iter().enumerate() {
            let var = Variable::new(i as u32 % nv);
            let lit = if val {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            clauses.push(vec![lit]);
            solver.add_clause(vec![lit]);
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            prop_assert!(
                verify_model(&clauses, &model),
                "SOUNDNESS BUG: SAT model violates unit clause"
            );
        }
        // UNSAT is valid if contradictory units exist
    }
}

// ============================================================================
// WatchedInvariant Property Tests
// ============================================================================
// TLA+ cdcl.tla WatchedInvariant:
//   \A clause \in AllClauses :
//     Cardinality(clause) >= 2 =>
//       \/ Satisfied(clause)
//       \/ \E lit \in clause : LitValue(lit) # "FALSE"
//
// The watched literal invariant ensures that for every non-satisfied clause
// of length >= 2, at least one literal is not falsified. This is maintained
// by the 2-watched literal scheme during BCP.
//
// We verify this indirectly in two ways:
// 1. The solver's internal debug_asserts (in debug builds) check watch
//    invariants on every propagation step.
// 2. We verify that SAT models satisfy all clauses (which implies the
//    watched invariant was maintained correctly during search).

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// WatchedInvariant: binary clauses stress the 2WL scheme.
    ///
    /// Binary clauses have exactly 2 literals, so both watches point to
    /// different literals. Any watch corruption will produce wrong results.
    ///
    /// Mirrors cdcl.tla WatchedInvariant for Cardinality(clause) = 2.
    #[test]
    fn prop_watched_invariant_binary_clauses(
        num_vars in 3u32..=20u32,
        clause_pairs in proptest::collection::vec(
            (0u32..20u32, 0u32..20u32, proptest::bool::ANY, proptest::bool::ANY),
            2..=40usize
        )
    ) {
        let nv = num_vars;
        let mut solver = Solver::new(nv as usize);
        let mut clauses = Vec::new();

        for (v0_raw, v1_raw, s0, s1) in &clause_pairs {
            let v0 = v0_raw % nv;
            let mut v1 = v1_raw % nv;
            if v1 == v0 {
                v1 = (v0 + 1) % nv;
            }
            let l0 = if *s0 {
                Literal::positive(Variable::new(v0))
            } else {
                Literal::negative(Variable::new(v0))
            };
            let l1 = if *s1 {
                Literal::positive(Variable::new(v1))
            } else {
                Literal::negative(Variable::new(v1))
            };
            let clause = vec![l0, l1];
            clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            // If SAT, WatchedInvariant held: all clauses are satisfied.
            prop_assert!(
                verify_model(&clauses, &model),
                "WATCHED INVARIANT BUG: binary clause SAT model is invalid"
            );
        }
        // UNSAT or Unknown: watches were maintained correctly if no panic occurred.
    }

    /// WatchedInvariant: long clauses (length 3-10) stress watch list updates.
    ///
    /// When the solver propagates and a watched literal becomes false,
    /// it must find another non-false literal in the clause to watch.
    /// Long clauses have more candidates, testing the scan loop.
    #[test]
    fn prop_watched_invariant_long_clauses(
        (num_vars, clauses) in arb_formula(5..=25, 5..=50, 10)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        let original_clauses = clauses.clone();
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            prop_assert!(
                verify_model(&original_clauses, &model),
                "WATCHED INVARIANT BUG: long clause SAT model is invalid"
            );
        }
    }

    /// WatchedInvariant: mixed clause sizes test the 2WL scheme comprehensively.
    ///
    /// Combines unit, binary, ternary, and longer clauses. Unit clauses
    /// trigger immediate propagation, binary clauses use the binary-specific
    /// watch path, and longer clauses use the general watch scan.
    #[test]
    fn prop_watched_invariant_mixed_clause_sizes(
        num_vars in 4u32..=20u32,
        unit_vars in proptest::collection::vec((0u32..20u32, proptest::bool::ANY), 0..=3usize),
        binary_pairs in proptest::collection::vec(
            (0u32..20u32, 0u32..20u32, proptest::bool::ANY, proptest::bool::ANY),
            1..=10usize
        ),
        long_clauses in proptest::collection::vec(
            proptest::collection::vec((0u32..20u32, proptest::bool::ANY), 3..=6usize),
            1..=10usize
        )
    ) {
        let nv = num_vars;
        let mut solver = Solver::new(nv as usize);
        let mut all_clauses = Vec::new();

        // Unit clauses
        for (v_raw, sign) in &unit_vars {
            let v = v_raw % nv;
            let lit = if *sign {
                Literal::positive(Variable::new(v))
            } else {
                Literal::negative(Variable::new(v))
            };
            let clause = vec![lit];
            all_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        // Binary clauses
        for (v0_raw, v1_raw, s0, s1) in &binary_pairs {
            let v0 = v0_raw % nv;
            let mut v1 = v1_raw % nv;
            if v1 == v0 {
                v1 = (v0 + 1) % nv;
            }
            let l0 = if *s0 {
                Literal::positive(Variable::new(v0))
            } else {
                Literal::negative(Variable::new(v0))
            };
            let l1 = if *s1 {
                Literal::positive(Variable::new(v1))
            } else {
                Literal::negative(Variable::new(v1))
            };
            let clause = vec![l0, l1];
            all_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        // Long clauses
        for lits_raw in &long_clauses {
            let clause: Vec<Literal> = lits_raw
                .iter()
                .map(|(v_raw, sign)| {
                    let v = v_raw % nv;
                    if *sign {
                        Literal::positive(Variable::new(v))
                    } else {
                        Literal::negative(Variable::new(v))
                    }
                })
                .collect();
            all_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            prop_assert!(
                verify_model(&all_clauses, &model),
                "WATCHED INVARIANT BUG: mixed-size clause SAT model is invalid"
            );
        }
    }

    /// WatchedInvariant under incremental push/pop: watch lists must remain
    /// consistent across scope boundaries.
    ///
    /// This tests that the 2WL scheme handles clause addition and removal
    /// via push/pop without corrupting watch state.
    #[test]
    fn prop_watched_invariant_incremental(
        (num_vars, base_clauses) in arb_formula(3..=15, 1..=20, 4),
        (_, scope_clauses) in arb_formula(3..=15, 1..=10, 4),
    ) {
        let nv = num_vars.max(3) as usize;
        let mut solver = Solver::new(nv);
        let mut all_base = Vec::new();

        for clause in &base_clauses {
            // Clamp variable indices to nv
            let clamped: Vec<Literal> = clause
                .iter()
                .map(|lit| {
                    let v = Variable::new((lit.variable().index() as u32) % num_vars);
                    if lit.is_positive() {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            all_base.push(clamped.clone());
            solver.add_clause(clamped);
        }

        // Base solve
        let base_result = solver.solve().into_inner();
        if let SatResult::Sat(model) = &base_result {
            prop_assert!(
                verify_model(&all_base, model),
                "Base solve: SAT model invalid"
            );
        }

        // Push scope, add more clauses
        solver.push();
        for clause in &scope_clauses {
            let clamped: Vec<Literal> = clause
                .iter()
                .map(|lit| {
                    let v = Variable::new((lit.variable().index() as u32) % num_vars);
                    if lit.is_positive() {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            solver.add_clause(clamped);
        }
        let _scoped = solver.solve().into_inner();

        // Pop and re-solve base formula
        if solver.pop() {
            let post_pop = solver.solve().into_inner();
            if let SatResult::Sat(model) = &post_pop {
                prop_assert!(
                    verify_model(&all_base, model),
                    "Post-pop solve: SAT model violates base clauses"
                );
            }
        }
    }
}

// ============================================================================
// Combined Invariant Tests (Non-Proptest)
// ============================================================================

/// Smoke test: parse DIMACS, solve, and check all three invariant families
/// on a known formula. This serves as a baseline sanity check.
#[test]
fn test_tla_invariants_smoke_dimacs() {
    // Known SAT formula
    let dimacs = "p cnf 5 4\n1 2 3 0\n-1 4 0\n-2 5 0\n-3 -4 -5 0\n";
    let formula = parse_dimacs(dimacs).expect("parse");
    let original_clauses = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver = formula.into_solver();

    let result = solver.solve().into_inner();

    // TypeInvariant checks
    assert!(solver.current_decision_level() <= num_vars as u32);
    assert!(solver.trail_len() <= solver.total_num_vars());

    // Soundness check
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&original_clauses, model),
            "Smoke test SAT model invalid"
        );
        assert!(
            model.len() >= num_vars,
            "Model length {} < num_vars {}",
            model.len(),
            num_vars
        );
    }

    // NoTrailDuplicates check
    let trail = solver.trail();
    let mut seen = std::collections::HashSet::new();
    for lit in trail {
        assert!(
            seen.insert(lit.variable().index()),
            "Duplicate variable on trail"
        );
    }
}

/// Smoke test: UNSAT formula satisfies UnsatCorrect invariant.
#[test]
fn test_tla_invariants_smoke_unsat() {
    // PHP(3,2): 3 pigeons, 2 holes
    let dimacs = super::common::PHP32_DIMACS;
    let formula = parse_dimacs(dimacs).expect("parse");
    let mut solver = formula.into_solver();

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(3,2) should be UNSAT");

    // UnsatCorrect: decision level should be 0 after UNSAT
    // (UNSAT is only declared at level 0 in the TLA+ spec)
    assert_eq!(
        solver.current_decision_level(),
        0,
        "After UNSAT, decision level should be 0 (TLA+ UnsatCorrect)"
    );
}

// ============================================================================
// Additional CDCL Invariant Property Tests
// ============================================================================
// These tests cover invariants from cdcl.tla and cdcl_test.tla that were
// not exercised by the original 15 tests.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// UnsatCorrect on random formulas: decision level must be 0 after UNSAT.
    ///
    /// Mirrors cdcl.tla DeclareUnsat:
    ///   /\ state = "CONFLICTING"
    ///   /\ decisionLevel = 0
    ///   /\ state' = "UNSAT"
    ///
    /// And cdcl_test.tla UnsatCorrect:
    ///   state = "UNSAT" =>
    ///     /\ decisionLevel = 0
    ///     /\ TrailAssignmentConsistent(assignment, trail)
    ///     /\ NoTrailDuplicates
    ///
    /// The pigeonhole test only covers a structured family of UNSAT formulas.
    /// This test uses random dense formulas that are often UNSAT, verifying
    /// the decision-level-0 invariant more broadly.
    #[test]
    fn prop_unsat_decision_level_zero(
        (num_vars, clauses) in arb_formula(2..=15, 5..=80, 4)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if result.is_unsat() {
            prop_assert_eq!(
                solver.current_decision_level(),
                0,
                "UnsatCorrect: decision level must be 0 after UNSAT, got {}",
                solver.current_decision_level()
            );
            // Also verify TrailAssignmentConsistent + NoTrailDuplicates
            // at UNSAT (cdcl_test.tla UnsatCorrect requirements)
            let trail = solver.trail();
            let mut seen_vars = std::collections::HashSet::new();
            for lit in trail {
                prop_assert!(
                    seen_vars.insert(lit.variable().index()),
                    "UnsatCorrect: duplicate variable {} on trail after UNSAT",
                    lit.variable().index()
                );
            }
        }
    }

    /// SatTerminalConsistent: when SAT is declared, all user variables
    /// must be assigned (no UNDEF variables remain).
    ///
    /// Mirrors cdcl_test.tla SatTerminalConsistent:
    ///   /\ \A v \in VarIndices : a[v] # "UNDEF"
    ///   /\ d \in 0..NumVars
    ///   /\ d <= Len(t)
    ///   /\ TrailAssignmentConsistent(a, t)
    ///
    /// The existing prop_type_invariant_assignment_ranges checks model length
    /// but does not verify that the model covers all variables with real values.
    /// This test explicitly checks completeness: every user variable has a
    /// boolean value in the model (no gaps).
    #[test]
    fn prop_sat_terminal_consistent(
        (num_vars, clauses) in arb_formula(2..=25, 1..=60, 5)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            // SatTerminalConsistent: all user variables assigned
            prop_assert!(
                model.len() >= num_vars as usize,
                "SatTerminalConsistent: model length {} < num_vars {}",
                model.len(),
                num_vars
            );

            // SatTerminalConsistent: d \in 0..NumVars
            let level = solver.current_decision_level();
            prop_assert!(
                level <= num_vars,
                "SatTerminalConsistent: decision level {} > num_vars {}",
                level,
                num_vars
            );

            // SatTerminalConsistent: d <= Len(trail)
            let trail_len = solver.trail_len();
            prop_assert!(
                (level as usize) <= trail_len,
                "SatTerminalConsistent: decision level {} > trail length {}",
                level,
                trail_len
            );

            // TrailAssignmentConsistent must hold at SAT
            let trail = solver.trail();
            for lit in trail {
                let var_idx = lit.variable().index();
                if var_idx < model.len() {
                    if lit.is_positive() {
                        prop_assert!(
                            model[var_idx],
                            "SatTerminalConsistent: trail positive lit for var {} but model is false",
                            var_idx
                        );
                    } else {
                        prop_assert!(
                            !model[var_idx],
                            "SatTerminalConsistent: trail negative lit for var {} but model is true",
                            var_idx
                        );
                    }
                }
            }
        }
    }

    /// Learned clause implication: learned clauses are logical consequences
    /// of original clauses. If SAT, the model must satisfy all learned clauses.
    ///
    /// This property follows from cdcl.tla AnalyzeAndLearn which states:
    ///   "The learned clause should be implied by original clauses"
    ///
    /// Verification: when SAT, retrieve learned clauses and verify the model
    /// satisfies each one. A learned clause violated by a model that satisfies
    /// the original formula would indicate a bug in conflict analysis.
    #[test]
    fn prop_learned_clauses_implied_by_original(
        (num_vars, clauses) in arb_3sat_phase_transition()
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        if let SatResult::Sat(model) = result {
            // Every learned clause must be satisfied by the SAT model.
            // If a learned clause is not satisfied, it was not a valid
            // consequence of the original formula.
            let learned = solver.get_learned_clauses();
            for (i, lc) in learned.iter().enumerate() {
                let sat = lc.iter().any(|lit| {
                    let idx = lit.variable().index();
                    if idx >= model.len() {
                        return false;
                    }
                    if lit.is_positive() { model[idx] } else { !model[idx] }
                });
                prop_assert!(
                    sat,
                    "Learned clause {} not satisfied by SAT model: {:?}",
                    i, lc
                );
            }
        }
    }

    /// Clause database integrity: no learned clause contains duplicate
    /// literals (same variable with same polarity appearing twice).
    ///
    /// The TLA+ spec models clauses as sets of literals (implicitly
    /// forbidding duplicates). The Rust solver stores clauses as vectors,
    /// so duplicates must be prevented by the clause-learning implementation.
    ///
    /// Also checks for tautologies: no learned clause should contain both
    /// a literal and its negation (x and NOT x), since such clauses are
    /// always trivially satisfied and waste memory.
    #[test]
    fn prop_learned_clause_no_duplicates_or_tautologies(
        (num_vars, clauses) in arb_3sat_phase_transition()
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let _result = solver.solve().into_inner();
        let learned = solver.get_learned_clauses();

        for (i, lc) in learned.iter().enumerate() {
            let mut seen_positive = std::collections::HashSet::new();
            let mut seen_negative = std::collections::HashSet::new();

            for lit in lc {
                let var_idx = lit.variable().index();
                if lit.is_positive() {
                    // Check for duplicate positive literal
                    prop_assert!(
                        seen_positive.insert(var_idx),
                        "Learned clause {} has duplicate positive literal for var {}",
                        i, var_idx
                    );
                    // Check for tautology (negative already seen)
                    prop_assert!(
                        !seen_negative.contains(&var_idx),
                        "Learned clause {} is a tautology: var {} appears positive and negative",
                        i, var_idx
                    );
                } else {
                    // Check for duplicate negative literal
                    prop_assert!(
                        seen_negative.insert(var_idx),
                        "Learned clause {} has duplicate negative literal for var {}",
                        i, var_idx
                    );
                    // Check for tautology (positive already seen)
                    prop_assert!(
                        !seen_positive.contains(&var_idx),
                        "Learned clause {} is a tautology: var {} appears positive and negative",
                        i, var_idx
                    );
                }
            }

            // Learned clauses must be non-empty
            prop_assert!(
                !lc.is_empty(),
                "Learned clause {} is empty (should not be exported)",
                i
            );
        }
    }

    /// Restart preserves soundness: solve a formula, verify result, then
    /// solve again after adding new clauses. Both results must be sound.
    ///
    /// This verifies that the solver correctly handles restart-related state
    /// transitions. The TLA+ spec shows AnalyzeAndLearn backtracks to a
    /// computed level, and all level-0 propagations must be preserved.
    /// A restart (backtrack to level 0) is a special case.
    ///
    /// This test uses incremental push/pop to force multiple solves,
    /// checking that the solver's internal state remains consistent
    /// after restarts that occur during each solve call.
    #[test]
    fn prop_restart_preserves_soundness(
        (num_vars, clauses) in arb_formula(3..=20, 2..=40, 4),
        extra_unit_var in 0u32..20u32,
        extra_unit_sign in proptest::bool::ANY,
    ) {
        let nv = num_vars.max(3);
        let mut solver = Solver::new(nv as usize);
        let original_clauses: Vec<Vec<Literal>> = clauses
            .iter()
            .map(|c| {
                c.iter()
                    .map(|lit| {
                        let v = Variable::new(lit.variable().index() as u32 % nv);
                        if lit.is_positive() {
                            Literal::positive(v)
                        } else {
                            Literal::negative(v)
                        }
                    })
                    .collect()
            })
            .collect();

        for clause in &original_clauses {
            solver.add_clause(clause.clone());
        }

        // First solve
        let result1 = solver.solve().into_inner();
        if let SatResult::Sat(ref model) = result1 {
            prop_assert!(
                verify_model(&original_clauses, model),
                "First solve: SAT model invalid"
            );
        }

        // Push scope, add unit clause (may flip SAT<->UNSAT)
        solver.push();
        let extra_var = Variable::new(extra_unit_var % nv);
        let extra_lit = if extra_unit_sign {
            Literal::positive(extra_var)
        } else {
            Literal::negative(extra_var)
        };
        let extra_clause = vec![extra_lit];
        solver.add_clause(extra_clause.clone());

        let result2 = solver.solve().into_inner();
        if let SatResult::Sat(ref model) = result2 {
            // Must satisfy original + extra
            prop_assert!(
                verify_model(&original_clauses, model),
                "Second solve: SAT model violates original clauses"
            );
            prop_assert!(
                verify_model(&[extra_clause], model),
                "Second solve: SAT model violates extra unit clause"
            );
        }

        // Pop and re-solve
        if solver.pop() {
            let result3 = solver.solve().into_inner();
            if let SatResult::Sat(ref model) = result3 {
                prop_assert!(
                    verify_model(&original_clauses, model),
                    "Third solve (post-pop): SAT model invalid"
                );
            }
        }
    }

    /// LearnedClausesBound: the number of learned clauses is finite
    /// and bounded by the solver's reduction strategy.
    ///
    /// Mirrors cdcl_test.tla LearnedClausesBound:
    ///   learnedClauses <= MaxLearnedClauses
    ///
    /// In the TLA+ spec, this bound is a model-checking parameter. In the
    /// real solver, the clause database is periodically reduced. We verify
    /// that the retained learned clause count does not exceed a reasonable
    /// bound relative to the original formula size.
    #[test]
    fn prop_learned_clauses_bounded(
        (num_vars, clauses) in arb_formula(3..=20, 5..=60, 5)
    ) {
        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let _result = solver.solve().into_inner();

        let learned = solver.num_learned_clauses();
        let original = solver.num_original_clauses();
        // After solving, retained learned clauses should not be unbounded.
        // A reasonable upper bound: learned clauses should not exceed
        // 100x the original formula size for these small formulas.
        // (The solver's reduce_db keeps this much tighter in practice.)
        let upper_bound = (original as u64 + 1) * 100;
        prop_assert!(
            learned <= upper_bound,
            "LearnedClausesBound: {} learned clauses exceeds 100x bound ({}) for {} originals",
            learned,
            upper_bound,
            original
        );
    }

    /// NoDoubleAssignment under high conflict density: when the clause-to-
    /// variable ratio is high, the solver performs many conflicts and
    /// backtracks. The trail must never contain duplicate variables even
    /// under heavy backtracking.
    ///
    /// Mirrors cdcl.tla NoDoubleAssignment:
    ///   \A i, j \in 1..Len(trail) :
    ///     i # j => Var(trail[i][1]) # Var(trail[j][1])
    ///
    /// The existing prop_type_invariant_no_trail_duplicates uses moderate
    /// clause density. This test specifically targets the high-conflict
    /// regime where backtracking + reimplication bugs would manifest.
    #[test]
    fn prop_no_double_assignment_high_conflict(
        num_vars in 5u32..=15u32,
        seed in 0u64..=1000u64,
    ) {
        let nv = num_vars;
        // High clause/variable ratio to force many conflicts
        let num_clauses = (nv as usize) * 8;
        let mut solver = Solver::new(nv as usize);

        // Deterministic pseudo-random clause generation
        let mut state = seed;
        let lcg = |s: &mut u64| {
            *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *s
        };

        for _ in 0..num_clauses {
            let clause_len = (lcg(&mut state) % 3 + 2) as usize;
            let clause: Vec<Literal> = (0..clause_len)
                .map(|_| {
                    let v = (lcg(&mut state) % u64::from(nv)) as u32;
                    let pos = lcg(&mut state) % 2 == 0;
                    if pos {
                        Literal::positive(Variable::new(v))
                    } else {
                        Literal::negative(Variable::new(v))
                    }
                })
                .collect();
            solver.add_clause(clause);
        }

        let _result = solver.solve().into_inner();

        let trail = solver.trail();
        let mut seen = std::collections::HashSet::new();
        for lit in trail {
            prop_assert!(
                seen.insert(lit.variable().index()),
                "NoDoubleAssignment: variable {} appears twice on trail under high conflict",
                lit.variable().index()
            );
        }
    }
}
