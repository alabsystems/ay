// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! OTFS (on-the-fly strengthening) soundness regression tests (Part of #3267).
//!
//! These tests exercise formulas where OTFS should fire during conflict
//! analysis. The formulas are structured to force multiple resolution steps
//! with reason clauses containing level-0 (root) literals, which OTFS
//! removes. After solving, the model (SAT) or UNSAT result is verified
//! against the original clauses.
//!
//! OTFS was re-enabled in #4598 (non-proof mode only, with analysis restart).
//! The `test_otfs_many_resolution_steps_sat` test includes a non-vacuity
//! check asserting `otfs_subsumed() > 0` to confirm the technique fires.
//!
//! If OTFS introduces a stale reason pointer or incorrect learned clause,
//! these tests will produce wrong SAT/UNSAT results or invalid models.

use ay_sat::{Literal, SatResult, Solver, Variable};

/// SAT formula with deep implication chains and root-level forced literals.
///
/// Structure: unit clauses force some variables at level 0, then binary/ternary
/// clauses create long implication chains at higher levels. OTFS should fire
/// when reason clauses contain level-0 literals during conflict analysis.
#[test]
fn test_otfs_sat_deep_implication_chain_with_root_lits() {
    let n = 12;
    let mut solver = Solver::new(n);
    let v: Vec<Variable> = (0..n).map(|i| Variable::new(i as u32)).collect();

    let clauses = vec![
        // Force v0=T, v1=T at level 0 (unit clauses)
        vec![Literal::positive(v[0])],
        vec![Literal::positive(v[1])],
        // Chain: v0 ∧ ¬v2 → v3 (i.e., ¬v0 ∨ v2 ∨ v3)
        vec![
            Literal::negative(v[0]),
            Literal::positive(v[2]),
            Literal::positive(v[3]),
        ],
        // Chain: v1 ∧ ¬v3 → v4 (i.e., ¬v1 ∨ v3 ∨ v4)
        vec![
            Literal::negative(v[1]),
            Literal::positive(v[3]),
            Literal::positive(v[4]),
        ],
        // Chain: v0 ∧ ¬v4 → v5 (reason clause with root literal v0)
        vec![
            Literal::negative(v[0]),
            Literal::positive(v[4]),
            Literal::positive(v[5]),
        ],
        // Chain: v1 ∧ ¬v5 → v6 (reason clause with root literal v1)
        vec![
            Literal::negative(v[1]),
            Literal::positive(v[5]),
            Literal::positive(v[6]),
        ],
        // Conflict-inducing clauses that force backtracking
        vec![Literal::positive(v[7]), Literal::negative(v[8])],
        vec![Literal::negative(v[7]), Literal::negative(v[8])],
        vec![Literal::positive(v[8]), Literal::positive(v[9])],
        // Additional clauses to make the formula satisfiable
        vec![Literal::positive(v[10]), Literal::positive(v[11])],
        vec![Literal::negative(v[9]), Literal::positive(v[10])],
    ];

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&clauses, &model, "otfs_deep_chain");
        }
        SatResult::Unsat(_) => {
            // If UNSAT, verify this is genuinely UNSAT by checking a known-SAT assignment
            // (v0=T, v1=T, v2=T, v3=T, v4=T, v5=T, v6=T, v7=T, v8=F, v9=T, v10=T, v11=T)
            // satisfies all clauses — so UNSAT would be a bug.
            // Derivation: C6+C7 force v8=F, then C8 forces v9=T, C10 forces v10=T.
            let test_model = vec![
                true, true, true, true, true, true, true, true, false, true, true, true,
            ];
            super::common::assert_model_satisfies(&clauses, &test_model, "otfs_deep_chain_witness");
            panic!("Solver returned UNSAT but formula is SAT (test model verified)");
        }
        SatResult::Unknown => panic!("Solver returned Unknown unexpectedly"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    // OTFS non-vacuity: on this 12-var formula, OTFS may not fire because
    // the resolvent/antecedent size condition is hard to satisfy on small
    // instances. Non-vacuity is asserted on the 20-var formula below.
}

/// SAT formula with reason clauses containing root-level literals.
///
/// OTFS should strengthen reason clauses by removing root-level false literals.
/// If the strengthening is incorrect, the solver might produce a wrong result.
///
/// The formula is SAT: v0=T forced, then C5+C6 force exactly-one-of(v1,v2).
/// Case v1=T,v2=F: C2→v3=T, C4→v4 free, C5→v4=F. Model valid.
/// Case v1=F,v2=T: C3→v4=T, C4→v3 free, C5→v3=F. Model valid.
/// Returning UNSAT here would be a soundness bug.
#[test]
fn test_otfs_sat_formula_with_root_level_reasons() {
    let n = 8;
    let mut solver = Solver::new(n);
    let v: Vec<Variable> = (0..n).map(|i| Variable::new(i as u32)).collect();

    // Force v0=T at level 0
    solver.add_clause(vec![Literal::positive(v[0])]);

    // Clauses creating implications through v0 (root literal in reasons):
    // ¬v0 ∨ v1 ∨ v2 (reason for v1 or v2, contains root lit v0)
    solver.add_clause(vec![
        Literal::negative(v[0]),
        Literal::positive(v[1]),
        Literal::positive(v[2]),
    ]);
    // ¬v0 ∨ ¬v1 ∨ v3 (reason contains root lit v0)
    solver.add_clause(vec![
        Literal::negative(v[0]),
        Literal::negative(v[1]),
        Literal::positive(v[3]),
    ]);
    // ¬v0 ∨ ¬v2 ∨ v4 (reason contains root lit v0)
    solver.add_clause(vec![
        Literal::negative(v[0]),
        Literal::negative(v[2]),
        Literal::positive(v[4]),
    ]);

    // Force contradiction: v3 and v4 cannot both be true with these constraints
    solver.add_clause(vec![Literal::negative(v[3]), Literal::negative(v[4])]);
    solver.add_clause(vec![Literal::negative(v[1]), Literal::negative(v[2])]);

    // Additional constraints to close all escape paths
    solver.add_clause(vec![Literal::positive(v[1]), Literal::positive(v[2])]);
    solver.add_clause(vec![Literal::positive(v[3]), Literal::positive(v[4])]);

    let clauses = vec![
        vec![Literal::positive(v[0])],
        vec![
            Literal::negative(v[0]),
            Literal::positive(v[1]),
            Literal::positive(v[2]),
        ],
        vec![
            Literal::negative(v[0]),
            Literal::negative(v[1]),
            Literal::positive(v[3]),
        ],
        vec![
            Literal::negative(v[0]),
            Literal::negative(v[2]),
            Literal::positive(v[4]),
        ],
        vec![Literal::negative(v[3]), Literal::negative(v[4])],
        vec![Literal::negative(v[1]), Literal::negative(v[2])],
        vec![Literal::positive(v[1]), Literal::positive(v[2])],
        vec![Literal::positive(v[3]), Literal::positive(v[4])],
    ];

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&clauses, &model, "otfs_root_reasons");
        }
        SatResult::Unsat(_) => {
            // Formula is provably SAT — UNSAT is a soundness bug.
            // Witness: v0=T, v1=T, v2=F, v3=T, v4=F (satisfies all 8 clauses).
            let witness = vec![true, true, false, true, false, false, false, false];
            super::common::assert_model_satisfies(&clauses, &witness, "otfs_root_reasons_witness");
            panic!("Solver returned UNSAT but formula is SAT (witness verified above)");
        }
        SatResult::Unknown => panic!("Solver returned Unknown unexpectedly"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    // OTFS non-vacuity: see note in test_otfs_sat_deep_implication_chain.
}

/// SAT formula with reconvergent fan-out structure to force OTFS.
///
/// OTFS fires when `resolvent_size < antecedent_size` with `antecedent_size > 2`
/// (CaDiCaL analyze.cpp:1068). This requires a reason clause whose non-level-0
/// non-pivot literals are already in the seen-set.
///
/// The formula uses a fan-out + reconverge pattern:
///   x=F → a=T, b=T, c=T  (binary implications from decision x)
///   a ∧ b ∧ c → d         (4-literal reconverging clause)
///   conflict: ¬a ∧ ¬b ∧ ¬c ∧ ¬d  (conflict when all true)
///
/// During analysis of (¬a ∨ ¬b ∨ ¬c ∨ ¬d) at the decision level of x:
///   seen = {a, b, c, d}, counter=4, resolvent_size=4
///   Resolve on d (last propagated): d's reason is (¬a ∨ ¬b ∨ ¬c ∨ d)
///     antecedent_size = 1+3 = 4, resolvent_size → 3 (after pivot decrement)
///     a, b, c already seen → no new variables → resolvent_size stays 3
///     3 < 4 → OTFS fires! Strengthened clause (¬a ∨ ¬b ∨ ¬c) has 3 lits.
///
/// The formula is SAT (x=T satisfies all clauses). Initial phase is set to
/// negative so the solver first decides x=F, hits the conflict, learns
/// (x), backtracks, and finds the SAT assignment on the second try.
///
/// Inprocessing is disabled to prevent conditioning from eliminating d
/// (which appears in only 2 clauses) and trivializing the formula.
#[test]
fn test_otfs_many_resolution_steps_sat() {
    let n = 5;
    let mut solver = Solver::new(n);
    // Disable all inprocessing so conditioning doesn't eliminate d and
    // trivialize the formula (d only appears in the reconverge + conflict
    // clauses, making it a prime BVE candidate).
    solver.disable_all_inprocessing();
    // Set negative initial phase so solver decides x=F first, triggering
    // the reconvergent conflict chain where OTFS can fire.
    let v: Vec<Variable> = (0..n).map(|i| Variable::new(i as u32)).collect();
    for &var in &v {
        solver.set_var_phase(var, false);
    }
    let x = v[0];
    let a = v[1];
    let b = v[2];
    let c = v[3];
    let d = v[4];

    let clauses = vec![
        // Fan-out: x=F → a=T, x=F → b=T, x=F → c=T
        vec![Literal::positive(x), Literal::positive(a)],
        vec![Literal::positive(x), Literal::positive(b)],
        vec![Literal::positive(x), Literal::positive(c)],
        // Reconverge: (¬a ∨ ¬b ∨ ¬c ∨ d) — a ∧ b ∧ c → d
        vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::negative(c),
            Literal::positive(d),
        ],
        // Conflict trigger: (¬a ∨ ¬b ∨ ¬c ∨ ¬d) — conflict when a,b,c,d all true
        vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::negative(c),
            Literal::negative(d),
        ],
    ];

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&clauses, &model, "otfs_reconverge");
        }
        SatResult::Unsat(_) => {
            panic!("Solver returned UNSAT but formula is SAT (x=T satisfies all clauses)");
        }
        SatResult::Unknown => panic!("Solver returned Unknown unexpectedly"),
        #[allow(unreachable_patterns)]
        _ => panic!("Unexpected SatResult variant"),
    }

    // Non-vacuity: OTFS must fire on this reconvergent formula. The
    // resolvent_size decrement (CaDiCaL analyze.cpp:1185) is required for
    // the trigger condition to be satisfiable.
    assert!(
        solver.otfs_subsumed() > 0 || solver.otfs_strengthened() > 0,
        "OTFS non-vacuity: expected OTFS to fire on reconvergent fan-out formula \
         (conflicts={}, subsumed={}, strengthened={})",
        solver.num_conflicts(),
        solver.otfs_subsumed(),
        solver.otfs_strengthened(),
    );
}
