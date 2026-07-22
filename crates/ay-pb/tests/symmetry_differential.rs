// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Differential tests for instance-level symmetry breaking.
//!
//! These tests assert the central soundness contract: solving the original
//! instance and the symmetry-augmented instance yields the **same verdict**
//! (SAT/UNSAT) and the **same optimum** — symmetry breaking changes search
//! effort, never the answer. A flipped verdict here is a disqualifying soundness
//! bug.

use ay_pb::{
    break_symmetries, eval_objective, parse_opb, verify_all_constraints, PbCdclResult,
    PbCdclSolver, PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Decision verdict reduced to a comparable summary. For SAT we also return the
/// model so callers can validate it against the *original* constraints.
#[derive(Debug)]
enum DecisionVerdict {
    Sat(Vec<bool>),
    Unsat,
    /// Solver could not decide (should not happen for these tiny instances).
    Unknown,
}

fn decision_verdict(instance: &PbInstance) -> DecisionVerdict {
    let mut solver = PbCdclSolver::new(instance);
    match solver.solve() {
        PbCdclResult::Satisfiable(model) => DecisionVerdict::Sat(model),
        PbCdclResult::Unsatisfiable => DecisionVerdict::Unsat,
        _ => DecisionVerdict::Unknown,
    }
}

/// Proven optimum, or `None` if not decided to optimality.
fn optimum(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let mut solver = PbCdclSolver::new(instance);
    match solver.solve_optimize(objective, None) {
        PbCdclResult::Optimal(_, value) => Some(value),
        _ => None,
    }
}

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn t(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

/// Asserts that the original and symmetry-augmented instances agree on the
/// decision verdict, and that any returned model satisfies the *original*
/// constraints.
fn assert_decision_verdict_unchanged(instance: &PbInstance, label: &str) {
    let (augmented, res) = break_symmetries(instance);
    // The augmented instance must never introduce new variables.
    assert_eq!(
        augmented.num_vars, instance.num_vars,
        "{label}: symmetry breaking changed num_vars"
    );

    let orig = decision_verdict(instance);
    let aug = decision_verdict(&augmented);
    match (&orig, &aug) {
        (DecisionVerdict::Unsat, DecisionVerdict::Unsat) => {}
        (DecisionVerdict::Sat(om), DecisionVerdict::Sat(am)) => {
            assert!(
                verify_all_constraints(&instance.constraints, om),
                "{label}: original model invalid"
            );
            // The augmented model must satisfy the ORIGINAL constraints too
            // (added lex rows only prune; they never invent new solutions).
            assert!(
                verify_all_constraints(&instance.constraints, am),
                "{label}: augmented model violates original constraints (UNSOUND)"
            );
        }
        other => panic!(
            "{label}: verdict flipped or undecided (added {} lex rows): {other:?}",
            res.lex_constraints_added
        ),
    }
}

/// Asserts the proven optimum is identical with and without symmetry breaking.
fn assert_optimum_unchanged(instance: &PbInstance, label: &str) {
    let objective = instance
        .objective
        .as_ref()
        .expect("instance must have objective");
    let (augmented, _res) = break_symmetries(instance);
    let orig = optimum(instance, objective);
    let aug = optimum(&augmented, objective);
    assert_eq!(
        orig, aug,
        "{label}: optimum changed under symmetry breaking (UNSOUND)"
    );
    // If an optimum was found on the augmented instance, the witnessing search
    // must be consistent with the original objective range.
    if let Some(v) = aug {
        // Brute-force the true optimum and confirm.
        let n = instance.num_vars as usize;
        assert!(n <= 18, "{label}: brute force only for tiny instances");
        let mut best: Option<i128> = None;
        for mask in 0u32..(1u32 << n) {
            let a: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &a) {
                let ov = eval_objective(objective, &a);
                best = Some(best.map_or(ov, |b: i128| b.min(ov)));
            }
        }
        assert_eq!(
            Some(v),
            best,
            "{label}: proven optimum disagrees with brute force"
        );
    }
}

fn load(name: &str) -> PbInstance {
    let path = format!("{}/tests/instances/{name}", env!("CARGO_MANIFEST_DIR"));
    let content = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    parse_opb(&content).unwrap_or_else(|e| panic!("parse {path}: {e}"))
}

// ---------------------------------------------------------------------------
// Synthetic instances with known symmetry
// ---------------------------------------------------------------------------

/// Pigeonhole 4 pigeons into 3 holes as a column-symmetric cardinality matrix:
/// every variable column is interchangeable across the at-most-one hole rows.
/// Here we encode it so that columns are genuinely interchangeable.
#[test]
fn interchangeable_columns_sat_unchanged() {
    // 4 variables, all appearing identically in two rows: SAT.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge(vec![t(1, 1), t(1, 2), t(1, 3), t(1, 4)], 2),
            ge(vec![t(-1, 1), t(-1, 2), t(-1, 3), t(-1, 4)], -3),
        ],
        objective: None,
    };
    let (_aug, res) = break_symmetries(&instance);
    assert!(res.changed_instance(), "expected symmetry to be detected");
    assert_decision_verdict_unchanged(&instance, "interchangeable_columns_sat");
}

#[test]
fn interchangeable_columns_unsat_unchanged() {
    // Need >=3 of 3 columns true but also <=2 true: UNSAT, columns symmetric.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge(vec![t(1, 1), t(1, 2), t(1, 3)], 3),
            ge(vec![t(-1, 1), t(-1, 2), t(-1, 3)], -2),
        ],
        objective: None,
    };
    let (_aug, res) = break_symmetries(&instance);
    assert!(res.changed_instance());
    assert_decision_verdict_unchanged(&instance, "interchangeable_columns_unsat");
}

#[test]
fn interchangeable_columns_optimum_unchanged() {
    // Minimize sum subject to >= 2 of 4 equal columns; optimum is 2.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 1,
        constraints: vec![ge(vec![t(1, 1), t(1, 2), t(1, 3), t(1, 4)], 2)],
        objective: Some(PbObjective {
            terms: vec![t(1, 1), t(1, 2), t(1, 3), t(1, 4)],
        }),
    };
    let (_aug, res) = break_symmetries(&instance);
    assert!(res.changed_instance());
    assert_optimum_unchanged(&instance, "interchangeable_columns_optimum");
}

#[test]
fn verified_matrix_row_swap_unsat_unchanged() {
    // Weighted matrix with an exactly-verified (x1 x3)(x2 x4) row swap, made
    // UNSAT by conflicting bounds. The binary-weighted lex row must not flip it.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 4,
        constraints: vec![
            ge(vec![t(3, 1), t(2, 2)], 5),   // x1=x2=1 (sum 5)
            ge(vec![t(3, 3), t(2, 4)], 5),   // x3=x4=1
            ge(vec![t(-1, 1), t(-1, 3)], 0), // x1+x3 <= 0 -> both 0: contradiction
            ge(vec![t(1, 2), t(1, 4)], 1),
        ],
        objective: None,
    };
    assert_decision_verdict_unchanged(&instance, "verified_matrix_row_swap_unsat");
}

#[test]
fn verified_matrix_row_swap_sat_unchanged() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge(vec![t(3, 1), t(2, 2)], 1),
            ge(vec![t(3, 3), t(2, 4)], 1),
            ge(vec![t(1, 1), t(1, 3)], 1),
        ],
        objective: None,
    };
    assert_decision_verdict_unchanged(&instance, "verified_matrix_row_swap_sat");
}

// ---------------------------------------------------------------------------
// Real bundled instances
// ---------------------------------------------------------------------------

#[test]
fn bundled_instances_decision_verdict_unchanged() {
    for name in ["sat_simple.opb", "unsat_simple.opb", "cardinality_3of5.opb"] {
        let instance = load(name);
        if instance.objective.is_none() {
            assert_decision_verdict_unchanged(&instance, name);
        }
    }
}

#[test]
fn bundled_optimization_optimum_unchanged() {
    for name in ["weighted_opt.opb", "opt_pigeonhole.opb"] {
        let instance = load(name);
        if instance.objective.is_some() && instance.num_vars <= 18 {
            assert_optimum_unchanged(&instance, name);
        }
    }
}

#[test]
fn pigeonhole_opb_text_unsat_unchanged() {
    // The canonical PHP-3-2 instance (the spot-check fixture): must stay UNSAT.
    let text = "* #variable= 6 #constraint= 5\n\
                +1 x1 +1 x2 >= 1 ;\n\
                +1 x3 +1 x4 >= 1 ;\n\
                +1 x5 +1 x6 >= 1 ;\n\
                -1 x1 -1 x3 -1 x5 >= -1 ;\n\
                -1 x2 -1 x4 -1 x6 >= -1 ;\n";
    let instance = parse_opb(text).expect("parse php-3-2");
    assert_decision_verdict_unchanged(&instance, "php-3-2");
}
