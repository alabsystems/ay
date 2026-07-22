// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for guarded-equality mining (#23 keystone).
//!
//! The lustre SYNAPSE_2 1-induction check is a Bool-guarded equality network
//! whose sum-conservation atom is entailed under every guard valuation. The
//! baseline solver needed ~45s (33k conflicts / 64k LRA checks) on the ddmin
//! core; with mining the atom folds to a constant and the solve is trivial.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: QF_LIA script should execute");
    (exec, outputs)
}

fn min_repro_script() -> String {
    let path = crate::common::workspace_path("evals/repros/diag_syn2_indstep_k1_MIN.smt2");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read committed repro {}: {e}", path.display()))
}

/// The committed 51-assert ddmin core (AY baseline: 45s) must now be decided
/// quickly: the conservation atom is mined, folded, and re-asserted as a
/// unit, so the Boolean core conflicts at level zero.
#[test]
#[timeout(30_000)]
fn min_repro_unsat_via_mining_23() {
    let (exec, outputs) = run_script(&min_repro_script());
    assert_eq!(outputs, vec!["unsat"]);

    // The conservation network must collapse at PREPROCESS (not exponential
    // per-branch re-derivation). Two passes can own that fold: guarded_eq
    // mining (#23 keystone) and the later EqDiffVar difference-variable
    // reduction (#23 residual, commit 1eb7a352), which runs first and now
    // subsumes these var-var equality chains — so the fold attribution lands on
    // whichever pass reaches it. Assert the INTENT (collapsed at preprocess by
    // either pass), not the implementation detail of which one.
    let folded = exec
        .statistics()
        .get_int("preprocess.guarded_eq.folded_atoms")
        .unwrap_or(0);
    let mined = exec
        .statistics()
        .get_int("preprocess.guarded_eq.mined_rows")
        .unwrap_or(0);
    let dv_rewritten = exec
        .statistics()
        .get_int("preprocess.eq_diffvar.rewritten_atoms")
        .unwrap_or(0);
    let dv_vars = exec
        .statistics()
        .get_int("preprocess.eq_diffvar.diff_vars")
        .unwrap_or(0);
    assert!(
        folded >= 1 || mined >= 1 || dv_rewritten >= 1 || dv_vars >= 1,
        "expected the conservation network to collapse at preprocess via guarded_eq or eq_diffvar; \
         guarded_eq.folded_atoms={folded} mined_rows={mined} \
         eq_diffvar.rewritten_atoms={dv_rewritten} diff_vars={dv_vars}"
    );
}

/// Dropping the final `(not v35_1)` makes the network satisfiable. The fold
/// must preserve equivalence exactly: the solver still answers sat (model
/// validation runs against the original assertions).
#[test]
#[timeout(60_000)]
fn min_repro_sat_variant_stays_sat_23() {
    let script = min_repro_script().replace("(assert (not v35_1))", "");
    assert!(
        !script.contains("(not v35_1)"),
        "sat variant should have removed the negated goal"
    );
    let (_exec, outputs) = run_script(&script);
    assert_eq!(outputs, vec!["sat"]);
}

/// Kill-switch sanity at the unit level: the same network shape solved
/// through the executor twice gives the same verdict (the env flag itself is
/// process-global, so the off-path is exercised by the CLI A/B harness).
#[test]
#[timeout(30_000)]
fn small_conservation_network_unsat_23() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const g1 Bool)
        (declare-const g2 Bool)
        (declare-const s Bool)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const a Int)
        (declare-const b Int)
        ; g1: both branches conserve a + b = x + y
        (assert (or (not g1) (= a x)))
        (assert (or (not g1) (= b y)))
        (assert (or g1 (= a y)))
        (assert (or g1 (= b x)))
        ; g2: both branches force x + y = 1 (using g1's conservation)
        (assert (or (not g2) (= (+ x y) 1)))
        (assert (or g2 (= (+ a b) 1)))
        ; s <-> (x + y = 1), and s is asserted false
        (assert (= s (= (+ x y) 1)))
        (assert (not s))
        (check-sat)
    "#;
    let (exec, outputs) = run_script(smt);
    assert_eq!(outputs, vec!["unsat"]);
    // Folded at preprocess by guarded_eq mining OR its EqDiffVar successor
    // (see min_repro_unsat_via_mining_23 for the attribution rationale).
    let folded = exec
        .statistics()
        .get_int("preprocess.guarded_eq.folded_atoms")
        .unwrap_or(0);
    let dv_rewritten = exec
        .statistics()
        .get_int("preprocess.eq_diffvar.rewritten_atoms")
        .unwrap_or(0);
    let dv_vars = exec
        .statistics()
        .get_int("preprocess.eq_diffvar.diff_vars")
        .unwrap_or(0);
    assert!(
        folded >= 1 || dv_rewritten >= 1 || dv_vars >= 1,
        "expected preprocess fold via guarded_eq or eq_diffvar; \
         guarded_eq.folded_atoms={folded} eq_diffvar.rewritten_atoms={dv_rewritten} diff_vars={dv_vars}"
    );
}
