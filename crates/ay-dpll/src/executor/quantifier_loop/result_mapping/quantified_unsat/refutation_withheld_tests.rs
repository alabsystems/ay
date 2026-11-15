// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `quantified_refutation_withheld` (#refutation-withheld): the DOWNGRADE arm
//! sets it, the two SAT producers decline while it is set, and it never
//! outlives a public solve.

use crate::executor::model::Model;
use crate::executor::Executor;
use crate::executor_types::{SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;
use ay_frontend::parse;

/// Satisfied by the constant interpretation `f := λ_. #x00, y := z := #x00`
/// (the `certifies_bv_heads_with_constant_candidates` fixture).
const CONST_INTERP_SAT: &str = "(set-logic ALL)
     (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
     (declare-fun y () (_ BitVec 8))
     (declare-fun z () (_ BitVec 8))
     (assert (forall ((x Int)) (=> (>= x 0) (= (bvadd (f y) z) z))))";

fn executor_for(input: &str) -> Executor {
    let commands = parse(input).expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture executes");
    exec
}

/// The producer side: a refutation withheld only for want of a translated
/// proof marks the executor. `:produce-proofs` makes the artifact mandatory
/// and the lone universal leaves every consulting and building leg nothing to
/// work with, so the arm downgrades.
#[test]
fn the_downgrade_arm_marks_the_refutation_withheld() {
    let mut exec = executor_for(
        "(set-option :produce-proofs true)
         (set-logic ALL)
         (declare-fun p (Int) Bool)
         (assert (forall ((x Int)) (p x)))",
    );
    assert!(!exec.quantified_refutation_withheld);
    let result = exec.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled);
    assert!(
        matches!(result, Ok(SolveResult::Unknown)),
        "no leg can authorize this refutation: {result:?}"
    );
    assert!(exec.quantified_refutation_withheld);
}

#[test]
fn withheld_refutation_declines_the_const_interp_certificate() {
    let mut exec = executor_for(CONST_INTERP_SAT);
    let assertions = exec.ctx.assertions.clone();
    exec.quantified_refutation_withheld = true;
    assert!(exec
        .try_const_interp_sat_certificate(&assertions, LogicCategory::QfBvLiaIndep)
        .is_none());
    exec.quantified_refutation_withheld = false;
    assert!(exec
        .try_const_interp_sat_certificate(&assertions, LogicCategory::QfBvLiaIndep)
        .is_some());
}

#[test]
fn withheld_refutation_declines_the_snapshot_ground_model_probe() {
    let mut exec = executor_for("(set-logic QF_LIA) (declare-const x Int) (assert (= x 1))");
    let snapshot = exec.ctx.assertions.clone();
    exec.last_model = Some(Model::empty());
    exec.quantified_refutation_withheld = true;
    assert!(!exec.ensure_snapshot_ground_model_for_completion(&snapshot, LogicCategory::QfLia));
    exec.quantified_refutation_withheld = false;
    assert!(exec.ensure_snapshot_ground_model_for_completion(&snapshot, LogicCategory::QfLia));
}

#[test]
fn withheld_refutation_does_not_outlive_its_public_solve() {
    let mut exec = executor_for(CONST_INTERP_SAT);
    exec.quantified_refutation_withheld = true;
    let outputs = exec
        .execute_all(&parse("(check-sat)").expect("parses"))
        .expect("executes");
    assert_eq!(outputs.first().map(|line| line.trim()), Some("sat"));
}

/// D7: the flag reaches the statistics block as `quantifier.refutation_withheld`,
/// and only on an Unknown exit, so a corpus scan can tell a withheld
/// refutation from a quantifier with no strategy.
#[test]
fn withheld_refutation_is_a_statistic_only_on_an_unknown_exit() {
    let key = "quantifier.refutation_withheld";
    let mut exec = executor_for("(set-logic QF_LIA) (declare-const x Int) (assert (= x 1))");
    exec.last_result = Some(SolveResult::Unknown);
    exec.finalize_unknown_diagnostics();
    assert_eq!(exec.last_statistics.get_int(key), None);
    exec.quantified_refutation_withheld = true;
    exec.finalize_unknown_diagnostics();
    assert_eq!(exec.last_statistics.get_int(key), Some(1));

    let mut decided = executor_for("(set-logic QF_LIA) (declare-const x Int) (assert (= x 1))");
    decided.last_result = Some(SolveResult::Sat);
    decided.quantified_refutation_withheld = true;
    decided.finalize_unknown_diagnostics();
    assert_eq!(decided.last_statistics.get_int(key), None);
}
