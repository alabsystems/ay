// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The option is read as a Boolean and nothing else, and a refinement that
//! would refute is left out, with no instance added, exactly when it says
//! `false`.

use ay_core::TermId;
use ay_frontend::Command;

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

fn load(smt: &str) -> Executor {
    let commands = ay_frontend::parse(smt).expect("fixture parses");
    let mut exec = Executor::new();
    for command in &commands {
        let output = exec.execute(command).expect("fixture executes");
        assert!(output.is_none(), "fixture must not contain a query command");
    }
    exec
}

#[test]
fn only_the_boolean_false_switches_model_based_instantiation_off() {
    for (options, off) in [
        ("", false),
        ("(set-option :smt.mbqi false)", true),
        ("(set-option :smt.mbqi true)", false),
        (
            "(set-option :smt.mbqi false) (set-option :smt.mbqi true)",
            false,
        ),
        (
            "(set-option :smt.mbqi true) (set-option :smt.mbqi false)",
            true,
        ),
        ("(set-option :smt.mbqi 0)", false),
        ("(set-option :smt.mbqi.max_iterations 0)", false),
        ("(set-option :smt.ematching false)", false),
    ] {
        let exec = load(options);
        assert_eq!(
            exec.model_based_instantiation_is_off(),
            off,
            "after `{options}`"
        );
    }
}

/// `a` is outside `p`; the universal, which has no ground instance yet, says
/// nothing is. `options` is the only thing the callers vary.
fn falsified_universal(options: &str) -> String {
    format!(
        "{options}
         (set-logic ALL)
         (declare-sort U 0)
         (declare-fun p (U) Bool)
         (declare-const a U)
         (assert (not (p a)))
         (assert (forall ((x U)) (p x)))"
    )
}

/// Solve the ground part so the executor holds its model, then ask for the
/// refinement of that model against the universal. Returns the executor, the
/// ground root and what the refinement answered.
fn refine(options: &str) -> (Executor, TermId, Option<Result<SolveResult>>) {
    let mut exec = load(&falsified_universal(options));
    let roots = exec.ctx.assertions.clone();
    let (ground, universal) = (roots[0], roots[1]);
    exec.ctx.assertions = vec![ground];
    let verdict = exec
        .execute(&Command::CheckSat)
        .expect("ground part solves");
    assert_eq!(verdict.as_deref(), Some("sat"), "the ground part is sat");
    assert!(
        exec.last_model.is_some(),
        "the ground solve keeps its model"
    );
    let answer = exec.try_mbqi_refinement(&[universal], LogicCategory::QfUf, &roots);
    (exec, ground, answer)
}

/// With no option the model's `p a = false` falsifies the universal at `a`,
/// the instance is conjoined, and the re-solve refutes.
#[test]
fn the_refinement_refutes_a_falsified_universal_when_it_may_run() {
    for options in ["", "(set-option :smt.mbqi true)"] {
        let (exec, _, answer) = refine(options);
        assert!(
            matches!(answer, Some(Ok(SolveResult::Unsat(_)))),
            "after `{options}`: {answer:?}"
        );
        assert!(
            exec.last_statistics.quantifier_mbqi_rounds >= 1,
            "a refinement round ran"
        );
        assert_eq!(
            exec.last_statistics.get_int("quantifier.mbqi.switched_off"),
            None,
            "nothing was switched off"
        );
    }
}

/// The twin, one option different: the same universal, the same model, and
/// the refinement has no verdict. It adds no instance and probes nothing, so
/// what the caller fails closed on is the ground problem it had.
#[test]
fn switched_off_the_refinement_adds_no_instance_and_has_no_verdict() {
    let (exec, ground, answer) = refine("(set-option :smt.mbqi false)");
    assert!(answer.is_none(), "{answer:?}");
    assert_eq!(exec.ctx.assertions, vec![ground], "no instance was added");
    assert_eq!(exec.last_statistics.quantifier_mbqi_rounds, 0);
    assert_eq!(exec.last_statistics.quantifier_mbqi_candidates_probed, 0);
    assert_eq!(
        exec.last_statistics.get_int("quantifier.mbqi.switched_off"),
        Some(1)
    );
}

/// Without a universal there is nothing to refine and nothing to count,
/// whatever the option says.
#[test]
fn an_empty_refinement_is_not_counted_as_switched_off() {
    let mut exec = load("(set-option :smt.mbqi false)");
    assert!(exec
        .try_mbqi_refinement(&[], LogicCategory::QfUf, &[])
        .is_none());
    assert_eq!(
        exec.last_statistics.get_int("quantifier.mbqi.switched_off"),
        None
    );
}

/// No 32-bit `a` is above every 32-bit `x`. No trigger reaches the universal
/// and enumeration cannot cover the width; the bit-vector lane decides it.
/// `options` is the only thing the callers vary.
fn wide_binder(options: &str, relation: &str) -> String {
    format!(
        "{options}
         (set-logic BV)
         (declare-fun a () (_ BitVec 32))
         (assert (bvugt a #x00000005))
         (assert (forall ((x (_ BitVec 32))) ({relation} x a)))
         (check-sat)"
    )
}

fn answer(smt: &str) -> (Executor, String) {
    let commands = ay_frontend::parse(smt).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    (exec, outputs.last().cloned().unwrap_or_default())
}

/// The option keeps the generic candidate path out, not the bit-vector lane:
/// the refutation is the same with the option on either side, and nothing is
/// counted as switched off.
#[test]
fn the_bit_vector_lane_refutes_with_the_option_on_either_side() {
    for options in ["", "(set-option :smt.mbqi false)"] {
        let (exec, verdict) = answer(&wide_binder(options, "bvult"));
        assert_eq!(verdict, "unsat", "after `{options}`");
        assert_eq!(
            exec.last_statistics.get_int("quantifier.mbqi.switched_off"),
            None,
            "after `{options}`: the generic path was never reached"
        );
    }
}

/// The twin, one operator different: `x <=u a` holds for every `x` once `a`
/// is all ones, so the problem has a model and is never refuted.
#[test]
fn the_twin_a_wide_enough_bound_satisfies_is_not_refuted() {
    for options in ["", "(set-option :smt.mbqi false)"] {
        let (_, verdict) = answer(&wide_binder(options, "bvule"));
        assert_eq!(verdict, "sat", "after `{options}`");
    }
}

/// End to end, through the quantifier pipeline: the same falsified universal
/// with the option on either side. Trigger matching instantiates `p x` at `a`
/// by itself here, so the refutation does not depend on the refinement and
/// must survive switching it off.
#[test]
fn a_refutation_from_trigger_matching_does_not_depend_on_the_option() {
    for options in ["", "(set-option :smt.mbqi false)"] {
        let mut exec = load(&falsified_universal(options));
        let verdict = exec.execute(&Command::CheckSat).expect("solves");
        assert_eq!(verdict.as_deref(), Some("unsat"), "after `{options}`");
    }
}
