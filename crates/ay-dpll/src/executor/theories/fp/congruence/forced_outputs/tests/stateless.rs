// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::executor::Executor;
use crate::executor_types::{SolveResult, UnknownReason};

fn setup(script: &str) -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse(script).unwrap())
        .unwrap();
    executor
}

fn declarations(count: usize) -> String {
    let mut script = String::from("(declare-fun g ((_ FloatingPoint 5 11)) Bool)\n");
    for i in 0..count {
        script.push_str(&format!("(declare-const x{i} (_ FloatingPoint 5 11))\n"));
    }
    script
}

#[test]
fn oversized_opposite_results_on_equal_or_nan_arguments_are_unsat() {
    for constraint in [
        "(assert (= x0 x64))",
        "(assert (fp.isNaN x0)) (assert (fp.isNaN x64))",
    ] {
        let mut script = declarations(65);
        for i in 0..64 {
            script.push_str(&format!("(assert (g x{i}))\n"));
        }
        script.push_str("(assert (not (g x64)))\n");
        script.push_str(constraint);
        let mut executor = setup(&script);
        // All 64 residual pairs are now encoded. This is an actual conflict,
        // not merely refusal to publish a model of the relaxation.
        assert!(executor.solve_fp_stateless().unwrap().is_unsat());
        assert!(executor.last_model.is_none());
    }
}

#[test]
fn small_groups_keep_nan_identity_and_signed_zero_distinction() {
    for (constraints, expected_unsat) in [
        ("(assert (fp.isNaN x0)) (assert (fp.isNaN x1))", true),
        (
            "(assert (= x0 (_ +zero 5 11))) (assert (= x1 (_ -zero 5 11)))",
            false,
        ),
    ] {
        let mut script = declarations(2);
        script.push_str("(assert (g x0)) (assert (not (g x1)))\n");
        script.push_str(constraints);
        let mut executor = setup(&script);
        let result = executor.solve_fp_stateless().unwrap();
        if expected_unsat {
            assert!(result.is_unsat(), "NaN denotes one SMT value: {result:?}");
        } else {
            assert!(
                matches!(result, SolveResult::Sat),
                "signed zeros are distinct: {result:?}"
            );
            assert!(executor.last_model.is_some());
        }
    }
}

#[test]
fn stateless_oversized_forcing_follows_current_push_pop_activations() {
    let mut script = declarations(65);
    script.push_str("(declare-const condition Bool)\n");
    for i in 0..65 {
        script.push_str(&format!("(assert (or condition (g x{i})))\n"));
    }
    let mut executor = setup(&script);
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Unknown
    ));
    executor
        .execute_all(&ay_frontend::parse("(push 1) (assert (not condition))").unwrap())
        .unwrap();
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Sat
    ));
    assert!(executor.last_model.is_some());
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Unknown
    ));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
    assert!(executor.last_model.is_none());
}

fn assert_api_model(solver: &mut crate::api::Solver) {
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated, "{details:?}");
    assert!(solver.try_get_model_for_consumer().is_ok());
    assert!(solver.try_get_model_str().unwrap().contains("define-fun g"));
}

#[test]
fn mixed_residual_outputs_publish_a_validated_model_and_preserve_push_pop() {
    use crate::api::{Logic, ModelValue, Solver, Sort};
    for (positive, negative) in [("+zero", "-zero"), ("-zero", "+zero")] {
        let mut solver = Solver::new(Logic::QfFp);
        let g = solver.declare_fun("g", &[Sort::FloatingPoint(5, 11)], Sort::Bool);
        let mut args = Vec::new();
        let mut apps = Vec::new();
        for i in 0..65 {
            let arg = solver.declare_const(&format!("x{i}"), Sort::FloatingPoint(5, 11));
            let app = solver.try_apply(&g, &[arg]).unwrap();
            args.push(arg);
            apps.push(app);
            let literal = if i == 64 { solver.not(app) } else { app };
            solver.assert_term(literal);
        }
        solver
            .parse_smtlib2(&format!(
                "(assert (= x0 (_ {positive} 5 11))) (assert (= x64 (_ {negative} 5 11)))"
            ))
            .unwrap();
        assert_api_model(&mut solver);
        let expected: Vec<_> = (0..65).map(|i| ModelValue::Bool(i != 64)).collect();
        assert_eq!(solver.try_get_values(&apps).unwrap(), expected);

        solver.push();
        // x1 has no fixed bits: this conflict needs the x1/x64 residual
        // congruence implication, not contradictory constant equalities.
        let equal = solver.eq(args[1], args[64]);
        solver.assert_term(equal);
        assert!(solver.check_sat().is_unsat());
        assert!(solver.try_get_model_for_consumer().is_err());
        solver.pop();
        assert!(solver.try_get_model_for_consumer().is_err());
        assert_api_model(&mut solver);
        assert_eq!(solver.try_get_values(&apps).unwrap(), expected);
    }
}

#[test]
fn unforced_residual_outputs_keep_all_pairs_and_replay_original_assertions() {
    let mut script = declarations(65);
    script.push_str("(declare-const condition Bool)\n");
    for i in 0..63 {
        script.push_str(&format!("(assert (g x{i}))\n"));
    }
    // Both g(x63) and g(x64) remain unforced by unit resolution. With
    // condition=true they may agree, even at the same FP argument.
    script.push_str("(assert (or condition (g x63))) (assert (or condition (not (g x64)))) (assert (= x63 x64))\n");
    let mut solver = crate::api::Solver::new(crate::api::Logic::QfFp);
    solver.parse_smtlib2(&script).unwrap();
    assert_api_model(&mut solver);
    solver.push();
    solver.parse_smtlib2("(assert (not condition))").unwrap();
    assert!(
        solver.check_sat().is_unsat(),
        "activated residual outputs conflict on equal arguments"
    );
    assert!(solver.try_get_model_for_consumer().is_err());
    solver.pop();
    assert_api_model(&mut solver);

    // Unit closure still cannot force either UF result, but the Boolean
    // clauses require opposite outputs in both branches of condition.
    script.push_str(
        "(assert (or (not condition) (not (g x63)))) (assert (or (not condition) (g x64)))\n",
    );
    let mut executor = setup(&script);
    assert!(
        executor.solve_fp_stateless().unwrap().is_unsat(),
        "the unknown/unknown pair must not be omitted"
    );
    assert!(executor.last_model.is_none());
}
