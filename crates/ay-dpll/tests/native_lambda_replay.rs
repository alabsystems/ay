// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use ay_core::{term::TermData, Sort, TermId};
use ay_dpll::api::{
    Logic, NativeReplayArtifact, NativeReplayEventKind, NativeReplayExportBudget,
    NativeReplayExportLimits, NativeReplayMetadata, Solver, Term, TermKind,
};

fn capture(solver: &Solver) -> NativeReplayArtifact {
    let mut budget = NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        16 * 1024 * 1024,
        8 * 1024 * 1024,
        4 * 1024 * 1024,
        128,
    ));
    let json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true,
        )
        .expect("capture complete native input");
    NativeReplayArtifact::from_json_str(&json).expect("parse native input")
}

fn retain_contradiction(solver: &mut Solver, value: Term) {
    let sort = solver.get_sort(value);
    let marker = solver
        .try_declare_fun("native_lambda_marker", &[sort], Sort::Bool)
        .expect("declare marker");
    let atom = solver.try_apply(&marker, &[value]).expect("retain value");
    let negated = solver.not(atom);
    solver.assert_term(atom);
    solver.assert_term(negated);
}

fn assert_checked_unsat(artifact: &NativeReplayArtifact) {
    let replay =
        Solver::replay_native_replay_artifact_with_proofs(artifact, Duration::from_secs(5))
            .expect("reconstruct native input");
    assert!(replay.result.is_unsat(), "{replay:?}");
    assert!(
        replay.verification.unsat_proof_strictly_verified,
        "{replay:?}"
    );
}

fn dependent_lambda() -> (Solver, TermId, TermId) {
    let mut solver = Solver::new(Logic::All);
    let index = solver.fresh_var("native_lambda_index", Sort::Int);
    let one = solver.int_const(1);
    let body = solver.add(index, one);
    let lambda = solver.lambda_array(index, body);
    retain_contradiction(&mut solver, lambda);
    (solver, lambda.id(), one.id())
}

#[test]
fn dependent_lambda_round_trips_through_bounded_native_input() {
    let (solver, _, _) = dependent_lambda();
    assert_checked_unsat(&capture(&solver));
}

#[test]
fn a_declared_constant_keeps_its_free_occurrences_outside_the_lambda() {
    let mut solver = Solver::new(Logic::All);
    let index = solver.declare_const("native_lambda_declared_index", Sort::Int);
    let one = solver.int_const(1);
    let body = solver.add(index, one);
    let lambda = solver.lambda_array(index, body);
    let global = solver.eq(index, one);
    solver.assert_term(global);
    retain_contradiction(&mut solver, lambda);
    assert_checked_unsat(&capture(&solver));
}

#[test]
fn the_lambda_array_operator_cannot_be_shadowed_by_a_native_function() {
    let mut solver = Solver::new(Logic::All);
    assert!(solver
        .try_declare_fun("lambda-array", &[Sort::Bool, Sort::Int], Sort::Bool)
        .is_err());
}

/// Retain the lambda in the captured DAG, then read it directly in the
/// serialized input. Constructing this select before capture would beta-reduce
/// it and would never exercise replay's lambda reconstruction. The marker's
/// assertion is replaced in both root inventories so it contributes no premise.
fn semantic_lambda_read(declared_binder: bool, expected: i64) -> NativeReplayArtifact {
    let mut solver = Solver::new(Logic::All);
    let global = solver.declare_const("native_lambda_global", Sort::Int);
    let seven = solver.int_const(7);
    let global_value = solver.eq(global, seven);
    solver.assert_term(global_value);
    let binder = if declared_binder {
        global
    } else {
        solver.fresh_var("native_lambda_bound", Sort::Int)
    };
    let offset = if declared_binder {
        solver.int_const(1)
    } else {
        global
    };
    let body = solver.add(binder, offset);
    let lambda = solver.lambda_array(binder, body);
    let marker = solver
        .try_declare_fun(
            "native_lambda_retainer",
            &[solver.get_sort(lambda)],
            Sort::Bool,
        )
        .unwrap();
    let retained = solver.try_apply(&marker, &[lambda]).unwrap();
    solver.assert_term(retained);
    let placeholder = solver.declare_const("native_lambda_placeholder", solver.get_sort(lambda));
    let two = solver.int_const(2);
    let read = solver.select(placeholder, two);
    let expected = solver.int_const(expected);
    let value = solver.eq(read, expected);
    solver.assert_term(value);
    let mut artifact = capture(&solver);
    let read_node = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == read.id())
        .unwrap();
    let TermData::App(_, args) = &mut read_node.data else {
        panic!("placeholder select must survive capture");
    };
    assert_eq!(args[0], placeholder.id());
    args[0] = lambda.id();
    for assertion in &mut artifact.assertions {
        if assertion.term == retained.id() {
            assertion.term = global_value.id();
        }
    }
    for event in &mut artifact.events {
        if let NativeReplayEventKind::Assert { term, .. } = &mut event.kind {
            if *term == retained.id() {
                *term = global_value.id();
            }
        }
    }
    artifact
}

#[test]
fn lambda_replay_preserves_the_dependent_body_and_independent_free_variable() {
    for (declared_binder, expected) in [(false, 9), (true, 3)] {
        let artifact = semantic_lambda_read(declared_binder, expected);
        let replay =
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
                .expect("replay lambda read with a free global");
        assert!(replay.result.is_sat(), "{declared_binder}: {replay:?}");
        assert!(
            replay.result.was_model_validated() && replay.verification.sat_model_validated,
            "{declared_binder}: {replay:?}"
        );
        assert_checked_unsat(&semantic_lambda_read(declared_binder, expected - 1));
    }
}

#[test]
fn lambda_binders_shadow_only_their_exact_variable_under_a_quantifier() {
    let mut solver = Solver::new(Logic::All);
    let outer = solver.fresh_var("native_lambda_outer", Sort::Int);
    let binder = solver.fresh_var("native_lambda_inner", Sort::Bool);
    let zero = solver.int_const(0);
    let free_outer = solver.ge(outer, zero);
    let body = solver.and(binder, free_outer);
    let lambda = solver.lambda_array(binder, body);
    let marker = solver
        .try_declare_fun(
            "native_nested_lambda_marker",
            &[solver.get_sort(lambda)],
            Sort::Bool,
        )
        .expect("declare marker");
    let atom = solver.try_apply(&marker, &[lambda]).expect("retain lambda");
    let quantifier = solver.try_forall(&[outer], atom).expect("bind outer Int");
    let negated = solver.not(quantifier);
    solver.assert_term(quantifier);
    solver.assert_term(negated);
    let mut artifact = capture(&solver);
    let TermKind::Var { name } = solver.term_kind(outer) else {
        panic!("outer is a variable");
    };
    let inner = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == binder.id())
        .unwrap();
    let TermData::Var(inner_name, _) = &mut inner.data else {
        panic!("lambda binder is a variable");
    };
    *inner_name = name;
    assert_checked_unsat(&artifact);
}

#[test]
fn malformed_lambda_binders_and_result_sorts_are_rejected() {
    let (solver, lambda, one) = dependent_lambda();
    let source = capture(&solver);
    for malformed in ["arity", "binder", "index", "element"] {
        let mut artifact = source.clone();
        let node = artifact
            .terms
            .iter_mut()
            .find(|node| node.id == lambda)
            .unwrap();
        let TermData::App(_, args) = &mut node.data else {
            panic!("lambda is an application");
        };
        match malformed {
            "arity" => {
                args.pop();
            }
            "binder" => args[0] = one,
            "index" => node.sort = Sort::array(Sort::Bool, Sort::Int),
            "element" => node.sort = Sort::array(Sort::Int, Sort::Bool),
            _ => unreachable!(),
        }
        let error = Solver::replay_native_replay_artifact(&artifact)
            .expect_err("malformed native lambda must be rejected");
        assert!(error.to_string().contains("lambda"), "{malformed}: {error}");
    }
}
