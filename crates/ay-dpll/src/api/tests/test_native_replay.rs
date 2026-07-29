// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay artifact tests for downstream reducer handoff.

use std::time::Duration;

use crate::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, NativeReplayArtifact,
    NativeReplayEventKind, NativeReplayMetadata, SolveResult, Solver, SolverError, Sort, Term,
};
use ay_core::term::{Symbol, TermData};
use ay_core::TermId;

fn assert_native_replay_rejected(artifact: &NativeReplayArtifact) {
    assert!(matches!(
        Solver::replay_native_replay_artifact(artifact),
        Err(SolverError::InvalidArgument {
            operation: "native_replay",
            ..
        })
    ));
}

fn boolean_unsat_native_replay_artifact() -> NativeReplayArtifact {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat());
    solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details))
}

#[cfg(feature = "proof-checker")]
#[test]
fn native_replay_with_proofs_returns_only_strict_complete_unsat_authority() {
    let artifact = boolean_unsat_native_replay_artifact();
    let replay =
        Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
            .expect("strict proof replay");

    assert!(replay.result.is_unsat());
    assert!(replay.verification_level.has_proof_checking());
    assert!(replay.verification.unsat_proof_available);
    assert_eq!(replay.verification.unsat_proof_checker_failures, 0);
    assert!(replay.statistics.proof_complete);
    assert_eq!(replay.statistics.get_int("proof_trust"), Some(0));
    assert_eq!(replay.statistics.get_int("proof_checker_failures"), Some(0));
    let checked = replay
        .statistics
        .get_int("proof_checker_checked_steps")
        .expect("checked step count");
    let total = replay
        .statistics
        .get_int("proof_checker_total_steps")
        .expect("total step count");
    assert!(total > 0);
    assert_eq!(checked, total);
    assert_eq!(
        replay
            .statistics
            .get_int("proof_checker_skipped_hole_steps"),
        Some(0)
    );
}

#[test]
fn ordinary_native_replay_remains_proofless() {
    let artifact = boolean_unsat_native_replay_artifact();
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("ordinary replay");

    assert!(replay.result.is_unsat());
    assert!(
        !replay.verification_level.has_proof_checking(),
        "the existing replay API must not silently enable proof production"
    );
    assert!(!replay.verification.unsat_proof_available);
    assert_eq!(replay.statistics.get_int("proof_checker_failures"), None);
}

#[test]
fn native_replay_with_proofs_honors_caller_and_artifact_timeout_bounds() {
    let solver = Solver::try_new(Logic::QfUf).expect("solver");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let caller_bounded =
        Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::ZERO)
            .expect("Unknown is diagnostic, not proof authority");
    assert!(
        caller_bounded.result.is_unknown(),
        "a zero caller deadline must fail closed as Unknown"
    );

    let mut recorded_bounded = artifact;
    recorded_bounded.timeout_ms = Some(0);
    let replay = Solver::replay_native_replay_artifact_with_proofs(
        &recorded_bounded,
        Duration::from_secs(5),
    )
    .expect("the recorded timeout is the tighter bound");
    assert!(
        replay.result.is_unknown(),
        "the recorded zero deadline must win over a longer caller deadline"
    );
}

#[test]
fn native_replay_with_proofs_rejects_tampered_identity_tables() {
    let mut artifact = boolean_unsat_native_replay_artifact();
    artifact
        .terms
        .push(artifact.terms.first().expect("Boolean term").clone());
    assert!(matches!(
        Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5)),
        Err(SolverError::InvalidArgument {
            operation: "native_replay",
            ..
        })
    ));
}

#[test]
fn native_replay_artifact_round_trips_active_assertions() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let x_gt_zero = solver.try_gt(x, zero).expect("x > 0");
    solver
        .try_assert_named(x_gt_zero, "precondition")
        .expect("assert");
    let x_eq_one = solver.try_eq(x, one).expect("x = 1");
    solver.try_assert_term(x_eq_one).expect("assert");

    let details = solver.check_sat_with_details();
    assert_eq!(*details.result.result(), SolveResult::Sat);

    let artifact = solver.export_native_replay_artifact(
        NativeReplayMetadata {
            consumer: Some("verification-consumer".to_string()),
            fixture_path: Some("tests/should_succeed/take_first_mut.rs".to_string()),
            obligation_kind: Some("ensures".to_string()),
            ..Default::default()
        },
        Some(&details),
    );

    assert_eq!(artifact.schema, "ay.native-replay.v1");
    assert_eq!(
        artifact.metadata.consumer.as_deref(),
        Some("verification-consumer")
    );
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::CheckSat)));
    assert_eq!(artifact.assertions.len(), 2);
    let json = artifact.to_pretty_json();
    assert!(json.contains("precondition"));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    assert_eq!(replay.result.result(), details.result.result());

    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse native replay JSON");
    let replay_from_json =
        Solver::replay_native_replay_artifact(&parsed).expect("native replay from parsed JSON");
    assert_eq!(replay_from_json.result.result(), details.result.result());

    let replay_from_json_str =
        Solver::replay_native_replay_json_str(&json).expect("native replay from JSON string");
    assert_eq!(
        replay_from_json_str.result.result(),
        details.result.result()
    );
}

#[test]
fn native_replay_round_trips_registered_nullary_uf() {
    let mut solver = Solver::try_new(Logic::Auflia).expect("solver");
    let function = solver
        .try_declare_fun("replay_nullary_opaque", &[], Sort::Int)
        .expect("declare nullary UF");
    let application = solver.try_apply(&function, &[]).expect("apply nullary UF");
    let forty_two = solver.int_const(42);
    let differs = solver
        .try_distinct(&[application, forty_two])
        .expect("nullary UF differs from 42");
    solver.try_assert_term(differs).expect("assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact.function_declarations.iter().any(|declaration| {
        declaration.name == "replay_nullary_opaque" && declaration.domain.is_empty()
    }));

    let replay =
        Solver::replay_native_replay_artifact(&artifact).expect("in-memory nullary UF replay");
    assert_eq!(replay.result.result(), details.result.result());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("JSON nullary UF replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_prefers_registered_internal_looking_function_names() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let map_named = solver
        .try_declare_fun("map[replay_user]", &[Sort::Int], Sort::Bool)
        .expect("declare map-looking UF");
    let as_array_named = solver
        .try_declare_fun("as-array[replay_user]", &[Sort::Int], Sort::Bool)
        .expect("declare as-array-looking UF");
    let argument = solver.declare_const("replay_internal_looking_arg", Sort::Int);
    let map_application = solver
        .try_apply(&map_named, &[argument])
        .expect("apply map-looking UF");
    let as_array_application = solver
        .try_apply(&as_array_named, &[argument])
        .expect("apply as-array-looking UF");
    let disjunction = solver
        .try_or(map_application, as_array_application)
        .expect("combine applications");
    solver.try_assert_term(disjunction).expect("assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("registered internal-looking names replay as UFs");
    assert_eq!(replay.result.result(), details.result.result());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("registered internal-looking names replay from JSON");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_rejects_undeclared_internal_variable_identity() {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let p = solver.declare_const("p", Sort::Bool);
    solver.try_assert_term(p).expect("assert p");
    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);

    artifact.declarations.clear();
    let p_node = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == p.0)
        .expect("replay closure contains p");
    let var_id = match &p_node.data {
        TermData::Var(_, var_id) => *var_id,
        _ => panic!("p must export as a variable"),
    };
    p_node.data = TermData::Var("__ay_ext_diff!replay".to_string(), var_id);

    assert!(matches!(
        Solver::replay_native_replay_artifact(&artifact),
        Err(SolverError::InvalidArgument {
            operation: "native_replay",
            ..
        })
    ));
}

#[test]
fn native_replay_rejects_ambiguous_or_mismatched_identity_tables() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let a = solver.declare_const("replay_identity_a", Sort::Int);
    let b = solver.declare_const("replay_identity_b", Sort::Int);
    let zero = solver.int_const(0);
    let equality = solver.try_eq(a, b).expect("equality");
    solver.try_assert_term(equality).expect("assert");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);

    let mut duplicate_node = artifact.clone();
    duplicate_node.terms.push(duplicate_node.terms[0].clone());
    assert_native_replay_rejected(&duplicate_node);

    let mut duplicate_term_declaration = artifact.clone();
    duplicate_term_declaration
        .declarations
        .push(duplicate_term_declaration.declarations[0].clone());
    assert_native_replay_rejected(&duplicate_term_declaration);

    let mut duplicate_name = artifact.clone();
    duplicate_name.declarations[1].name = duplicate_name.declarations[0].name.clone();
    assert_native_replay_rejected(&duplicate_name);

    let mut mismatched_name = artifact.clone();
    let declaration = mismatched_name.declarations[0].clone();
    let node = mismatched_name
        .terms
        .iter_mut()
        .find(|node| node.id == declaration.term)
        .expect("declared node");
    let TermData::Var(name, _) = &mut node.data else {
        unreachable!();
    };
    *name = "replay_identity_forged".to_string();
    assert_native_replay_rejected(&mismatched_name);

    let mut non_variable_target = artifact.clone();
    let declaration = &mut non_variable_target.declarations[0];
    declaration.term = zero.0;
    assert_native_replay_rejected(&non_variable_target);

    let mut constructor_collision = artifact;
    let declaration = constructor_collision.declarations[0].clone();
    let node = constructor_collision
        .terms
        .iter_mut()
        .find(|node| node.id == declaration.term)
        .expect("declared node");
    node.is_datatype_constructor = true;
    assert_native_replay_rejected(&constructor_collision);
}

#[test]
fn native_replay_rejects_reserved_malformed_and_missing_builtin_applications() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("replay_builtin_x", Sort::Int);
    let zero = solver.int_const(0);
    let less = solver.try_lt(x, zero).expect("x < 0");
    solver.try_assert_term(less).expect("assert");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);

    let app_index = artifact
        .terms
        .iter()
        .position(|node| matches!(&node.data, TermData::App(Symbol::Named(name), _) if name == "<"))
        .expect("comparison application");

    let mut reserved = artifact.clone();
    let TermData::App(symbol, _) = &mut reserved.terms[app_index].data else {
        unreachable!();
    };
    *symbol = Symbol::Named("__ay_ext_diff!forged_app".to_string());
    assert_native_replay_rejected(&reserved);

    let mut wrong_arity = artifact.clone();
    let TermData::App(_, args) = &mut wrong_arity.terms[app_index].data else {
        unreachable!();
    };
    args.pop();
    assert_native_replay_rejected(&wrong_arity);

    let mut missing_child = artifact;
    let TermData::App(_, args) = &mut missing_child.terms[app_index].data else {
        unreachable!();
    };
    args[0] = TermId(u32::MAX);
    assert_native_replay_rejected(&missing_child);
}

#[test]
fn native_replay_reconstructs_const_array_and_rejects_malformed_shape() {
    let mut solver = Solver::try_new(Logic::QfAuflia).expect("solver");
    let zero = solver.int_const(0);
    let constant = solver
        .try_const_array(Sort::Int, zero)
        .expect("constant array");
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = solver.declare_const("replay_const_array", array_sort.clone());
    let definition = solver.try_eq(array, constant).expect("array definition");
    solver
        .try_assert_term(definition)
        .expect("assert definition");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    assert!(
        details.result.was_model_validated() && details.verification.sat_model_validated,
        "original const-array query must carry a validated SAT model"
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let const_array_index = artifact
        .terms
        .iter()
        .position(|node| {
            matches!(
                &node.data,
                TermData::App(Symbol::Named(name), args)
                    if name == "const-array" && args.len() == 1
            )
        })
        .expect("const-array node");
    assert_eq!(artifact.terms[const_array_index].sort, array_sort);

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("in-memory replay");
    assert_eq!(replay.result.result(), details.result.result());
    assert!(
        replay.result.was_model_validated() && replay.verification.sat_model_validated,
        "in-memory const-array replay must carry a validated SAT model"
    );
    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
    assert!(
        replay_from_json.result.was_model_validated()
            && replay_from_json.verification.sat_model_validated,
        "JSON const-array replay must carry a validated SAT model"
    );

    let mut non_array_result = artifact.clone();
    non_array_result.terms[const_array_index].sort = Sort::Int;
    assert_native_replay_rejected(&non_array_result);

    let mut wrong_element_sort = artifact.clone();
    wrong_element_sort.terms[const_array_index].sort = Sort::array(Sort::Int, Sort::Bool);
    assert_native_replay_rejected(&wrong_element_sort);

    let mut wrong_arity = artifact;
    let TermData::App(_, args) = &mut wrong_arity.terms[const_array_index].data else {
        unreachable!();
    };
    args.clear();
    assert_native_replay_rejected(&wrong_arity);
}

#[test]
fn native_replay_authenticates_registered_uf_and_datatype_applications() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let boolean = solver.declare_const("replay_wrong_uf_arg", Sort::Bool);
    let integer = solver.declare_const("replay_right_uf_arg", Sort::Int);
    let function = solver
        .try_declare_fun("replay_checked_uf", &[Sort::Int], Sort::Bool)
        .expect("declare function");
    let application = solver
        .try_apply(&function, &[integer])
        .expect("apply function");
    let conjunction = solver.try_and(boolean, application).expect("conjunction");
    solver.try_assert_term(conjunction).expect("assert");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect("valid UF replay");

    let mut wrong_uf_argument = artifact;
    let uf_node = wrong_uf_argument
        .terms
        .iter_mut()
        .find(|node| {
            matches!(&node.data, TermData::App(Symbol::Named(name), _) if name == "replay_checked_uf")
        })
        .expect("UF application");
    let TermData::App(_, args) = &mut uf_node.data else {
        unreachable!();
    };
    args[0] = boolean.0;
    assert_native_replay_rejected(&wrong_uf_argument);

    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let datatype = DatatypeSort::new(
        "ReplayCheckedBox",
        vec![DatatypeConstructor::new(
            "ReplayCheckedBoxMk",
            vec![DatatypeField::new("replay_checked_value", Sort::Int)],
        )],
    );
    solver.try_declare_datatype(&datatype).expect("datatype");
    let value = solver.int_const(1);
    let boxed = solver.datatype_constructor(&datatype, "ReplayCheckedBoxMk", &[value]);
    let variable = solver.declare_const("replay_checked_box", Sort::Datatype(datatype.clone()));
    let equality = solver.try_eq(variable, boxed).expect("box equality");
    solver.try_assert_term(equality).expect("assert");
    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let constructor = artifact
        .terms
        .iter_mut()
        .find(|node| {
            matches!(&node.data, TermData::App(Symbol::Named(name), _) if name == "ReplayCheckedBoxMk")
        })
        .expect("constructor application");
    constructor.sort = Sort::Bool;
    assert_native_replay_rejected(&artifact);
}

#[test]
fn native_replay_authenticates_indexed_builtin_shape_and_sort() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("solver");
    let byte = solver.declare_const("replay_indexed_byte", Sort::bitvec(8));
    let nibble = solver.try_bvextract(byte, 3, 0).expect("extract");
    let expected = solver.bv_const(0xb, 4);
    let equality = solver.try_eq(nibble, expected).expect("equality");
    solver.try_assert_term(equality).expect("assert");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect("valid indexed replay");

    let mut invalid_index = artifact.clone();
    let indexed = invalid_index
        .terms
        .iter_mut()
        .find(|node| {
            matches!(&node.data, TermData::App(Symbol::Indexed(name, _), _) if name == "extract")
        })
        .expect("indexed extract");
    let TermData::App(Symbol::Indexed(_, indices), _) = &mut indexed.data else {
        unreachable!();
    };
    indices[0] = 8;
    assert_native_replay_rejected(&invalid_index);

    let mut wrong_sort = artifact;
    let indexed = wrong_sort
        .terms
        .iter_mut()
        .find(|node| {
            matches!(&node.data, TermData::App(Symbol::Indexed(name, _), _) if name == "extract")
        })
        .expect("indexed extract");
    indexed.sort = Sort::bitvec(5);
    assert_native_replay_rejected(&wrong_sort);
}

#[test]
fn native_replay_rejects_malformed_structural_nodes_and_lying_sorts() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let condition = solver.declare_const("replay_structure_condition", Sort::Bool);
    let integer = solver.declare_const("replay_structure_integer", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let ite = solver.try_ite(condition, zero, one).expect("ite");
    let equality = solver.try_eq(ite, integer).expect("equality");
    let negated = solver.try_not(condition).expect("not");
    let assertion = solver.try_and(equality, negated).expect("conjunction");
    solver.try_assert_term(assertion).expect("assert");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);

    let mut bad_condition = artifact.clone();
    let ite_node = bad_condition
        .terms
        .iter_mut()
        .find(|node| matches!(node.data, TermData::Ite(_, _, _)))
        .expect("ite node");
    let TermData::Ite(condition_id, _, _) = &mut ite_node.data else {
        unreachable!();
    };
    *condition_id = integer.0;
    assert_native_replay_rejected(&bad_condition);

    let mut bad_not = artifact.clone();
    let not_node = bad_not
        .terms
        .iter_mut()
        .find(|node| matches!(node.data, TermData::Not(_)))
        .expect("not node");
    let TermData::Not(inner) = &mut not_node.data else {
        unreachable!();
    };
    *inner = integer.0;
    assert_native_replay_rejected(&bad_not);

    let mut repeated_let_binding = artifact.clone();
    let root = repeated_let_binding
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.0)
        .expect("assertion root");
    root.data = TermData::Let(
        vec![
            ("repeated".to_string(), zero.0),
            ("repeated".to_string(), one.0),
        ],
        equality.0,
    );
    assert_native_replay_rejected(&repeated_let_binding);

    let mut valid_let = artifact.clone();
    let root = valid_let
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.0)
        .expect("assertion root");
    root.data = TermData::Let(
        vec![("replay_structure_condition".to_string(), condition.0)],
        negated.0,
    );
    let _ = Solver::replay_native_replay_artifact(&valid_let).expect("well-sorted let replay");

    let mut mismatched_let_sort = artifact.clone();
    let root = mismatched_let_sort
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.0)
        .expect("assertion root");
    root.data = TermData::Let(
        vec![("replay_structure_condition".to_string(), integer.0)],
        negated.0,
    );
    assert_native_replay_rejected(&mismatched_let_sort);

    let mut lying_sort = artifact;
    let zero_node = lying_sort
        .terms
        .iter_mut()
        .find(|node| node.id == zero.0)
        .expect("zero constant");
    zero_node.sort = Sort::Bool;
    assert_native_replay_rejected(&lying_sort);

    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let bound = solver.fresh_var("replay_quantified", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_ge(bound, zero).expect("body");
    let quantified = solver.try_forall(&[bound], body).expect("forall");
    solver.try_assert_term(quantified).expect("assert forall");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect("valid quantifier replay");

    let mut wrong_binder_sort = artifact.clone();
    let quantifier = wrong_binder_sort
        .terms
        .iter_mut()
        .find(|node| matches!(node.data, TermData::Forall(_, _, _)))
        .expect("quantifier");
    let TermData::Forall(vars, _, _) = &mut quantifier.data else {
        unreachable!();
    };
    vars[0].1 = Sort::Bool;
    assert_native_replay_rejected(&wrong_binder_sort);

    let mut non_boolean_body = artifact;
    let quantifier = non_boolean_body
        .terms
        .iter_mut()
        .find(|node| matches!(node.data, TermData::Forall(_, _, _)))
        .expect("quantifier");
    let TermData::Forall(_, body, _) = &mut quantifier.data else {
        unreachable!();
    };
    *body = bound.0;
    assert_native_replay_rejected(&non_boolean_body);
}

#[test]
fn native_replay_requires_each_trigger_to_contain_a_well_sorted_bound_variable() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let bound = solver.fresh_var("replay_trigger_bound", Sort::Int);
    let other = solver.fresh_var("replay_trigger_other", Sort::Int);
    let function = solver
        .try_declare_fun("replay_trigger_f", &[Sort::Int], Sort::Int)
        .expect("function");
    let bound_app = solver.try_apply(&function, &[bound]).expect("bound app");
    let other_app = solver.try_apply(&function, &[other]).expect("other app");
    let zero = solver.int_const(0);
    let body = solver.try_ge(bound_app, zero).expect("body");
    let quantified = solver
        .try_forall_with_triggers(&[bound], body, &[&[bound_app]])
        .expect("quantifier");
    solver
        .try_assert_term(quantified)
        .expect("assert quantifier");
    let other_root = solver.try_ge(other_app, zero).expect("other root");
    solver
        .try_assert_term(other_root)
        .expect("retain other app");
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect("valid trigger replay");

    let mut unbound_trigger = artifact;
    let quantifier = unbound_trigger
        .terms
        .iter_mut()
        .find(|node| matches!(node.data, TermData::Forall(_, _, _)))
        .expect("quantifier");
    let TermData::Forall(_, _, triggers) = &mut quantifier.data else {
        unreachable!();
    };
    triggers[0][0] = other_app.0;
    assert_native_replay_rejected(&unbound_trigger);
}

#[test]
fn native_replay_binder_scan_respects_nested_same_name_shadowing() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let outer_var = solver.fresh_var("replay_shadowed", Sort::Int);
    let outer_name = match solver.terms().get(outer_var.0) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("fresh variable should be a Var, got {other:?}"),
    };
    let inner_var = solver
        .terms_mut()
        .mk_fresh_named_var(outer_name.clone(), Sort::Bool);
    let inner = solver
        .terms_mut()
        .mk_forall(vec![(outer_name.clone(), Sort::Bool)], inner_var);
    let outer = Term(
        solver
            .terms_mut()
            .mk_forall(vec![(outer_name, Sort::Int)], inner),
    );
    solver
        .try_assert_term(outer)
        .expect("nested quantifier assertion");

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact)
        .expect("nested same-name binder should shadow the outer binder");
}

#[test]
fn native_replay_scans_many_bindings_against_a_shared_body_once() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let body_atoms: Vec<Term> = (0..512)
        .map(|index| solver.declare_const(&format!("replay_body_{index}"), Sort::Bool))
        .collect();
    let body = solver.try_and_many(&body_atoms).expect("wide Boolean body");
    let bound: Vec<Term> = (0..256)
        .map(|index| solver.fresh_var(&format!("replay_bound_{index}"), Sort::Int))
        .collect();
    let quantified = solver
        .try_forall(&bound, body)
        .expect("many-binder quantifier");
    solver
        .try_assert_term(quantified)
        .expect("quantified assertion");

    // A per-name traversal performs more than 100,000 node visits here even
    // though there are fewer than 1,000 distinct validation states. Replay
    // should use one binder-name map and one aggregate scan of the shared body.
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact)
        .expect("aggregate binder validation should remain within its envelope");
}

#[test]
fn native_replay_artifact_carries_checked_replay_proof_model_status() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let x_eq_one = solver.try_eq(x, one).expect("x = 1");
    solver
        .try_assert_named(x_eq_one, "verification-consumer-ensures")
        .expect("assert");

    let details = solver.check_sat_with_details();
    assert_eq!(*details.result.result(), SolveResult::Sat);

    let artifact = solver.export_native_replay_artifact(
        NativeReplayMetadata {
            consumer: Some("verification-consumer".to_string()),
            fixture_path: Some("tests/should_succeed/bitvectors/popcount.rs".to_string()),
            obligation_kind: Some("ensures".to_string()),
            ..Default::default()
        },
        Some(&details),
    );
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    let artifact = artifact.with_checked_replay(&replay);

    let checked = artifact.checked_replay.as_ref().expect("checked replay");
    assert_eq!(checked.original_result.as_deref(), Some("sat"));
    assert_eq!(checked.replay_result, "sat");
    assert!(checked.result_matches);
    assert_eq!(
        checked.original_proof_status.as_deref(),
        Some("not-applicable")
    );
    assert_eq!(checked.replay_proof_status, "not-applicable");
    assert!(checked.proof_status_matches);
    assert_eq!(
        checked.original_model_status.as_deref(),
        Some(checked.replay_model_status.as_str())
    );
    assert!(checked.model_status_matches);

    let json = artifact.to_json_value();
    assert_eq!(
        json["checked_replay"]["result_matches"].as_bool(),
        Some(true)
    );
    assert_eq!(
        json["checked_replay"]["replay_proof_status"].as_str(),
        Some("not-applicable")
    );
    assert!(json["checked_replay"]["replay_model_status"].is_string());

    let parsed =
        NativeReplayArtifact::from_json_str(&artifact.to_pretty_json()).expect("parse JSON");
    assert_eq!(parsed.checked_replay, artifact.checked_replay);
}

#[test]
fn native_replay_verification_consumer_hashmap_get_restore_bridge_replays_sat() {
    let artifact = NativeReplayArtifact::from_json_str(include_str!(
        "../../../tests/fixtures/verification_consumer_9185/hashmap_get_init_native_min.json"
    ))
    .expect("parse verification-consumer hashmap get native replay fixture");
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    assert_eq!(
        *replay.result.result(),
        SolveResult::Sat,
        "unknown_reason={:?} diagnostic={:?}",
        replay.unknown_reason,
        replay.unknown_diagnostic,
    );
}

#[test]
fn native_replay_artifact_carries_unknown_progress() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    solver.set_timeout(Some(Duration::ZERO));

    let artifact = solver.try_check_sat_with_native_replay(NativeReplayMetadata {
        consumer: Some("verification-consumer".to_string()),
        notes: Some("timeout preflight".to_string()),
        ..Default::default()
    });

    let solve = artifact.solve.as_ref().expect("solve summary");
    assert_eq!(solve.result, "unknown");
    assert_eq!(solve.unknown_reason.as_deref(), Some("timeout"));
    assert_eq!(solve.unknown_phase.as_deref(), Some("search-control"));
    let progress = solve.unknown_progress.as_ref().expect("unknown progress");
    assert_eq!(progress.reason, "timeout");
    assert_eq!(
        progress.responsible_phase.as_deref(),
        Some("search-control")
    );
    assert_eq!(progress.wall_time_budget_ms, Some(0));
    assert!(artifact.to_pretty_json().contains("unknown_progress"));
}

#[test]
fn native_replay_artifact_records_scopes_and_duplicate_assertion_names() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_ge_zero, "scoped-shadow")
        .expect("scoped assert");
    solver.try_pop().expect("pop");
    solver
        .try_assert_named(x_ge_zero, "base-lower-bound-duplicate")
        .expect("duplicate base assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let json = artifact.to_pretty_json();

    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::Push)));
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::Pop)));
    assert!(json.contains("\"event\": \"push\""));
    assert!(json.contains("\"event\": \"pop\""));
    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[0].name.as_deref(),
        Some("base-lower-bound")
    );
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("base-lower-bound-duplicate")
    );

    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse scoped replay JSON");
    assert_eq!(parsed.events.len(), artifact.events.len());
    let replay = Solver::replay_native_replay_artifact(&parsed).expect("scoped replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_artifact_preserves_active_same_term_scope_depths() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_ge_zero, "scoped-lower-bound")
        .expect("scoped assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));

    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[0].name.as_deref(),
        Some("base-lower-bound")
    );
    assert_eq!(artifact.assertions[0].scope_depth, 0);
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("scoped-lower-bound")
    );
    assert_eq!(artifact.assertions[1].scope_depth, 1);

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("active scoped replay");
    assert_eq!(replay.result.result(), details.result.result());

    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_replays_active_scoped_assertions_from_json() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");
    let x_lt_zero = solver.try_lt(x, zero).expect("x < 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_lt_zero, "scoped-upper-bound")
        .expect("scoped assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("scoped-upper-bound")
    );
    assert_eq!(artifact.assertions[1].scope_depth, 1);

    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_replays_check_sat_assuming_event() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");
    let x_lt_zero = solver.try_lt(x, zero).expect("x < 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    let details = solver.check_sat_assuming_with_details(&[x_lt_zero]);
    assert!(details.solve.result.result().is_unsat());

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details.solve));
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::CheckSatAssuming { .. })));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("assumption replay");
    assert_eq!(replay.result.result(), details.solve.result.result());

    let parsed =
        NativeReplayArtifact::from_json_str(&artifact.to_pretty_json()).expect("parse JSON");
    let replay_from_json =
        Solver::replay_native_replay_artifact(&parsed).expect("assumption replay from JSON");
    assert_eq!(
        replay_from_json.result.result(),
        details.solve.result.result()
    );
}

#[test]
fn native_replay_preserves_datatype_semantics_in_memory_and_json() {
    let mut solver = Solver::try_new(Logic::Uf).expect("solver");
    let color = DatatypeSort::new(
        "ReplayColor",
        vec![
            DatatypeConstructor::unit("ReplayRed"),
            DatatypeConstructor::unit("ReplayBlue"),
        ],
    );
    solver
        .try_declare_datatype(&color)
        .expect("declare datatype");
    let value = solver.declare_const("replay_color_value", Sort::Datatype(color.clone()));
    let red = solver.datatype_constructor(&color, "ReplayRed", &[]);
    let blue = solver.datatype_constructor(&color, "ReplayBlue", &[]);
    let value_is_red = solver.try_eq(value, red).expect("value = red");
    let value_is_blue = solver.try_eq(value, blue).expect("value = blue");
    solver.try_assert_term(value_is_red).expect("assert red");
    solver.try_assert_term(value_is_blue).expect("assert blue");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact.events.iter().any(|event| matches!(
        &event.kind,
        NativeReplayEventKind::DeclareDatatype { datatype } if datatype == &color
    )));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("datatype replay");
    assert!(replay.result.result().is_unsat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("datatype JSON replay");
    assert!(replay_from_json.result.result().is_unsat());
}

#[test]
fn native_replay_exports_only_active_term_dependencies() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let active = solver.declare_const("active", Sort::Int);
    let dead = solver.declare_const("dead", Sort::Int);
    let one = solver.int_const(1);
    let dead_sum = solver.try_add(dead, one).expect("dead expression");
    let active_eq_one = solver.try_eq(active, one).expect("active = 1");
    solver
        .try_assert_term(active_eq_one)
        .expect("assert active");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact.terms.iter().all(|node| node.id != dead.0));
    assert!(artifact.terms.iter().all(|node| node.id != dead_sum.0));
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| declaration.term != dead.0));

    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("dependency-sliced JSON replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_distinguishes_fresh_vars_shadowing_nullary_constructors() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let color = DatatypeSort::new(
        "ShadowColor",
        vec![
            DatatypeConstructor::unit("ShadowRed"),
            DatatypeConstructor::unit("ShadowBlue"),
        ],
    );
    solver.try_declare_datatype(&color).expect("datatype");
    let red = solver.datatype_constructor(&color, "ShadowRed", &[]);
    let shadow = solver.declare_const_with_fresh_identity(
        "ShadowRed",
        "!ay.test-shadow-red",
        Sort::Datatype(color.clone()),
    );
    let shadow_ne_red = solver
        .try_eq(shadow, red)
        .and_then(|equal| solver.try_not(equal))
        .expect("shadow != red");
    solver.try_assert_term(shadow_ne_red).expect("assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let shadow_node = artifact
        .terms
        .iter()
        .find(|node| node.id == shadow.0)
        .expect("shadow node");
    assert!(!shadow_node.is_datatype_constructor);
    let red_node = artifact
        .terms
        .iter()
        .find(|node| node.id == red.0)
        .expect("constructor node");
    assert!(red_node.is_datatype_constructor);

    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("shadowing replay");
    assert!(
        replay.result.result().is_sat(),
        "replay result={:?} unknown={:?} executor={:?}",
        replay.result.result(),
        replay.unknown_reason,
        replay.executor_error
    );
}

#[test]
fn native_replay_structural_sorts_round_trip_without_kind_loss() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let char_value = solver.declare_const("char_value", Sort::Char);
    let finite_sort = Sort::FiniteDomain("FiniteFive".to_string(), 5);
    let finite_value = solver.declare_const("finite_value", finite_sort.clone());
    let type_var_sort = Sort::TypeVar("TypeAlpha".to_string());
    let type_left = solver.declare_const("type_left", type_var_sort.clone());
    let type_right = solver.declare_const("type_right", type_var_sort.clone());
    let zero = solver.int_const(0);
    let char_nonnegative = solver.try_ge(char_value, zero).expect("char >= 0");
    let finite_nonnegative = solver.try_ge(finite_value, zero).expect("finite >= 0");
    let types_equal = solver
        .try_eq(type_left, type_right)
        .expect("type vars equal");
    solver
        .try_assert_term(char_nonnegative)
        .expect("assert char");
    solver
        .try_assert_term(finite_nonnegative)
        .expect("assert finite");
    solver
        .try_assert_term(types_equal)
        .expect("assert type var");

    let nested = DatatypeSort::new(
        "StructuralBox",
        vec![DatatypeConstructor::new(
            "StructuralBoxMk",
            vec![DatatypeField::new("structural_char", Sort::Char)],
        )],
    );
    solver
        .try_declare_datatype(&nested)
        .expect("nested datatype");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let parsed = NativeReplayArtifact::from_json_str(&artifact.to_pretty_json())
        .expect("parse structural sorts");
    for expected in [Sort::Char, finite_sort, type_var_sort] {
        assert!(parsed
            .declarations
            .iter()
            .any(|declaration| declaration.sort == expected));
    }
    assert!(parsed.events.iter().any(|event| matches!(
        &event.kind,
        NativeReplayEventKind::DeclareDatatype { datatype } if datatype == &nested
    )));
    let replay = Solver::replay_native_replay_artifact(&parsed).expect("structural sort replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_u128_json_is_lossless_above_u64() {
    let solver = Solver::try_new(Logic::QfLia).expect("solver");
    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let large = u128::from(u64::MAX) + 42;
    artifact.created_unix_ms = large;
    artifact.timeout_ms = Some(large + 1);

    let json = artifact.to_pretty_json();
    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse large u128 values");
    assert_eq!(parsed.created_unix_ms, large);
    assert_eq!(parsed.timeout_ms, Some(large + 1));
}

#[test]
fn native_replay_keeps_functions_referenced_by_as_array_and_array_map() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver
        .try_declare_fun("replay_array_function", &[Sort::Int], Sort::Int)
        .expect("declare mapped function");
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let as_array = solver.as_array("replay_array_function", array_sort.clone());
    let source = solver.declare_const("replay_source_array", array_sort.clone());
    let mapped = solver.array_map("replay_array_function", &[source], array_sort.clone());
    let zero = solver.int_const(0);
    let as_array_value = solver.try_select(as_array, zero).expect("select as-array");
    let mapped_value = solver.try_select(mapped, zero).expect("select map");
    let values_equal = solver
        .try_eq(as_array_value, mapped_value)
        .expect("array values equal");
    solver.try_assert_term(values_equal).expect("assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact
        .function_declarations
        .iter()
        .any(|declaration| declaration.name == "replay_array_function"));
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("higher-order array replay");
    assert_eq!(replay.result.result(), details.result.result());
}
