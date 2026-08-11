// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay artifact tests for downstream reducer handoff.

use std::time::Duration;

use crate::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, NativeReplayArtifact,
    NativeReplayEventKind, NativeReplayMetadata, NativeReplaySolverIdentity,
    NativeReplaySymbolKind, ProofAcceptanceMode, SolveResult, Solver, SolverError, Sort,
    StrictProofVerdict, Term,
};
use ay_core::term::{Constant, Symbol, TermData};
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

fn boolean_sat_native_replay_artifact() -> NativeReplayArtifact {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let p = solver.declare_const("native_replay_evidence_p", Sort::Bool);
    solver.assert_term(p);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat());
    assert!(
        details.result.was_model_validated() && details.verification.sat_model_validated,
        "evidence test requires validated source SAT evidence"
    );
    solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details))
}

fn native_replay_evidence_identity(artifact: &NativeReplayArtifact) -> NativeReplaySolverIdentity {
    NativeReplaySolverIdentity::current_for_engine(
        artifact.selected_route.as_deref().unwrap_or("native-api"),
    )
    .with_solver_binary_sha256("ab".repeat(32))
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
    assert!(replay.verification.unsat_proof_strictly_verified);
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

#[cfg(feature = "proof-checker")]
#[test]
fn native_replay_with_checked_proof_returns_the_same_strict_artifact() {
    let artifact = boolean_unsat_native_replay_artifact();
    let (replay, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&artifact, Duration::from_secs(5))
            .expect("strict replay and retained proof artifact");
    let proof = proof.expect("accepted UNSAT replay must return its proof artifact");

    assert!(replay.result.is_unsat());
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("returned artifact must carry strict consumer authority");
    let strict_quality = match &proof.strict_verdict {
        StrictProofVerdict::Verified(quality) => quality,
        StrictProofVerdict::Rejected(reason) => {
            panic!("strict replay returned a rejected proof artifact: {reason}")
        }
    };
    assert_eq!(strict_quality.trust_count, 0);
    assert_eq!(strict_quality.hole_count, 0);
    assert_eq!(
        Some(u64::from(strict_quality.total_steps)),
        replay.statistics.get_int("proof_checker_total_steps"),
        "SolveDetails and UnsatProofArtifact must describe the same replay"
    );
    assert!(proof.alethe.contains("(cl)"));
    assert!(!proof.alethe.contains(":rule trust"));
    assert!(!proof.alethe.contains(":rule hole"));
}

#[cfg(feature = "proof-checker")]
#[test]
fn native_replay_with_proofs_checks_lia_equality_against_negated_bound() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict proof checking");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let x_eq_one = solver.try_eq(x, one).expect("x = 1");
    let x_gt_zero = solver.try_gt(x, zero).expect("x > 0");
    let not_x_gt_zero = solver.try_not(x_gt_zero).expect("not (x > 0)");
    solver
        .try_assert_named(x_eq_one, "__verification_consumer_precondition_0")
        .expect("assert x = 1");
    solver
        .try_assert_term(not_x_gt_zero)
        .expect("assert not (x > 0)");

    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat());
    let direct_proof = solver
        .export_last_unsat_artifact()
        .expect("named native assertion must retain its checked proof");
    assert!(matches!(
        direct_proof.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.trust_count == 0
    ));
    assert!(!direct_proof.alethe.contains(":rule trust"));
    assert!(
        !direct_proof.farkas_certificates.is_empty(),
        "the LIA conflict must be discharged by a checked Farkas certificate"
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_eq!(
        artifact.assertions[0].name.as_deref(),
        Some("__verification_consumer_precondition_0"),
        "the proof fix must not erase native unsat-core attribution"
    );
    let replay =
        Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
            .expect("the exact LIA contradiction must have strict proof authority");

    assert!(replay.result.is_unsat());
    assert!(replay.verification_level.has_proof_checking());
    assert!(replay.verification.unsat_proof_available);
    assert_eq!(replay.verification.unsat_proof_checker_failures, 0);
    assert!(replay.statistics.proof_complete);
    assert_eq!(replay.statistics.get_int("proof_trust"), Some(0));
    assert_eq!(
        replay
            .statistics
            .get_int("proof_checker_skipped_hole_steps"),
        Some(0)
    );
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
    // The mandatory publication firewall may check an internal refutation and
    // retain its zero-failure counter even when this API did not request or
    // expose a proof.  Authority is carried by the two assertions above, not
    // by absence of diagnostic counters.
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
        .find(|node| node.id == p.id())
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

    let mut duplicate_core_name = artifact.clone();
    duplicate_core_name.declarations[1].core_name =
        duplicate_core_name.declarations[0].core_name.clone();
    assert_native_replay_rejected(&duplicate_core_name);

    let mut duplicate_identity_core = artifact.clone();
    duplicate_identity_core.symbol_identities[1].core_name = duplicate_identity_core
        .symbol_identities[0]
        .core_name
        .clone();
    assert_native_replay_rejected(&duplicate_identity_core);

    let mut wrong_identity_kind = artifact.clone();
    wrong_identity_kind.symbol_identities[0].kind = NativeReplaySymbolKind::Theory;
    assert_native_replay_rejected(&wrong_identity_kind);

    let mut wrong_identity_range = artifact.clone();
    wrong_identity_range.symbol_identities[0].engine_range = Sort::Bool;
    assert_native_replay_rejected(&wrong_identity_range);

    let mut wrong_identity_api_range = artifact.clone();
    wrong_identity_api_range.symbol_identities[0].api_range = Sort::Char;
    assert_native_replay_rejected(&wrong_identity_api_range);

    let mut arbitrary_private_core = artifact.clone();
    arbitrary_private_core.declarations[0].core_name = "replay_private_forged".to_string();
    assert_native_replay_rejected(&arbitrary_private_core);

    // An allocator-shaped spelling alone is not authority: this ordinary
    // public name has no canonical-theory collision requiring a private core.
    let mut forged_allocator_private_core = artifact.clone();
    let declaration = &mut forged_allocator_private_core.declarations[0];
    declaration.core_name = "__ay_overload_999999".to_string();
    let declaration = declaration.clone();
    let node = forged_allocator_private_core
        .terms
        .iter_mut()
        .find(|node| node.id == declaration.term)
        .expect("declared node");
    let TermData::Var(name, _) = &mut node.data else {
        unreachable!();
    };
    *name = declaration.core_name;
    assert_native_replay_rejected(&forged_allocator_private_core);

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
    declaration.term = zero.id();
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
    args[0] = boolean.id();
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
fn native_replay_preserves_builtin_colliding_uf_identity() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let left = solver.int_const(1);
    let right = solver.int_const(2);
    let user_equality = solver
        .try_declare_fun("=", &[Sort::Int, Sort::Int], Sort::Bool)
        .expect("declare user equality");
    let application = solver
        .try_apply(&user_equality, &[left, right])
        .expect("apply user equality");
    solver.try_assert_term(application).expect("assert user UF");

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    assert!(artifact
        .function_declarations
        .iter()
        .any(|declaration| declaration.name == "="));
    assert!(artifact.terms.iter().any(|node| {
        matches!(
            &node.data,
            TermData::App(Symbol::Named(name), args)
                if name == user_equality.core_name() && name != "=" && args.len() == 2
        )
    }));
    let _replayed = Solver::replay_native_replay_artifact(&artifact)
        .expect("private native declaration identity must replay");
}

#[test]
fn native_replay_rejects_legacy_canonical_core_hijack() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let user_equality = solver
        .try_declare_fun("=", &[Sort::Int, Sort::Int], Sort::Bool)
        .expect("declare user equality");
    assert_ne!(user_equality.core_name(), "=");

    // Construct the builtin application without constant folding so the
    // artifact contains the raw canonical `=` head. The user UF is unused but
    // legacy surface-based dependency capture retained its declaration.
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let builtin_equality_id = solver.terms_mut().mk_app(
        Symbol::Named("=".to_string()),
        vec![zero.id(), one.id()],
        Sort::Bool,
    );
    let builtin_equality = solver.wrap_term(builtin_equality_id);
    solver.try_assert_term(builtin_equality).expect("assert");
    assert!(solver.check_sat().is_unsat());

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let declaration = artifact
        .function_declarations
        .iter()
        .find(|declaration| declaration.name == "=")
        .expect("legacy surface dependency retains declaration");
    assert_ne!(declaration.core_name, "=");
    assert!(artifact.terms.iter().any(|node| {
        matches!(&node.data, TermData::App(Symbol::Named(name), _) if name == "=")
    }));
    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("authenticated private UF must not capture builtin equality");
    assert!(replay.result.result().is_unsat());

    let mut legacy_json = artifact.to_json_value();
    let object = legacy_json.as_object_mut().expect("artifact object");
    object.remove("symbol_identities");
    for declaration in object["function_declarations"]
        .as_array_mut()
        .expect("function declarations")
    {
        if declaration["name"].as_str() == Some("=") {
            declaration
                .as_object_mut()
                .expect("function declaration")
                .remove("core_name");
        }
    }
    let legacy = NativeReplayArtifact::from_json_value(&legacy_json).expect("legacy artifact");
    assert_native_replay_rejected(&legacy);
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
    *condition_id = integer.id();
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
    *inner = integer.id();
    assert_native_replay_rejected(&bad_not);

    let mut repeated_let_binding = artifact.clone();
    let root = repeated_let_binding
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.id())
        .expect("assertion root");
    root.data = TermData::Let(
        vec![
            ("repeated".to_string(), zero.id()),
            ("repeated".to_string(), one.id()),
        ],
        equality.id(),
    );
    assert_native_replay_rejected(&repeated_let_binding);

    let mut valid_let = artifact.clone();
    let root = valid_let
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.id())
        .expect("assertion root");
    root.data = TermData::Let(
        vec![("replay_structure_condition".to_string(), condition.id())],
        negated.id(),
    );
    let _ = Solver::replay_native_replay_artifact(&valid_let).expect("well-sorted let replay");

    let mut mismatched_let_sort = artifact.clone();
    let root = mismatched_let_sort
        .terms
        .iter_mut()
        .find(|node| node.id == assertion.id())
        .expect("assertion root");
    root.data = TermData::Let(
        vec![("replay_structure_condition".to_string(), integer.id())],
        negated.id(),
    );
    assert_native_replay_rejected(&mismatched_let_sort);

    let mut lying_sort = artifact;
    let zero_node = lying_sort
        .terms
        .iter_mut()
        .find(|node| node.id == zero.id())
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
    *body = bound.id();
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
    triggers[0][0] = other_app.id();
    assert_native_replay_rejected(&unbound_trigger);
}

#[test]
fn native_replay_binder_scan_respects_nested_same_name_shadowing() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let outer_var = solver.fresh_var("replay_shadowed", Sort::Int);
    let outer_name = match solver.terms().get(outer_var.id()) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("fresh variable should be a Var, got {other:?}"),
    };
    let inner_var = solver
        .terms_mut()
        .mk_fresh_named_var(outer_name.clone(), Sort::Bool);
    let inner = solver
        .terms_mut()
        .mk_forall(vec![(outer_name.clone(), Sort::Bool)], inner_var);
    let outer_id = solver
        .terms_mut()
        .mk_forall(vec![(outer_name, Sort::Int)], inner);
    let outer = solver.wrap_term(outer_id);
    solver
        .try_assert_term(outer)
        .expect("nested quantifier assertion");

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact)
        .expect("nested same-name binder should shadow the outer binder");
}

#[test]
fn native_replay_alpha_renames_binders_that_spell_declaration_core_identities() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    // `div` is declarable through the native API, but must receive an
    // allocator-private core identity because the public spelling is also a
    // theory operator.
    let declared = solver.declare_const("div", Sort::Int);
    let bound = solver.fresh_var("replay_capture_bound", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_ge(bound, zero).expect("bound >= 0");
    let quantified = solver.try_forall(&[bound], body).expect("forall");
    let declared_eq_zero = solver.try_eq(declared, zero).expect("div = 0");
    let assertion = solver
        .try_and(quantified, declared_eq_zero)
        .expect("retain declaration and quantifier");
    solver.try_assert_term(assertion).expect("assert");

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let core_name = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == declared.id())
        .expect("div declaration")
        .core_name
        .clone();
    assert!(core_name.starts_with("__ay_overload_"));

    let mut quantified_capture = artifact.clone();
    let quantifier = quantified_capture
        .terms
        .iter_mut()
        .find(|node| node.id == quantified.id())
        .expect("quantifier node");
    let TermData::Forall(vars, _, _) = &mut quantifier.data else {
        unreachable!();
    };
    vars[0].0.clone_from(&core_name);
    let _ = Solver::replay_native_replay_artifact(&quantified_capture)
        .expect("quantifier binder is alpha-renamed away from the live declaration core");

    let mut let_capture = artifact;
    let quantifier = let_capture
        .terms
        .iter_mut()
        .find(|node| node.id == quantified.id())
        .expect("quantifier node");
    let TermData::Forall(_, quantified_body, _) = quantifier.data.clone() else {
        unreachable!();
    };
    quantifier.data = TermData::Let(vec![(core_name, zero.id())], quantified_body);
    let _ = Solver::replay_native_replay_artifact(&let_capture)
        .expect("let binder is alpha-renamed away from the live declaration core");
}

#[test]
fn native_replay_alpha_renames_binder_away_from_a_rebuilt_public_core_identity() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let declared = solver.declare_const("replay_rebuilt_capture", Sort::Int);
    let bound = solver.fresh_var("replay_rebuilt_bound", Sort::Int);
    let zero = solver.int_const(0);
    // The source binder is intentionally unused. After the artifact's old
    // private declaration core is remapped to the public replay core, changing
    // the binder to that public name would capture this exact free declaration
    // and turn a satisfiable formula into `forall x. x >= 0`.
    let body = solver.try_ge(declared, zero).expect("declared >= 0");
    let quantified = solver.try_forall(&[bound], body).expect("forall");
    let declared_eq_zero = solver.try_eq(declared, zero).expect("declared = 0");
    let assertion = solver
        .try_and(quantified, declared_eq_zero)
        .expect("retain declaration and quantifier");
    solver.try_assert_term(assertion).expect("assert");

    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let public_core = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == declared.id())
        .expect("ordinary declaration")
        .core_name
        .clone();
    assert_eq!(public_core, "replay_rebuilt_capture");

    // Model a valid artifact captured in a term store where this declaration
    // was a later incarnation: its exported core is private, while replay in a
    // fresh context rebuilds the same surface declaration at the public core.
    let exported_private_core = "__ay_overload_999999".to_string();
    let declaration = artifact
        .declarations
        .iter_mut()
        .find(|declaration| declaration.term == declared.id())
        .expect("ordinary declaration");
    declaration.core_name.clone_from(&exported_private_core);
    let declared_node = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == declared.id())
        .expect("declared node");
    let TermData::Var(name, _) = &mut declared_node.data else {
        unreachable!();
    };
    name.clone_from(&exported_private_core);
    let identity = artifact
        .symbol_identities
        .iter_mut()
        .find(|identity| {
            identity.surface_name == "replay_rebuilt_capture"
                && identity.kind == NativeReplaySymbolKind::Uninterpreted
                && identity.api_domain.is_empty()
        })
        .expect("ordinary identity row");
    identity.core_name = exported_private_core;

    let quantifier = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == quantified.id())
        .expect("quantifier node");
    let TermData::Forall(vars, _, _) = &mut quantifier.data else {
        unreachable!();
    };
    vars[0].0 = public_core;
    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("private-to-public declaration remap must not capture the binder");
    assert!(
        replay.result.is_sat(),
        "the declaration remains free and fixed to zero; accidental capture would make forall x. x >= 0"
    );
}

#[test]
fn native_replay_preserves_a_declared_constant_used_as_a_bound_identity() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let bound = solver.declare_const("replay_declared_bound", Sort::Bool);
    let quantified = solver.try_forall(&[bound], bound).expect("forall");
    solver
        .try_assert_term(quantified)
        .expect("quantified assertion");

    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect(
        "the replay must contextually alpha-rename the captured declaration TermId instead of aliasing its live declaration",
    );
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
fn native_replay_evidence_requires_the_strict_typed_workflow() {
    let artifact = boolean_sat_native_replay_artifact();
    let identity = native_replay_evidence_identity(&artifact);

    // Even a real replay result attached through the diagnostic convenience
    // API cannot authorize compiler admission.
    let diagnostic_replay = Solver::replay_native_replay_artifact(&artifact).expect("replay");
    let diagnostic = artifact.clone().with_checked_replay(&diagnostic_replay);
    let diagnostic_manifest = diagnostic.evidence_manifest_with_solver_identity(identity.clone());
    assert!(!diagnostic_manifest.admitted());
    assert!(diagnostic_manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("authoritative replay token is missing")));
    let mut forged_diagnostic_manifest = diagnostic_manifest;
    forged_diagnostic_manifest
        .admission_rejection_reasons
        .clear();
    assert!(
        !forged_diagnostic_manifest.admitted(),
        "clearing public diagnostics must not mint admission authority"
    );

    let sealed = Solver::replay_native_replay_artifact_for_evidence(
        artifact,
        identity.clone(),
        Duration::from_secs(5),
    )
    .expect("strict evidence replay");
    assert_eq!(sealed.timeout_ms, Some(5_000));
    let manifest = sealed.evidence_manifest();
    assert!(
        manifest.admitted(),
        "typed evidence should admit: {:?}",
        manifest.admission_rejection_reasons
    );
    assert_eq!(manifest.solver_identity, identity);
    assert_eq!(manifest.checked_result, "checked-sat");

    let mut mutated_body = manifest.clone();
    mutated_body.checked_result = "checked-unsat".to_string();
    assert!(
        !mutated_body.admitted(),
        "public manifest-body mutation must invalidate admission"
    );
    let mut mutated_digest = manifest;
    mutated_digest.manifest_sha256 = "00".repeat(32);
    assert!(
        !mutated_digest.admitted(),
        "public manifest digest mutation must invalidate admission"
    );
}

#[test]
fn native_replay_evidence_stale_details_and_json_summaries_are_non_authoritative() {
    let artifact = boolean_sat_native_replay_artifact();
    let identity = native_replay_evidence_identity(&artifact);

    let mut unrelated_solver = Solver::try_new(Logic::QfUf).expect("unrelated solver");
    let q = unrelated_solver.declare_const("unrelated_replay_q", Sort::Bool);
    unrelated_solver.assert_term(q);
    let unrelated_details = unrelated_solver.check_sat_with_details();
    assert!(unrelated_details.result.is_sat());

    let stale = artifact.clone().with_checked_replay(&unrelated_details);
    assert!(!stale
        .evidence_manifest_with_solver_identity(identity.clone())
        .admitted());

    let sealed = Solver::replay_native_replay_artifact_for_evidence(
        artifact,
        identity.clone(),
        Duration::from_secs(5),
    )
    .expect("strict evidence replay");
    let parsed = NativeReplayArtifact::from_json_str(&sealed.to_pretty_json())
        .expect("parse diagnostic evidence JSON");
    assert_eq!(parsed.checked_replay, sealed.checked_replay);
    let parsed_manifest = parsed.evidence_manifest_with_solver_identity(identity);
    assert!(!parsed_manifest.admitted());
    assert!(parsed_manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("authoritative replay token is missing")));
}

#[test]
fn native_replay_evidence_token_rejects_post_check_mutation() {
    let artifact = boolean_sat_native_replay_artifact();
    let identity = native_replay_evidence_identity(&artifact);
    let sealed = Solver::replay_native_replay_artifact_for_evidence(
        artifact,
        identity,
        Duration::from_secs(5),
    )
    .expect("strict evidence replay");

    let mut metadata_mutation = sealed.clone();
    metadata_mutation.metadata.notes = Some("changed after strict replay".to_string());
    let metadata_manifest = metadata_mutation.evidence_manifest();
    assert!(!metadata_manifest.admitted());
    assert!(metadata_manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("full-artifact binding does not match")));

    let mut summary_mutation = sealed;
    summary_mutation
        .checked_replay
        .as_mut()
        .expect("sealed summary")
        .replay_model_status = "missing".to_string();
    let summary_manifest = summary_mutation.evidence_manifest();
    assert!(!summary_manifest.admitted());
    assert!(summary_manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("checked-summary binding does not match")));
}

#[test]
fn native_replay_evidence_rejects_noncurrent_solver_identity() {
    let artifact = boolean_sat_native_replay_artifact();
    let identity = native_replay_evidence_identity(&artifact);

    let mut wrong_engine = identity.clone();
    wrong_engine.engine.push_str(":forged");
    assert!(matches!(
        Solver::replay_native_replay_artifact_for_evidence(
            artifact.clone(),
            wrong_engine,
            Duration::from_secs(5),
        ),
        Err(SolverError::InvalidArgument {
            operation: "native_replay_for_evidence",
            ..
        })
    ));

    let mut wrong_revision = identity.clone();
    wrong_revision.ay_revision.push_str("-stale");
    assert!(Solver::replay_native_replay_artifact_for_evidence(
        artifact.clone(),
        wrong_revision,
        Duration::from_secs(5),
    )
    .is_err());

    let mut wrong_version = identity.clone();
    wrong_version.ay_version.push_str("-stale");
    assert!(Solver::replay_native_replay_artifact_for_evidence(
        artifact.clone(),
        wrong_version,
        Duration::from_secs(5),
    )
    .is_err());

    let mut malformed_hash = identity.clone();
    malformed_hash.solver_binary_sha256 = Some("not-a-sha256".to_string());
    assert!(Solver::replay_native_replay_artifact_for_evidence(
        artifact.clone(),
        malformed_hash,
        Duration::from_secs(5),
    )
    .is_err());

    let sealed = Solver::replay_native_replay_artifact_for_evidence(
        artifact,
        identity.clone(),
        Duration::from_secs(5),
    )
    .expect("strict evidence replay");
    let mut substituted_identity = identity;
    substituted_identity.solver_binary_sha256 = Some("cd".repeat(32));
    let manifest = sealed.evidence_manifest_with_solver_identity(substituted_identity);
    assert!(!manifest.admitted());
    assert!(manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("solver identity binding does not match")));
}

#[test]
fn native_replay_evidence_rejects_legacy_identity_tables() {
    let mut artifact = boolean_sat_native_replay_artifact();
    let identity = native_replay_evidence_identity(&artifact);
    artifact.symbol_identities.clear();

    assert!(matches!(
        Solver::replay_native_replay_artifact_for_evidence(
            artifact.clone(),
            identity.clone(),
            Duration::from_secs(5),
        ),
        Err(SolverError::InvalidArgument {
            operation: "native_replay_for_evidence",
            ..
        })
    ));

    // Legacy public-name replay remains available for diagnostics, but its
    // caller-attached summary cannot be promoted to compiler authority.
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("diagnostic replay");
    let diagnostic = artifact.with_checked_replay(&replay);
    let manifest = diagnostic.evidence_manifest_with_solver_identity(identity);
    assert!(!manifest.admitted());
    assert!(manifest
        .admission_rejection_reasons
        .iter()
        .any(|reason| reason.contains("authenticated symbol identity table")));
}

#[test]
fn native_replay_verification_consumer_hashmap_get_restore_bridge_fails_closed() {
    let artifact = NativeReplayArtifact::from_json_str(include_str!(
        "../../../tests/fixtures/verification_consumer_9185/hashmap_get_init_native_min.json"
    ))
    .expect("parse verification-consumer hashmap get native replay fixture");
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    assert!(
        replay.result.is_unknown(),
        "an unconfirmed quantified model must not be published as SAT: {replay:?}"
    );
    assert_eq!(
        replay.unknown_reason,
        Some(crate::UnknownReason::Incomplete)
    );
    assert!(replay
        .unknown_diagnostic
        .as_ref()
        .is_some_and(|diagnostic| {
            diagnostic
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("failing closed"))
        }));
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
fn native_replay_remaps_interleaved_private_function_identities() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");

    // All three declarations collide with canonical arithmetic operator
    // spellings. The middle constant is unreachable and therefore sliced from
    // the artifact, so the retained function receives a different allocator
    // suffix in the replay context even though declaration order is preserved.
    let div = solver.declare_const("div", Sort::Int);
    let _unused_allocator_slot = solver.declare_const("abs", Sort::Int);
    let modulo = solver
        .try_declare_fun("mod", &[Sort::Int], Sort::Int)
        .expect("declare colliding function");
    let applied = solver.try_apply(&modulo, &[div]).expect("apply mod");

    // Exercise identities embedded in higher-order array wrappers as well as
    // an ordinary Named application head.
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let source = solver.declare_const("replay_private_source", array_sort.clone());
    let as_array = solver.as_array(modulo.core_name(), array_sort.clone());
    let mapped = solver.array_map(modulo.core_name(), &[source], array_sort);
    // Select eagerly rewrites both wrappers to direct applications, so retain
    // the wrapper nodes themselves through an array equality and its negation.
    // This is propositionally UNSAT and therefore does not depend on the
    // intentionally incomplete model validation for function-backed arrays.
    // Keep the direct Named application rooted by a separate scalar assertion.
    let wrappers_equal = solver.try_eq(as_array, mapped).expect("wrapper equality");
    let wrappers_not_equal = solver
        .try_not(wrappers_equal)
        .expect("negated wrapper equality");
    let zero = solver.int_const(0);
    let applied_is_zero = solver.try_eq(applied, zero).expect("application value");
    solver.try_assert_term(wrappers_equal).expect("assert");
    solver.try_assert_term(wrappers_not_equal).expect("assert");
    solver.try_assert_term(applied_is_zero).expect("assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let div_core = &artifact
        .declarations
        .iter()
        .find(|declaration| declaration.name == "div")
        .expect("div declaration")
        .core_name;
    let mod_declaration = artifact
        .function_declarations
        .iter()
        .find(|declaration| declaration.name == "mod")
        .expect("mod declaration");
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| declaration.name != "abs"));
    assert!(div_core.starts_with("__ay_overload_"));
    assert!(mod_declaration.core_name.starts_with("__ay_overload_"));
    assert_ne!(div_core, &mod_declaration.core_name);
    assert!(artifact.terms.iter().any(|node| {
        matches!(
            &node.data,
            TermData::App(Symbol::Named(name), _)
                if name == &format!("as-array[{}]", mod_declaration.core_name)
        )
    }));
    assert!(artifact.terms.iter().any(|node| {
        matches!(
            &node.data,
            TermData::App(Symbol::Named(name), _)
                if name == &format!("map[{}]", mod_declaration.core_name)
        )
    }));

    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("interleaved private function replay");
    assert!(replay.result.result().is_unsat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("interleaved private function JSON replay");
    assert!(replay_from_json.result.result().is_unsat());
}

#[test]
fn native_replay_remaps_interleaved_private_datatype_member_identities() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");

    // A constant and function intentionally use the same public spellings as
    // later datatype constructors. Replaying the datatype first would make
    // the earlier overloads impossible to reconstruct, so declaration-event
    // order is semantic here, independently of allocator suffix remapping.
    let modulo_value = solver.declare_const("mod", Sort::Int);
    let absolute = solver
        .try_declare_fun("abs", &[Sort::Bool], Sort::Int)
        .expect("declare member-surface overload");
    let operation = DatatypeSort::new(
        "ReplayPrivateOperation",
        vec![
            DatatypeConstructor::unit("mod"),
            DatatypeConstructor::new("abs", vec![DatatypeField::new("min", Sort::Int)]),
        ],
    );
    solver
        .try_declare_datatype(&operation)
        .expect("declare colliding datatype");
    let unit = solver.datatype_constructor(&operation, "mod", &[]);
    let boxed = solver.datatype_constructor(&operation, "abs", &[modulo_value]);
    let selected = solver.datatype_selector("min", boxed, Sort::Int);
    let unit_is_mod = solver.datatype_tester("mod", unit);
    let boxed_is_abs = solver.datatype_tester("abs", boxed);
    let selected_is_value = solver.try_eq(selected, modulo_value).expect("selector law");
    let true_value = solver.bool_const(true);
    let absolute_true = solver
        .try_apply(&absolute, &[true_value])
        .expect("apply member-surface overload");
    let zero = solver.int_const(0);
    let absolute_true_is_zero = solver.try_eq(absolute_true, zero).expect("overload value");
    let unit_is_not_mod = solver.try_not(unit_is_mod).expect("negated tester law");
    let boxed_is_not_abs = solver.try_not(boxed_is_abs).expect("negated tester law");
    let selected_is_not_value = solver
        .try_not(selected_is_value)
        .expect("negated selector law");
    solver
        .try_assert_term(absolute_true_is_zero)
        .expect("assert");
    solver.try_assert_term(unit_is_not_mod).expect("assert");
    solver.try_assert_term(boxed_is_not_abs).expect("assert");
    solver
        .try_assert_term(selected_is_not_value)
        .expect("assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let constant_core = &artifact
        .declarations
        .iter()
        .find(|declaration| declaration.name == "mod")
        .expect("constant overload")
        .core_name;
    let function_core = &artifact
        .function_declarations
        .iter()
        .find(|declaration| declaration.name == "abs")
        .expect("function overload")
        .core_name;
    let datatype_rows: Vec<_> = artifact
        .symbol_identities
        .iter()
        .filter(|identity| identity.datatype_surface.as_deref() == Some("ReplayPrivateOperation"))
        .collect();
    assert_eq!(datatype_rows.len(), 5);
    assert!(datatype_rows.iter().all(|identity| {
        identity.core_name.starts_with("__ay_overload_")
            || identity.core_name.starts_with("is-__ay_overload_")
    }));
    let constructor_mod = datatype_rows
        .iter()
        .find(|identity| {
            identity.surface_name == "mod"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .expect("mod constructor identity");
    let constructor_abs = datatype_rows
        .iter()
        .find(|identity| {
            identity.surface_name == "abs"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .expect("abs constructor identity");
    assert_ne!(constant_core, &constructor_mod.core_name);
    assert_ne!(function_core, &constructor_abs.core_name);
    assert!(artifact.terms.iter().any(|node| {
        node.is_datatype_constructor
            && matches!(
                &node.data,
                TermData::Var(name, _) if name.starts_with("__ay_overload_")
            )
    }));

    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("interleaved private datatype replay");
    assert!(replay.result.result().is_unsat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("interleaved private datatype JSON replay");
    assert!(replay_from_json.result.result().is_unsat());

    let mut unmapped_private_carrier = artifact.clone();
    let scalar = unmapped_private_carrier
        .terms
        .iter_mut()
        .find(|node| matches!(&node.data, TermData::Const(Constant::Int(_))))
        .expect("integer constant node");
    scalar.sort = Sort::Uninterpreted("__ay_datatype_sort_999998".to_string());
    assert_native_replay_rejected(&unmapped_private_carrier);

    let mut forged_carrier = artifact;
    for identity in &mut forged_carrier.symbol_identities {
        if identity.datatype_surface.as_deref() == Some("ReplayPrivateOperation") {
            identity.datatype_core = Some("__ay_datatype_sort_999999".to_string());
        }
    }
    assert_native_replay_rejected(&forged_carrier);
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
    assert!(artifact.terms.iter().all(|node| node.id != dead.id()));
    assert!(artifact.terms.iter().all(|node| node.id != dead_sum.id()));
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| declaration.term != dead.id()));

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
        .find(|node| node.id == shadow.id())
        .expect("shadow node");
    assert!(!shadow_node.is_datatype_constructor);
    let red_node = artifact
        .terms
        .iter()
        .find(|node| node.id == red.id())
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

    // A flag-false free variable is not allowed to reuse the live constructor
    // core spelling. The datatype engines key constructors by that identity;
    // accepting this mutation would silently turn the fresh value into Red.
    let mut collision = artifact;
    let shadow_core = collision
        .declarations
        .iter()
        .find(|declaration| declaration.term == shadow.id())
        .expect("shadow declaration")
        .core_name
        .clone();
    let constructor_core = collision
        .symbol_identities
        .iter()
        .find(|identity| {
            identity.surface_name == "ShadowRed"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .expect("constructor identity")
        .core_name
        .clone();
    collision
        .declarations
        .retain(|declaration| declaration.term != shadow.id());
    collision.events.retain(|event| {
        !matches!(
            &event.kind,
            NativeReplayEventKind::DeclareConst { term, .. } if *term == shadow.id()
        )
    });
    collision.symbol_identities.retain(|identity| {
        !(identity.kind == NativeReplaySymbolKind::Uninterpreted
            && identity.core_name == shadow_core)
    });
    let shadow_node = collision
        .terms
        .iter_mut()
        .find(|node| node.id == shadow.id())
        .expect("shadow node");
    let TermData::Var(name, _) = &mut shadow_node.data else {
        unreachable!();
    };
    name.clone_from(&constructor_core);
    assert!(!shadow_node.is_datatype_constructor);
    assert_native_replay_rejected(&collision);
}

#[test]
fn native_replay_rejects_forged_constructor_flag_targeting_an_ordinary_constant() {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let declared = solver.declare_const("replay_not_a_constructor", Sort::Bool);
    let fresh = solver.fresh_var("replay_independent_fresh", Sort::Bool);
    let distinct = solver
        .try_eq(declared, fresh)
        .and_then(|equal| solver.try_not(equal))
        .expect("declared != fresh");
    solver.try_assert_term(distinct).expect("assert");
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat());

    let mut artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let declared_core = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == declared.id())
        .expect("declared constant")
        .core_name
        .clone();
    let fresh_node = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == fresh.id())
        .expect("fresh node");
    let TermData::Var(name, _) = &mut fresh_node.data else {
        panic!("fresh term must be a Var");
    };
    *name = declared_core;
    fresh_node.is_datatype_constructor = true;

    assert_native_replay_rejected(&artifact);
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
