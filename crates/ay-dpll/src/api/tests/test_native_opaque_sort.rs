// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;
use std::time::Duration;

fn budget(work: usize, storage: usize) -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(work, storage, 128))
}
fn capture(solver: &Solver) -> NativeReplayArtifact {
    solver.export_native_replay_artifact(NativeReplayMetadata::default(), None)
}
fn group() -> Vec<DatatypeSort> {
    vec![
        DatatypeSort::new(
            "OpaqueTree",
            vec![
                DatatypeConstructor::new(
                    "opaque_leaf",
                    vec![DatatypeField::new(
                        "opaque_payload",
                        Sort::Uninterpreted("ExternalPayload".into()),
                    )],
                ),
                DatatypeConstructor::new(
                    "opaque_node",
                    vec![DatatypeField::new(
                        "opaque_children",
                        Sort::Uninterpreted("OpaqueForest".into()),
                    )],
                ),
            ],
        ),
        DatatypeSort::new(
            "OpaqueForest",
            vec![
                DatatypeConstructor::unit("opaque_nil"),
                DatatypeConstructor::new(
                    "opaque_cons",
                    vec![
                        DatatypeField::new("opaque_head", Sort::Uninterpreted("OpaqueTree".into())),
                        DatatypeField::new(
                            "opaque_tail",
                            Sort::Uninterpreted("OpaqueForest".into()),
                        ),
                    ],
                ),
            ],
        ),
    ]
}

#[test]
fn native_opaque_sort_global_scope_reset_and_exact_native_roundtrip() {
    let mut solver = Solver::new(Logic::All);
    solver.push();
    let sort = solver.try_declare_opaque_sort("ExternalPayload").unwrap();
    let a = solver.declare_const("external_a", sort.clone());
    let b = solver.declare_const("external_b", sort.clone());
    solver.pop();
    let distinct = solver.distinct(&[a, b]);
    solver.assert_term(distinct);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    let artifact = capture(&solver);
    assert!(artifact
        .replay_gaps
        .iter()
        .all(|gap| gap == "solve details were not captured"));
    assert_eq!(artifact.sort_declarations.len(), 1);
    assert_eq!(artifact.sort_declarations[0].name, "ExternalPayload");
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    let mut export = NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        32 << 20,
        16 << 20,
        4 << 20,
        128,
    ));
    let json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut export,
            &mut |_, _| true,
        )
        .unwrap();
    let bounded = NativeReplayArtifact::from_json_str(&json).unwrap();
    assert_eq!(bounded.sort_declarations, artifact.sort_declarations);
    assert_eq!(bounded.events, artifact.events);
    let replay = Solver::replay_native_replay_json_str(&json).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    solver.try_reset_assertions().unwrap();
    assert!(solver.try_declare_opaque_sort("ExternalPayload").is_err());
    assert_eq!(capture(&solver).sort_declarations.len(), 1);
    solver.try_reset().unwrap();
    assert!(capture(&solver).sort_declarations.is_empty());
    solver.try_declare_opaque_sort("ExternalPayload").unwrap();
}

#[test]
fn native_opaque_sort_ambient_forward_group_has_checked_model() {
    let mut solver = Solver::new(Logic::All);
    let types = group();
    let before = solver.native_replay_events().len();
    assert!(
        solver.try_declare_datatypes(&types).is_err(),
        "missing ambient sorts are not invented"
    );
    assert_eq!(solver.native_replay_events().len(), before);
    let sort = solver.try_declare_opaque_sort("ExternalPayload").unwrap();
    solver.try_declare_datatypes(&types).unwrap();
    let payload = solver.declare_const("ambient_payload", sort);
    let leaf = solver.datatype_constructor(&types[0], "opaque_leaf", &[payload]);
    let nil = solver.datatype_constructor(&types[1], "opaque_nil", &[]);
    let cons = solver.datatype_constructor(&types[1], "opaque_cons", &[leaf, nil]);
    let node = solver.datatype_constructor(&types[0], "opaque_node", &[cons]);
    let value = solver.declare_const("ambient_tree", Sort::Datatype(types[0].clone()));
    let same_value = solver.eq(value, node);
    solver.assert_term(same_value);
    let children =
        solver.datatype_selector("opaque_children", value, Sort::Datatype(types[1].clone()));
    let head = solver.datatype_selector("opaque_head", children, Sort::Datatype(types[0].clone()));
    let selected = solver.datatype_selector(
        "opaque_payload",
        head,
        Sort::Uninterpreted("ExternalPayload".into()),
    );
    let same = solver.eq(payload, selected);
    solver.assert_term(same);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    assert!(solver.model().is_some());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn native_opaque_sort_replay_refuses_missing_reordered_or_forged_identity() {
    let mut solver = Solver::new(Logic::All);
    let sort = solver.try_declare_opaque_sort("FirstOpaque").unwrap();
    solver.try_declare_opaque_sort("SecondOpaque").unwrap();
    let value = solver.declare_const("opaque_identity_value", sort.clone());
    let peer = solver.declare_const("opaque_identity_peer", sort);
    let same = solver.eq(value, peer);
    solver.assert_term(same);
    let original = capture(&solver);
    let mut missing = original.clone();
    missing.sort_declarations.remove(0);
    assert!(Solver::replay_native_replay_artifact(&missing).is_err());
    let mut missing_event = original.clone();
    missing_event.events.retain(|event| !matches!(&event.kind, NativeReplayEventKind::DeclareSort { name, .. } if name == "FirstOpaque"));
    assert!(Solver::replay_native_replay_artifact(&missing_event).is_err());
    let mut reordered = original.clone();
    reordered.sort_declarations.swap(0, 1);
    assert!(Solver::replay_native_replay_artifact(&reordered).is_err());
    let mut duplicate = original.clone();
    duplicate.sort_declarations[1].core_name = duplicate.sort_declarations[0].core_name.clone();
    if let NativeReplayEventKind::DeclareSort { core_name, .. } = &mut duplicate.events[2].kind {
        *core_name = duplicate.sort_declarations[0].core_name.clone();
    } else {
        panic!("exact second declaration event");
    }
    assert!(Solver::replay_native_replay_artifact(&duplicate).is_err());
    let mut forged = original;
    forged.sort_declarations[0].core_name = "SecondOpaque".into();
    assert!(Solver::replay_native_replay_artifact(&forged).is_err());
}

#[test]
fn native_opaque_sort_never_reinterprets_undeclared_term_or_signature_sorts() {
    for route in 0..3 {
        let mut solver = Solver::new(Logic::All);
        let sort = Sort::Uninterpreted("UnownedPayload".into());
        match route {
            0 => {
                solver.declare_const("old_payload", sort);
            }
            1 => {
                solver.fresh_var("old_fresh_payload", Sort::array(Sort::Int, sort));
            }
            _ => {
                solver.declare_fun("old_payload_fun", &[sort], Sort::Bool);
            }
        }
        let events = solver.native_replay_events().len();
        let terms = solver.terms().len();
        let prior_definition = solver
            .executor
            .context()
            .sort_definition("UnownedPayload")
            .cloned();
        assert!(solver.try_declare_opaque_sort("UnownedPayload").is_err());
        assert_eq!(solver.native_replay_events().len(), events);
        assert_eq!(solver.terms().len(), terms);
        assert_eq!(
            solver.executor.context().sort_definition("UnownedPayload"),
            prior_definition.as_ref()
        );
    }
}

#[test]
fn native_opaque_sort_conflicts_and_reserved_names_leave_source_unchanged() {
    let mut solver = Solver::new(Logic::All);
    for name in [
        "",
        "Bool",
        "Int",
        "Real",
        "String",
        "RegLan",
        "Seq",
        "Array",
        "__ay_datatype_sort_4",
    ] {
        let before = solver.native_replay_events().len();
        assert!(solver.try_declare_opaque_sort(name).is_err(), "{name}");
        assert_eq!(solver.native_replay_events().len(), before);
    }
    solver.try_declare_opaque_sort("OnceOnly").unwrap();
    let before = solver.native_replay_events().len();
    assert!(solver.try_declare_opaque_sort("OnceOnly").is_err());
    assert!(solver
        .try_declare_datatypes(&[DatatypeSort::new(
            "OnceOnly",
            vec![DatatypeConstructor::unit("not_opaque")]
        )])
        .is_err());
    assert_eq!(solver.native_replay_events().len(), before);
}

#[test]
fn native_opaque_sort_limits_and_cancel_are_atomic_and_sticky() {
    let mut solver = Solver::new(Logic::All);
    let truth = solver.bool_const(true);
    solver.assert_term(truth);
    assert!(solver.check_sat_with_details().result.is_sat());
    let before = solver.native_replay_events().len();
    let terms = solver.terms().len();
    for (work, storage) in [(0, 1 << 20), (1 << 20, 0)] {
        let mut owner = budget(work, storage);
        assert!(solver
            .try_declare_opaque_sort_with_progress("LimitOpaque", &mut owner, &mut |_, _| true)
            .is_err());
        assert!(owner.refusal().is_some());
        assert!(solver
            .try_declare_opaque_sort_with_progress("OtherLimitOpaque", &mut owner, &mut |_, _| true)
            .is_err());
    }
    let mut owner = budget(64 << 20, 64 << 20);
    let mut polls = 0;
    assert!(solver
        .try_declare_opaque_sort_with_progress(
            "CancelledOpaque",
            &mut owner,
            &mut |work, storage| {
                if work == 0 && storage == 0 {
                    polls += 1;
                }
                polls < 3
            }
        )
        .is_err());
    assert_eq!(polls, 3, "cancellation at the final precommit poll");
    assert_eq!(owner.refusal(), Some(NativeDeclarationRefusal::Cancelled));
    assert_eq!(solver.native_replay_events().len(), before);
    assert_eq!(solver.terms().len(), terms);
    assert!(solver
        .executor
        .context()
        .sort_definition("CancelledOpaque")
        .is_none());
    assert!(
        solver.model().is_some(),
        "refusal preserves the prior actual SAT result"
    );
}

#[test]
fn native_opaque_sort_actual_strict_proof_and_pinned_carcara() {
    let mut solver = Solver::new(Logic::All);
    let sort = solver.try_declare_opaque_sort("ProofOpaque").unwrap();
    let a = solver.declare_const("opaque_proof_a", sort.clone());
    let b = solver.declare_const("opaque_proof_b", sort.clone());
    let c = solver.declare_const("opaque_proof_c", sort);
    let ab = solver.eq(a, b);
    let bc = solver.eq(b, c);
    let ac = solver.eq(a, c);
    let not_ac = solver.not(ac);
    solver.assert_term(ab);
    solver.assert_term(bc);
    solver.assert_term(not_ac);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &capture(&solver),
        Duration::from_secs(5),
    )
    .unwrap();
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("actual independently checked proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("paired opaque-sort problem");
    assert!(problem.contains("declare-sort"));
    super::test_native_datatype_batch::check_whole_paired_document(
        problem,
        &proof.alethe,
        &proof.carcara_surface,
    );
}

#[test]
fn native_opaque_sort_private_reincarnation_preserves_exact_scope_identity() {
    let mut solver = Solver::new(Logic::All);
    // Source-text setup creates an old, unused scoped declaration. The native
    // API implementation itself never reparses sort text. The retired nominal
    // identity remains reserved, so the new live declaration must be private.
    let setup = ay_frontend::parse("(push 1) (declare-sort RebornOpaque 0) (pop 1)").unwrap();
    solver.executor.execute_all(&setup).unwrap();
    let sort = solver.try_declare_opaque_sort("RebornOpaque").unwrap();
    let a = solver.declare_const("reborn_a", sort.clone());
    let b = solver.declare_const("reborn_b", sort);
    let distinct = solver.distinct(&[a, b]);
    solver.assert_term(distinct);
    let artifact = capture(&solver);
    assert_ne!(artifact.sort_declarations[0].core_name, "RebornOpaque");
    let replay = Solver::replay_native_replay_artifact(&artifact).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    let mut owner = NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        32 << 20,
        16 << 20,
        4 << 20,
        128,
    ));
    let json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut owner,
            &mut |_, _| true,
        )
        .unwrap();
    let replay = Solver::replay_native_replay_json_str(&json).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    let mut forged = artifact;
    forged.sort_declarations[0].core_name = "RebornOpaque".into();
    assert!(Solver::replay_native_replay_artifact(&forged).is_err());
}

#[test]
fn native_opaque_sort_source_limit_and_missing_event_do_not_grant_member_ownership() {
    let mut solver = Solver::new(Logic::All);
    solver.try_declare_opaque_sort("ExternalPayload").unwrap();
    let types = group();
    solver.try_declare_datatypes(&types).unwrap();
    let nil = solver.datatype_constructor(&types[1], "opaque_nil", &[]);
    let tester = solver.datatype_tester("opaque_nil", nil);
    solver.assert_term(tester);
    let original = capture(&solver);
    let mut missing = original.clone();
    missing.sort_declarations.clear();
    missing
        .events
        .retain(|event| !matches!(event.kind, NativeReplayEventKind::DeclareSort { .. }));
    assert!(
        Solver::replay_native_replay_artifact(&missing).is_err(),
        "datatype fields require an actual prior native sort declaration"
    );
    let mut forged = original;
    let member = forged
        .symbol_identities
        .iter_mut()
        .find(|identity| {
            identity.surface_name == "opaque_nil"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .unwrap();
    member.datatype_surface = Some("ExternalPayload".into());
    member.datatype_core = Some("ExternalPayload".into());
    assert!(Solver::replay_native_replay_artifact(&forged).is_err());

    let events = solver.native_replay_events().len();
    // The caller can share this owner with datatype declaration attempts.
    // A name fits, but the preexisting source/scope-copy quote cannot fit.
    let mut owner = budget(1024, 1024);
    assert!(solver
        .try_declare_opaque_sort_with_progress("SourceLimited", &mut owner, &mut |_, _| true)
        .is_err());
    assert!(owner.refusal().is_some());
    assert_eq!(solver.native_replay_events().len(), events);
    assert!(solver
        .executor
        .context()
        .sort_definition("SourceLimited")
        .is_none());
}

#[test]
fn native_opaque_sort_unused_quantified_source_sort_and_implicit_datatype_sort_are_not_rebound() {
    for existential in [false, true] {
        let mut solver = Solver::new(Logic::All);
        let truth = solver.bool_const(true).id();
        let variables = vec![(
            "unused_binder".into(),
            Sort::Uninterpreted("BinderOnlyOpaque".into()),
        )];
        let quantifier = if existential {
            solver.terms_mut().mk_exists(variables, truth)
        } else {
            solver.terms_mut().mk_forall(variables, truth)
        };
        assert_eq!(solver.terms().sort(quantifier), &Sort::Bool);
        let events = solver.native_replay_events().len();
        let terms = solver.terms().len();
        assert!(solver.try_declare_opaque_sort("BinderOnlyOpaque").is_err());
        assert_eq!(solver.native_replay_events().len(), events);
        assert_eq!(solver.terms().len(), terms);
        assert!(solver
            .executor
            .context()
            .sort_definition("BinderOnlyOpaque")
            .is_none());
    }
    let mut solver = Solver::new(Logic::All);
    let legacy = DatatypeSort::new(
        "LegacyNativeWrapper",
        vec![DatatypeConstructor::new(
            "legacy_wrap",
            vec![DatatypeField::new(
                "legacy_payload",
                Sort::Uninterpreted("ImplicitOpaque".into()),
            )],
        )],
    );
    solver.try_declare_datatype(&legacy).unwrap();
    let before = solver
        .executor
        .context()
        .sort_definition("ImplicitOpaque")
        .cloned();
    assert!(
        before.is_some(),
        "legacy native field elaboration already allocated this sort"
    );
    let events = solver.native_replay_events().len();
    assert!(solver.try_declare_opaque_sort("ImplicitOpaque").is_err());
    assert_eq!(
        solver.executor.context().sort_definition("ImplicitOpaque"),
        before.as_ref()
    );
    assert_eq!(solver.native_replay_events().len(), events);
}

#[test]
fn native_opaque_sort_ambient_datatype_selector_has_strict_checked_proof() {
    let mut solver = Solver::new(Logic::All);
    let sort = solver.try_declare_opaque_sort("ExternalPayload").unwrap();
    let types = group();
    solver.try_declare_datatypes(&types).unwrap();
    let payload = solver.declare_const("proof_ambient_payload", sort.clone());
    let leaf = solver.datatype_constructor(&types[0], "opaque_leaf", &[payload]);
    let value = solver.declare_const("proof_ambient_tree", Sort::Datatype(types[0].clone()));
    let is_leaf = solver.eq(value, leaf);
    solver.assert_term(is_leaf);
    let field = solver.datatype_selector("opaque_payload", value, sort);
    let same_field = solver.eq(field, payload);
    let forged_field = solver.not(same_field);
    solver.assert_term(forged_field);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &capture(&solver),
        Duration::from_secs(5),
    )
    .unwrap();
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("actual checked native selector proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("paired opaque/native-datatype proof problem");
    assert!(problem.contains("declare-sort") && problem.contains("declare-datatypes"));
    super::test_native_datatype_batch::check_whole_paired_document(
        problem,
        &proof.alethe,
        &proof.carcara_surface,
    );
}
