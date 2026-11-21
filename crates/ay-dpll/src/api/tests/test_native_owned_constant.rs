// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;
use ay_core::term::{Symbol, TermData};

fn owner() -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 64 << 20, 128))
}

#[test]
fn native_owned_constant_five_inputs_share_original_million_after_all_bootstrap() {
    let mut solver = Solver::new(Logic::All);
    // Same ordinary ALL bootstrap as the WP encoder, outside this five-input
    // owner's lifetime. It leaves three actual entries in all affected maps.
    for name in ["heap", "domain", "perms"] {
        solver.declare_const(name, Sort::array(Sort::Int, Sort::Int));
    }
    let mut budget =
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(1_048_576, 16 << 20, 128));
    let mut calls = 0;
    let mut values = Vec::new();
    for (identity, sort) in [
        ("__verification_consumer_native_free_0", Sort::Bool),
        ("__verification_consumer_native_free_1", Sort::Int),
        ("__verification_consumer_native_free_2", Sort::bitvec(8)),
        ("__verification_consumer_native_free_3", Sort::bitvec(8)),
        ("__verification_consumer_native_free_4", Sort::Bool),
    ] {
        let value = solver
            .try_declare_const_with_fresh_identity_with_progress(
                "ignored",
                identity,
                &sort,
                &mut budget,
                &mut |_, _| {
                    calls += 1;
                    true
                },
            )
            .unwrap_or_else(|error| panic!("{identity}: {error:?}; usage={:?}", budget.usage()));
        assert!(
            matches!(solver.terms().get(value.id()), TermData::Var(name, _) if name == identity)
        );
        assert_eq!(solver.terms().sort(value.id()), &sort);
        assert_eq!(
            solver
                .executor
                .context()
                .symbol_info(identity)
                .and_then(|info| info.term),
            Some(value.id())
        );
        values.push(value);
    }
    assert!(calls > 5);
    assert!(budget.refusal().is_none());
    assert!(budget.usage().work <= 1_048_576);
    assert_eq!(values.len(), 5);
    assert_eq!(solver.native_replay_events().iter().filter(|event| matches!(&event.kind, NativeReplayEventKind::DeclareConst { name, .. } if name.starts_with("__verification_consumer_native_free_"))).count(), 5);
}

fn owned(solver: &mut Solver, display: &str, identity: &str, sort: &Sort) -> Term {
    solver
        .try_declare_const_with_fresh_identity_with_progress(
            display,
            identity,
            sort,
            &mut owner(),
            &mut |_, _| true,
        )
        .unwrap()
}

#[test]
fn native_owned_constant_display_is_not_identity_and_model_replay_are_genuine() {
    let mut solver = Solver::new(Logic::All);
    let left = owned(&mut solver, "and", "owned_value_left", &Sort::Int);
    let right = owned(&mut solver, "and", "owned_value_right", &Sort::Int);
    assert_ne!(left, right);
    let source = solver
        .executor
        .context()
        .symbol_info("owned_value_left")
        .unwrap();
    assert!(source.is_completion_eligible_declaration());
    assert!(!source.is_direct_source_declaration());
    assert_ne!(
        source.declaration_identity(),
        solver
            .executor
            .context()
            .symbol_info("owned_value_right")
            .unwrap()
            .declaration_identity()
    );
    assert!(
        matches!(solver.terms().get(left.id()), TermData::Var(name, _) if name == "owned_value_left")
    );
    let seven = solver.int_const(7);
    let nine = solver.int_const(9);
    let pin_left = solver.eq(left, seven);
    let pin_right = solver.eq(right, nine);
    solver.assert_term(pin_left);
    solver.assert_term(pin_right);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    assert_eq!(solver.value(left), Some(ModelValue::Int(7.into())));
    assert_eq!(solver.value(right), Some(ModelValue::Int(9.into())));
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    for term in [left, right] {
        let row = artifact
            .declarations
            .iter()
            .find(|row| row.term == term.id())
            .unwrap();
        assert!(row.name.starts_with("owned_value_"));
        assert!(!matches!(
            solver.terms().get(term.id()),
            TermData::App(_, _)
        ));
    }
    let replay = Solver::replay_native_replay_artifact(&artifact).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn native_owned_constant_refuses_source_raw_function_and_history_adoption() {
    let mut solver = Solver::new(Logic::All);
    solver.declare_const("owned_existing", Sort::Int);
    solver.declare_fun("owned_function", &[Sort::Int], Sort::Bool);
    solver.declare_fun("owned_nullary", &[], Sort::Int);
    solver
        .terms_mut()
        .mk_app(Symbol::named("owned_raw_app"), [], Sort::Int);
    solver.terms_mut().mk_var("owned_raw_var", Sort::Int);
    let setup = ay_frontend::parse("(define-fun owned_definition ((x Int)) Int (+ x 1)) (push 1) (declare-const owned_popped Int) (pop 1)").unwrap();
    solver.executor.execute_all(&setup).unwrap();
    let events = solver.native_replay_events().len();
    let stamp = solver.executor.context().source_context_stamp();
    for name in [
        "owned_existing",
        "owned_function",
        "owned_nullary",
        "owned_raw_app",
        "owned_raw_var",
        "owned_definition",
        "owned_popped",
        "and",
        "=",
        "__ay_owned",
        "",
    ] {
        let mut budget = owner();
        assert!(
            solver
                .try_declare_const_with_fresh_identity_with_progress(
                    "irrelevant",
                    name,
                    &Sort::Int,
                    &mut budget,
                    &mut |_, _| true
                )
                .is_err(),
            "{name}"
        );
        assert!(budget.refusal().is_some(), "{name}");
        assert_eq!(solver.native_replay_events().len(), events);
        assert_eq!(solver.executor.context().source_context_stamp(), stamp);
    }
}

#[test]
fn native_owned_constant_is_global_to_assertion_pop_and_revokes_old_result() {
    let mut solver = Solver::new(Logic::All);
    let initial = solver.check_sat_with_details();
    assert!(
        initial.result.is_sat() && initial.result.was_model_validated(),
        "{initial:?}"
    );
    solver.try_push().unwrap();
    let value = owned(
        &mut solver,
        "shadowed source",
        "owned_scope_value",
        &Sort::Int,
    );
    assert!(
        solver.model().is_none(),
        "new declaration revokes the old result"
    );
    solver.try_pop().unwrap();
    assert_eq!(
        solver
            .executor
            .context()
            .symbol_info("owned_scope_value")
            .and_then(|info| info.term),
        Some(value.id())
    );
    let four = solver.int_const(4);
    let pin = solver.eq(value, four);
    solver.assert_term(pin);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let replay = Solver::replay_native_replay_artifact(&artifact).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn native_owned_constant_live_nominals_and_kind_conflicts_are_checked() {
    let mut solver = Solver::new(Logic::All);
    let datatype = DatatypeSort::new(
        "OwnedValueCarrier",
        vec![DatatypeConstructor::unit("owned_value_ctor")],
    );
    solver.try_declare_datatype(&datatype).unwrap();
    let constructor = solver.datatype_constructor(&datatype, "owned_value_ctor", &[]);
    let declared = owned(
        &mut solver,
        "owned_value_ctor",
        "owned_dt_value",
        &Sort::Datatype(datatype.clone()),
    );
    assert_eq!(solver.get_sort(declared), solver.get_sort(constructor));
    assert!(solver
        .try_declare_const_with_fresh_identity_with_progress(
            "display",
            "owned_value_ctor",
            &Sort::Int,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    let nested = Sort::array(Sort::Int, Sort::seq(Sort::Datatype(datatype)));
    let value = owned(&mut solver, "nested", "owned_nested_value", &nested);
    let expected = solver
        .try_live_sort_with_progress(&nested, &mut owner(), &mut |_, _| true)
        .unwrap();
    assert_eq!(solver.terms().sort(value.id()), &expected);
    let unknown = Sort::Uninterpreted("NeverRegisteredOwnedValue".into());
    assert!(solver
        .try_declare_const_with_fresh_identity_with_progress(
            "unknown",
            "owned_unknown_value",
            &unknown,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    solver.try_reset().unwrap();
    assert!(solver
        .try_fresh_var_with_progress("stale", &nested, &mut owner(), &mut |_, _| true)
        .is_err());
}

#[test]
fn native_owned_constant_shared_budget_cancel_and_late_fence_publish_no_source() {
    let mut solver = Solver::new(Logic::All);
    let events = solver.native_replay_events().len();
    let stamp = solver.executor.context().source_context_stamp();
    let mut tiny = NativeDeclarationBudget::new(NativeDeclarationLimits::new(0, 0, 128));
    assert!(solver
        .try_declare_const_with_fresh_identity_with_progress(
            "x",
            "owned_tiny",
            &Sort::Int,
            &mut tiny,
            &mut |_, _| true
        )
        .is_err());
    solver.try_push().unwrap();
    solver.try_pop().unwrap();
    assert!(solver
        .try_fresh_var_with_progress("no_renewal", &Sort::Int, &mut tiny, &mut |_, _| true)
        .is_err());
    let mut cancelled = owner();
    let before_cancel = solver.executor.context().source_context_stamp();
    assert!(solver
        .try_declare_const_with_fresh_identity_with_progress(
            "x",
            "owned_cancel",
            &Sort::Int,
            &mut cancelled,
            &mut |_, _| false
        )
        .is_err());
    assert_eq!(
        solver.executor.context().source_context_stamp(),
        before_cancel
    );
    assert_eq!(solver.native_replay_events().len(), events + 2);
    assert_ne!(
        solver.executor.context().source_context_stamp(),
        stamp,
        "only real push/pop changed the context"
    );
    let mut baseline = Solver::new(Logic::All);
    let mut calls = 0usize;
    baseline
        .try_declare_const_with_fresh_identity_with_progress(
            "x",
            "owned_late",
            &Sort::Int,
            &mut owner(),
            &mut |_, _| {
                calls += 1;
                true
            },
        )
        .unwrap();
    let mut fresh = Solver::new(Logic::All);
    let fresh_stamp = fresh.executor.context().source_context_stamp();
    let fresh_events = fresh.native_replay_events().len();
    let mut visited = 0usize;
    let mut late = owner();
    assert!(fresh
        .try_declare_const_with_fresh_identity_with_progress(
            "x",
            "owned_late",
            &Sort::Int,
            &mut late,
            &mut |_, _| {
                visited += 1;
                visited < calls
            }
        )
        .is_err());
    assert_eq!(visited, calls);
    assert_eq!(fresh.executor.context().source_context_stamp(), fresh_stamp);
    assert_eq!(fresh.native_replay_events().len(), fresh_events);
    assert!(!fresh.var_terms_by_name.contains_key("owned_late"));
}

#[test]
fn native_owned_constant_fresh_binder_has_no_source_model_or_event_registration() {
    let mut solver = Solver::new(Logic::All);
    // A declaration need not yet have any App in the term arena. The data
    // factory still has to avoid its name without adopting/registering it.
    solver.declare_fun("bound_0", &[Sort::Int], Sort::Bool);
    let stamp = solver.executor.context().source_context_stamp();
    let events = solver.native_replay_events().len();
    let mut budget = owner();
    let one = solver
        .try_fresh_var_with_progress("bound", &Sort::Int, &mut budget, &mut |_, _| true)
        .unwrap();
    let usage = budget.usage();
    let two = solver
        .try_fresh_var_with_progress("bound", &Sort::Int, &mut budget, &mut |_, _| true)
        .unwrap();
    assert_ne!(one, two);
    assert!(budget.usage().work > usage.work);
    assert!(!solver.var_names.contains_key(&one.id()));
    assert!(!solver.var_sorts.contains_key(&one.id()));
    assert_eq!(solver.native_replay_events().len(), events);
    assert_eq!(solver.executor.context().source_context_stamp(), stamp);
    let name = match solver.terms().get(one.id()) {
        TermData::Var(name, _) => name.clone(),
        _ => panic!("binder Var"),
    };
    assert_ne!(name, "bound_0");
    assert!(solver.executor.context().symbol_info(&name).is_none());
}

#[test]
fn native_owned_constant_strict_source_proof_and_replay_keep_exact_roots() {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);
    let subject = owned(&mut solver, "and", "owned_proof_subject", &Sort::Bool);
    let opposite = solver.not(subject);
    solver.assert_term(subject);
    solver.assert_term(opposite);
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &artifact,
        std::time::Duration::from_secs(5),
    )
    .unwrap();
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("strict original owned-constant proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("faithful original problem");
    assert!(problem.contains("owned_proof_subject"));
    super::test_native_datatype_batch::check_whole_paired_document(
        problem,
        &proof.alethe,
        &proof.carcara_surface,
    );
}

#[test]
fn native_owned_constant_physical_sort_and_interrupt_refusals_preserve_source() {
    let mut solver = Solver::new(Logic::All);
    let mut deep = Sort::Int;
    for _ in 0..8 {
        deep = Sort::array(deep.clone(), deep);
    }
    let events = solver.native_replay_events().len();
    let before = solver.terms().len();
    let stamp = solver.executor.context().source_context_stamp();
    let mut small = NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 1024, 128));
    assert!(solver
        .try_declare_const_with_fresh_identity_with_progress(
            "wide",
            "owned_wide",
            &deep,
            &mut small,
            &mut |_, _| true
        )
        .is_err());
    assert!(matches!(
        small.refusal(),
        Some(NativeDeclarationRefusal::Storage { .. })
    ));
    assert_eq!(solver.terms().len(), before);
    assert_eq!(solver.native_replay_events().len(), events);
    assert_eq!(solver.executor.context().source_context_stamp(), stamp);
    solver.interrupt();
    let mut cancelled = owner();
    assert!(solver
        .try_fresh_var_with_progress("interrupt", &Sort::Int, &mut cancelled, &mut |_, _| true)
        .is_err());
    assert!(matches!(
        cancelled.refusal(),
        Some(NativeDeclarationRefusal::Cancelled)
    ));
    assert_eq!(solver.terms().len(), before);
}

#[test]
fn native_owned_constant_unmaterialized_families_own_their_names() {
    let mut solver = Solver::new(Logic::All);
    let mut setup =
        String::from("(declare-sort OwnedPolyMono0 0) (declare-sort OwnedPolyMono1 0) ");
    for index in 0..13 {
        setup.push_str(&format!("(declare-sort-parameter OwnedParam{index}) "));
    }
    let arguments = (0..13)
        .map(|index| format!("OwnedParam{index}"))
        .collect::<Vec<_>>()
        .join(" ");
    setup.push_str(&format!("(declare-fun owned_poly_0 ({arguments}) Bool) "));
    setup.push_str("(declare-datatypes ((OwnedPolyBox 1)) ((par (T) ((owned_poly_ctor (owned_poly_field T))))))");
    solver
        .executor
        .execute_all(&ay_frontend::parse(&setup).unwrap())
        .unwrap();
    assert!(
        solver
            .executor
            .context()
            .symbol_info("owned_poly_0")
            .is_none(),
        "the family must have no materialized instance"
    );
    assert!(
        solver
            .executor
            .context()
            .symbol_info("owned_poly_ctor")
            .is_none(),
        "the template must not have materialized members"
    );
    let events = solver.native_replay_events().len();
    let stamp = solver.executor.context().source_context_stamp();
    for name in [
        "owned_poly_0",
        "owned_poly_ctor",
        "owned_poly_field",
        "is-owned_poly_ctor",
        "OwnedParam0",
    ] {
        assert!(
            solver
                .try_declare_const_with_fresh_identity_with_progress(
                    "ignored",
                    name,
                    &Sort::Int,
                    &mut owner(),
                    &mut |_, _| true
                )
                .is_err(),
            "{name}"
        );
        assert_eq!(solver.executor.context().source_context_stamp(), stamp);
        assert_eq!(solver.native_replay_events().len(), events);
    }
    let binder = solver
        .try_fresh_var_with_progress("owned_poly", &Sort::Int, &mut owner(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(binder.id()), TermData::Var(name, _) if name != "owned_poly_0")
    );
    assert_eq!(solver.executor.context().source_context_stamp(), stamp);
    assert_eq!(solver.native_replay_events().len(), events);
}

#[test]
fn native_owned_constant_and_binder_support_within_budget_names_above4096() {
    let mut solver = Solver::new(Logic::All);
    let identity = "owned_big_name".repeat(400);
    assert!(identity.len() > 4096);
    let constant = owned(&mut solver, "and", &identity, &Sort::Int);
    let info = solver.executor.context().symbol_info(&identity).unwrap();
    assert_eq!(info.term, Some(constant.id()));
    assert!(info.is_completion_eligible_declaration());
    assert!(
        matches!(solver.terms().get(constant.id()), TermData::Var(name, _) if name == &identity)
    );
    let binder = solver
        .try_fresh_var_with_progress(&identity, &Sort::Int, &mut owner(), &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(solver.terms().get(binder.id()), TermData::Var(name, _) if name.len() > 4096 && name != &identity)
    );
    assert!(!solver.var_names.contains_key(&binder.id()));
}
