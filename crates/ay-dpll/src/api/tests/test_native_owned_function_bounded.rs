// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::api::*;
use ay_core::term::Symbol;

fn owner() -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(1_048_576, 16 << 20, 128))
}

fn declare(s: &mut Solver, name: &str, domain: &[Sort], range: &Sort) -> FuncDecl {
    s.try_declare_new_fun_with_progress(name, domain, range, &mut owner(), &mut |_, _| true)
        .unwrap()
}

#[test]
fn bounded_owned_function_fresh_full_arity_and_source_event_are_exact() {
    let mut s = Solver::new(Logic::All);
    let domain = vec![Sort::Bool; 257];
    let mut budget = owner();
    let f = s
        .try_declare_new_fun_with_progress(
            "bounded_wide",
            &domain,
            &Sort::Bool,
            &mut budget,
            &mut |_, _| true,
        )
        .unwrap();
    assert_eq!(f.arity(), 257);
    let values = vec![s.bool_const(true); 257];
    let value = s.try_apply(&f, &values).unwrap();
    assert_eq!(s.get_sort(value), Sort::Bool);
    let source = s.executor.context().symbol_info("bounded_wide").unwrap();
    assert!(source.is_completion_eligible_declaration());
    assert_eq!(source.arg_sorts, domain);
    assert_eq!(
        s.assertions_iter().len(),
        0,
        "declaration grants no equation or membership"
    );
    assert!(
        matches!(&s.native_replay_events().last().unwrap().kind, NativeReplayEventKind::DeclareFun { name, domain, range } if name == "bounded_wide" && domain.len() == 257 && range == &Sort::Bool)
    );
    assert!(budget.usage().work > 0 && budget.usage().storage_bytes > 0);
    assert!(budget.refusal().is_none());
}

#[test]
fn bounded_owned_function_real_model_and_json_replay_preserve_signature() {
    let mut s = Solver::new(Logic::QfUflia);
    let f = declare(&mut s, "bounded_model", &[Sort::Int], &Sort::Int);
    let zero = s.int_const(0);
    let value = s.try_apply(&f, &[zero]).unwrap();
    let one = s.int_const(1);
    let pin = s.eq(value, one);
    s.assert_term(pin);
    let details = s.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    assert_eq!(s.value(value), Some(ModelValue::Int(1.into())));
    let artifact = s.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let json = artifact.to_json_value().to_string();
    let restored = NativeReplayArtifact::from_json_str(&json).unwrap();
    let replay = Solver::replay_native_replay_artifact(&restored).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn bounded_owned_function_retained_frontend_and_raw_names_never_adopt() {
    let mut s = Solver::new(Logic::All);
    declare(&mut s, "occupied_function", &[Sort::Int], &Sort::Int);
    s.declare_const("occupied_constant", Sort::Int);
    s.terms_mut()
        .mk_app(Symbol::named("occupied_app"), [], Sort::Int);
    s.terms_mut().mk_var("occupied_var", Sort::Int);
    let truth = s.terms().true_term();
    s.terms_mut()
        .mk_let(vec![("occupied_let".into(), truth)], truth);
    s.terms_mut()
        .mk_forall(vec![("occupied_forall".into(), Sort::Int)], truth);
    s.terms_mut()
        .mk_exists(vec![("occupied_exists".into(), Sort::Int)], truth);
    s.terms_mut().mark_skolem_symbol("occupied_skolem");
    s.executor.execute_all(&ay_frontend::parse("(define-fun occupied_definition ((x Int)) Int x) (push 1) (declare-fun occupied_history (Int) Int) (pop 1) (declare-sort OccupiedSort 0)").unwrap()).unwrap();
    let events = s.native_replay_events().len();
    let stamp = s.executor.context().source_context_stamp();
    for name in [
        "occupied_function",
        "occupied_constant",
        "occupied_app",
        "occupied_var",
        "occupied_let",
        "occupied_forall",
        "occupied_exists",
        "occupied_skolem",
        "occupied_definition",
        "occupied_history",
        "OccupiedSort",
        "and",
        "+",
        "step",
        "",
        "__ay_owned",
    ] {
        assert!(
            s.try_declare_new_fun_with_progress(
                name,
                &[Sort::Int],
                &Sort::Int,
                &mut owner(),
                &mut |_, _| true
            )
            .is_err(),
            "{name}"
        );
        assert_eq!(s.executor.context().source_context_stamp(), stamp);
        assert_eq!(s.native_replay_events().len(), events);
    }
}

#[test]
fn bounded_owned_function_unmaterialized_families_members_and_aliases_are_occupied() {
    let mut s = Solver::new(Logic::All);
    let f = s.declare_fun("actual_alias_target", &[Sort::Int], Sort::Int);
    s.try_register_native_function_alias("occupied_alias", &f)
        .unwrap();
    let mut setup = String::new();
    for index in 0..13 {
        setup.push_str(&format!("(declare-sort-parameter FunctionParam{index}) "));
    }
    let arguments = (0..13)
        .map(|index| format!("FunctionParam{index}"))
        .collect::<Vec<_>>()
        .join(" ");
    setup.push_str(&format!(
        "(declare-fun unmaterialized_function ({arguments}) Bool) "
    ));
    setup.push_str("(declare-datatypes ((FunctionPolyBox 1)) ((par (T) ((function_poly_ctor (function_poly_field T))))))");
    s.executor
        .execute_all(&ay_frontend::parse(&setup).unwrap())
        .unwrap();
    assert!(s
        .executor
        .context()
        .symbol_info("unmaterialized_function")
        .is_none());
    assert!(s
        .executor
        .context()
        .symbol_info("function_poly_ctor")
        .is_none());
    let stamp = s.executor.context().source_context_stamp();
    let events = s.native_replay_events().len();
    for name in [
        "occupied_alias",
        "unmaterialized_function",
        "function_poly_ctor",
        "function_poly_field",
        "is-function_poly_ctor",
        "FunctionParam0",
    ] {
        assert!(
            s.try_declare_new_fun_with_progress(
                name,
                &[Sort::Int],
                &Sort::Int,
                &mut owner(),
                &mut |_, _| true
            )
            .is_err(),
            "{name}"
        );
    }
    assert_eq!(s.executor.context().source_context_stamp(), stamp);
    assert_eq!(s.native_replay_events().len(), events);
}

#[test]
fn bounded_owned_function_current_nominals_foreign_reset_and_forged_handles() {
    let mut s = Solver::new(Logic::All);
    let data = DatatypeSort::new(
        "BoundedCarrier",
        vec![DatatypeConstructor::unit("bounded_carrier_ctor")],
    );
    s.try_declare_datatype(&data).unwrap();
    let sort = Sort::Datatype(data.clone());
    let f = declare(&mut s, "bounded_nominal", &[sort.clone()], &sort);
    let arg = s.datatype_constructor(&data, "bounded_carrier_ctor", &[]);
    let result = s.try_apply(&f, &[arg]).unwrap();
    assert_eq!(s.get_sort(result), s.get_sort(arg));
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_unknown",
            &[Sort::Uninterpreted("MissingCarrier".into())],
            &Sort::Int,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    let mut other = Solver::new(Logic::All);
    other.try_declare_datatype(&data).unwrap();
    let other_arg = other.datatype_constructor(&data, "bounded_carrier_ctor", &[]);
    assert!(other.try_apply(&f, &[other_arg]).is_err());
    let fake = FuncDecl::new("bounded_nominal".into(), vec![sort.clone()], sort.clone());
    assert!(s.try_apply(&fake, &[arg]).is_err());
    s.try_reset().unwrap();
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_stale_sort",
            &[sort.clone()],
            &Sort::Int,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    s.try_declare_datatype(&data).unwrap();
    let arg = s.datatype_constructor(&data, "bounded_carrier_ctor", &[]);
    assert!(s.try_apply(&f, &[arg]).is_err());
    let current = declare(&mut s, "bounded_nominal", &[sort.clone()], &sort);
    assert!(s.try_apply(&current, &[arg]).is_ok());
}

#[test]
fn bounded_owned_function_scope_global_and_nullary_source_shapes_are_real() {
    let mut s = Solver::new(Logic::All);
    s.try_push().unwrap();
    let f = declare(&mut s, "bounded_global", &[Sort::Int], &Sort::Bool);
    let zero = declare(&mut s, "bounded_nullary", &[], &Sort::Int);
    assert!(s
        .executor
        .context()
        .symbol_info("bounded_nullary")
        .unwrap()
        .term
        .is_some());
    s.try_pop().unwrap();
    let x = s.int_const(0);
    assert!(s.try_apply(&f, &[x]).is_ok());
    assert!(s.try_apply(&zero, &[]).is_ok());
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_global",
            &[Sort::Int],
            &Sort::Bool,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_nullary",
            &[],
            &Sort::Int,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
}

#[test]
fn bounded_owned_function_popped_nominal_and_nested_kind_confusion_refuse_before_publication() {
    let mut s = Solver::new(Logic::All);
    s.try_push().unwrap();
    s.executor
        .execute_all(
            &ay_frontend::parse(
                "(declare-datatype ScopedFunctionCarrier ((scoped_function_ctor)))",
            )
            .unwrap(),
        )
        .unwrap();
    let source = Sort::Datatype(DatatypeSort::new(
        "ScopedFunctionCarrier",
        vec![DatatypeConstructor::unit("scoped_function_ctor")],
    ));
    let live = s
        .try_live_sort_with_progress(&source, &mut owner(), &mut |_, _| true)
        .unwrap();
    s.try_pop().unwrap();
    let events = s.native_replay_events().len();
    for sort in [source, live] {
        let nested = Sort::seq(Sort::array(Sort::Int, sort));
        assert!(s
            .try_declare_new_fun_with_progress(
                "popped_signature",
                &[nested],
                &Sort::Bool,
                &mut owner(),
                &mut |_, _| true
            )
            .is_err());
    }
    s.try_declare_opaque_sort("OpaqueNotDatatype").unwrap();
    let fake = Sort::Datatype(DatatypeSort::new(
        "OpaqueNotDatatype",
        vec![DatatypeConstructor::unit("forged_ctor")],
    ));
    assert!(s
        .try_declare_new_fun_with_progress(
            "wrong_nominal_kind",
            &[fake],
            &Sort::Int,
            &mut owner(),
            &mut |_, _| true
        )
        .is_err());
    assert_eq!(
        s.native_replay_events().len(),
        events + 1,
        "only real opaque-sort declaration is recorded"
    );
}

#[test]
fn bounded_owned_function_original_budget_cancel_depth_and_panic_are_sticky() {
    let mut s = Solver::new(Logic::All);
    let stamp = s.executor.context().source_context_stamp();
    let events = s.native_replay_events().len();
    for mut budget in [
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(0, 16 << 20, 128)),
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(1 << 20, 0, 128)),
    ] {
        assert!(s
            .try_declare_new_fun_with_progress(
                "bounded_refusal",
                &[Sort::Int],
                &Sort::Int,
                &mut budget,
                &mut |_, _| true
            )
            .is_err());
        assert!(s
            .try_declare_new_fun_with_progress(
                "bounded_retry",
                &[Sort::Int],
                &Sort::Int,
                &mut budget,
                &mut |_, _| true
            )
            .is_err());
    }
    let mut deep = Sort::Int;
    for _ in 0..8 {
        deep = Sort::seq(deep);
    }
    let mut budget =
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(1 << 20, 16 << 20, 3));
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_depth",
            &[deep],
            &Sort::Int,
            &mut budget,
            &mut |_, _| true
        )
        .is_err());
    let mut budget = owner();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| s
        .try_declare_new_fun_with_progress(
            "bounded_panic",
            &[Sort::Int],
            &Sort::Int,
            &mut budget,
            &mut |_, _| panic!("caller stop callback")
        )))
    .is_err());
    assert!(matches!(
        budget.refusal(),
        Some(NativeDeclarationRefusal::Cancelled)
    ));
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_after_panic",
            &[Sort::Int],
            &Sort::Int,
            &mut budget,
            &mut |_, _| true
        )
        .is_err());
    assert_eq!(s.executor.context().source_context_stamp(), stamp);
    assert_eq!(s.native_replay_events().len(), events);
}

#[test]
fn bounded_owned_function_solver_interrupt_is_original_and_refusal_is_sticky() {
    let mut s = Solver::new(Logic::All);
    let flag = s.interrupt_handle();
    flag.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut budget = owner();
    let events = s.native_replay_events().len();
    let stamp = s.executor.context().source_context_stamp();
    assert!(s
        .try_declare_new_fun_with_progress(
            "interrupted_function",
            &[Sort::Int],
            &Sort::Int,
            &mut budget,
            &mut |_, _| true
        )
        .is_err());
    assert!(matches!(
        budget.refusal(),
        Some(NativeDeclarationRefusal::Cancelled)
    ));
    flag.store(false, std::sync::atomic::Ordering::Relaxed);
    assert!(s
        .try_declare_new_fun_with_progress(
            "cleared_function",
            &[Sort::Int],
            &Sort::Int,
            &mut budget,
            &mut |_, _| true
        )
        .is_err());
    assert_eq!(s.executor.context().source_context_stamp(), stamp);
    assert_eq!(s.native_replay_events().len(), events);
}

#[test]
fn bounded_owned_function_late_fence_and_cumulative_owner_never_publish_partial_source() {
    let mut baseline = Solver::new(Logic::All);
    let mut count = 0;
    let mut budget = owner();
    baseline
        .try_declare_new_fun_with_progress(
            "bounded_fence",
            &[Sort::Int],
            &Sort::Bool,
            &mut budget,
            &mut |_, _| {
                count += 1;
                true
            },
        )
        .unwrap();
    let exact_work = budget.usage().work;
    let mut s = Solver::new(Logic::All);
    let stamp = s.executor.context().source_context_stamp();
    let events = s.native_replay_events().len();
    let mut seen = 0;
    let mut stopped = owner();
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_fence",
            &[Sort::Int],
            &Sort::Bool,
            &mut stopped,
            &mut |_, _| {
                seen += 1;
                seen != count
            }
        )
        .is_err());
    assert_eq!(seen, count);
    assert!(s.executor.context().symbol_info("bounded_fence").is_none());
    assert!(!s.native_fun_signatures.contains_key("bounded_fence"));
    assert_eq!(s.executor.context().source_context_stamp(), stamp);
    assert_eq!(s.native_replay_events().len(), events);
    let mut s = Solver::new(Logic::All);
    let mut tight =
        NativeDeclarationBudget::new(NativeDeclarationLimits::new(exact_work, 16 << 20, 128));
    s.try_declare_new_fun_with_progress(
        "bounded_fence",
        &[Sort::Int],
        &Sort::Bool,
        &mut tight,
        &mut |_, _| true,
    )
    .unwrap();
    let events = s.native_replay_events().len();
    assert!(s
        .try_declare_new_fun_with_progress(
            "bounded_later",
            &[Sort::Int],
            &Sort::Bool,
            &mut tight,
            &mut |_, _| true
        )
        .is_err());
    assert_eq!(s.native_replay_events().len(), events);
}

#[test]
fn bounded_owned_function_original_strict_proof_and_whole_pair_roundtrip() {
    let mut s = Solver::new(Logic::QfUf);
    s.set_produce_proofs(true);
    let f = declare(&mut s, "bounded_proof", &[Sort::Bool], &Sort::Bool);
    let arg = s.bool_const(true);
    let value = s.try_apply(&f, &[arg]).unwrap();
    let opposite = s.not(value);
    s.assert_term(value);
    s.assert_term(opposite);
    let artifact = s.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &artifact,
        std::time::Duration::from_secs(5),
    )
    .unwrap();
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("strict original function source proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("actual paired source");
    super::test_native_datatype_batch::check_whole_paired_document(
        problem,
        &proof.alethe,
        &proof.carcara_surface,
    );
}
