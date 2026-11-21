// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use serde_json::Value;

use ay_dpll::api::{
    Logic, NativeReplayArtifact, NativeReplayExportBudget as Budget,
    NativeReplayExportError as Error, NativeReplayExportLimits as Limits,
    NativeReplayExportResource as Resource, NativeReplayMetadata, Solver,
};

fn limits() -> Limits {
    Limits::new(16 * 1024 * 1024, 8 * 1024 * 1024, 4 * 1024 * 1024, 128)
}
fn capture(solver: &Solver) -> (String, Budget) {
    let mut budget = Budget::new(limits());
    let json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true,
        )
        .expect("bounded complete input");
    (json, budget)
}
fn normalized(mut value: Value) -> Value {
    value
        .as_object_mut()
        .expect("object")
        .remove("created_unix_ms");
    value["terms"]
        .as_array_mut()
        .expect("terms")
        .sort_unstable_by_key(|term| term["id"].as_u64());
    value
}
fn same_as_legacy(solver: &Solver) -> String {
    let (json, budget) = capture(solver);
    let value: Value = serde_json::from_str(&json).expect("complete JSON");
    let legacy = solver
        .export_native_replay_artifact(NativeReplayMetadata::default(), None)
        .to_json_value();
    assert_eq!(normalized(value), normalized(legacy));
    assert_eq!(budget.usage().output_bytes, json.len());
    assert!(budget.refusal().is_none());
    NativeReplayArtifact::from_json_str(&json).expect("existing v1 parser");
    json
}

#[test]
fn bounded_native_input_preserves_scopes_names_functions_and_checked_replay() {
    let mut solver = Solver::try_new(Logic::QfUflia).expect("solver");
    let x = solver.declare_const("x\"\n界", Sort::Int);
    let f = solver
        .try_declare_fun("native_export_function", &[Sort::Int], Sort::Int)
        .expect("function");
    let fx = solver.try_apply(&f, &[x]).expect("application");
    let zero = solver.int_const(0);
    let bound = solver.try_ge(fx, zero).expect("bound");
    solver
        .try_assert_named(bound, "base\u{0000}name")
        .expect("base");
    solver.try_push().expect("push");
    solver.try_assert_named(bound, "discarded").expect("scoped");
    solver.try_pop().expect("pop");
    solver.try_push().expect("push");
    solver
        .try_assert_named(bound, "active scoped duplicate")
        .expect("duplicate");
    let not_bound = solver.not(bound);
    solver.assert_term(not_bound);
    let before = solver.native_replay_events().len();
    let json = same_as_legacy(&solver);
    assert_eq!(solver.native_replay_events().len(), before);
    let artifact = NativeReplayArtifact::from_json_str(&json).expect("parse");
    let details = Solver::replay_native_replay_artifact_with_proofs(
        &artifact,
        std::time::Duration::from_secs(5),
    )
    .expect("strict replay");
    assert!(details.result.is_unsat(), "{details:?}");
    let source = solver.check_sat_with_details();
    assert!(source.result.is_unsat());
}

#[test]
fn bounded_native_input_preserves_datatype_members_and_shadowed_constructor() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let datatype = DatatypeSort::new(
        "ExportBox",
        vec![
            DatatypeConstructor::unit("ExportNone"),
            DatatypeConstructor::new(
                "ExportSome",
                vec![DatatypeField::new("export_value", Sort::Int)],
            ),
        ],
    );
    solver.try_declare_datatype(&datatype).expect("datatype");
    let one = solver.int_const(1);
    let boxed = solver.datatype_constructor(&datatype, "ExportSome", &[one]);
    let x = solver.declare_const("box_value", Sort::Datatype(datatype.clone()));
    let equality = solver.try_eq(x, boxed).expect("equality");
    solver.assert_term(equality);
    let shadow = solver.declare_const_with_fresh_identity(
        "ExportNone",
        "!ay.bounded-shadow",
        Sort::Datatype(datatype.clone()),
    );
    let none = solver.datatype_constructor(&datatype, "ExportNone", &[]);
    let shadow_eq_none = solver.try_eq(shadow, none).expect("shadow equality");
    let different = solver.not(shadow_eq_none);
    solver.assert_term(different);
    // Identical constructor/selector surfaces in another carrier retain their
    // exact private declarations, including members hidden by public heads.
    let other = DatatypeSort::new("OtherExportBox", datatype.constructors.clone());
    solver
        .try_declare_datatype(&other)
        .expect("overloaded datatype");
    let other_boxed = solver.datatype_constructor(&other, "ExportSome", &[one]);
    let other_x = solver.declare_const("other_box_value", Sort::Datatype(other));
    let other_equality = solver.try_eq(other_x, other_boxed).expect("other equality");
    solver.assert_term(other_equality);
    same_as_legacy(&solver);
}

#[test]
fn bounded_native_input_preserves_quantifiers_triggers_and_structural_sorts() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let bound = solver.fresh_var("bound", Sort::Int);
    let f = solver
        .try_declare_fun("quantified_export_f", &[Sort::Int], Sort::Int)
        .expect("function");
    let application = solver.try_apply(&f, &[bound]).expect("application");
    let zero = solver.int_const(0);
    let body = solver.try_ge(application, zero).expect("body");
    let quantified = solver
        .try_forall_with_triggers(&[bound], body, &[&[application]])
        .expect("quantifier");
    solver.assert_term(quantified);
    for (name, sort) in [
        ("character", Sort::Char),
        ("finite", Sort::FiniteDomain("ExportDomain".into(), 7)),
        ("typevar", Sort::TypeVar("ExportType".into())),
    ] {
        let variable = solver.declare_const(name, sort);
        let other = solver.fresh_var("other", solver.get_sort(variable));
        let equality = solver.try_eq(variable, other).expect("structural equality");
        solver.assert_term(equality);
    }
    same_as_legacy(&solver);
}

#[test]
fn bounded_native_input_refuses_output_before_buffer_and_preserves_solver() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("output_bound", Sort::Int);
    let zero = solver.int_const(0);
    let positive = solver.try_ge(x, zero).expect("bound");
    solver.assert_term(positive);
    let (json, _) = capture(&solver);
    let before = normalized(
        solver
            .export_native_replay_artifact(NativeReplayMetadata::default(), None)
            .to_json_value(),
    );
    let mut exact = Budget::new(Limits::new(16 << 20, 8 << 20, json.len(), 128));
    let exact_json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut exact,
            &mut |_, _| true,
        )
        .expect("exact output allowance");
    assert_eq!(exact_json.len(), json.len());
    let mut short = Budget::new(Limits::new(16 << 20, 8 << 20, json.len() - 1, 128));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut short,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Output,
            ..
        })
    ));
    assert_eq!(
        short.usage().output_bytes,
        0,
        "count pass refuses before buffer emission"
    );
    assert_eq!(
        before,
        normalized(
            solver
                .export_native_replay_artifact(NativeReplayMetadata::default(), None)
                .to_json_value()
        )
    );
    assert!(solver.check_sat_with_details().result.was_model_validated());
}

#[test]
fn bounded_native_input_cumulative_budget_cannot_be_reset_by_retry() {
    let solver = Solver::try_new(Logic::QfUf).expect("solver");
    let (json, _) = capture(&solver);
    let mut budget = Budget::new(Limits::new(16 << 20, 8 << 20, json.len(), 128));
    solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true,
        )
        .expect("first input");
    let first = budget.usage();
    let second = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true,
        )
        .expect_err("cumulative output exhausted");
    assert!(matches!(
        second,
        Error::Limit {
            resource: Resource::Output,
            ..
        }
    ));
    assert!(budget.usage().work >= first.work);
    assert_eq!(budget.usage().output_bytes, json.len());
    let usage = budget.usage();
    assert_eq!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| panic!("must not poll after refusal")
        ),
        Err(second)
    );
    assert_eq!(budget.usage(), usage);
}

#[test]
fn bounded_native_input_cancel_and_caught_callback_panic_are_sticky() {
    let solver = Solver::try_new(Logic::QfUf).expect("solver");
    let mut cancelled = Budget::new(limits());
    assert_eq!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut cancelled,
            &mut |_, _| false
        ),
        Err(Error::Cancelled)
    );
    assert_eq!(cancelled.usage().output_bytes, 0);
    assert_eq!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut cancelled,
            &mut |_, _| panic!("no retry")
        ),
        Err(Error::Cancelled)
    );
    let mut panicked = Budget::new(limits());
    let result = catch_unwind(AssertUnwindSafe(|| {
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut panicked,
            &mut |_, _| panic!("caller cancellation panic"),
        )
    }));
    assert!(result.is_err());
    assert_eq!(panicked.refusal(), Some(Error::Cancelled));
    assert_eq!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut panicked,
            &mut |_, _| true
        ),
        Err(Error::Cancelled)
    );
}

#[test]
fn bounded_native_input_raw_unused_event_names_bigints_and_depth_are_admitted_first() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let unused_name = "x".repeat(65536);
    solver.declare_const(&unused_name, Sort::Int);
    let mut budget = Budget::new(Limits::new(4096, 4096, 1 << 20, 128));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Work,
            ..
        })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    assert!(budget.usage().storage_bytes < 4096);

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let huge = num_bigint::BigInt::from(1u32) << 65536;
    let huge = solver.int_const_bigint(&huge);
    let variable = solver.declare_const("huge_target", Sort::Int);
    let comparison = solver.try_eq(huge, variable).expect("comparison");
    solver.assert_term(comparison);
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Work,
            ..
        })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    let mut shallow = Budget::new(Limits::new(16 << 20, 8 << 20, 4 << 20, 0));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut shallow,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Depth,
            ..
        })
    ));
}

#[test]
fn bounded_native_input_zero_storage_and_mid_capture_cancel_do_not_change_assertions() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("unchanged", Sort::Int);
    let one = solver.int_const(1);
    let equality = solver.try_eq(x, one).expect("equality");
    solver.assert_term(equality);
    let (baseline, qualified) = capture(&solver);
    let mut zero = Budget::new(Limits::new(16 << 20, 0, 4 << 20, 128));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut zero,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Storage,
            ..
        })
    ));
    assert_eq!(zero.usage().output_bytes, 0);
    let mut budget = Budget::new(limits());
    let mut work = 0usize;
    let threshold = qualified.usage().work - baseline.len() / 2;
    let result = solver.try_export_native_replay_input_json(
        &NativeReplayMetadata::default(),
        &mut budget,
        &mut |amount, _| {
            work += amount;
            work < threshold
        },
    );
    assert_eq!(result, Err(Error::Cancelled));
    assert!(
        budget.usage().output_bytes > 0,
        "cancellation is exercised during actual emission"
    );
    assert_eq!(
        normalized(serde_json::from_str(&baseline).expect("baseline")),
        normalized(serde_json::from_str(&capture(&solver).0).expect("unchanged"))
    );
    assert!(solver.check_sat_with_details().result.was_model_validated());
}

#[test]
fn bounded_native_input_keeps_every_structural_sort_and_constant_shape() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let sorts = [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::bitvec(13),
        Sort::array(Sort::Int, Sort::seq(Sort::String)),
        Sort::String,
        Sort::RegLan,
        Sort::FloatingPoint(8, 24),
        Sort::Uninterpreted("ExportOpaque".into()),
        Sort::seq(Sort::Int),
        Sort::Char,
        Sort::FiniteDomain("ExportSeven".into(), 7),
        Sort::TypeVar("ExportParameter".into()),
    ];
    for (index, sort) in sorts.into_iter().enumerate() {
        let value = solver.declare_const(&format!("sort_value_{index}"), sort.clone());
        let consumer = solver
            .try_declare_fun(&format!("sort_consumer_{index}"), &[sort], Sort::Bool)
            .expect("typed consumer");
        let root = solver
            .try_apply(&consumer, &[value])
            .expect("typed application");
        solver.assert_term(root);
    }
    let constants = [
        solver.bool_const(true),
        solver.int_const(-123),
        solver.rational_const(-7, 3),
        solver.bv_const(127, 13),
    ];
    for (index, constant) in constants.into_iter().enumerate() {
        let sort = solver.get_sort(constant);
        let consumer = solver
            .try_declare_fun(&format!("constant_consumer_{index}"), &[sort], Sort::Bool)
            .expect("constant consumer");
        let root = solver
            .try_apply(&consumer, &[constant])
            .expect("constant application");
        solver.assert_term(root);
    }
    same_as_legacy(&solver);
}

#[test]
fn bounded_native_input_string_indexed_application_and_ite_remain_full_v1() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let string = solver.string_const("quoted\"\\\n\u{0000}界");
    let consume_string = solver
        .try_declare_fun("consume_string", &[Sort::String], Sort::Bool)
        .expect("string consumer");
    let string_root = solver
        .try_apply(&consume_string, &[string])
        .expect("string application");
    solver.assert_term(string_root);
    let vector = solver.declare_const("extract_source", Sort::bitvec(16));
    let extract = solver.try_bvextract(vector, 7, 0).expect("indexed extract");
    let consume_vector = solver
        .try_declare_fun("consume_vector", &[Sort::bitvec(8)], Sort::Bool)
        .expect("vector consumer");
    let vector_root = solver
        .try_apply(&consume_vector, &[extract])
        .expect("vector application");
    solver.assert_term(vector_root);
    let condition = solver.declare_const("ite_condition", Sort::Bool);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let ite = solver.try_ite(condition, one, two).expect("ite");
    let consume_integer = solver
        .try_declare_fun("consume_ite", &[Sort::Int], Sort::Bool)
        .expect("integer consumer");
    let ite_root = solver
        .try_apply(&consume_integer, &[ite])
        .expect("ite application");
    solver.assert_term(ite_root);
    let exists = solver.try_exists(&[vector], vector_root).expect("exists");
    solver.assert_term(exists);
    same_as_legacy(&solver);
}

#[test]
fn bounded_native_input_many_empty_datatype_events_pay_comparison_work() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let common = "d".repeat(64);
    for index in 0..64 {
        let datatype = DatatypeSort::new(format!("{common}_{index}"), Vec::new());
        solver
            .try_declare_datatype(&datatype)
            .expect("empty declaration is accepted by producer");
    }
    let (json, usage) = capture(&solver);
    assert!(
        usage.usage().work >= 64 * 64 * 64,
        "deep history comparisons are admitted even with zero members"
    );
    let mut bounded = Budget::new(Limits::new(64 * 64 * 64 - 1, 8 << 20, 4 << 20, 128));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut bounded,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Work,
            ..
        })
    ));
    assert_eq!(bounded.usage().output_bytes, 0);
    let value: Value = serde_json::from_str(&json).expect("full input");
    assert_eq!(
        value["events"]
            .as_array()
            .expect("events")
            .iter()
            .filter(|event| event["kind"]["event"] == "declare_datatype")
            .count(),
        64
    );
    same_as_legacy(&solver);
}

#[test]
fn bounded_native_input_assertion_iterator_preserves_order_duplicates_scopes_and_tags() {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let p = solver.declare_const("iterator_p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.try_push().expect("push");
    solver.assert_term(p);
    solver.assert_term(not_p);
    let mut borrowed = solver.assertions_iter();
    assert_eq!(borrowed.len(), 3);
    assert_eq!(borrowed.next(), Some(p));
    assert_eq!(borrowed.len(), 2);
    assert_eq!(borrowed.collect::<Vec<_>>(), solver.assertions()[1..]);
    assert_eq!(
        solver.assertions_iter().collect::<Vec<_>>(),
        vec![p, p, not_p]
    );
    solver.try_pop().expect("pop");
    assert_eq!(solver.assertions_iter().collect::<Vec<_>>(), vec![p]);
    solver.try_reset_assertions().expect("reset assertions");
    assert_eq!(solver.assertions_iter().len(), 0);
}

#[test]
fn bounded_native_input_preserves_explicit_last_check_assumptions() {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    let p = solver.declare_const("assumed_p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(not_p);
    assert!(solver
        .check_sat_assuming_with_details(&[p])
        .solve
        .result
        .is_unsat());
    let json = same_as_legacy(&solver);
    let parsed = NativeReplayArtifact::from_json_str(&json).expect("input");
    assert_eq!(
        parsed.assertions.len(),
        1,
        "assumptions stay in their v1 event"
    );
    let checked = Solver::replay_native_replay_artifact_with_proofs(
        &parsed,
        std::time::Duration::from_secs(5),
    )
    .expect("checked assuming replay");
    assert!(checked.result.is_unsat());
    assert!(checked.verification.unsat_proof_strictly_verified);
}

#[test]
fn bounded_native_input_future_only_v1_placeholders_refuse_without_debug_copy() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.declare_const("unused_complex", Sort::Complex);
    let before = solver.native_replay_events().len();
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::UnsupportedSource { .. })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    assert_eq!(solver.native_replay_events().len(), before);
    assert_eq!(solver.assertions_iter().len(), 0);
}

#[test]
fn bounded_native_input_large_constructor_metadata_refuses_before_copying_owner_names() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let datatype = DatatypeSort::new(
        "large_owner_".repeat(6000),
        vec![DatatypeConstructor::unit("small_member")],
    );
    solver.try_declare_datatype(&datatype).expect("datatype");
    let member = solver.datatype_constructor(&datatype, "small_member", &[]);
    let value = solver.declare_const("owner_value", Sort::Datatype(datatype));
    let equality = solver.try_eq(member, value).expect("same carrier");
    solver.assert_term(equality);
    let mut budget = Budget::new(Limits::new(128 << 20, 8192, 4 << 20, 128));
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::Limit {
            resource: Resource::Storage,
            ..
        })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    assert!(budget.usage().storage_bytes <= 8192);
    assert_eq!(solver.assertions_iter().len(), 1);
}

#[test]
fn bounded_native_input_text_owned_uf_is_an_explicit_refusal_not_an_invented_header() {
    let mut solver = Solver::try_new(Logic::QfUflia).expect("solver");
    solver
        .parse_smtlib2("(declare-fun text_only_f (Int) Bool) (assert (text_only_f 0))")
        .expect("text declarations");
    let before = solver.assertions();
    assert!(
        solver
            .export_native_replay_artifact(NativeReplayMetadata::default(), None)
            .function_declarations
            .is_empty(),
        "legacy history lacks this declaration"
    );
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::UnsupportedSource { .. })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    assert_eq!(solver.assertions(), before);
}

#[test]
fn bounded_native_input_text_and_mixed_assertions_with_recorded_dependencies_remain_supported() {
    let mut text = Solver::try_new(Logic::QfLia).expect("solver");
    text.parse_smtlib2("(define-fun expanded ((i Int)) Int (+ i 1)) (assert (> (expanded 1) 0))")
        .expect("expanded text");
    let text_json = same_as_legacy(&text);
    assert!(Solver::replay_native_replay_json_str(&text_json)
        .expect("ground text replay")
        .result
        .is_sat());

    let mut mixed = Solver::try_new(Logic::QfLia).expect("solver");
    let x = mixed.declare_const("mixed_x", Sort::Int);
    let zero = mixed.int_const(0);
    let positive = mixed.try_ge(x, zero).expect("native root");
    mixed.assert_term(positive);
    mixed
        .parse_smtlib2("(assert (> mixed_x 1))")
        .expect("text assertion");
    let mixed_json = same_as_legacy(&mixed);
    assert!(Solver::replay_native_replay_json_str(&mixed_json)
        .expect("mixed replay")
        .result
        .is_sat());
}

#[test]
fn bounded_native_input_mixed_unrecorded_binding_refuses_without_losing_native_roots() {
    let mut solver = Solver::try_new(Logic::QfUflia).expect("solver");
    let native = solver
        .try_declare_fun("recorded_f", &[Sort::Int], Sort::Bool)
        .expect("native function");
    let zero = solver.int_const(0);
    let application = solver
        .try_apply(&native, &[zero])
        .expect("native application");
    solver.assert_term(application);
    same_as_legacy(&solver);
    solver
        .parse_smtlib2("(declare-fun unrecorded_g (Int) Bool) (assert (unrecorded_g 0))")
        .expect("text function");
    let before = solver.assertions();
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::UnsupportedSource { .. })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
    assert_eq!(solver.assertions(), before);
}

#[test]
fn bounded_native_input_missing_datatype_theory_refuses_even_without_constructor_terms() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.parse_smtlib2("(declare-datatypes () ((UnrecordedTwo (UnrecordedRed) (UnrecordedBlue)))) (assert (exists ((a UnrecordedTwo) (b UnrecordedTwo) (c UnrecordedTwo)) (distinct a b c)))").expect("text datatype and bound-only use");
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::UnsupportedSource { .. })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
}

#[test]
fn bounded_native_input_missing_sort_alias_refuses_before_erasing_its_meaning() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    solver
        .parse_smtlib2("(define-sort MissingAlias () Int)")
        .expect("text alias");
    let x = solver.declare_const(
        "native_alias_value",
        Sort::Uninterpreted("MissingAlias".into()),
    );
    let zero = solver.int_const(0);
    let positive = solver.try_ge(x, zero).expect("lowered alias");
    solver.assert_term(positive);
    let mut budget = Budget::new(limits());
    assert!(matches!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::UnsupportedSource { .. })
    ));
    assert_eq!(budget.usage().output_bytes, 0);
}

#[test]
fn bounded_native_input_scope_audit_keeps_bound_names_local() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let parsed = solver
        .parse_smtlib2("(declare-const source_bound Int)")
        .expect("unrecorded global");
    assert!(parsed.is_empty());
    // A native binder can adopt an existing global term as its local identity;
    // the unused original declaration must not become a needed free binding.
    let term = solver
        .parse_smtlib2("(assert (forall ((source_bound Int)) (>= source_bound 0)))")
        .expect("local shadow");
    assert_eq!(term.len(), 1);
    same_as_legacy(&solver);
}
