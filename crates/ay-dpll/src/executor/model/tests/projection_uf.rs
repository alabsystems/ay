// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Projection-UF model evaluation and output stay on one exact symbolic
//! interpretation instead of falling back to finite EUF samples.

use super::*;
use ay_frontend::parse;
use ay_model_check::{
    check_projection_implication, CheckedProjectionImplication, ProjectionImplicationCandidate,
    ProjectionUfCandidate,
};

fn bv8_projection(symbol: Symbol, projected_argument: usize) -> ProjectionUfModel {
    let bv8 = Sort::bitvec(8);
    ProjectionUfModel::from_test_definitions([(
        symbol,
        vec![bv8.clone(), bv8.clone()],
        bv8,
        projected_argument,
    )])
    .expect("well-typed BV projection")
}

fn checked_bv8_projection(
    terms: &mut TermStore,
    symbol: Symbol,
) -> (CheckedProjectionImplication, TermId) {
    let bv8 = Sort::bitvec(8);
    let x = terms.mk_var("x", bv8.clone());
    let y = terms.mk_var("y", bv8.clone());
    let zero = terms.mk_bitvec(BigInt::zero(), 8);
    let premise = terms.mk_eq(x, zero);
    let application = terms.mk_app(symbol.clone(), vec![y, x], bv8.clone());
    let conclusion = terms.mk_eq(application, zero);
    let body = terms.mk_implies(premise, conclusion);
    let root = terms.mk_forall(
        vec![
            ("x".to_string(), bv8.clone()),
            ("y".to_string(), bv8.clone()),
        ],
        body,
    );
    let candidate = ProjectionImplicationCandidate {
        definitions: vec![ProjectionUfCandidate {
            symbol,
            parameter_sorts: vec![bv8.clone(), bv8.clone()],
            result_sort: bv8,
            projected_parameter: 1,
        }],
        conclusion,
    };
    let checked = check_projection_implication(terms, &[root], &candidate)
        .expect("the premise proves the checked second-argument projection");
    (checked, root)
}

#[test]
fn projection_evaluation_precedes_finite_table_and_checks_signature() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let first = executor.ctx.terms.mk_bitvec(BigInt::from(0x11u8), 8);
    let second = executor.ctx.terms.mk_bitvec(BigInt::from(0x22u8), 8);
    let application = executor.ctx.terms.mk_app(
        Symbol::named("f!overload!bv8"),
        vec![first, second],
        bv8.clone(),
    );

    let mut function_tables = HashMap::default();
    function_tables.insert(
        "f!overload!bv8".to_string(),
        vec![(
            vec!["#x11".to_string(), "#x22".to_string()],
            "#x33".to_string(),
        )],
    );
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        function_tables,
        ..Default::default()
    });
    model.projection_ufs = bv8_projection(Symbol::named("f!overload!bv8"), 1);

    assert_eq!(
        executor.evaluate_term(&model, application),
        EvalValue::BitVec {
            value: BigInt::from(0x22u8),
            width: 8,
        }
    );

    // Reusing the same text with another signature is not the certified
    // declaration. It must not select the BV projection.
    let bool_arg = executor.ctx.terms.true_term();
    let mismatched =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("f!overload!bv8"), vec![bool_arg], Sort::Bool);
    assert_eq!(
        executor.evaluate_term(&model, mismatched),
        EvalValue::Unknown
    );
}

#[test]
fn projection_signature_conflict_fails_closed_in_every_model_consumer() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_UF)
        (declare-fun f (Bool) Bool)
    "#,
    )
    .expect("valid declaration");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declaration executes");

    let (identity, argument_sorts, result_sort) = executor
        .ctx
        .symbol_iter()
        .find(|(name, _)| name.as_str() == "f")
        .map(|(name, info)| {
            (
                executor.ctx.symbol_identity_name(name, info).to_string(),
                info.arg_sorts.clone(),
                info.sort.clone(),
            )
        })
        .expect("declared f signature");
    assert_eq!(argument_sorts, vec![Sort::Bool]);
    assert_eq!(result_sort, Sort::Bool);

    let argument = executor.ctx.terms.true_term();
    let application =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named(&identity), vec![argument], Sort::Bool);
    let mut function_tables = HashMap::default();
    function_tables.insert(
        identity.clone(),
        vec![(vec!["true".to_string()], "true".to_string())],
    );
    let bv8 = Sort::bitvec(8);
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        function_tables,
        ..Default::default()
    });
    model.dt_pins.insert(application, EvalValue::Bool(true));
    model.projection_ufs = ProjectionUfModel::from_test_definitions([(
        Symbol::named(&identity),
        vec![bv8.clone(), bv8.clone()],
        bv8,
        1,
    )])
    .expect("the fault-injected projection is internally well typed");

    assert_eq!(
        executor.evaluate_term(&model, application),
        EvalValue::Unknown,
        "solver evaluation must not consult the matching table or dt pin"
    );
    let value_error = executor
        .term_value_string(&model, application)
        .expect_err("get-value must reject the conflicting signature");
    assert!(
        value_error.contains("model read requested"),
        "{value_error}"
    );

    executor.ctx.assertions = vec![application];
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    match executor.confirm_sat_with_independent_gate() {
        ay_model_check::GateVerdict::CannotConfirm { reason } => {
            assert!(reason.contains("inconsistent symbolic projection model"));
        }
        other => panic!("independent evaluation must fail closed, got {other:?}"),
    }
    assert_eq!(
        executor.model(),
        "(error \"checked projection model conflicts with current declaration signature\")"
    );

    executor.last_model_validated = true;
    assert!(
        !executor.complete_unconstrained_functions_for_output(&[]),
        "output completion must report the projection conflict"
    );
    assert!(
        !executor.last_model_validated,
        "completion conflict must revoke validation of the candidate model"
    );
    assert_eq!(
        executor
            .last_statistics
            .get_int("model_validation.projection_signature_conflict"),
        Some(1)
    );

    // Exercise the final post-gate completion boundary directly. A mismatched
    // symbolic model on an otherwise-vacuous query must not receive vacuous
    // SAT authority merely because no assertion forces an earlier read.
    executor.ctx.assertions.clear();
    let emitted = executor
        .emit_sat_verdict(SolveResult::Sat, &[])
        .expect("signature conflict degrades rather than raising an executor error");
    assert_eq!(emitted, SolveResult::Unknown);
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_model.is_none());
}

#[test]
fn projection_selected_argument_precedes_conflicting_term_keyed_state_everywhere() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let symbol = Symbol::named("projection_precedence");
    let first = executor.ctx.terms.mk_bitvec(BigInt::from(0x11u8), 8);
    let second = executor.ctx.terms.mk_bitvec(BigInt::from(0x22u8), 8);
    let application = executor
        .ctx
        .terms
        .mk_app(symbol.clone(), vec![first, second], bv8.clone());
    let assertion = executor.ctx.terms.mk_eq(application, second);

    let mut function_tables = HashMap::default();
    function_tables.insert(
        "projection_precedence".to_string(),
        vec![(
            vec!["#x11".to_string(), "#x22".to_string()],
            "#x33".to_string(),
        )],
    );
    let conflicting = EvalValue::BitVec {
        value: BigInt::from(0x44u8),
        width: 8,
    };
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        function_tables,
        ..Default::default()
    });
    model.dt_pins.insert(application, conflicting.clone());
    model.completed_values.insert(
        application,
        EvalValue::BitVec {
            value: BigInt::from(0x55u8),
            width: 8,
        },
    );
    model.dt_ground.insert(
        application,
        ay_model_check::ModelValue::bitvec(BigInt::from(0x66u8), 8),
    );

    // Seed the result memo with the stale application pin before installing
    // the test projection. This deliberately violates the immutable-session
    // contract to fault-inject the strongest possible precedence conflict.
    let _memo = EvalMemoSession::new();
    assert_eq!(executor.evaluate_term(&model, application), conflicting);
    model.projection_ufs = bv8_projection(symbol, 1);

    let selected = EvalValue::BitVec {
        value: BigInt::from(0x22u8),
        width: 8,
    };
    assert_eq!(
        executor.evaluate_term(&model, application),
        selected,
        "projection dispatch must precede a stale result memo and dt pin"
    );
    assert_eq!(
        executor
            .term_value_string(&model, application)
            .expect("the selected constant is printable"),
        "#x22",
        "get-value must ignore every application-keyed fallback"
    );

    executor.ctx.assertions = vec![assertion];
    executor.last_model = Some(model);
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
}

#[test]
fn projection_gate_reuses_outer_congruent_uf_value() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let projection_symbol = Symbol::named("graph_projection");
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 8);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 8);
    let dummy = executor.ctx.terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let equivalent_one =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), vec![zero, one], bv8.clone());
    let direct = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![one], bv8.clone());
    let equivalent =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("g"), vec![equivalent_one], bv8.clone());
    let projected = executor.ctx.terms.mk_app(
        projection_symbol.clone(),
        vec![dummy, equivalent],
        bv8.clone(),
    );
    let assertion = executor.ctx.terms.mk_app(
        Symbol::named("distinct"),
        vec![direct, projected],
        Sort::Bool,
    );

    let mut values = HashMap::default();
    values.insert(direct, BigInt::from(0x10u8));
    values.insert(equivalent, BigInt::from(0x20u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.projection_ufs = bv8_projection(projection_symbol, 1);
    executor.ctx.assertions = vec![assertion];
    executor.last_model = Some(model);

    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ModelViolates {
            assertion: violated
        } if violated == assertion
    ));
}

#[test]
fn projection_printer_rejects_malformed_model_without_panicking() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_BV)
        (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
    "#,
    )
    .expect("valid declarations");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declarations execute");

    let (identity, argument_sorts, result_sort) = executor
        .ctx
        .symbol_iter()
        .find(|(name, info)| name.as_str() == "f" && info.arg_sorts.len() == 2)
        .map(|(name, info)| {
            (
                executor.ctx.symbol_identity_name(name, info).to_string(),
                info.arg_sorts.clone(),
                info.sort.clone(),
            )
        })
        .expect("declared f signature");
    let mut model = empty_model();
    model.projection_ufs = ProjectionUfModel::from_malformed_test_definition_unchecked(
        Symbol::named(identity),
        argument_sorts,
        result_sort,
        2,
    );
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    assert_eq!(
        executor.model(),
        "(error \"malformed checked projection model\")",
        "the user-facing boundary must propagate a fallible invariant check"
    );

    let out_of_bounds = executor
        .format_projection_function("f", &[Sort::Bool], &Sort::Bool, 1)
        .expect_err("an out-of-bounds selected argument is malformed");
    assert!(out_of_bounds.contains("outside arity 1"), "{out_of_bounds}");

    let sort_mismatch = executor
        .format_projection_function("f", &[Sort::Int], &Sort::Bool, 0)
        .expect_err("a projection result must have the selected argument's sort");
    assert!(sort_mismatch.contains("not result sort"), "{sort_mismatch}");
}

#[test]
fn projection_printer_rejects_define_fun_source_kind_conflict() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_BV)
        (define-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8) x)
    "#,
    )
    .expect("valid definition");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("definition executes");

    let (identity, argument_sorts, result_sort) = executor
        .ctx
        .symbol_iter()
        .find(|(name, info)| name.as_str() == "f" && info.arg_sorts.len() == 2)
        .map(|(name, info)| {
            (
                executor.ctx.symbol_identity_name(name, info).to_string(),
                info.arg_sorts.clone(),
                info.sort.clone(),
            )
        })
        .expect("defined f signature");
    assert!(executor.ctx.is_defined_fun("f"));
    assert!(executor.ctx.adopted_macro_interp("f").is_none());

    // Fault-inject an impossible projection token over an authored definition.
    // Output must not let projection-first dispatch replace the define-fun body.
    let mut model = empty_model();
    model.projection_ufs = ProjectionUfModel::from_test_definitions([(
        Symbol::named(identity),
        argument_sorts,
        result_sort,
        1,
    )])
    .expect("well-typed fault-injected projection");
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    assert_eq!(
        executor.model(),
        "(error \"checked projection model conflicts with current source binding\")",
        "a projection token must not override define-fun"
    );
}

#[test]
fn projection_printer_rejects_adopted_macro_source_kind_conflict() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_BV)
        (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
    "#,
    )
    .expect("valid declaration");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declaration executes");

    let (identity, argument_sorts, result_sort) = executor
        .ctx
        .symbol_iter()
        .find(|(name, info)| name.as_str() == "f" && info.arg_sorts.len() == 2)
        .map(|(name, info)| {
            (
                executor.ctx.symbol_identity_name(name, info).to_string(),
                info.arg_sorts.clone(),
                info.sort.clone(),
            )
        })
        .expect("declared f signature");
    let body = executor.ctx.terms.mk_bitvec(BigInt::from(0x5au8), 8);
    let params = vec![
        ("x".to_string(), argument_sorts[0].clone()),
        ("y".to_string(), argument_sorts[1].clone()),
    ];
    assert!(executor
        .ctx
        .try_register_native_adopted_macro_interp("f", &params, body, false));
    assert!(executor.ctx.adopted_macro_interp("f").is_some());
    assert!(
        !executor.ctx.is_defined_fun("f"),
        "exercise the adopted-macro check independently of define-fun"
    );

    // Fault-inject a stale semantic projection token after the declaration
    // has acquired an authored interpretation. The real producer rejects
    // adopted macros; the printer must independently reject this impossible
    // combination instead of letting projection-first dispatch replace the
    // macro body.
    let mut model = empty_model();
    model.projection_ufs = ProjectionUfModel::from_test_definitions([(
        Symbol::named(identity),
        argument_sorts,
        result_sort,
        1,
    )])
    .expect("well-typed fault-injected projection");
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    assert_eq!(
        executor.model(),
        "(error \"checked projection model conflicts with current source binding\")",
        "a projection token is not positive free-UF provenance"
    );
}

#[test]
fn malformed_projection_sort_never_falls_through_to_term_keyed_state() {
    let mut executor = Executor::new();
    let symbol = Symbol::named("malformed_sort_projection");
    let one = executor.ctx.terms.mk_int(BigInt::one());
    let application = executor
        .ctx
        .terms
        .mk_app(symbol.clone(), vec![one], Sort::Bool);
    let mut model = empty_model();
    model.projection_ufs = ProjectionUfModel::from_malformed_test_definition_unchecked(
        symbol,
        vec![Sort::Int],
        Sort::Bool,
        0,
    );
    model.dt_pins.insert(application, EvalValue::Bool(true));

    assert_eq!(
        executor.evaluate_term(&model, application),
        EvalValue::Unknown,
        "a malformed projection must not fall through to its stale dt pin"
    );
    let error = executor
        .term_value_string(&model, application)
        .expect_err("get-value must fail closed on the same malformed projection");
    assert!(error.contains("application result sort"), "{error}");
}

#[test]
fn projection_get_model_and_get_value_round_trip_exactly() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_BV)
        (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
    "#,
    )
    .expect("valid declarations");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declarations execute");

    let (identity, result_sort) = executor
        .ctx
        .symbol_iter()
        .find(|(name, info)| name.as_str() == "f" && info.arg_sorts.len() == 2)
        .map(|(name, info)| {
            (
                executor.ctx.symbol_identity_name(name, info).to_string(),
                info.sort.clone(),
            )
        })
        .expect("declared f signature");

    let first = executor.ctx.terms.mk_bitvec(BigInt::from(0x11u8), 8);
    let second = executor.ctx.terms.mk_bitvec(BigInt::from(0x22u8), 8);
    let application = executor.ctx.terms.mk_app(
        Symbol::named(&identity),
        vec![first, second],
        result_sort.clone(),
    );

    // Seed a conflicting finite sample as stale prior-result state. Checked
    // installation must replace the whole ground model, not retain this row.
    let mut function_tables = HashMap::default();
    function_tables.insert(
        identity.clone(),
        vec![(
            vec!["#x11".to_string(), "#x22".to_string()],
            "#x33".to_string(),
        )],
    );
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        function_tables,
        ..Default::default()
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    executor.last_model_validated = true;

    let (checked, root) = checked_bv8_projection(&mut executor.ctx.terms, Symbol::named(&identity));
    executor.ctx.assertions = vec![root];
    executor
        .install_checked_projection_model(&checked, &[root])
        .expect("only sealed checker output crosses the model boundary");
    assert!(
        executor.last_result.is_none(),
        "installing model data must revoke the prior SAT verdict"
    );
    assert!(
        !executor.last_model_validated,
        "installing model data must revoke prior validation evidence"
    );
    assert!(
        executor
            .last_model
            .as_ref()
            .expect("installed model")
            .euf_model
            .is_none(),
        "checked installation must discard stale finite-table state"
    );
    assert_eq!(
        executor.model(),
        "(error \"model is not available\")",
        "the installed model must not inherit output authority from stale SAT"
    );

    let model = executor.last_model.as_ref().expect("installed model");
    assert_eq!(
        executor
            .term_value_string(model, application)
            .expect("projection application has the selected argument's value"),
        "#x22"
    );

    // Model-formatting coverage below represents a later SAT funnel granting a
    // fresh verdict. The installer itself deliberately cannot grant one.
    executor.last_result = Some(SolveResult::Sat);
    let printed = executor.model();
    assert_eq!(
        printed,
        "(model\n  (define-fun f ((__ay_projection_arg_0 (_ BitVec 8)) (__ay_projection_arg_1 (_ BitVec 8))) (_ BitVec 8)\n    __ay_projection_arg_1)\n)"
    );
    assert!(
        !printed.contains("#x33"),
        "finite-table value leaked: {printed}"
    );
    assert!(!printed.contains("ite"), "finite table leaked: {printed}");

    // Replay the emitted definition as ordinary SMT-LIB and check a point that
    // was not justified by a table lookup. This pins the renderer's lambda
    // binding and selected parameter, not merely its text shape.
    let definition = printed
        .strip_prefix("(model\n")
        .and_then(|text| text.strip_suffix("\n)"))
        .expect("model response wrapper");
    let replay =
        format!("(set-logic QF_BV)\n{definition}\n(assert (= (f #x44 #x55) #x55))\n(check-sat)");
    let replay_commands = parse(&replay).expect("emitted definition parses");
    let mut replay_executor = Executor::new();
    let outputs = replay_executor
        .execute_all(&replay_commands)
        .expect("emitted definition executes");
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn projection_install_revokes_sat_certificate_and_builds_missing_model() {
    let mut executor = Executor::new();
    let emitted = executor
        .emit_sat_verdict(SolveResult::Sat, &[])
        .expect("the empty formula has a vacuous model");
    assert_eq!(emitted, SolveResult::Sat);
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());

    let (checked, root) =
        checked_bv8_projection(&mut executor.ctx.terms, Symbol::named("checked_f"));
    executor.ctx.assertions = vec![root];
    // Simulate a certificate-only quantified solve with no ground model while
    // deliberately retaining stale evidence from the preceding result.
    executor.last_model = None;

    executor
        .install_checked_projection_model(&checked, &[root])
        .expect("checked model installation succeeds");
    assert!(executor.last_result.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_model.is_some());
}

#[test]
fn projection_install_rejects_noncurrent_roots_without_mutation() {
    let mut executor = Executor::new();
    let emitted = executor
        .emit_sat_verdict(SolveResult::Sat, &[])
        .expect("the empty formula has a vacuous model");
    assert_eq!(emitted, SolveResult::Sat);

    let (checked, root) =
        checked_bv8_projection(&mut executor.ctx.terms, Symbol::named("same_store_f"));
    let current_root = executor.ctx.terms.true_term();
    executor.ctx.assertions = vec![current_root];

    let error = executor
        .install_checked_projection_model(&checked, &[root])
        .expect_err("caller roots cannot substitute for the executor's live query");
    assert!(matches!(
        error,
        crate::executor::model::projection_uf::ProjectionUfModelError::LiveQueryMismatch
    ));

    // The checked snapshot and caller roots agree with each other, but not
    // with the live query. Rejection must precede every result-state mutation.
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());
    assert!(executor.last_model.is_some());
}

#[test]
fn projection_install_rejects_foreign_snapshot_without_mutation() {
    let mut executor = Executor::new();
    let emitted = executor
        .emit_sat_verdict(SolveResult::Sat, &[])
        .expect("the empty formula has a vacuous model");
    assert_eq!(emitted, SolveResult::Sat);
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());

    let mut stale_table = HashMap::default();
    stale_table.insert(
        "stale".to_string(),
        vec![(vec!["#x00".to_string()], "#x01".to_string())],
    );
    executor
        .last_model
        .as_mut()
        .expect("vacuous model exists")
        .euf_model = Some(EufModel {
        function_tables: stale_table,
        ..Default::default()
    });

    let mut foreign_terms = TermStore::new();
    let (foreign_checked, foreign_root) =
        checked_bv8_projection(&mut foreign_terms, Symbol::named("foreign_f"));
    // Make the caller roots equal the live query so the independent frozen
    // term-graph comparison, rather than the query-binding check, rejects it.
    executor.ctx.assertions = vec![foreign_root];
    let error = executor
        .install_checked_projection_model(&foreign_checked, &[foreign_root])
        .expect_err("a certificate from another term graph must fail closed");
    assert!(matches!(
        error,
        crate::executor::model::projection_uf::ProjectionUfModelError::SnapshotMismatch
    ));

    // Snapshot rejection happens before every state mutation.
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());
    assert!(executor
        .last_model
        .as_ref()
        .and_then(|model| model.euf_model.as_ref())
        .is_some_and(|euf| euf.function_tables.contains_key("stale")));
}

#[test]
fn projection_evaluator_and_get_value_peeling_are_bounded_without_native_recursion() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let symbol = Symbol::named("deep_projection");
    let fixed = executor.ctx.terms.mk_bitvec(BigInt::from(0x11u8), 8);
    let mut nested = executor.ctx.terms.mk_bitvec(BigInt::from(0x22u8), 8);
    // One more than the production peel limit. The formatter must return a
    // controlled error, not recurse through native stack frames.
    for _ in 0..=4096 {
        nested = executor
            .ctx
            .terms
            .mk_app(symbol.clone(), vec![fixed, nested], bv8.clone());
    }
    let mut model = empty_model();
    model.projection_ufs = bv8_projection(symbol, 1);

    assert_eq!(
        executor.evaluate_term(&model, nested),
        EvalValue::Unknown,
        "the evaluator must fail closed at the shared projection-link limit"
    );

    let error = executor
        .term_value_string(&model, nested)
        .expect_err("an adversarially deep projection chain fails closed");
    assert!(error.contains("4096-link evaluation limit"), "{error}");
}
