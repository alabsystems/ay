// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::{seed_eval_memo_for_test, EvalMemoSession, EvalValue, Model};
use crate::executor::theories::fp::flatten_reads::{plan as flatten_plan, FlattenPlan};
use crate::executor_types::SolveResult;
use num_bigint::BigInt;

fn executor() -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(set-logic ALL)
                 (set-option :produce-models true)
                 (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
                 (declare-fun g ((_ BitVec 8)) Bool)
                 (declare-fun h ((_ BitVec 8)) Bool)
                 (assert (g (select a #x00)))
                 (assert (not (g (select a #x01))))",
            )
            .unwrap(),
        )
        .unwrap();
    executor
}

fn fixture() -> (Executor, FlattenPlan, BoolUfTransport) {
    let mut executor = executor();
    let roots = executor.ctx.assertions.clone();
    let plan = flatten_plan(&mut executor.ctx.terms, &roots).unwrap();
    let mut transport = plan.capture_bool_uf_transport(&mut executor).unwrap();
    transport.pairs.sort_by_key(|pair| pair.original);
    assert_eq!(transport.pairs.len(), 2);
    assert_eq!(transport.bindings.len(), 1);
    let mut model = Model::empty();
    model.sat_model = vec![true, false];
    for (index, pair) in transport.pairs.iter().enumerate() {
        assert_ne!(pair.original, pair.image);
        model.term_to_var.insert(pair.image, index as u32);
    }
    model.bv_model = Some(ay_bv::BvModel {
        values: plan
            .cells
            .iter()
            .enumerate()
            .map(|(index, cell)| (cell.fresh, BigInt::from(7 + index * 2)))
            .collect(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);
    (executor, plan, transport)
}

fn applications(executor: &Executor, transport: &BoolUfTransport) -> Vec<(TermId, Vec<TermId>)> {
    transport
        .pairs
        .iter()
        .map(|pair| {
            let TermData::App(_, args) = executor.ctx.terms.get(pair.original) else {
                panic!("original UF application");
            };
            (pair.original, args.clone())
        })
        .collect()
}

fn argument_value(executor: &Executor, argument: TermId) -> BigInt {
    match executor.evaluate_term(executor.last_model.as_ref().unwrap(), argument) {
        EvalValue::BitVec { value, width: 8 } => value,
        other => panic!("expected original array argument value, got {other:?}"),
    }
}

#[test]
fn exact_rewrite_values_reach_original_apps_and_printed_rows() {
    let (mut executor, plan, transport) = fixture();
    assert!(executor.attach_flattened_array_model(&plan.cells));
    let apps = applications(&executor, &transport);
    let model = executor.last_model.as_mut().unwrap();
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    executor.last_model_validated = true;
    let _memo = EvalMemoSession::new();
    seed_eval_memo_for_test(apps[0].0, EvalValue::Unknown);
    assert!(matches!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), apps[0].0),
        EvalValue::Unknown
    ));
    assert!(transport.install(&mut executor));
    let model = executor.last_model.as_ref().unwrap();
    assert!(!executor.last_model_validated);
    assert!(!model.carries_quantified_confirmation(&confirmation));
    assert!(!model.carries_quantified_grant_model(&grant));
    assert!(
        model.euf_model.is_none(),
        "no fabricated EUF interpretation"
    );
    for (index, &(app, _)) in apps.iter().enumerate() {
        assert_eq!(model.term_to_var[&app], index as u32);
        assert!(
            matches!(executor.evaluate_term(model, app), EvalValue::Bool(value) if value == (index == 0))
        );
    }
    assert_ne!(
        argument_value(&executor, apps[0].1[0]),
        argument_value(&executor, apps[1].1[0]),
    );
    // Exercise the real get-model printer on this synthetic candidate. Setting
    // the output precondition is test setup, not a solver verdict or a seal.
    executor.last_result = Some(SolveResult::Sat);
    let printed = executor.model();
    assert!(!printed.contains("(error"), "{printed}");
    assert!(printed.contains("(define-fun g "), "{printed}");
    assert!(
        printed.contains("true") && printed.contains("false"),
        "{printed}"
    );
}

#[test]
fn missing_invalid_and_conflicting_assignments_refuse_atomically() {
    for case in 0..4 {
        let (mut executor, _, transport) = fixture();
        let first = &transport.pairs[0];
        let last = &transport.pairs[1];
        let model = executor.last_model.as_mut().unwrap();
        match case {
            0 => {
                model.term_to_var.remove(&last.image);
            }
            1 => {
                model.term_to_var.insert(last.image, u32::MAX);
            }
            2 => {
                model.term_to_var.insert(last.original, 0);
            }
            _ => {
                model.term_to_var.insert(last.original, u32::MAX);
            }
        }
        let before = model.term_to_var.clone();
        let confirmation = model.seal_quantified_confirmation();
        let grant = model.seal_quantified_grant_model();
        executor.last_model_validated = true;
        assert!(!transport.install(&mut executor), "case {case}");
        let model = executor.last_model.as_ref().unwrap();
        assert_eq!(model.term_to_var, before);
        assert!(!model.term_to_var.contains_key(&first.original));
        assert!(model.carries_quantified_confirmation(&confirmation));
        assert!(model.carries_quantified_grant_model(&grant));
        assert!(executor.last_model_validated);
    }
}

#[test]
fn agreeing_original_assignment_keeps_its_existing_index() {
    let (mut executor, _, transport) = fixture();
    let original = transport.pairs[0].original;
    let model = executor.last_model.as_mut().unwrap();
    model.sat_model.push(true);
    model.term_to_var.insert(original, 2);
    assert!(transport.install(&mut executor));
    assert_eq!(
        executor.last_model.as_ref().unwrap().term_to_var[&original],
        2
    );
}

#[test]
fn malformed_images_and_unproven_argument_maps_are_rejected() {
    for case in 0..6 {
        let (mut executor, plan, transport) = fixture();
        let pair = &transport.pairs[0];
        let TermData::App(symbol, args) = executor.ctx.terms.get(pair.image).clone() else {
            panic!("rewritten application");
        };
        let malformed = match case {
            0 => executor
                .ctx
                .terms
                .mk_app(Symbol::named("h"), args, Sort::Bool),
            1 => executor.ctx.terms.mk_app(symbol, vec![], Sort::Bool),
            2 => executor.ctx.terms.mk_app(symbol, args, Sort::bitvec(8)),
            3 => {
                let unrelated = executor.ctx.terms.mk_bitvec(BigInt::from(42), 8);
                executor
                    .ctx
                    .terms
                    .mk_app(symbol, vec![unrelated], Sort::Bool)
            }
            4 => executor.ctx.terms.true_term(),
            _ => TermId::SENTINEL,
        };
        let mut bad = plan.rewrites.clone();
        bad.insert(pair.original, malformed);
        assert!(
            BoolUfTransport::capture(&mut executor, &bad).is_none(),
            "case {case}"
        );
    }
}

#[test]
fn builtins_are_not_transported_and_undeclared_heads_are_not_ufs() {
    let mut executor = executor();
    let roots = executor.ctx.assertions.clone();
    let first = roots[0];
    let TermData::App(_, args) = executor.ctx.terms.get(first).clone() else {
        panic!("fixture application");
    };
    let zero = executor.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    let predicate =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvult"), vec![args[0], zero], Sort::Bool);
    let plan = flatten_plan(&mut executor.ctx.terms, &[predicate]).unwrap();
    let transport = plan.capture_bool_uf_transport(&mut executor).unwrap();
    assert!(transport.pairs.is_empty());
    let unknown = executor
        .ctx
        .terms
        .mk_app(Symbol::named("not_declared"), args, Sort::Bool);
    let plan = flatten_plan(&mut executor.ctx.terms, &[unknown]).unwrap();
    assert!(plan.capture_bool_uf_transport(&mut executor).is_none());
}

#[test]
fn recycled_term_slots_and_changed_source_scope_are_rejected() {
    let mut executor = executor();
    let checkpoint = executor.ctx.terms.rollback_checkpoint();
    let roots = executor.ctx.assertions.clone();
    let plan = flatten_plan(&mut executor.ctx.terms, &roots).unwrap();
    let transport = plan.capture_bool_uf_transport(&mut executor).unwrap();
    executor.ctx.terms.rollback_to(checkpoint);
    let _replacement = flatten_plan(&mut executor.ctx.terms, &roots).unwrap();
    let mut model = Model::empty();
    model.sat_model = vec![true];
    for pair in &transport.pairs {
        assert_ne!(
            executor.ctx.terms.entry_stamp(pair.image),
            Some(pair.image_stamp)
        );
        model.term_to_var.insert(pair.image, 0);
    }
    executor.last_model = Some(model);
    assert!(!transport.install(&mut executor));

    let (mut executor, _, transport) = fixture();
    let model = executor.last_model.take().unwrap();
    executor
        .execute_all(&ay_frontend::parse("(push 1) (pop 1)").unwrap())
        .unwrap();
    executor.last_model = Some(model);
    let before = executor.last_model.as_ref().unwrap().term_to_var.clone();
    assert!(!transport.install(&mut executor));
    assert_eq!(executor.last_model.as_ref().unwrap().term_to_var, before);
}

#[test]
fn foreign_term_arena_and_cancellation_leave_no_aliases() {
    let (mut executor, _, transport) = fixture();
    let (foreign, _, _) = fixture();
    executor.ctx.terms = foreign.ctx.terms;
    assert!(!transport.install(&mut executor));
    let (mut executor, _, transport) = fixture();
    let before = executor.last_model.as_ref().unwrap().term_to_var.clone();
    executor.solve_interrupt = Some(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    assert!(!transport.install(&mut executor));
    assert_eq!(executor.last_model.as_ref().unwrap().term_to_var, before);
}

#[test]
fn transport_does_not_certify_conflicting_function_points() {
    let (mut executor, plan, transport) = fixture();
    let model = executor.last_model.as_mut().unwrap();
    for value in model.bv_model.as_mut().unwrap().values.values_mut() {
        *value = BigInt::from(7);
    }
    assert!(executor.attach_flattened_array_model(&plan.cells));
    assert!(transport.install(&mut executor));
    let apps = applications(&executor, &transport);
    assert_eq!(
        argument_value(&executor, apps[0].1[0]),
        argument_value(&executor, apps[1].1[0]),
    );
    let model = executor.last_model.as_ref().unwrap();
    assert!(matches!(
        executor.evaluate_term(model, apps[0].0),
        EvalValue::Bool(true)
    ));
    assert!(matches!(
        executor.evaluate_term(model, apps[1].0),
        EvalValue::Bool(false)
    ));
    // The existing printer's ground-application pipeline must refuse to emit
    // this contradictory function, even with its output precondition staged.
    executor.last_result = Some(SolveResult::Sat);
    let printed = executor.model();
    assert!(!printed.contains("(error"), "{printed}");
    assert!(!printed.contains("(define-fun g "), "{printed}");
    assert!(!executor.last_model_validated);
}

#[test]
fn oversized_names_and_recursive_argument_sorts_refuse_capture() {
    let (mut executor, plan, transport) = fixture();
    let pair = &transport.pairs[0];
    let TermData::App(_, args) = executor.ctx.terms.get(pair.original).clone() else {
        panic!("original application");
    };
    let TermData::App(_, images) = executor.ctx.terms.get(pair.image).clone() else {
        panic!("image application");
    };
    let symbol = Symbol::named("n".repeat(MAX_IDENTITY_BYTES + 1));
    let original = executor.ctx.terms.mk_app(symbol.clone(), args, Sort::Bool);
    let image = executor.ctx.terms.mk_app(symbol, images, Sort::Bool);
    let mut rewrites = plan.rewrites.clone();
    rewrites.insert(original, image);
    assert!(BoolUfTransport::capture(&mut executor, &rewrites).is_none());

    let sort = Sort::array(Sort::bitvec(8), Sort::array(Sort::bitvec(8), Sort::Bool));
    let arg = executor.ctx.terms.mk_var("recursive_arg", sort.clone());
    let arg_image = executor.ctx.terms.mk_var("recursive_image", sort);
    let original = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![arg], Sort::Bool);
    let image = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![arg_image], Sort::Bool);
    let rewrites = [(arg, arg_image), (original, image)].into_iter().collect();
    assert!(BoolUfTransport::capture(&mut executor, &rewrites).is_none());
}

#[test]
fn redeclaration_rejects_stale_transport_without_widening_private_name_reader() {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(set-logic ALL)
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
         (push 1) (declare-fun g ((_ BitVec 8)) Bool)
         (assert (g (select a #x00)))",
            )
            .unwrap(),
        )
        .unwrap();
    let roots = executor.ctx.assertions.clone();
    let plan = flatten_plan(&mut executor.ctx.terms, &roots).unwrap();
    let old = plan.capture_bool_uf_transport(&mut executor).unwrap();
    assert_eq!(old.pairs.len(), 1);
    executor
        .execute_all(
            &ay_frontend::parse(
                "(pop 1) (declare-fun g ((_ BitVec 8)) Bool)
         (assert (g (select a #x00)))",
            )
            .unwrap(),
        )
        .unwrap();
    let mut model = Model::empty();
    model.sat_model = vec![true];
    model.term_to_var.insert(old.pairs[0].image, 0);
    executor.last_model = Some(model);
    assert!(!old.install(&mut executor));
    let roots = executor.ctx.assertions.clone();
    let plan = flatten_plan(&mut executor.ctx.terms, &roots).unwrap();
    let info = executor.ctx.symbol_info("g").unwrap();
    let identity = executor.ctx.symbol_identity_name("g", info);
    assert!(identity.starts_with("__ay_"));
    // The source binding is genuinely ordinary, but the pre-existing Bool
    // reader refuses this private spelling. Transport must not widen it.
    assert!(executor
        .ctx
        .check_projection_declaration(&ProjectionBindingRequest {
            symbol: Symbol::named(identity),
            parameter_sorts: info.arg_sorts.clone(),
            result_sort: info.sort.clone(),
        })
        .is_ok());
    assert!(Executor::is_known_theory_symbol(identity));
    assert!(plan
        .capture_bool_uf_transport(&mut executor)
        .unwrap()
        .pairs
        .is_empty());
}
