// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::model::{independent_gate::IndependentModelView, CertifiedConstInterpWitness};
use ay_model_check::{EvalOutcome, Evaluator, ModelValue};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::sync::Arc;

fn loaded(script: &str) -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(script).unwrap())
        .unwrap();
    exec
}

fn binding(exec: &Executor, name: &str) -> ay_frontend::CheckedProjectionBinding {
    let info = exec.ctx.symbol_info(name).unwrap();
    exec.ctx
        .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
            symbol: Symbol::named(exec.ctx.symbol_identity_name(name, info)),
            parameter_sorts: info.arg_sorts.clone(),
            result_sort: info.sort.clone(),
        })
        .unwrap()
}

fn seq_sort() -> Sort {
    Sort::Seq(Box::new(Sort::Int))
}

fn unit(exec: &mut Executor, value: i64) -> TermId {
    let value = exec.ctx.terms.mk_int(BigInt::from(value));
    exec.ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), [value], seq_sort())
}

fn concat_model(exec: &mut Executor) -> Model {
    let left = exec.ctx.terms.mk_fresh_var("__ay_body_left", seq_sort());
    let right = exec.ctx.terms.mk_fresh_var("__ay_body_right", seq_sort());
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), [left, right], seq_sort());
    let body = CertifiedExpressionBody::capture(&exec.ctx, vec![left, right], root).unwrap();
    let mut model = Model::empty();
    model
        .install_certified_const_interps(
            &exec.ctx,
            vec![(
                binding(exec, "f"),
                CertifiedConstInterpWitness::Expression(Arc::new(body)),
            )],
        )
        .unwrap();
    model
}

#[test]
fn sequence_expression_reads_are_pointwise_nested_and_model_owned() {
    let mut exec = loaded("(set-logic ALL) (declare-fun f ((Seq Int) (Seq Int)) (Seq Int))");
    let model = concat_model(&mut exec);
    let one = unit(&mut exec, 1);
    let two = unit(&mut exec, -2);
    let first = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [one, two], seq_sort());
    let second = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [two, one], seq_sort());
    let nested = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [first, one], seq_sort());
    for (term, expected) in [
        (first, vec![1, -2]),
        (second, vec![-2, 1]),
        (nested, vec![1, -2, 1]),
    ] {
        let native = EvalValue::Seq(
            expected
                .iter()
                .map(|&value| EvalValue::Rational(BigRational::from_integer(BigInt::from(value))))
                .collect(),
        );
        assert_eq!(exec.evaluate_term(&model, term), native);
        let view = IndependentModelView::new(&exec, &model);
        let result = Evaluator::new(&exec.ctx.terms, &view).evaluate(term);
        let EvalOutcome::Value(ModelValue::Seq(elements)) = result else {
            panic!("expected an independently evaluated sequence, got {result:?}");
        };
        let integers: Option<Vec<_>> = elements
            .into_iter()
            .map(|element| match element {
                ModelValue::Int(value) => Some(value),
                _ => None,
            })
            .collect();
        assert_eq!(
            integers,
            Some(expected.into_iter().map(BigInt::from).collect())
        );
    }
    // Cloning semantic model data preserves the body, without borrowing a
    // mutable producer-side interpretation or a previous argument environment.
    assert_eq!(
        exec.evaluate_term(&model.clone(), second),
        exec.evaluate_term(&model, second)
    );
    let mut contaminated = model;
    contaminated
        .dt_pins
        .insert(first, EvalValue::Seq(Vec::new()));
    assert_eq!(
        exec.evaluate_term(&contaminated, first),
        EvalValue::Seq(vec![
            EvalValue::Rational(BigRational::from_integer(BigInt::from(1))),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(-2))),
        ]),
        "an ambient application pin must not override the printed function body"
    );
}

#[test]
fn expression_capture_refuses_ambient_heads_variables_and_malformed_native_types() {
    let mut exec = loaded("(set-logic ALL) (declare-fun g ((Seq Int)) (Seq Int))");
    let parameter = exec
        .ctx
        .terms
        .mk_fresh_var("__ay_body_parameter", seq_sort());
    let ambient = exec.ctx.terms.mk_fresh_var("ambient", seq_sort());
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], ambient).is_none());
    let recursive = exec
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [parameter], seq_sort());
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], recursive).is_none());
    let mistyped = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), [parameter], Sort::Bool);
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], mistyped).is_none());
    assert!(
        CertifiedExpressionBody::capture(&exec.ctx, vec![parameter, parameter], parameter)
            .is_none()
    );
    let integer = exec.ctx.terms.mk_var("same_parameter", Sort::Int);
    let boolean = exec.ctx.terms.mk_var("same_parameter", Sort::Bool);
    assert_ne!(integer, boolean);
    let body =
        CertifiedExpressionBody::capture(&exec.ctx, vec![integer, boolean], integer).unwrap();
    assert_eq!(
        exec.format_model_expression(&body),
        "x!0",
        "formal slots are alpha-renamed independently of their source spelling"
    );
}

#[test]
fn expression_rendering_is_hygienic_and_expansion_is_bounded() {
    let mut exec = Executor::new();
    let parameter = exec.ctx.terms.mk_var("seq.++", seq_sort());
    let empty = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.empty"), [], seq_sort());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), [parameter, empty], seq_sort());
    let body = CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], concat).unwrap();
    assert_eq!(
        exec.format_model_expression(&body),
        "(seq.++ x!0 (as seq.empty (Seq Int)))"
    );

    let mut doubled = parameter;
    for _ in 0..10 {
        doubled = exec
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), [doubled, doubled], seq_sort());
    }
    assert!(
        CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], doubled).is_none(),
        "eleven compact nodes must not admit a 2047-node expanded model body"
    );

    let mut deep = parameter;
    for _ in 0..MAX_BODY_DEPTH {
        deep = exec
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), [deep, empty], seq_sort());
    }
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], deep).is_none());
}

#[test]
fn expression_capture_and_currentness_refuse_a_non_theory_builtin_owner() {
    let mut exec = Executor::new();
    let parameter = exec.ctx.terms.mk_fresh_var("s", seq_sort());
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), [parameter], Sort::Int);
    let body = CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], root).unwrap();
    assert!(body.is_current(&exec.ctx, &[seq_sort()], &Sort::Int));
    let forged = exec.ctx.terms.mk_fresh_named_var("seq.len", Sort::Int);
    exec.ctx
        .register_symbol("seq.len".to_string(), forged, Sort::Int);
    assert_eq!(
        exec.ctx.effective_declaration_kind(
            exec.ctx
                .symbol_info_by_identity("seq.len")
                .unwrap()
                .declaration_id()
        ),
        Some(DeclarationKind::Uninterpreted)
    );
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], root).is_none());
    assert!(!body.is_current(&exec.ctx, &[seq_sort()], &Sort::Int));
}

#[test]
fn expression_capture_and_currentness_refuse_raw_uf_metadata_without_a_symbol_entry() {
    let mut exec = Executor::new();
    let parameter = exec.ctx.terms.mk_fresh_var("s", seq_sort());
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), [parameter], Sort::Int);
    let body = CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], root).unwrap();
    let birth = exec.ctx.terms.entry_stamp(root);
    assert!(exec.ctx.symbol_info_by_identity("seq.len").is_none());
    exec.context_mut()
        .terms
        .register_declared_function("seq.len");
    assert!(exec.ctx.symbol_info_by_identity("seq.len").is_none());
    assert_eq!(
        exec.ctx.terms.entry_stamp(root),
        birth,
        "only metadata changed"
    );
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], root).is_none());
    assert!(!body.is_current(&exec.ctx, &[seq_sort()], &Sort::Int));
}

#[test]
fn expression_capture_rejects_a_well_sorted_cycle_but_accepts_shared_subterms() {
    let mut exec = Executor::new();
    let parameter = exec
        .ctx
        .terms
        .mk_fresh_var("__ay_body_parameter", seq_sort());
    let future = TermId::new(u32::try_from(exec.ctx.terms.len()).unwrap());
    let cycle =
        exec.ctx
            .terms
            .mk_app_structural(Symbol::named("seq.++"), [future, parameter], seq_sort());
    assert_eq!(
        cycle, future,
        "the fixture must create an actual core self edge"
    );
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], cycle).is_none());

    let shared = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), [parameter, parameter], seq_sort());
    assert!(CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], shared).is_some());
}

#[test]
fn expression_installation_rejects_signature_change_without_clobbering_model() {
    let mut exec = loaded(
        "(set-logic ALL)
        (declare-fun f ((Seq Int) (Seq Int)) (Seq Int))
        (declare-fun integer_head (Int) Int)",
    );
    let mut model = concat_model(&mut exec);
    let parameter = exec
        .ctx
        .terms
        .mk_fresh_var("__ay_body_parameter", seq_sort());
    let body = CertifiedExpressionBody::capture(&exec.ctx, vec![parameter], parameter).unwrap();
    assert!(model
        .install_certified_const_interps(
            &exec.ctx,
            vec![(
                binding(&exec, "integer_head"),
                CertifiedConstInterpWitness::Expression(Arc::new(body))
            )],
        )
        .is_none());
    let one = unit(&mut exec, 1);
    let point = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [one, one], seq_sort());
    assert_eq!(
        exec.evaluate_term(&model, point),
        EvalValue::Seq(vec![
            EvalValue::Rational(BigRational::from_integer(BigInt::from(1))),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(1))),
        ])
    );
}

#[test]
fn popped_or_foreign_same_spelling_declaration_cannot_reuse_expression_body() {
    let mut exec = loaded(
        "(set-logic ALL) (push 1)
        (declare-fun f ((Seq Int) (Seq Int)) (Seq Int))",
    );
    let model = concat_model(&mut exec);
    exec.execute_all(
        &ay_frontend::parse(
            "(pop 1)
        (declare-fun f ((Seq Int) (Seq Int)) (Seq Int))",
        )
        .unwrap(),
    )
    .unwrap();
    let one = unit(&mut exec, 1);
    let point = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [one, one], seq_sort());
    assert_eq!(exec.evaluate_term(&model, point), EvalValue::Unknown);
    let view = IndependentModelView::new(&exec, &model);
    assert!(matches!(
        Evaluator::new(&exec.ctx.terms, &view).evaluate(point),
        EvalOutcome::Unevaluable(_)
    ));

    let mut foreign = loaded("(set-logic ALL) (declare-fun f ((Seq Int) (Seq Int)) (Seq Int))");
    let one = unit(&mut foreign, 1);
    let point = foreign
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [one, one], seq_sort());
    assert_eq!(foreign.evaluate_term(&model, point), EvalValue::Unknown);
}
