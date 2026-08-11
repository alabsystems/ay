// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn quantified_certificate_pin_package_rejects_orphaned_term() {
    let mut exec = Executor::new();
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let orphan = exec.ctx.terms.mk_var("orphan", Sort::Bool);
    exec.ctx.terms.rollback_to(checkpoint);

    let mut model = empty_model();
    assert!(
        model
            .install_quantified_certificate_pins(
                &exec.ctx.terms,
                [(orphan, EvalValue::Bool(true))],
            )
            .is_none(),
        "a pin package naming a dead term entry must fail closed"
    );
    assert_eq!(model.quantified_certificate_pin_count(), 0);
}

#[test]
fn quantified_certificate_pin_rejects_reused_term_slot() {
    let mut exec = Executor::new();
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let original = exec.ctx.terms.mk_var("original", Sort::Bool);
    let original_stamp = exec.ctx.terms.entry_stamp(original);
    let mut model = empty_model();
    model
        .install_quantified_certificate_pins(&exec.ctx.terms, [(original, EvalValue::Bool(true))])
        .expect("live original pin package");
    assert_eq!(exec.evaluate_term(&model, original), EvalValue::Bool(true));

    exec.ctx.terms.rollback_to(checkpoint);
    let replacement = exec.ctx.terms.mk_var("replacement", Sort::Bool);
    assert_eq!(
        replacement, original,
        "rollback must reuse the numeric slot"
    );
    assert_ne!(
        exec.ctx.terms.entry_stamp(replacement),
        original_stamp,
        "the replacement must have a distinct entry identity"
    );
    assert_eq!(
        exec.evaluate_term(&model, replacement),
        EvalValue::Unknown,
        "the old pin and its pre-rollback memo value must not apply to the reused slot"
    );
}

#[test]
fn quantified_certificate_pins_belong_to_passed_model_not_executor_state() {
    let mut exec = Executor::new();
    let predicate = exec
        .ctx
        .terms
        .mk_app(Symbol::named("p"), Vec::new(), Sort::Bool);

    let mut model_a = empty_model();
    model_a
        .install_quantified_certificate_pins(&exec.ctx.terms, [(predicate, EvalValue::Bool(true))])
        .expect("model A pin package");
    let model_b = empty_model();

    assert_eq!(
        exec.evaluate_term(&model_a, predicate),
        EvalValue::Bool(true)
    );
    assert_ne!(
        exec.evaluate_term(&model_b, predicate),
        EvalValue::Bool(true),
        "an orphaned model-A pin must not affect evaluation of model B"
    );

    let mut model_b = model_b;
    model_b
        .install_quantified_certificate_pins(&exec.ctx.terms, [(predicate, EvalValue::Bool(false))])
        .expect("model B pin package");
    assert_eq!(
        exec.evaluate_term(&model_b, predicate),
        EvalValue::Bool(false),
        "the passed model's own pin must win even after model A populated the TermId memo"
    );
    assert_eq!(
        exec.evaluate_term(&model_a, predicate),
        EvalValue::Bool(true),
        "replacing the evaluated model must not mutate model A's package"
    );
}

#[test]
fn quantified_certificate_pin_package_currentness_checks_every_entry_and_scope() {
    let mut exec = Executor::new();
    let stable = exec.ctx.terms.mk_var("stable", Sort::Bool);
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let scoped = exec.ctx.terms.mk_var("scoped", Sort::Bool);
    let mut model = empty_model();
    model
        .install_quantified_certificate_pins(
            &exec.ctx.terms,
            [
                (stable, EvalValue::Bool(true)),
                (scoped, EvalValue::Bool(false)),
            ],
        )
        .expect("two live ground pins");

    assert!(model.quantified_certificate_pins_are_current(&exec.ctx.terms));
    let _suffix = exec.ctx.terms.mk_var("append-only-suffix", Sort::Bool);
    assert!(
        model.quantified_certificate_pins_are_current(&exec.ctx.terms),
        "unrelated append-only term growth preserves every pinned entry"
    );

    let current_in_scope =
        dt_model::with_scoped_term_override(scoped, EvalValue::Bool(true), || {
            model.quantified_certificate_pins_are_current(&exec.ctx.terms)
        });
    assert!(
        !current_in_scope,
        "an ambient pin package is not current when any pin depends on an active binder"
    );
    assert!(model.quantified_certificate_pins_are_current(&exec.ctx.terms));

    exec.ctx.terms.rollback_to(checkpoint);
    let replacement = exec.ctx.terms.mk_var("replacement", Sort::Bool);
    assert_eq!(
        replacement, scoped,
        "rollback must reuse the stale pin's numeric slot"
    );
    assert!(
        !model.quantified_certificate_pins_are_current(&exec.ctx.terms),
        "one stale entry invalidates the whole pin package even while another remains live"
    );
}

#[test]
fn certified_total_uf_installs_revoke_quantified_grant_only_on_commit() {
    let mut model = empty_model();
    let rejected_epoch = model.seal_quantified_grant_model();
    assert!(
        model
            .install_certified_total_uf(
                String::new(),
                vec![Sort::Int],
                Sort::Int,
                Vec::new(),
                EvalValue::Rational(BigRational::zero()),
            )
            .is_none(),
        "an empty UF name is not a valid certified interpretation"
    );
    assert!(
        model.carries_quantified_grant_model(&rejected_epoch),
        "a rejected install must leave the prior model identity intact"
    );

    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            Vec::new(),
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed scalar total UF");
    assert!(
        !model.carries_quantified_grant_model(&rejected_epoch),
        "committing a scalar certified table changes the sealed model"
    );

    let datatype_epoch = model.seal_quantified_grant_model();
    model
        .install_certified_total_dt_uf(
            "score".to_string(),
            vec![Sort::Uninterpreted("D".to_string())],
            Sort::Int,
            Vec::new(),
            Vec::new(),
            EvalValue::Rational(BigRational::one()),
        )
        .expect("well-typed datatype-keyed total UF");
    assert!(
        !model.carries_quantified_grant_model(&datatype_epoch),
        "committing a datatype-keyed certified table changes the sealed model"
    );
}
