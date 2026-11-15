// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;
use crate::CancellationToken;
use ay_core::time::Instant;
use std::time::Duration;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun f (Bool (_ BitVec 136)) (_ BitVec 136))
         (declare-fun |unused wide| () (_ BitVec 136))
         (declare-fun query_0 ((_ BitVec 8)) (_ BitVec 8))
         (declare-fun error_p7 () Bool)
         (assert error_p7)
         (assert (=> error_p7 false))
         (check-sat)",
    )
    .unwrap()
}

fn models() -> Vec<ScalarFunctionModel> {
    let arguments = [Sort::Bool, Sort::bitvec(136)];
    let byte_arguments = [Sort::bitvec(8)];
    let wide = Sort::bitvec(136);
    let byte = Sort::bitvec(8);
    // This is checked model DATA only. There is no solver, accepted SAT model,
    // native emission witness, trace constructor or replay in these fixtures.
    ScalarFunctionModel::decode_smtlib(
        "(model
          (define-fun query_0 ((byte (_ BitVec 8))) (_ BitVec 8) byte)
          (define-fun |unused wide| () (_ BitVec 136)
            (concat (_ bv128 8) (_ bv0 128)))
          (define-fun f ((flag Bool) (x (_ BitVec 136))) (_ BitVec 136)
            (ite flag x (bvadd x (_ bv1 136)))))",
        &[
            ("f", arguments.as_slice(), &wide),
            ("unused wide", &[][..], &wide),
            ("query_0", byte_arguments.as_slice(), &byte),
        ],
    )
    .unwrap()
}

fn wire(models: &[ScalarFunctionModel]) -> String {
    let mut text = String::from("(model");
    for model in models {
        text.push(' ');
        text.push_str(model.definition_smtlib());
    }
    text.push(')');
    text
}

#[test]
fn complete_ordered_wide_unused_and_query_named_functions_roundtrip_as_data() {
    let source = source();
    let models = models();
    let token = CancellationToken::new();
    let exported = export(&models, &source, &control(&token)).unwrap();
    assert_eq!(exported, wire(&models));
    assert!(!exported.contains('\n'));
    assert_eq!(models[1].name(), "unused wide");
    assert_eq!(models[1].result_sort(), &Sort::bitvec(136));
    assert!(models[1].arg_sorts().is_empty());
    assert!(models[1].definition_smtlib().contains("(concat #x80 "));
    assert_eq!(models[2].name(), "query_0");
    assert_eq!(source.source_view().clauses().count(), 2);
    let imported = import(&exported, &source, &control(&token)).unwrap();
    assert_eq!(imported, models);
    assert_eq!(
        export(&imported, &source, &control(&token)).unwrap(),
        exported
    );
}

#[test]
fn complete_empty_inventory_has_one_exact_wire_without_synthetic_models() {
    let source =
        QuantifiedChcProblem::parse_smtlib("(set-logic HORN) (assert false) (check-sat)").unwrap();
    let token = CancellationToken::new();
    assert_eq!(export(&[], &source, &control(&token)).unwrap(), "(model)");
    assert!(import("(model)", &source, &control(&token))
        .unwrap()
        .is_empty());
    for text in ["(model )", " (model)", "(model)\n", "(model);comment"] {
        assert!(import(text, &source, &control(&token)).is_none());
    }
    assert!(import(&wire(&models()), &source, &control(&token)).is_none());
    assert!(export(&models(), &source, &control(&token)).is_none());
    // The only empty wire needs no parser or fixed decoder reservation.
    let small = control(&token);
    small.bytes(64 * 1024 * 1024 - 64).unwrap();
    assert!(import("(model)", &source, &small).unwrap().is_empty());
    assert!(small.poll().is_some());
}

#[test]
fn missing_duplicate_extra_and_reordered_inventories_never_publish_a_prefix() {
    let source = source();
    let models = models();
    let token = CancellationToken::new();
    let mut missing = models.clone();
    missing.remove(1);
    let mut duplicate = models.clone();
    duplicate[1] = duplicate[0].clone();
    let mut extra = models.clone();
    extra.push(models[0].clone());
    let mut reordered = models.clone();
    reordered.swap(0, 2);
    for malformed in [missing, duplicate, extra, reordered] {
        assert!(export(&malformed, &source, &control(&token)).is_none());
        assert!(import(&wire(&malformed), &source, &control(&token)).is_none());
    }
    assert!(import("(model)", &source, &control(&token)).is_none());
    assert!(import(&wire(&models), &source, &control(&token)).is_some());
}

#[test]
fn source_signatures_and_names_are_not_taken_from_the_wire() {
    let source = source();
    let models = models();
    let token = CancellationToken::new();
    for changed in [
        source.source_smtlib().replace("query_0", "query_1"),
        source.source_smtlib().replace("BitVec 8", "BitVec 9"),
        source
            .source_smtlib()
            .replace("(Bool (_ BitVec 136))", "((_ BitVec 1) (_ BitVec 136))"),
        source.source_smtlib().replace(
            "|unused wide| () (_ BitVec 136)",
            "|unused wide| () (_ BitVec 135)",
        ),
    ] {
        let changed = QuantifiedChcProblem::parse_smtlib(&changed).unwrap();
        assert_ne!(changed.source_smtlib(), source.source_smtlib());
        assert!(export(&models, &changed, &control(&token)).is_none());
        assert!(import(&wire(&models), &changed, &control(&token)).is_none());
    }
}

#[test]
fn noncanonical_alpha_names_literals_and_trailing_commands_are_refused() {
    let source = source();
    let canonical = wire(&models());
    let token = CancellationToken::new();
    assert!(canonical.contains("ay_uf_v0"));
    assert!(canonical.contains("#x80"));
    for text in [
        format!(" {canonical}"),
        format!("{canonical}(check-sat)"),
        canonical.replace("ay_uf_v0", "other_parameter"),
        canonical.replace("#x80", "(_ bv128 8)"),
        canonical.replace("#x80", "#x100"),
        canonical.replace("ay_uf_v1", "unbound"),
    ] {
        assert_ne!(text, canonical);
        assert!(import(&text, &source, &control(&token)).is_none());
    }
    assert!(import(&canonical, &source, &control(&token)).is_some());
}

#[test]
fn another_total_interpretation_changes_data_but_is_not_a_sat_claim() {
    let source = source();
    let original = models();
    let mut changed = original.clone();
    let wide = Sort::bitvec(136);
    changed[1] = ScalarFunctionModel::decode_smtlib(
        "(model (define-fun |unused wide| () (_ BitVec 136) (_ bv0 136)))",
        &[("unused wide", &[][..], &wide)],
    )
    .unwrap()
    .remove(0);
    let token = CancellationToken::new();
    let original_wire = export(&original, &source, &control(&token)).unwrap();
    let changed_wire = export(&changed, &source, &control(&token)).unwrap();
    assert_ne!(original_wire, changed_wire);
    assert_eq!(
        import(&original_wire, &source, &control(&token)).unwrap(),
        original
    );
    assert_eq!(
        import(&changed_wire, &source, &control(&token)).unwrap(),
        changed
    );
    // Pin/trace identity and fresh full-source SAT are the caller's separate
    // obligations. Well-typed alternate DATA must not be treated as evidence.
}

#[test]
fn decoder_allowance_and_shared_work_copy_refusal_are_sticky_and_retryable() {
    let source = source();
    let models = models();
    let text = wire(&models);
    let token = CancellationToken::new();
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(import(&text, &source, &exhausted).is_none());
    assert!(export(&models, &source, &exhausted).is_none());
    assert!(exhausted.poll().is_none());
    let allowance = control(&token);
    allowance
        .bytes(64 * 1024 * 1024 - DECODER_BYTES + 1)
        .unwrap();
    assert!(import(&text, &source, &allowance).is_none());
    assert!(allowance.poll().is_none());
    let work = control(&token);
    assert!(work.charge(usize::MAX).is_none());
    assert!(import(&text, &source, &work).is_none());
    assert!(export(&models, &source, &work).is_none());
    assert!(import(&text, &source, &control(&token)).is_some());
    assert!(export(&models, &source, &control(&token)).is_some());
    assert!(!token.is_cancelled());
}

#[test]
fn original_deadline_observed_cancellation_and_wire_size_refuse() {
    let source = source();
    let models = models();
    let text = wire(&models);
    let token = CancellationToken::new();
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(import(&text, &source, &expired).is_none());
    assert!(export(&models, &source, &expired).is_none());
    let cancelled = control(&token);
    token.cancel();
    assert!(import(&text, &source, &cancelled).is_none());
    token.reset();
    assert!(export(&models, &source, &cancelled).is_none());
    assert!(import(&text, &source, &cancelled).is_none());
    let oversized = " ".repeat(MAX_OUTPUT + 1);
    assert!(import(&oversized, &source, &control(&token)).is_none());
    assert!(import(&text, &source, &control(&token)).is_some());
}
