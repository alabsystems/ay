// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for bounded source trees and dynamic printer policy.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermStore, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::SExpr;

use super::{
    live_proof_rendering_is_static, render_roots_have_bounded_depth, surface_pass_work,
    surface_source_is_bounded, surface_source_work, surface_sources_have_bounded_work,
    ProofSourcePass, ProofSourceWorkEnvelope, MAX_AGGREGATE_SOURCE_WORK, MAX_SURFACE_DEPTH,
};
use crate::executor::proof_surface_syntax::{
    surface_override_map_is_bounded, surface_override_roots_have_bounded_work,
};
use crate::executor::Executor;

#[test]
fn source_bound_strips_annotations_and_rejects_excess_depth() {
    let annotated = FrontendTerm::Annotated(
        Box::new(FrontendTerm::Symbol("bounded_source".to_string())),
        Vec::new(),
    );
    assert!(surface_source_is_bounded(&annotated));

    let mut deep = FrontendTerm::Symbol("deep_source".to_string());
    for _ in 0..=MAX_SURFACE_DEPTH {
        deep = FrontendTerm::App("not".to_string(), vec![deep]);
    }
    assert!(!surface_source_is_bounded(&deep));
    let mut executor = Executor::new();
    assert!(executor.raw_intern_surface(&deep).is_none());
}

#[test]
fn source_bound_charges_annotation_payloads_before_clone() {
    let annotated = FrontendTerm::Annotated(
        Box::new(FrontendTerm::Symbol("annotation_body".to_string())),
        vec![(":payload".to_string(), SExpr::String("x".repeat(1_100_000)))],
    );
    assert!(!surface_source_is_bounded(&annotated));

    let nested = FrontendTerm::Annotated(
        Box::new(FrontendTerm::Symbol("annotation_body".to_string())),
        vec![(
            ":payload".to_string(),
            (0..=MAX_SURFACE_DEPTH).fold(SExpr::True, |inner, _| SExpr::List(vec![inner])),
        )],
    );
    assert!(!surface_source_is_bounded(&nested));
}

/// A parsed source whose single-pass cost is a known fraction of the envelope.
fn sized_source(symbols: usize) -> FrontendTerm {
    FrontendTerm::App(
        "and".to_string(),
        (0..symbols)
            .map(|index| FrontendTerm::Symbol(format!("envelope_leaf_{index:08}")))
            .collect(),
    )
}

/// PARITY: the per-pass ceiling is exactly what it always was. A stack that a
/// SINGLE pass cannot render inside `MAX_AGGREGATE_SOURCE_WORK` is refused on
/// its first spend, with a full envelope, and the refusal debits nothing.
#[test]
fn one_pass_over_genuinely_oversized_sources_still_fails_closed() {
    let envelope = ProofSourceWorkEnvelope::default();
    let full = envelope.remaining_for_test();
    let row = sized_source(2_048);
    let per_row = surface_pass_work(std::iter::once(&row)).expect("one row is bounded");
    let rows = MAX_AGGREGATE_SOURCE_WORK / per_row + 1;
    let stack: Vec<&FrontendTerm> = std::iter::repeat_n(&row, rows).collect();

    assert!(!surface_sources_have_bounded_work(stack.iter().copied()));
    assert!(!envelope.spend(ProofSourcePass::UnsatProofBuild, stack.iter().copied()));
    assert_eq!(
        envelope.remaining_for_test(),
        full,
        "a refused pass must not debit the envelope",
    );
}

/// PARITY: an unbounded root fails closed and debits nothing, at every pass.
#[test]
fn an_unbounded_root_fails_closed_without_debiting() {
    let envelope = ProofSourceWorkEnvelope::default();
    let full = envelope.remaining_for_test();
    let mut deep = FrontendTerm::Symbol("envelope_unbounded".to_string());
    for _ in 0..=MAX_SURFACE_DEPTH {
        deep = FrontendTerm::App("not".to_string(), vec![deep]);
    }
    assert!(surface_source_work(&deep).is_none());
    for pass in [
        ProofSourcePass::UnsatProofBuild,
        ProofSourcePass::OriginalAssertionRebuild,
        ProofSourcePass::InputSyntaxRewrite,
        ProofSourcePass::InputSyntaxOverridePairs,
        ProofSourcePass::InternalCertificateScope,
    ] {
        assert!(!envelope.spend(pass, std::iter::once(&deep)));
        assert_eq!(envelope.remaining_for_test(), full);
    }
}

/// PARITY: the aggregate ceiling is real, not assumed. Passes drain ONE shared
/// envelope, so a query that keeps re-walking its sources still exhausts — the
/// pre-charge was removed, the ceiling was not.
#[test]
fn passes_drain_one_shared_envelope_until_it_refuses() {
    let row = sized_source(1_024);
    let stack = [&row];
    let per_pass = surface_pass_work(stack.iter().copied()).expect("bounded");
    let envelope = ProofSourceWorkEnvelope::default();
    envelope.set_remaining_for_test(per_pass * 2);

    assert!(envelope.spend(ProofSourcePass::UnsatProofBuild, stack.iter().copied()));
    assert_eq!(envelope.remaining_for_test(), per_pass);
    assert!(envelope.spend(ProofSourcePass::InputSyntaxRewrite, stack.iter().copied()));
    assert_eq!(envelope.remaining_for_test(), 0);
    assert!(!envelope.spend(
        ProofSourcePass::InputSyntaxOverridePairs,
        stack.iter().copied()
    ));
    assert_eq!(envelope.remaining_for_test(), 0);
}

/// PARITY: each site's own repetition factor is charged, and it is charged HERE
/// rather than pre-billed at the build preflight. `OriginalAssertionRebuild`
/// really does walk, clone, and re-elaborate the stack, so it pays three passes;
/// every other site walks once and pays one. A future memo that silently drops a
/// multiplier — or reinstates a pre-charge for a pass it does not perform —
/// fails here.
#[test]
fn every_pass_charges_exactly_the_traversals_it_performs() {
    let row = sized_source(512);
    let stack = [&row];
    let single = surface_pass_work(stack.iter().copied()).expect("bounded");

    for (pass, expected_passes) in [
        (ProofSourcePass::UnsatProofBuild, 1usize),
        (ProofSourcePass::OriginalAssertionRebuild, 3),
        (ProofSourcePass::InputSyntaxRewrite, 1),
        (ProofSourcePass::InputSyntaxOverridePairs, 1),
        (ProofSourcePass::InternalCertificateScope, 1),
    ] {
        let envelope = ProofSourceWorkEnvelope::default();
        let full = envelope.remaining_for_test();
        assert!(envelope.spend(pass, stack.iter().copied()));
        assert_eq!(
            full - envelope.remaining_for_test(),
            single * expected_passes,
            "{pass:?} must charge exactly {expected_passes} pass(es)",
        );
    }
}

/// The whole query's proof pipeline fits one envelope, and refilling is a
/// per-query event: work measured beside one assertion stack is meaningless
/// beside the next one.
#[test]
fn reset_refills_the_envelope_for_the_next_query() {
    let row = sized_source(1_024);
    let stack = [&row];
    let mut envelope = ProofSourceWorkEnvelope::default();
    assert!(envelope.spend(ProofSourcePass::UnsatProofBuild, stack.iter().copied()));
    assert!(envelope.remaining_for_test() < MAX_AGGREGATE_SOURCE_WORK);
    envelope.reset();
    assert_eq!(envelope.remaining_for_test(), MAX_AGGREGATE_SOURCE_WORK);
}

/// THE REGRESSION ITSELF. A source stack whose complete single-pass cost is a
/// small fraction of the envelope, but whose cost times the old sixteen-fold
/// pre-charge exceeds it, is admitted — and the five real passes of a whole
/// proof pipeline still fit, with room left over. Measured shape: the QF_UF
/// `qg5/iso_brn673` family, 25 assertions / 48 KB of SMT-LIB / 2.9 MiB of
/// single-pass source work, which the pre-charge refused a proof outright.
#[test]
fn a_stack_the_old_pre_charge_refused_now_funds_the_whole_pipeline() {
    let rows: Vec<FrontendTerm> = (0..25).map(|_| sized_source(700)).collect();
    let single = surface_pass_work(rows.iter()).expect("every row is bounded");
    assert!(
        single <= MAX_AGGREGATE_SOURCE_WORK,
        "one pass must fit the envelope",
    );
    assert!(
        single * 16 > MAX_AGGREGATE_SOURCE_WORK,
        "this stack must be one the old sixteen-fold pre-charge refused \
         (single-pass work {single})",
    );

    let envelope = ProofSourceWorkEnvelope::default();
    for pass in [
        ProofSourcePass::UnsatProofBuild,
        ProofSourcePass::InputSyntaxRewrite,
        ProofSourcePass::InputSyntaxOverridePairs,
        ProofSourcePass::OriginalAssertionRebuild,
        ProofSourcePass::InternalCertificateScope,
    ] {
        assert!(
            envelope.spend(pass, rows.iter()),
            "{pass:?} must fit the shared envelope",
        );
    }
    assert!(envelope.remaining_for_test() > 0);
}

#[test]
fn collected_override_map_has_a_hard_entry_boundary() {
    let mut overrides = HashMap::default();
    for index in 0..8_192u32 {
        overrides.insert(ay_core::TermId(index), "x".to_string());
    }
    assert!(surface_override_map_is_bounded(&overrides));
    overrides.insert(ay_core::TermId(8_192), "x".to_string());
    assert!(!surface_override_map_is_bounded(&overrides));
}

#[test]
fn repeated_override_roots_are_charged_per_collection() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("repeated_override_root", Sort::Bool);
    assert!(surface_override_roots_have_bounded_work(
        &terms,
        std::iter::repeat_n(root, 8_192),
    ));
    assert!(!surface_override_roots_have_bounded_work(
        &terms,
        std::iter::repeat_n(root, 8_193),
    ));
}

#[test]
fn rendered_root_depth_rechecks_a_shared_tail() {
    let mut terms = TermStore::new();
    let mut shared = terms.mk_var("shared_depth_tail", Sort::Bool);
    for _ in 0..200 {
        shared = terms.mk_app(Symbol::named("depth_f"), [shared], Sort::Bool);
    }
    let shallow = shared;
    let mut deep = shared;
    for _ in 0..100 {
        deep = terms.mk_app(Symbol::named("depth_g"), [deep], Sort::Bool);
    }
    assert!(!render_roots_have_bounded_depth(
        &terms,
        &[shallow, deep],
        1_000,
        10_000,
    ));
}

#[test]
fn dynamic_printer_sources_fail_closed_only_when_live_or_selected() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("dynamic_surface_p", Sort::Bool);
    let mut skolem = Proof::new();
    skolem.add_rule_step(AletheRule::Skolem, vec![p], Vec::new(), Vec::new());
    assert!(!live_proof_rendering_is_static(
        &skolem,
        &[true],
        &terms,
        &HashMap::default(),
    ));
    assert!(live_proof_rendering_is_static(
        &skolem,
        &[false],
        &terms,
        &HashMap::default(),
    ));

    let mut array = Proof::new();
    array.add_step(ProofStep::TheoryLemma {
        theory: "Arrays".to_string(),
        clause: vec![p],
        farkas: None,
        kind: TheoryLemmaKind::ArrayExtensionality,
        lia: None,
    });
    assert!(!live_proof_rendering_is_static(
        &array,
        &[true],
        &terms,
        &HashMap::default(),
    ));

    let mut annotated_resolution = Proof::new();
    annotated_resolution.add_rule_step(AletheRule::Resolution, vec![p], Vec::new(), vec![p]);
    let mut active = HashMap::default();
    active.insert(p, "dynamic_surface_p".to_string());
    assert!(!live_proof_rendering_is_static(
        &annotated_resolution,
        &[true],
        &terms,
        &active,
    ));

    let mut selected_let = HashMap::default();
    selected_let.insert(p, "(let ((q true)) q)".to_string());
    assert!(!live_proof_rendering_is_static(
        &Proof::new(),
        &[],
        &terms,
        &selected_let,
    ));
}
