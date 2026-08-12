// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for bounded source trees and dynamic printer policy.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermStore, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::SExpr;

use super::{
    live_proof_rendering_is_static, render_roots_have_bounded_depth, surface_source_is_bounded,
    MAX_SURFACE_DEPTH,
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
