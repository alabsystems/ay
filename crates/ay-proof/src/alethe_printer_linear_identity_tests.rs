// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External lowering tests for strict LIA linear identities.
//!
//! The pinned Carcara checker ignores `lia_generic`, so a ground identity must
//! use its independently checked `evaluate` rule. The lowering is deliberately
//! limited to truths admitted by the independent ground evaluator; symbolic or
//! false ground literals keep their faithful `lia_generic` surface.

use super::*;
use ay_core::{FarkasAnnotation, LiaAnnotation, Sort, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::Rational64;

fn one_coefficient() -> FarkasAnnotation {
    FarkasAnnotation::new(vec![Rational64::from_integer(1)])
}

fn lia_step(literal: TermId, annotation: LiaAnnotation) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![literal],
        farkas: Some(one_coefficient()),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: Some(annotation),
    }
}

#[test]
fn ground_linear_identity_lowers_to_argument_free_evaluate() {
    let mut terms = TermStore::new();
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let sum = terms.mk_app(Symbol::named("+"), [two, three], Sort::Int);
    let identity = terms.mk_app(Symbol::named("="), [sum, five], Sort::Bool);
    let step = lia_step(identity, LiaAnnotation::LinearIdentity);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("ground identity must render");

    assert_eq!(rendered, "(step t7 (cl (= (+ 2 3) 5)) :rule evaluate)");
    assert!(!rendered.contains(":args"), "{rendered}");
    assert!(!rendered.contains("lia_generic"), "{rendered}");
}

#[test]
fn symbolic_linear_identity_preserves_lia_generic() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let sum = terms.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let step = lia_step(identity, LiaAnnotation::LinearIdentity);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(8))
        .expect("symbolic identity must retain its ordinary rendering");

    assert!(
        rendered.contains(":rule lia_generic :args (1)"),
        "{rendered}"
    );
    assert!(!rendered.contains(":rule evaluate"), "{rendered}");
}

#[test]
fn ground_disequality_lowers_to_checked_evaluate_bridge() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let equality = terms.mk_app(Symbol::named("="), [zero, one], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);
    let step = lia_step(disequality, LiaAnnotation::Divisibility);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(9))
        .expect("ground disequality must render");

    assert_eq!(
        rendered,
        "(step t9.ev (cl (= (= 0 1) false)) :rule evaluate)\n\
         (step t9.q (cl (not (= 0 1)) false) :rule equiv1 :premises (t9.ev))\n\
         (step t9.f (cl (not false)) :rule false)\n\
         (step t9 (cl (not (= 0 1))) :rule resolution :premises (t9.q t9.f))"
    );
    assert!(!rendered.contains("lia_generic"), "{rendered}");
}

#[test]
fn false_ground_disequality_preserves_lia_generic() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let equality = terms.mk_app(Symbol::named("="), [zero, zero], Sort::Bool);
    let false_disequality = terms.mk_not_raw(equality);
    let step = lia_step(false_disequality, LiaAnnotation::Divisibility);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(10))
        .expect("false ground literal must retain its ordinary rendering");

    assert!(
        rendered.contains(":rule lia_generic :args (1)"),
        "{rendered}"
    );
    assert!(!rendered.contains(":rule evaluate"), "{rendered}");
}

#[test]
fn ground_truth_with_surface_drift_preserves_lia_generic() {
    let mut terms = TermStore::new();
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let sum = terms.mk_app(Symbol::named("+"), [two, three], Sort::Int);
    let identity = terms.mk_app(Symbol::named("="), [sum, five], Sort::Bool);
    let step = lia_step(identity, LiaAnnotation::LinearIdentity);
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(five, "6".to_string());

    let rendered = AlethePrinter::new_with_overrides(&terms, Some(&overrides))
        .format_step(&step, ProofId(11))
        .expect("surface drift must retain the ordinary rendering");

    assert!(rendered.contains("(= (+ 2 3) 6)"), "{rendered}");
    assert!(
        rendered.contains(":rule lia_generic :args (1)"),
        "{rendered}"
    );
    assert!(!rendered.contains(":rule evaluate"), "{rendered}");
}
