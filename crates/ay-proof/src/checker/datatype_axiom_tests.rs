// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness tests for `TheoryLemmaKind::DatatypeDistinct` strict validation
//! (#8419 / trust_count→0).
//!
//! The datatype solver refutes `(= C1(..) C2(..))` for two distinct
//! constructors of the same datatype. These tests assert the strict checker:
//!  - ACCEPTS the genuine distinctness schemas (unit and binary) when the
//!    constructors are registered and distinct;
//!  - REJECTS forgeries — same constructor (injectivity, not distinctness),
//!    cross-datatype pairs, and non-constructor heads — so a forged "datatype
//!    distinctness" lemma cannot drive a bogus UNSAT;
//!  - FAILS CLOSED when no datatype registry is supplied (it never assumes
//!    distinctness by shape alone).

use crate::checker::*;
use ay_core::{ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

/// `(declare-datatype Color (red green blue))` plus `(Light (on off))`.
fn two_datatypes() -> Vec<(String, Vec<String>)> {
    vec![
        (
            "Color".to_string(),
            vec!["red".to_string(), "green".to_string(), "blue".to_string()],
        ),
        (
            "Light".to_string(),
            vec!["on".to_string(), "off".to_string()],
        ),
    ]
}

/// A nullary constructor application `C` of datatype sort `dt`.
fn ctor(terms: &mut TermStore, name: &str, dt: &str) -> TermId {
    terms.mk_app(
        Symbol::named(name),
        Vec::<TermId>::new(),
        Sort::Uninterpreted(dt.to_string()),
    )
}

/// `(not (= a b))`.
fn neq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    let eq = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    terms.mk_not(eq)
}

/// Validate a `DatatypeDistinct` step in strict mode with the given registry.
fn validate(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeDistinct,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step_with_datatypes(
        terms,
        &mut derived,
        ProofId(0),
        &step,
        true,
        dt_decls,
        None,
        None,
    )
}

#[test]
fn accepts_unit_distinctness_of_distinct_constructors() {
    // (not (= red green)) — two distinct constructors of Color.
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let lit = neq(&mut terms, red, green);
    let decls = two_datatypes();

    validate(&terms, vec![lit], Some(&decls))
        .expect("distinctness of red != green must be accepted");
    assert!(recognize_datatype_distinct(&terms, &[lit], &decls));
}

#[test]
fn accepts_binary_exclusion_shared_term() {
    // (not (= t red)) (not (= t green)) — t cannot be two distinct constructors.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let l0 = neq(&mut terms, t, red);
    let l1 = neq(&mut terms, t, green);
    let decls = two_datatypes();

    validate(&terms, vec![l0, l1], Some(&decls))
        .expect("binary exclusion t!=red | t!=green must be accepted");
}

#[test]
fn rejects_same_constructor_both_sides() {
    // (not (= red red)) — identical constructor; this is injectivity, NOT
    // distinctness, and is not a tautology of distinctness.
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let lit = neq(&mut terms, red, red);
    let decls = two_datatypes();

    let err = validate(&terms, vec![lit], Some(&decls))
        .expect_err("same-constructor disequality must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_distinct(&terms, &[lit], &decls));
}

#[test]
fn rejects_cross_datatype_constructors() {
    // (not (= red on)) — red ∈ Color, on ∈ Light. Different datatypes: a value
    // of one cannot be compared as a tautology of the other; reject.
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let on = ctor(&mut terms, "on", "Light");
    let lit = neq(&mut terms, red, on);
    let decls = two_datatypes();

    let err = validate(&terms, vec![lit], Some(&decls))
        .expect_err("cross-datatype constructor pair must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_distinct(&terms, &[lit], &decls));
}

#[test]
fn rejects_non_constructor_head() {
    // (not (= red f(x))) where f is an ordinary uninterpreted function, not a
    // registered constructor. f(x) could equal red, so this is NOT a
    // distinctness tautology — reject (fail closed).
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let x = terms.mk_var("x", Sort::Uninterpreted("Color".to_string()));
    let fx = terms.mk_app(
        Symbol::named("f"),
        vec![x],
        Sort::Uninterpreted("Color".to_string()),
    );
    let lit = neq(&mut terms, red, fx);
    let decls = two_datatypes();

    let err = validate(&terms, vec![lit], Some(&decls))
        .expect_err("non-constructor head must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_distinct(&terms, &[lit], &decls));
}

#[test]
fn fails_closed_without_registry() {
    // Same valid clause, but NO datatype registry supplied. Strict mode must
    // not assume distinctness by shape alone — it fails closed.
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let lit = neq(&mut terms, red, green);

    let err = validate(&terms, vec![lit], None)
        .expect_err("datatype distinctness with no registry must fail closed");
    assert!(matches!(
        err,
        ProofCheckError::UnsupportedTheoryLemmaKind { .. }
    ));
}

#[test]
fn rejects_non_distinctness_shapes() {
    // A clause that is not a negated equality at all (a bare Boolean literal)
    // must be rejected even with the registry present.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let decls = two_datatypes();

    let err = validate(&terms, vec![p], Some(&decls))
        .expect_err("non-distinctness clause shape must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

// ---- Datatype selector-projection (`DatatypeSelectorProject`) validation ----

/// `(declare-datatype Pair ((mk (fst Int) (snd Int))))` selector registry:
/// constructor `mk` has selectors `fst` (field 0) and `snd` (field 1).
fn pair_selectors() -> Vec<(String, Vec<String>)> {
    vec![("mk".to_string(), vec!["fst".to_string(), "snd".to_string()])]
}

/// `(mk a b)` — a binary constructor application of carrier sort `Pair`.
fn mk_pair(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(
        Symbol::named("mk"),
        vec![a, b],
        Sort::Uninterpreted("Pair".to_string()),
    )
}

/// `(sel inner)` — a selector application (raw; `mk_app` does not fold).
fn sel(terms: &mut TermStore, name: &str, inner: TermId) -> TermId {
    terms.mk_app(Symbol::named(name), vec![inner], Sort::Int)
}

/// `(= a b)`.
fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
}

/// Validate a `DatatypeSelectorProject` step with the given selector registry.
fn validate_project(
    terms: &TermStore,
    clause: Vec<TermId>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeSelectorProject,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step_with_datatypes(
        terms,
        &mut derived,
        ProofId(0),
        &step,
        true,
        None,
        ctor_selectors,
        None,
    )
}

#[test]
fn project_accepts_field0_and_field1() {
    // (= (fst (mk a b)) a) and (= (snd (mk a b)) b) — true projections.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let fst = sel(&mut terms, "fst", p);
    let snd = sel(&mut terms, "snd", p);
    let l0 = eq(&mut terms, fst, a);
    let l1 = eq(&mut terms, snd, b);
    let sels = pair_selectors();

    validate_project(&terms, vec![l0], Some(&sels)).expect("fst(mk a b)=a must be accepted");
    validate_project(&terms, vec![l1], Some(&sels)).expect("snd(mk a b)=b must be accepted");
    assert!(recognize_datatype_selector_project(&terms, &[l0], &sels));
    assert!(recognize_datatype_selector_project(&terms, &[l1], &sels));
}

#[test]
fn project_accepts_selector_on_right() {
    // (= a (fst (mk a b))) — selector on the right-hand side.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let fst = sel(&mut terms, "fst", p);
    let lit = eq(&mut terms, a, fst);
    let sels = pair_selectors();

    validate_project(&terms, vec![lit], Some(&sels)).expect("a=fst(mk a b) must be accepted");
}

#[test]
fn project_rejects_wrong_field() {
    // (= (snd (mk a b)) a) — snd projects field 1 (= b), NOT a. This is FALSE
    // when a != b, so it must be rejected.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let snd = sel(&mut terms, "snd", p);
    let lit = eq(&mut terms, snd, a);
    let sels = pair_selectors();

    let err = validate_project(&terms, vec![lit], Some(&sels))
        .expect_err("snd(mk a b)=a (wrong field) must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_selector_project(&terms, &[lit], &sels));
}

#[test]
fn project_rejects_wrong_argument() {
    // (= (fst (mk a b)) b) — fst projects field 0 (= a), NOT b. Reject.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let fst = sel(&mut terms, "fst", p);
    let lit = eq(&mut terms, fst, b);
    let sels = pair_selectors();

    let err = validate_project(&terms, vec![lit], Some(&sels))
        .expect_err("fst(mk a b)=b (wrong argument) must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn project_rejects_unregistered_selector() {
    // (= (third (mk a b)) a) — `third` is not a registered selector of mk. Reject.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let third = sel(&mut terms, "third", p);
    let lit = eq(&mut terms, third, a);
    let sels = pair_selectors();

    let err = validate_project(&terms, vec![lit], Some(&sels))
        .expect_err("unregistered selector must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn project_rejects_selector_over_non_constructor() {
    // (= (fst x) a) where x is a plain variable, not a constructor application.
    // `fst x` does not reduce, so this is not a projection tautology — reject.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let x = terms.mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let fst = sel(&mut terms, "fst", x);
    let lit = eq(&mut terms, fst, a);
    let sels = pair_selectors();

    let err = validate_project(&terms, vec![lit], Some(&sels))
        .expect_err("selector over a non-constructor must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn project_fails_closed_without_registry() {
    // A genuine projection, but NO selector registry: strict mode must not
    // assume the field mapping by shape alone — it fails closed.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p = mk_pair(&mut terms, a, b);
    let fst = sel(&mut terms, "fst", p);
    let lit = eq(&mut terms, fst, a);

    let err = validate_project(&terms, vec![lit], None)
        .expect_err("selector projection with no registry must fail closed");
    assert!(matches!(
        err,
        ProofCheckError::UnsupportedTheoryLemmaKind { .. }
    ));
}
