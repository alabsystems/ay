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

// ─── DatatypeTesterExclusive (#dt-lazy-axiom-authority) ────────────────────

/// Validate a `DatatypeTesterExclusive` step in strict mode.
fn validate_tester_exclusive(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeTesterExclusive,
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
        Some(&[]),
        None,
        None,
        None,
        None,
    )
}

#[test]
fn tester_exclusive_accepts_distinct_sibling_pair() {
    // (not (is-red t)) (not (is-green t)).
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let l0 = terms.mk_not(is_red);
    let l1 = terms.mk_not(is_green);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![l0, l1], Some(&decls))
        .expect("exclusivity of two distinct sibling testers must be accepted");
    assert!(recognize_datatype_tester_exclusive(
        &terms,
        &[l0, l1],
        &decls
    ));
}

#[test]
fn tester_exclusive_accepts_the_emitters_folded_or_form() {
    // [(or (not (is-red t)) (not (is-green t)))] — the single-term shape the
    // DT axiom emitters intern and record.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let l0 = terms.mk_not(is_red);
    let l1 = terms.mk_not(is_green);
    let folded = terms.mk_or(vec![l0, l1]);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![folded], Some(&decls))
        .expect("the or-folded emitter form must be accepted");
    assert!(recognize_datatype_tester_exclusive(
        &terms,
        &[folded],
        &decls
    ));
}

#[test]
fn tester_exclusive_rejects_repeated_tester() {
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let l0 = terms.mk_not(is_red);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![l0, l0], Some(&decls))
        .expect_err("the same tester twice is not an exclusivity pair");
}

#[test]
fn tester_exclusive_rejects_cross_datatype_pair() {
    // is-red is a Color tester, is-on a Light tester.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_on = tester(&mut terms, "on", t);
    let l0 = terms.mk_not(is_red);
    let l1 = terms.mk_not(is_on);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![l0, l1], Some(&decls))
        .expect_err("testers of two different datatypes must be rejected");
}

#[test]
fn tester_exclusive_rejects_positive_testers() {
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![is_red, is_green], Some(&decls))
        .expect_err("positive testers are exhaustiveness, not exclusivity");
}

#[test]
fn tester_exclusive_rejects_constructor_headed_scrutinee() {
    // (not (is-red green)) over an explicit constructor is tester EVALUATION.
    let mut terms = TermStore::new();
    let green_app = ctor(&mut terms, "green", "Color");
    let is_red = tester(&mut terms, "red", green_app);
    let blue_app = ctor(&mut terms, "blue", "Color");
    let _ = blue_app;
    let is_green = tester(&mut terms, "green", green_app);
    let l0 = terms.mk_not(is_red);
    let l1 = terms.mk_not(is_green);
    let decls = two_datatypes();

    validate_tester_exclusive(&terms, vec![l0, l1], Some(&decls))
        .expect_err("a constructor-headed scrutinee belongs to tester evaluation");
}

#[test]
fn tester_exclusive_fails_closed_without_registry() {
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let l0 = terms.mk_not(is_red);
    let l1 = terms.mk_not(is_green);

    validate_tester_exclusive(&terms, vec![l0, l1], None)
        .expect_err("without the datatype registry the kind must fail closed");
}

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
        Some(&[]),
        None,
        None,
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

#[test]
fn rejects_indexed_homonyms_of_datatype_distinctness_symbols() {
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let decls = two_datatypes();

    let indexed_eq = terms.mk_app(Symbol::indexed("=", vec![0]), vec![red, green], Sort::Bool);
    let indexed_eq_lit = terms.mk_not_raw(indexed_eq);
    validate(&terms, vec![indexed_eq_lit], Some(&decls))
        .expect_err("an indexed `=` is an uninterpreted homonym, not equality");

    let indexed_red = terms.mk_app(
        Symbol::indexed("red", vec![0]),
        Vec::new(),
        Sort::Uninterpreted("Color".to_string()),
    );
    let indexed_green = terms.mk_app(
        Symbol::indexed("green", vec![0]),
        Vec::new(),
        Sort::Uninterpreted("Color".to_string()),
    );
    let indexed_ctor_lit = neq(&mut terms, indexed_red, indexed_green);
    validate(&terms, vec![indexed_ctor_lit], Some(&decls))
        .expect_err("indexed constructor homonyms are not declared constructors");

    let genuine_lit = neq(&mut terms, red, green);
    let indexed_or = terms.mk_app(
        Symbol::indexed("or", vec![0]),
        vec![genuine_lit],
        Sort::Bool,
    );
    validate(&terms, vec![indexed_or], Some(&decls))
        .expect_err("an indexed `or` must not be flattened as a proof clause");
}

#[test]
fn rejects_ill_sorted_datatype_distinctness_terms() {
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green_wrong_carrier = terms.mk_app(
        Symbol::named("green"),
        Vec::new(),
        Sort::Uninterpreted("Light".to_string()),
    );
    let mismatched = terms.mk_app(
        Symbol::named("="),
        vec![red, green_wrong_carrier],
        Sort::Bool,
    );
    let mismatched_lit = terms.mk_not_raw(mismatched);
    let decls = two_datatypes();
    validate(&terms, vec![mismatched_lit], Some(&decls))
        .expect_err("constructor equality operands must have one carrier sort");

    let red_wrong_carrier = terms.mk_app(
        Symbol::named("red"),
        Vec::new(),
        Sort::Uninterpreted("Other".to_string()),
    );
    let green_wrong_carrier = terms.mk_app(
        Symbol::named("green"),
        Vec::new(),
        Sort::Uninterpreted("Other".to_string()),
    );
    let wrong_carrier_lit = neq(&mut terms, red_wrong_carrier, green_wrong_carrier);
    validate(&terms, vec![wrong_carrier_lit], Some(&decls))
        .expect_err("registered names at another carrier sort are not constructors of Color");
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
        Some(&[]),
        None,
        None,
        None,
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

// ---- Datatype tester evaluation (`DatatypeTesterEval`) validation ----

fn tester(terms: &mut TermStore, ctor_name: &str, value: TermId) -> TermId {
    terms.mk_app(
        Symbol::named(format!("is-{ctor_name}")),
        vec![value],
        Sort::Bool,
    )
}

fn validate_tester(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    validate_tester_with_selectors(terms, clause, dt_decls, None)
}

fn validate_tester_with_selectors(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeTesterEval,
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
        ctor_selectors,
        Some(&[]),
        None,
        None,
        None,
        None,
    )
}

#[test]
fn tester_accepts_matching_positive_and_distinct_negative() {
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let is_red_red = tester(&mut terms, "red", red);
    let is_red_green = tester(&mut terms, "red", green);
    let not_is_red_green = terms.mk_not_raw(is_red_green);
    let decls = two_datatypes();

    validate_tester(&terms, vec![is_red_red], Some(&decls))
        .expect("a constructor's own tester must evaluate true");
    validate_tester(&terms, vec![not_is_red_green], Some(&decls))
        .expect("another constructor's tester must evaluate false");
    assert!(recognize_datatype_tester_eval(
        &terms,
        &[is_red_red],
        &decls
    ));
    assert!(recognize_datatype_tester_eval(
        &terms,
        &[not_is_red_green],
        &decls
    ));
}

#[test]
fn tester_rejects_wrong_polarity_cross_datatype_and_missing_registry() {
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let on = ctor(&mut terms, "on", "Light");
    let wrong_positive = tester(&mut terms, "red", green);
    let matching = tester(&mut terms, "red", red);
    let wrong_negative = terms.mk_not_raw(matching);
    let cross_datatype = tester(&mut terms, "red", on);
    let decls = two_datatypes();

    for forged in [wrong_positive, wrong_negative, cross_datatype] {
        validate_tester(&terms, vec![forged], Some(&decls))
            .expect_err("forged datatype tester evaluation must fail closed");
        assert!(!recognize_datatype_tester_eval(&terms, &[forged], &decls));
    }
    validate_tester(&terms, vec![matching], None)
        .expect_err("tester evaluation without declarations must fail closed");
}

#[test]
fn tester_rejects_unregistered_head_and_non_constructor_argument() {
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let unregistered = tester(&mut terms, "purple", red);
    let value = terms.mk_var("value", Sort::Uninterpreted("Color".to_string()));
    let non_constructor = tester(&mut terms, "red", value);
    let decls = two_datatypes();

    validate_tester(&terms, vec![unregistered], Some(&decls))
        .expect_err("an unregistered tester head must be rejected");
    validate_tester(&terms, vec![non_constructor], Some(&decls))
        .expect_err("a tester over a non-constructor is not a concrete evaluation theorem");
}

#[test]
fn tester_accepts_symbolic_exclusion_and_exact_exhaustiveness() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("value", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", value);
    let is_green = tester(&mut terms, "green", value);
    let not_red = terms.mk_not_raw(is_red);
    let not_green = terms.mk_not_raw(is_green);
    let decls = vec![(
        "Color".to_string(),
        vec!["red".to_string(), "green".to_string()],
    )];
    let selectors = vec![
        ("red".to_string(), Vec::new()),
        ("green".to_string(), Vec::new()),
    ];

    validate_tester(&terms, vec![not_red, not_green], Some(&decls))
        .expect("distinct constructor testers on one symbolic value are exclusive");
    validate_tester(&terms, vec![is_red, is_green], Some(&decls))
        .expect("all constructors of Color form an exhaustive tester clause");

    let red = ctor(&mut terms, "red", "Color");
    let value_is_red = eq(&mut terms, value, red);
    validate_tester_with_selectors(
        &terms,
        vec![is_green, value_is_red],
        Some(&decls),
        Some(&selectors),
    )
    .expect("two-constructor exhaustiveness may name a nullary sibling by equality");
}

#[test]
fn tester_symbolic_schemas_reject_forged_or_incomplete_clauses() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Uninterpreted("Color".to_string()));
    let y = terms.mk_var("y", Sort::Uninterpreted("Color".to_string()));
    let is_red_x = tester(&mut terms, "red", x);
    let is_green_x = tester(&mut terms, "green", x);
    let is_green_y = tester(&mut terms, "green", y);
    let not_red_x = terms.mk_not_raw(is_red_x);
    let not_green_y = terms.mk_not_raw(is_green_y);
    let decls = two_datatypes();

    validate_tester(&terms, vec![not_red_x, not_green_y], Some(&decls))
        .expect_err("tester exclusion over different subjects is not a theorem");
    validate_tester(&terms, vec![is_red_x], Some(&decls))
        .expect_err("one symbolic tester does not exhaust a two-constructor datatype");

    let mut three = decls.clone();
    three[0].1.push("blue".to_string());
    validate_tester(&terms, vec![is_red_x, is_green_x], Some(&three))
        .expect_err("omitting a registered constructor must fail closed");

    let wrong_sort = terms.mk_var("wrong", Sort::Uninterpreted("Light".to_string()));
    let red_wrong = tester(&mut terms, "red", wrong_sort);
    let green_wrong = tester(&mut terms, "green", wrong_sort);
    let not_red_wrong = terms.mk_not_raw(red_wrong);
    let not_green_wrong = terms.mk_not_raw(green_wrong);
    validate_tester(&terms, vec![not_red_wrong, not_green_wrong], Some(&decls))
        .expect_err("tester exclusion must authenticate the subject datatype sort");

    let two = vec![(
        "Color".to_string(),
        vec!["red".to_string(), "green".to_string()],
    )];
    let selectors = vec![
        ("red".to_string(), Vec::new()),
        ("green".to_string(), Vec::new()),
    ];
    let payload = terms.mk_int(1.into());
    let forged_non_nullary = terms.mk_app(
        Symbol::named("red"),
        vec![payload],
        Sort::Uninterpreted("Color".to_string()),
    );
    let x_is_forged = eq(&mut terms, x, forged_non_nullary);
    validate_tester_with_selectors(
        &terms,
        vec![is_green_x, x_is_forged],
        Some(&two),
        Some(&selectors),
    )
    .expect_err("a non-nullary constructor lookalike must not enter the nullary lane");

    let red_ctor = ctor(&mut terms, "red", "Color");
    let x_is_red = eq(&mut terms, x, red_ctor);
    let forged_arity = vec![
        ("red".to_string(), vec!["payload".to_string()]),
        ("green".to_string(), Vec::new()),
    ];
    validate_tester_with_selectors(
        &terms,
        vec![is_green_x, x_is_red],
        Some(&two),
        Some(&forged_arity),
    )
    .expect_err(
        "a syntactically nullary constructor must still match declaration-backed arity metadata",
    );

    validate_tester_with_selectors(&terms, vec![is_green_x, x_is_red], Some(&two), None)
        .expect_err("nullary exhaustiveness without constructor arity metadata must fail closed");
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

#[test]
fn project_rejects_indexed_homonyms() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pair = mk_pair(&mut terms, a, b);
    let sels = pair_selectors();

    let indexed_selector = terms.mk_app(Symbol::indexed("fst", vec![0]), vec![pair], Sort::Int);
    let indexed_selector_lit = eq(&mut terms, indexed_selector, a);
    validate_project(&terms, vec![indexed_selector_lit], Some(&sels))
        .expect_err("an indexed selector homonym is not a declared selector");

    let indexed_ctor = terms.mk_app(
        Symbol::indexed("mk", vec![0]),
        vec![a, b],
        Sort::Uninterpreted("Pair".to_string()),
    );
    let fst_indexed_ctor = sel(&mut terms, "fst", indexed_ctor);
    let indexed_ctor_lit = eq(&mut terms, fst_indexed_ctor, a);
    validate_project(&terms, vec![indexed_ctor_lit], Some(&sels))
        .expect_err("an indexed constructor homonym is not a declared constructor");

    let fst = sel(&mut terms, "fst", pair);
    let indexed_eq = terms.mk_app(Symbol::indexed("=", vec![0]), vec![fst, a], Sort::Bool);
    validate_project(&terms, vec![indexed_eq], Some(&sels))
        .expect_err("an indexed `=` is not a selector-projection equality");
}

#[test]
fn project_rejects_ill_sorted_constructor_selector_and_equality_apps() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let sels = pair_selectors();

    let wrong_carrier_ctor = terms.mk_app(Symbol::named("mk"), vec![a, b], Sort::Int);
    let selector_over_wrong_carrier = sel(&mut terms, "fst", wrong_carrier_ctor);
    let wrong_carrier_lit = eq(&mut terms, selector_over_wrong_carrier, a);
    validate_project(&terms, vec![wrong_carrier_lit], Some(&sels))
        .expect_err("a constructor application must have a datatype carrier sort");

    let pair = mk_pair(&mut terms, a, b);
    let bool_selector = terms.mk_app(Symbol::named("fst"), vec![pair], Sort::Bool);
    let mismatched_equality = terms.mk_app(Symbol::named("="), vec![bool_selector, a], Sort::Bool);
    validate_project(&terms, vec![mismatched_equality], Some(&sels))
        .expect_err("selector result and projected field must have the same sort");

    let fst = sel(&mut terms, "fst", pair);
    let non_bool_equality = terms.mk_app(Symbol::named("="), vec![fst, a], Sort::Int);
    validate_project(&terms, vec![non_bool_equality], Some(&sels))
        .expect_err("a projection equality must itself have sort Bool");
}

// ---- Datatype constructor coverage (`DatatypeExhaustive`) validation ----

/// Validate a `DatatypeExhaustive` step with the given datatype registry.
fn validate_exhaustive(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeExhaustive,
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
        Some(&[]),
        None,
        None,
        None,
        None,
    )
}

#[test]
fn exhaustive_accepts_full_coverage_disjunction() {
    // (cl (is-red t) (is-green t) (is-blue t)) over t : Color — every declared
    // constructor covered exactly once. Accepted both as a multi-literal
    // clause and as the single interned `or` term the emitter records.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let is_blue = tester(&mut terms, "blue", t);
    let decls = two_datatypes();

    validate_exhaustive(&terms, vec![is_red, is_green, is_blue], Some(&decls))
        .expect("full Color coverage must be accepted");
    let or_term = terms.mk_or(vec![is_red, is_green, is_blue]);
    validate_exhaustive(&terms, vec![or_term], Some(&decls))
        .expect("the interned or-term form must be accepted");
    assert!(recognize_datatype_exhaustive(&terms, &[or_term], &decls));
}

#[test]
fn exhaustive_accepts_single_constructor_unit() {
    // For (declare-datatype Single ((only ...))) the coverage disjunction
    // degenerates to the unit tester (that is what `mk_or` interns).
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Single".to_string()));
    let is_only = tester(&mut terms, "only", t);
    let decls = vec![("Single".to_string(), vec!["only".to_string()])];

    validate_exhaustive(&terms, vec![is_only], Some(&decls))
        .expect("single-constructor unit coverage must be accepted");
    assert!(recognize_datatype_exhaustive(&terms, &[is_only], &decls));
}

#[test]
fn exhaustive_rejects_non_exhaustive_tester_list() {
    // (cl (is-red t) (is-green t)) omits blue — NOT a tautology (t may be
    // blue). The coverage list comes from the registry, never the clause.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let decls = two_datatypes();

    let err = validate_exhaustive(&terms, vec![is_red, is_green], Some(&decls))
        .expect_err("truncated coverage must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_exhaustive(
        &terms,
        &[is_red, is_green],
        &decls
    ));
}

#[test]
fn exhaustive_rejects_wrong_sort_scrutinee() {
    // Color testers over a Light-sorted scrutinee: is-red etc. decide nothing
    // about a Light value, so the clause is not a Color-coverage tautology.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Light".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let is_blue = tester(&mut terms, "blue", t);
    let decls = two_datatypes();

    let err = validate_exhaustive(&terms, vec![is_red, is_green, is_blue], Some(&decls))
        .expect_err("scrutinee sort must match the testers' datatype");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn exhaustive_rejects_mixed_subjects_datatypes_negations_and_duplicates() {
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let u = terms.mk_var("u", Sort::Uninterpreted("Color".to_string()));
    let is_red_t = tester(&mut terms, "red", t);
    let is_green_t = tester(&mut terms, "green", t);
    let is_blue_t = tester(&mut terms, "blue", t);
    let is_blue_u = tester(&mut terms, "blue", u);
    let decls = two_datatypes();

    // Mixed subjects: coverage must be over ONE scrutinee.
    validate_exhaustive(&terms, vec![is_red_t, is_green_t, is_blue_u], Some(&decls))
        .expect_err("mixed scrutinees must be rejected");

    // A negative literal is not coverage.
    let not_is_blue_t = terms.mk_not(is_blue_t);
    validate_exhaustive(
        &terms,
        vec![is_red_t, is_green_t, not_is_blue_t],
        Some(&decls),
    )
    .expect_err("negated testers must be rejected");

    // Duplicate tester padding the count to the constructor count.
    validate_exhaustive(&terms, vec![is_red_t, is_red_t, is_green_t], Some(&decls))
        .expect_err("duplicate testers must be rejected");

    // Cross-datatype tester mixed in.
    let is_on_t = tester(&mut terms, "on", t);
    validate_exhaustive(&terms, vec![is_red_t, is_green_t, is_on_t], Some(&decls))
        .expect_err("cross-datatype testers must be rejected");

    // Unregistered tester head.
    let is_unknown_t = tester(&mut terms, "unknown", t);
    validate_exhaustive(
        &terms,
        vec![is_red_t, is_green_t, is_unknown_t],
        Some(&decls),
    )
    .expect_err("unregistered testers must be rejected");
}

#[test]
fn exhaustive_rejects_constructor_application_scrutinee() {
    // Coverage over an explicit constructor application is the tester
    // EVALUATION family; the exhaustiveness lane stays disjoint from it.
    let mut terms = TermStore::new();
    let red = ctor(&mut terms, "red", "Color");
    let is_red = tester(&mut terms, "red", red);
    let is_green = tester(&mut terms, "green", red);
    let is_blue = tester(&mut terms, "blue", red);
    let decls = two_datatypes();

    let err = validate_exhaustive(&terms, vec![is_red, is_green, is_blue], Some(&decls))
        .expect_err("constructor-application scrutinee must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn exhaustive_fails_closed_without_registry() {
    // A genuine coverage clause, but NO datatype registry: strict mode cannot
    // establish that the tester list is complete — it fails closed.
    let mut terms = TermStore::new();
    let t = terms.mk_var("t", Sort::Uninterpreted("Color".to_string()));
    let is_red = tester(&mut terms, "red", t);
    let is_green = tester(&mut terms, "green", t);
    let is_blue = tester(&mut terms, "blue", t);

    let err = validate_exhaustive(&terms, vec![is_red, is_green, is_blue], None)
        .expect_err("exhaustiveness with no registry must fail closed");
    assert!(matches!(
        err,
        ProofCheckError::UnsupportedTheoryLemmaKind { .. }
    ));
}

include!("datatype_axiom_tests/reconstruction.rs");
