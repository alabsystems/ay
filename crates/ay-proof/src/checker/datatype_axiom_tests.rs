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
        Some(&[]),
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

// ---- Guarded constructor reconstruction (`DatatypeConstructorReconstruct`) ----

/// `(declare-datatype Pair ((mk (fst Int) (snd Int))))` datatype registry.
fn pair_datatype() -> Vec<(String, Vec<String>)> {
    vec![("Pair".to_string(), vec!["mk".to_string()])]
}

/// `(declare-datatype List ((nil) (cons (hd Int) (tl List))))` registries.
fn list_datatype() -> Vec<(String, Vec<String>)> {
    vec![(
        "List".to_string(),
        vec!["nil".to_string(), "cons".to_string()],
    )]
}

fn list_selectors() -> Vec<(String, Vec<String>)> {
    vec![
        ("nil".to_string(), Vec::new()),
        ("cons".to_string(), vec!["hd".to_string(), "tl".to_string()]),
    ]
}

/// Validate a `DatatypeConstructorReconstruct` step with the given registries.
fn validate_reconstruct(
    terms: &TermStore,
    clause: Vec<TermId>,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeConstructorReconstruct,
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
    )
}

/// `(mk (fst x) (snd x))` — the canonical reconstruction of `x : Pair`.
fn rebuilt_pair(terms: &mut TermStore, x: TermId) -> TermId {
    let fst_x = sel(terms, "fst", x);
    let snd_x = sel(terms, "snd", x);
    terms.mk_app(
        Symbol::named("mk"),
        vec![fst_x, snd_x],
        Sort::Uninterpreted("Pair".to_string()),
    )
}

#[test]
fn reconstruct_accepts_pair_shape_in_all_orientations() {
    // (cl (not (is-mk x)) (= x (mk (fst x) (snd x)))) — both literal orders
    // and both equality orientations (mk_or/mk_eq canonicalize arbitrarily),
    // plus the single interned or-term the emitter records.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let is_mk = tester(&mut terms, "mk", x);
    let guard = terms.mk_not(is_mk);
    let rebuilt = rebuilt_pair(&mut terms, x);
    let eq_xr = eq(&mut terms, x, rebuilt);
    let eq_rx = eq(&mut terms, rebuilt, x);
    let decls = pair_datatype();
    let sels = pair_selectors();

    for clause in [
        vec![guard, eq_xr],
        vec![eq_xr, guard],
        vec![guard, eq_rx],
        vec![eq_rx, guard],
    ] {
        validate_reconstruct(&terms, clause, Some(&decls), Some(&sels))
            .expect("guarded pair reconstruction must be accepted in every orientation");
    }
    let or_term = terms.mk_or(vec![guard, eq_xr]);
    validate_reconstruct(&terms, vec![or_term], Some(&decls), Some(&sels))
        .expect("the interned or-term form must be accepted");
    assert!(recognize_datatype_constructor_reconstruct(
        &terms,
        &[or_term],
        &decls,
        &sels
    ));
}

#[test]
fn reconstruct_accepts_registry_nullary_constant() {
    // (cl (not (is-nil x)) (= x nil)) — nil is REGISTERED with zero fields,
    // so the conclusion is the bare constant.
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", list_sort.clone());
    let nil = terms.mk_var("nil", list_sort);
    let is_nil = tester(&mut terms, "nil", x);
    let guard = terms.mk_not(is_nil);
    let concl = eq(&mut terms, x, nil);
    let decls = list_datatype();
    let sels = list_selectors();

    validate_reconstruct(&terms, vec![guard, concl], Some(&decls), Some(&sels))
        .expect("nullary reconstruction must be accepted");
    assert!(recognize_datatype_constructor_reconstruct(
        &terms,
        &[guard, concl],
        &decls,
        &sels
    ));
}

#[test]
fn reconstruct_rejects_wrong_selector_order() {
    // (cl (not (is-mk x)) (= x (mk (snd x) (fst x)))) — PERMUTED fields. This
    // swaps the components and is FALSE whenever fst(x) != snd(x).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let is_mk = tester(&mut terms, "mk", x);
    let guard = terms.mk_not(is_mk);
    let fst_x = sel(&mut terms, "fst", x);
    let snd_x = sel(&mut terms, "snd", x);
    let permuted = terms.mk_app(
        Symbol::named("mk"),
        vec![snd_x, fst_x],
        Sort::Uninterpreted("Pair".to_string()),
    );
    let concl = eq(&mut terms, x, permuted);
    let decls = pair_datatype();
    let sels = pair_selectors();

    let err = validate_reconstruct(&terms, vec![guard, concl], Some(&decls), Some(&sels))
        .expect_err("permuted selector order must be rejected");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
    assert!(!recognize_datatype_constructor_reconstruct(
        &terms,
        &[guard, concl],
        &decls,
        &sels
    ));
}

#[test]
fn reconstruct_rejects_truncated_repeated_or_foreign_selector_chains() {
    let mut terms = TermStore::new();
    let pair_sort = Sort::Uninterpreted("Pair".to_string());
    let x = terms.mk_var("x", pair_sort.clone());
    let y = terms.mk_var("y", pair_sort.clone());
    let is_mk = tester(&mut terms, "mk", x);
    let guard = terms.mk_not(is_mk);
    let fst_x = sel(&mut terms, "fst", x);
    let snd_y = sel(&mut terms, "snd", y);
    let decls = pair_datatype();
    let sels = pair_selectors();

    // Truncated: mk applied to ONE selector.
    let truncated = terms.mk_app(Symbol::named("mk"), vec![fst_x], pair_sort.clone());
    let concl_truncated = eq(&mut terms, x, truncated);
    validate_reconstruct(
        &terms,
        vec![guard, concl_truncated],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("truncated selector chain must be rejected");

    // Repeated: (mk (fst x) (fst x)) — snd position not projected.
    let repeated = terms.mk_app(Symbol::named("mk"), vec![fst_x, fst_x], pair_sort.clone());
    let concl_repeated = eq(&mut terms, x, repeated);
    validate_reconstruct(
        &terms,
        vec![guard, concl_repeated],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("repeated selector must be rejected");

    // Foreign subject inside the chain: (mk (fst x) (snd y)).
    let foreign = terms.mk_app(Symbol::named("mk"), vec![fst_x, snd_y], pair_sort.clone());
    let concl_foreign = eq(&mut terms, x, foreign);
    validate_reconstruct(
        &terms,
        vec![guard, concl_foreign],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("selector over a different subject must be rejected");

    // Correct chain but the equality relates the WRONG subject.
    let rebuilt_x = rebuilt_pair(&mut terms, x);
    let concl_wrong_subject = eq(&mut terms, y, rebuilt_x);
    validate_reconstruct(
        &terms,
        vec![guard, concl_wrong_subject],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("equality subject must be the guarded scrutinee");

    // Positive guard: (cl (is-mk x) (= x (mk (fst x) (snd x)))) is NOT the
    // guarded reconstruction shape.
    let concl = eq(&mut terms, x, rebuilt_x);
    validate_reconstruct(&terms, vec![is_mk, concl], Some(&decls), Some(&sels))
        .expect_err("a positive guard must be rejected");
}

#[test]
fn reconstruct_rejects_wrong_sort_and_unregistered_names() {
    let mut terms = TermStore::new();
    let decls = pair_datatype();
    let sels = pair_selectors();

    // Scrutinee whose sort is NOT the constructor's datatype.
    let wrong = terms.mk_var("w", Sort::Uninterpreted("Color".to_string()));
    let is_mk_wrong = tester(&mut terms, "mk", wrong);
    let guard_wrong = terms.mk_not(is_mk_wrong);
    let fst_w = sel(&mut terms, "fst", wrong);
    let snd_w = sel(&mut terms, "snd", wrong);
    let rebuilt_w = terms.mk_app(
        Symbol::named("mk"),
        vec![fst_w, snd_w],
        Sort::Uninterpreted("Color".to_string()),
    );
    let concl_wrong = eq(&mut terms, wrong, rebuilt_w);
    validate_reconstruct(
        &terms,
        vec![guard_wrong, concl_wrong],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("scrutinee sort must match the constructor's datatype");

    // Unregistered constructor name (registry knows only `mk`).
    let x = terms.mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let is_other = tester(&mut terms, "other", x);
    let guard_other = terms.mk_not(is_other);
    let fst_x = sel(&mut terms, "fst", x);
    let snd_x = sel(&mut terms, "snd", x);
    let rebuilt_other = terms.mk_app(
        Symbol::named("other"),
        vec![fst_x, snd_x],
        Sort::Uninterpreted("Pair".to_string()),
    );
    let concl_other = eq(&mut terms, x, rebuilt_other);
    validate_reconstruct(
        &terms,
        vec![guard_other, concl_other],
        Some(&decls),
        Some(&sels),
    )
    .expect_err("unregistered constructor must be rejected");

    // Registered constructor but MISSING selector-registry entry: nullarity /
    // field list cannot be established -> fail closed.
    let is_mk = tester(&mut terms, "mk", x);
    let guard = terms.mk_not(is_mk);
    let rebuilt = rebuilt_pair(&mut terms, x);
    let concl = eq(&mut terms, x, rebuilt);
    let empty_sels: Vec<(String, Vec<String>)> = Vec::new();
    validate_reconstruct(&terms, vec![guard, concl], Some(&decls), Some(&empty_sels))
        .expect_err("missing selector-registry entry must fail closed");

    // Forged nullary: cons is registered WITH fields, so `(= x cons)` (a bare
    // Var named cons) must not pass as a reconstruction.
    let list_sort = Sort::Uninterpreted("List".to_string());
    let l = terms.mk_var("l", list_sort.clone());
    let cons_const = terms.mk_var("cons", list_sort);
    let is_cons = tester(&mut terms, "cons", l);
    let guard_cons = terms.mk_not(is_cons);
    let concl_cons = eq(&mut terms, l, cons_const);
    let ldecls = list_datatype();
    let lsels = list_selectors();
    validate_reconstruct(
        &terms,
        vec![guard_cons, concl_cons],
        Some(&ldecls),
        Some(&lsels),
    )
    .expect_err("a non-nullary constructor must not reconstruct as a bare constant");
}

#[test]
fn reconstruct_fails_closed_without_either_registry() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let is_mk = tester(&mut terms, "mk", x);
    let guard = terms.mk_not(is_mk);
    let rebuilt = rebuilt_pair(&mut terms, x);
    let concl = eq(&mut terms, x, rebuilt);
    let decls = pair_datatype();
    let sels = pair_selectors();

    for (dt, cs) in [
        (None, Some(&sels[..])),
        (Some(&decls[..]), None),
        (None, None),
    ] {
        let err = validate_reconstruct(&terms, vec![guard, concl], dt, cs)
            .expect_err("reconstruction without both registries must fail closed");
        assert!(matches!(
            err,
            ProofCheckError::UnsupportedTheoryLemmaKind { .. }
        ));
    }
}

#[test]
fn c5b_kinds_remain_inert_with_both_registries() {
    let terms = TermStore::new();
    let dt_decls = pair_datatype();
    let ctor_selectors = pair_selectors();

    // `DatatypeAcyclicDirect` was PROMOTED out of the inert set on
    // 2026-08-19 (real validator: iterative bounded constructor-containment
    // walk); it is covered by its own shape tests plus the engaged-but-
    // fail-closed assertion below the loop.
    for kind in [
        TheoryLemmaKind::DatatypeInjective,
        TheoryLemmaKind::DatatypeValueEqCongruence,
    ] {
        let step = ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: Vec::new(),
            farkas: None,
            kind,
            lia: None,
        };
        let mut derived = Vec::new();
        let error = validate_step_with_datatypes(
            &terms,
            &mut derived,
            ProofId(0),
            &step,
            true,
            Some(&dt_decls),
            Some(&ctor_selectors),
            Some(&[]),
            None,
            None,
            None,
        )
        .expect_err("inert C5b kinds must fail closed even with both registries");

        assert_eq!(
            error,
            ProofCheckError::UnsupportedTheoryLemmaKind {
                step: ProofId(0),
                kind,
            }
        );
    }

    // The promoted acyclicity kind is ENGAGED with both registries: an empty
    // clause is now refused by the VALIDATOR (InvalidTheoryLemma), not by the
    // unsupported-kind gate — and without the registry it still fails closed
    // as unsupported.
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::DatatypeAcyclicDirect,
        lia: None,
    };
    let mut derived = Vec::new();
    let engaged = validate_step_with_datatypes(
        &terms,
        &mut derived,
        ProofId(0),
        &step,
        true,
        Some(&dt_decls),
        Some(&ctor_selectors),
        Some(&[]),
        None,
        None,
        None,
    )
    .expect_err("empty acyclicity clause must be rejected by the validator");
    assert!(
        matches!(engaged, ProofCheckError::InvalidTheoryLemma { .. }),
        "promoted kind must reach its validator with both registries: {engaged:?}"
    );
    let mut derived = Vec::new();
    let unauthorized = validate_step_with_datatypes(
        &terms,
        &mut derived,
        ProofId(0),
        &step,
        true,
        None,
        None,
        None,
        None,
        None,
        None,
    )
    .expect_err("acyclicity without the registry must fail closed");
    assert!(
        matches!(
            unauthorized,
            ProofCheckError::UnsupportedTheoryLemmaKind { .. }
        ),
        "registry-free acyclicity must stay unsupported: {unauthorized:?}"
    );
}
