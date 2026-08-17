// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn norm_proves_constructor_characterization() {
    // (= (= (Some v) x) (and (is-Some x) (= v (value x)))) — a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq = app(&mut ts, "=", &[v, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "constructor characterization must be proved"
    );
}

#[test]
fn norm_proves_is_ctor_roundtrip_and_sole_ctor() {
    // (= (is-Mk x) (= x (Mk (fst x) (snd x)))) — round-trip, sole ctor.
    let mut ts = TermStore::new();
    let bx = box_sort();
    let x = ts.mk_var("x", bx.clone());
    let is_mk = app(&mut ts, "is-Mk", &[x], Sort::Bool);
    let fst = app(&mut ts, "fst", &[x], Sort::Int);
    let snd = app(&mut ts, "snd", &[x], Sort::Int);
    let mk = app(&mut ts, "Mk", &[fst, snd], bx.clone());
    let eq = app(&mut ts, "=", &[x, mk], Sort::Bool);
    let bicond = app(&mut ts, "=", &[is_mk, eq], Sort::Bool);
    assert!(is_taut(&ts, bicond), "is-C round-trip must be proved");

    // Sole-constructor tester is a tautology: (is-Mk x).
    assert!(is_taut(&ts, is_mk), "sole-ctor tester must be proved");
}

#[test]
fn norm_proves_nullary_and_none_equality() {
    // None is nullary: (is-None None), (not (is-Some None)),
    // (= (= None x) (is-None x)).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone()); // front-end lowering of `(None)`
    let x = ts.mk_var("x", opt.clone());
    let is_none_none = app(&mut ts, "is-None", &[none], Sort::Bool);
    assert!(is_taut(&ts, is_none_none), "is-None(None) must be proved");

    let is_some_none = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let not_is_some = app(&mut ts, "not", &[is_some_none], Sort::Bool);
    assert!(
        is_taut(&ts, not_is_some),
        "(not is-Some(None)) must be proved"
    );

    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let is_none_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, is_none_x], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "(= (= None x)(is-None x)) must be proved"
    );
}

#[test]
fn norm_rejects_missing_field_characterization() {
    // SOUNDNESS near-miss: DROP the field equality.
    // (= (= (Some v) x) (is-Some x)) is NOT a tautology (needs v = value x).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, is_some], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "dropping the field eq must NOT be proved (unsound)"
    );
}

#[test]
fn norm_rejects_wrong_field_and_bare_constructor_eq() {
    // (= (= (Some a) x) (and (is-Some x) (= b (value x)))) with a != b: NOT valid.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let inner = app(&mut ts, "=", &[some_a, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq_b = app(&mut ts, "=", &[b, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq_b], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "wrong field var must NOT be proved (unsound)"
    );

    // Bare (= (Some a) x) is NOT a tautology.
    assert!(
        !is_taut(&ts, inner),
        "bare constructor eq must NOT be proved"
    );

    // Injectivity is NOT vacuous: (= (Some a)(Some b)) is NOT a tautology.
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let inj = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    assert!(
        !is_taut(&ts, inj),
        "(= (Some a)(Some b)) must NOT be proved"
    );
}

#[test]
fn norm_rejects_two_ctor_tester_and_distinctness_confusion() {
    // (is-Some x) for the 2-ctor Opt with x free: NOT a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(
        !is_taut(&ts, is_some),
        "2-ctor tester on free var must NOT be proved"
    );

    // (= (Some a) None) reduces to false; asserting it is NOT a tautology,
    // but its NEGATION is: (not (= (Some a) None)).
    let a = ts.mk_var("a", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let none = ts.mk_var("None", opt.clone());
    let eq = app(&mut ts, "=", &[some_a, none], Sort::Bool);
    assert!(
        !is_taut(&ts, eq),
        "(= (Some a) None) must NOT be proved true"
    );
    let neg = app(&mut ts, "not", &[eq], Sort::Bool);
    assert!(
        is_taut(&ts, neg),
        "distinct constructors: negation IS a tautology"
    );
}

#[test]
fn norm_proves_injectivity_biconditional() {
    // (= (= (Some a) (Some b)) (= a b)) — injectivity, a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let lhs = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    let rhs = app(&mut ts, "=", &[a, b], Sort::Bool);
    let bicond = app(&mut ts, "=", &[lhs, rhs], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "injectivity biconditional must be proved"
    );
}

#[test]
fn norm_proves_nested_datatype_field_characterization() {
    // Mirrors g4: PbConstraint_mk(fld_terms: Vec, ...) where Vec is itself a
    // single-ctor datatype. The congruence axiom over a NESTED constructor field
    // must characterize recursively through the selector path.
    let mut ts = TermStore::new();
    let vec_s = Sort::Datatype(DatatypeSort::new(
        "Vec",
        vec![DatatypeConstructor::new(
            "Vmk",
            vec![DatatypeField::new("data", Sort::Int)],
        )],
    ));
    let pc = Sort::Datatype(DatatypeSort::new(
        "PC",
        vec![DatatypeConstructor::new(
            "Pmk",
            vec![
                DatatypeField::new("terms", vec_s.clone()),
                DatatypeField::new("rhs", Sort::Int),
            ],
        )],
    ));
    let x = ts.mk_var("x", pc.clone());
    let d = ts.mk_var("d", Sort::Int);
    let rhs = ts.mk_var("rhs", Sort::Int);
    let vmk = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let pmk = app(&mut ts, "Pmk", &[vmk, rhs], pc.clone());
    let inner = app(&mut ts, "=", &[pmk, x], Sort::Bool);
    // RHS: (and (is-Pmk x) (= (Vmk d) (terms x)) (= rhs (rhs x)))
    let is_pmk = app(&mut ts, "is-Pmk", &[x], Sort::Bool);
    let terms_x = app(&mut ts, "terms", &[x], vec_s.clone());
    let vmk2 = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let eq_terms = app(&mut ts, "=", &[vmk2, terms_x], Sort::Bool);
    let rhs_x = app(&mut ts, "rhs", &[x], Sort::Int);
    let eq_rhs = app(&mut ts, "=", &[rhs, rhs_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_pmk, eq_terms, eq_rhs], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "nested-field constructor characterization must be proved"
    );

    // SOUNDNESS near-miss: swap the nested field var d -> e (e != d).
    let e = ts.mk_var("e", Sort::Int);
    let vmk_e = app(&mut ts, "Vmk", &[e], vec_s.clone());
    let eq_terms_bad = app(&mut ts, "=", &[vmk_e, terms_x], Sort::Bool);
    let conj_bad = app(&mut ts, "and", &[is_pmk, eq_terms_bad, eq_rhs], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj_bad], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "mismatched nested field must NOT be proved (unsound)"
    );
}

#[test]
fn norm_proves_structural_equality_characterization_two_ctor() {
    // (= (= None x) (and (= (is-None x)(is-None None)) (= (is-Some x)(is-Some None))
    //                    (or (not (is-Some None)) (= (value x)(value None)))))
    // — the full 2-ctor structural-equality axiom; a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone());
    let x = ts.mk_var("x", opt.clone());
    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let isn_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let isn_n = app(&mut ts, "is-None", &[none], Sort::Bool);
    let e1 = app(&mut ts, "=", &[isn_x, isn_n], Sort::Bool);
    let iss_x = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let iss_n = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let e2 = app(&mut ts, "=", &[iss_x, iss_n], Sort::Bool);
    let not_iss_n = app(&mut ts, "not", &[iss_n], Sort::Bool);
    let val_x = app(&mut ts, "value", &[x], Sort::Int);
    let val_n = app(&mut ts, "value", &[none], Sort::Int);
    let e3v = app(&mut ts, "=", &[val_x, val_n], Sort::Bool);
    let e3 = app(&mut ts, "or", &[not_iss_n, e3v], Sort::Bool);
    let big = app(&mut ts, "and", &[e1, e2, e3], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, big], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "2-ctor structural-eq characterization must be proved"
    );
}

#[test]
fn norm_two_ctor_exclusivity_is_not_overreaching() {
    // SOUNDNESS: is-None(x) alone is NOT a tautology; nor is is-Some(x); nor their
    // conjunction; but their disjunction IS (exhaustiveness).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let isn = app(&mut ts, "is-None", &[x], Sort::Bool);
    let iss = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(!is_taut(&ts, isn), "is-None(x) must NOT be a tautology");
    assert!(!is_taut(&ts, iss), "is-Some(x) must NOT be a tautology");
    let conj = app(&mut ts, "and", &[isn, iss], Sort::Bool);
    assert!(
        !is_taut(&ts, conj),
        "is-None ∧ is-Some must NOT be a tautology"
    );
    let disj = app(&mut ts, "or", &[isn, iss], Sort::Bool);
    assert!(
        is_taut(&ts, disj),
        "is-None ∨ is-Some IS a tautology (exhaustive)"
    );
}
