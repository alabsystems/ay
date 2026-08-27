// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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

fn assert_value_eq_congruence_engaged_and_fail_closed(
    terms: &TermStore,
    dt_decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) {
    let value_eq_step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::DatatypeValueEqCongruence,
        lia: None,
    };
    let mut derived = Vec::new();
    let engaged = validate_step_with_datatypes(
        terms,
        &mut derived,
        ProofId(0),
        &value_eq_step,
        true,
        Some(dt_decls),
        Some(ctor_selectors),
        Some(&[]),
        None,
        None,
        None,
        None,
    )
    .expect_err("empty value-eq clause must be rejected by the validator");
    assert!(
        matches!(engaged, ProofCheckError::InvalidTheoryLemma { .. }),
        "promoted kind must reach its validator with both registries: {engaged:?}"
    );
    let mut derived = Vec::new();
    let unauthorized = validate_step_with_datatypes(
        terms,
        &mut derived,
        ProofId(0),
        &value_eq_step,
        true,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
    )
    .expect_err("value-eq without the registries must fail closed");
    assert!(
        matches!(
            unauthorized,
            ProofCheckError::UnsupportedTheoryLemmaKind { .. }
        ),
        "registry-free value-eq must stay unsupported: {unauthorized:?}"
    );
}

#[test]
fn c5b_kinds_remain_inert_with_both_registries() {
    let terms = TermStore::new();
    let dt_decls = pair_datatype();
    let ctor_selectors = pair_selectors();

    // `DatatypeAcyclicDirect` was PROMOTED out of the inert set on
    // 2026-08-19 (real validator: iterative bounded constructor-containment
    // walk) and `DatatypeValueEqCongruence` on 2026-08-20 (registry-complete
    // biconditional validator); both are covered by their own shape tests
    // plus the engaged-but-fail-closed assertions below the loop.
    {
        let kind = TheoryLemmaKind::DatatypeInjective;
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
        None,
    )
    .expect_err("empty acyclicity clause must be rejected by the validator");
    assert!(
        matches!(engaged, ProofCheckError::InvalidTheoryLemma { .. }),
        "promoted kind must reach its validator with both registries: {engaged:?}"
    );
    assert_value_eq_congruence_engaged_and_fail_closed(&terms, &dt_decls, &ctor_selectors);
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
