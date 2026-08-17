// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::funnel::DatatypeRegistryData;
use super::*;
use num_bigint::BigInt;

// =====================================================================
// #trust->0 C3: funnel EUF/DT recognition
// =====================================================================

/// The funnel classifies an EUF transitivity clause handed to it in a
/// NON-validator order, returns the validator order, and the reordered
/// clause is the same literal set.
#[test]
fn c3_funnel_recognizes_and_reorders_euf_transitive() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let c = terms.mk_var("c", u);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_ab = terms.mk_not(eq_ab);
    let not_bc = terms.mk_not(eq_bc);

    // Conclusion FIRST — the order the EUF validator rejects.
    let clause = vec![eq_ac, not_ab, not_bc];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::EufTransitive);
    let ordered = ordered.into_owned();
    assert_eq!(*ordered.last().expect("non-empty"), eq_ac);
    let mut sorted_in = clause.clone();
    sorted_in.sort_unstable();
    let mut sorted_out = ordered.clone();
    sorted_out.sort_unstable();
    assert_eq!(sorted_in, sorted_out, "reorder must be a permutation");
    // Classifier == validator on the RETURNED clause.
    assert!(ay_proof::recognize_euf_transitive(&terms, &ordered));
    assert!(
        !ay_proof::recognize_euf_transitive(&terms, &clause),
        "precondition: the input order itself must be validator-rejected"
    );
}

/// Congruence and congruent-pred shapes classify with the validator order.
#[test]
fn c3_funnel_recognizes_euf_congruent_and_pred() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let eq_ab = terms.mk_eq(a, b);
    let not_ab = terms.mk_not(eq_ab);
    let f_a = terms.mk_app(Symbol::named("f"), [a], u.clone());
    let f_b = terms.mk_app(Symbol::named("f"), [b], u);
    let eq_fafb = terms.mk_eq(f_a, f_b);

    let clause = vec![eq_fafb, not_ab];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::EufCongruent);
    assert!(ay_proof::recognize_euf_congruent(&terms, &ordered));

    let p_a = terms.mk_app(Symbol::named("p"), [a], Sort::Bool);
    let p_b = terms.mk_app(Symbol::named("p"), [b], Sort::Bool);
    let not_p_a = terms.mk_not(p_a);
    let clause = vec![p_b, not_ab, not_p_a];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::EufCongruentPred);
    assert!(ay_proof::recognize_euf_congruent_pred(&terms, &ordered));
}

/// A reflexive conclusion carrying premise literals must DECLINE: the
/// conflict-lane inference would shrink the clause to the reflexive unit,
/// and a funnel result that drops literals from a materialized (possibly
/// trace-recorded) clause would break set-equivalence authentication.
/// The pure unit reflexive clause still classifies.
#[test]
fn c3_funnel_reflexive_only_when_no_literal_is_dropped() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u);
    let eq_ab = terms.mk_eq(a, b);
    let not_ab = terms.mk_not(eq_ab);
    // Raw `(= a a)` — `mk_eq` folds it to `true`.
    let raw_eq_aa = terms.mk_app(Symbol::named("="), [a, a], Sort::Bool);

    let (kind, _) = infer_theory_lemma_kind_from_clause_terms_and_farkas(
        &terms,
        &[not_ab, raw_eq_aa],
        None,
        None,
    );
    assert_eq!(
        kind,
        TheoryLemmaKind::Generic,
        "literal-dropping inference must decline"
    );

    let unit_clause = [raw_eq_aa];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &unit_clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::EufReflexive);
    assert_eq!(ordered.as_ref(), &unit_clause);
}

/// DT recognition is registry-gated fail-closed: the same clause is
/// `Generic` without registries and the validator-backed DT kind with
/// them; the clause is never reordered.
#[test]
fn c3_funnel_dt_recognition_is_registry_gated() {
    let mut terms = TermStore::new();
    let pair = Sort::Uninterpreted("Pair".to_string());
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let mk_pair = terms.mk_app(Symbol::named("mk"), [one, two], pair.clone());
    let first_app = terms.mk_app(Symbol::named("first"), [mk_pair], Sort::Int);
    let selector_axiom = terms.mk_eq(first_app, one);
    let tester = terms.mk_app(Symbol::named("is-mk"), [mk_pair], Sort::Bool);
    let mk2_pair = terms.mk_app(Symbol::named("mk2"), [one, two], pair);
    let ctor_eq = terms.mk_eq(mk_pair, mk2_pair);
    let distinct_axiom = terms.mk_not(ctor_eq);

    let registry_data: DatatypeRegistryData = (
        vec![(
            "Pair".to_string(),
            vec!["mk".to_string(), "mk2".to_string()],
        )],
        vec![
            (
                "mk".to_string(),
                vec!["first".to_string(), "second".to_string()],
            ),
            (
                "mk2".to_string(),
                vec!["fst2".to_string(), "snd2".to_string()],
            ),
        ],
    );
    let registries = DatatypeRegistries::from_data(&registry_data);

    for (clause, with_registry_kind) in [
        (
            vec![selector_axiom],
            TheoryLemmaKind::DatatypeSelectorProject,
        ),
        (vec![tester], TheoryLemmaKind::DatatypeTesterEval),
        (vec![distinct_axiom], TheoryLemmaKind::DatatypeDistinct),
    ] {
        let (kind, ordered) =
            infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
        assert_eq!(kind, TheoryLemmaKind::Generic, "no registry => Generic");
        assert_eq!(ordered.as_ref(), clause.as_slice());

        let (kind, ordered) = infer_theory_lemma_kind_from_clause_terms_and_farkas(
            &terms,
            &clause,
            None,
            Some(&registries),
        );
        assert_eq!(kind, with_registry_kind);
        assert_eq!(ordered.as_ref(), clause.as_slice(), "DT never reorders");
    }
}

/// The macro-arm recorder adopts the funnel's reordered clause: the
/// tracker step and the returned clause are BOTH the validator order.
#[test]
fn c3_record_funnel_classified_lemma_adopts_reordered_clause() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let c = terms.mk_var("c", u);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_ab = terms.mk_not(eq_ab);
    let not_bc = terms.mk_not(eq_bc);

    let mut tracker = ProofTracker::new();
    tracker.enable();
    let (kind, recorded) =
        record_funnel_classified_lemma(&mut tracker, &terms, vec![eq_ac, not_ab, not_bc], None);
    assert_eq!(kind, TheoryLemmaKind::EufTransitive);
    assert_eq!(*recorded.last().expect("non-empty"), eq_ac);
    assert!(ay_proof::recognize_euf_transitive(&terms, &recorded));

    let proof = tracker.take_proof();
    let step = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ay_core::ProofStep::TheoryLemma { kind, clause, .. } => Some((kind, clause)),
            _ => None,
        })
        .expect("theory lemma recorded");
    assert_eq!(*step.0, TheoryLemmaKind::EufTransitive);
    assert_eq!(step.1, &recorded, "tracker must hold the validator order");
}
