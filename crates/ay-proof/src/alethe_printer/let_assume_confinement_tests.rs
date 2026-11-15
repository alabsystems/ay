// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A certified `let` assume spelling is confined to its `assume` before any
//! step prints, and leaves the wire view; an uncertified one stays where it
//! was. See `let_assume_confinement.rs`.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, TermId, TermStore};

/// `(and p q r)` authored as `surface`, projected to `p` by a step that comes
/// BEFORE the `assume` it resolves against: the order the `storeinv_nf`
/// refutations have, where an array lemma over the assumed equality precedes
/// that equality's `assume`.
fn projected_before_assume(
    surface: &str,
) -> (TermStore, TermId, DetHashMap<TermId, String>, Proof) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let gate = terms.mk_not(and_term);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(and_term, surface.to_string());
    let mut proof = Proof::new();
    let projection =
        proof.add_rule_step(AletheRule::AndPos(0), vec![gate, p], vec![], vec![and_term]);
    let assumed = proof.add_assume(and_term, None);
    proof.add_resolution(vec![p], and_term, assumed, projection);
    (terms, and_term, overrides, proof)
}

/// Whether the planned wire view still spells `term` through the producer's
/// table.
fn wire_keeps(
    terms: &TermStore,
    term: TermId,
    overrides: &DetHashMap<TermId, String>,
    proof: &Proof,
) -> bool {
    crate::effective_wire_term_overrides_for_proof(proof, terms, Some(overrides))
        .expect("the planner admits the table")
        .is_some_and(|wire| wire.contains_key(&term))
}

/// Whether the table a fragment renderer reads
/// ([`crate::term_overrides_outside_confined_let_assumes`]) still spells
/// `term` through the producer's table.
fn fragment_table_keeps(
    terms: &TermStore,
    term: TermId,
    overrides: &DetHashMap<TermId, String>,
    proof: &Proof,
) -> bool {
    crate::term_overrides_outside_confined_let_assumes(
        proof,
        terms,
        Some(overrides),
        crate::AletheAuthoredSurfaces::default(),
    )
    .expect("the planner admits the table")
    .is_some_and(|table| table.contains_key(&term))
}

/// Before confinement the `and_pos` at `t0` printed `(not (let ..))`, a gate
/// no Alethe rule has, because the bridge installed the eliminated rendering
/// only once it reached the `assume` at `t1`.
#[test]
fn a_certified_let_spelling_never_reaches_a_step_printed_before_its_assume() {
    let surface = "(let ((?v_0 q)) (and p ?v_0 r))";
    let (terms, and_term, overrides, proof) = projected_before_assume(surface);
    assert!(
        !wire_keeps(&terms, and_term, &overrides, &proof),
        "a confined spelling leaves the wire view"
    );
    assert!(
        !fragment_table_keeps(&terms, and_term, &overrides, &proof),
        "a fragment renders a confined spelling as the export prints it"
    );
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[and_term],
        Some(&overrides),
    )
    .expect("the confined document renders");
    assert!(
        document.contains("(step t0 (cl (not (and p q r)) p) :rule and_pos :args (0))"),
        "{document}"
    );
    // The `assume` keeps the authored text and derives the eliminated unit
    // on the certified arm.
    assert!(
        document.contains(&format!("(assume t1.a {surface})")),
        "{document}"
    );
    assert!(document.contains(":rule let)"), "{document}");
    assert!(
        document.contains("(step t1 (cl (and p q r)) :rule resolution :premises (t1.e t1.l t1.a))"),
        "{document}"
    );
    assert!(!document.contains(":rule hole"), "{document}");
    // The authored text appears inside the bridge only.
    for line in document.lines().filter(|line| line.contains("(let ")) {
        assert!(
            ["(assume t1.a ", "(step t1.l ", "(step t1.e "]
                .iter()
                .any(|bridge| line.starts_with(bridge)),
            "the let spelling leaked outside its bridge: {line}\n{document}"
        );
    }
}

/// NEGATIVE: a `let` the bridge eliminates only through its `hole` arm (the
/// authored operand order is not AY's) is not confined. Its spelling stays in
/// the wire view, so every wire judgement keeps failing closed on it exactly
/// as before, and its `assume` bridge stays the visible hole.
#[test]
fn an_uncertified_let_spelling_stays_document_wide() {
    let surface = "(let ((?v_0 q)) (and ?v_0 p r))";
    let (terms, and_term, overrides, proof) = projected_before_assume(surface);
    assert!(
        !crate::certified_let_assume_bridge_is_supported(
            &terms,
            and_term,
            surface,
            Some(&overrides)
        ),
        "the fixture is the uncertified arm"
    );
    assert!(
        wire_keeps(&terms, and_term, &overrides, &proof),
        "an uncertified let spelling keeps its wire entry"
    );
    assert!(
        fragment_table_keeps(&terms, and_term, &overrides, &proof),
        "a fragment keeps reading an uncertified let spelling document-wide"
    );
}

/// NEGATIVE: an outer `let` root whose certified text spells an inner root's
/// authored `let` is not confined, and neither is the inner root. The outer
/// rendering went through the inner root's authored text, which stops
/// printing once that root is confined; confining the inner root alone made
/// every producer screen that recomputes the outer bridge from the wire view
/// see a gap (MEASURED: a QF_UF pair that published with one hole was
/// refused). The whole nested group keeps its document-wide reading.
#[test]
fn a_let_spelling_above_another_confined_one_stays_document_wide() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let s = terms.mk_var("s".to_string(), Sort::Bool);
    let inner = terms.mk_and(vec![p, q, r]);
    let outer = terms.mk_or(vec![inner, s]);
    let inner_surface = "(let ((?v_0 q)) (and p ?v_0 r))";
    let inner_canonical = crate::render_term_canonical(&terms, inner);
    let outer_body =
        crate::render_term_canonical(&terms, outer).replacen(&inner_canonical, inner_surface, 1);
    let outer_surface = format!("(let ((?v_1 p)) {outer_body})");
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(inner, inner_surface.to_string());
    overrides.insert(outer, outer_surface.clone());
    assert!(
        crate::certified_let_assume_bridge_is_supported(
            &terms,
            outer,
            &outer_surface,
            Some(&overrides)
        ),
        "alone, the outer spelling is certified: {outer_surface}"
    );
    // Both leaves consumed, so neither is an assume-only spelling.
    let mut proof = Proof::new();
    let inner_leaf = proof.add_assume(inner, None);
    let outer_leaf = proof.add_assume(outer, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![p],
        vec![inner_leaf, outer_leaf],
        Vec::new(),
    );
    assert!(wire_keeps(&terms, inner, &overrides, &proof));
    assert!(wire_keeps(&terms, outer, &overrides, &proof));
}
