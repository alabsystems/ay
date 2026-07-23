// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Source-grep guard: detect unintentional drift in ProofAddKind assignments
// across inprocessing, OTFS, and the clause-DB interface.

#![allow(clippy::panic)]

fn count_occurrences(source: &str, needle: &str) -> usize {
    source.match_indices(needle).count()
}

fn without_whitespace(source: &str) -> String {
    source.chars().filter(|ch| !ch.is_whitespace()).collect()
}

fn block_body<'a>(source: &'a str, marker: &str) -> &'a str {
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("block marker `{marker}` must exist"));
    let open_brace = source[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("block opening brace must exist");

    let mut depth = 0usize;
    for (offset, ch) in source[open_brace..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let close_brace = open_brace + offset;
                    return &source[open_brace + 1..close_brace];
                }
            }
            _ => {}
        }
    }

    panic!("block marker `{marker}` closing brace must exist");
}

fn inprocessing_source() -> String {
    [
        include_str!("../../src/solver/inprocessing.rs"),
        include_str!("../../src/solver/inprocessing/backbone.rs"),
        include_str!("../../src/solver/inprocessing/bce.rs"),
        include_str!("../../src/solver/inprocessing/bve/mod.rs"),
        include_str!("../../src/solver/inprocessing/bve/apply.rs"),
        include_str!("../../src/solver/inprocessing/bve/body.rs"),
        include_str!("../../src/solver/inprocessing/bve/gpu_dispatch.rs"),
        include_str!("../../src/solver/inprocessing/bve/state.rs"),
        include_str!("../../src/solver/inprocessing/cce.rs"),
        include_str!("../../src/solver/inprocessing/condition.rs"),
        include_str!("../../src/solver/inprocessing/congruence/mod.rs"),
        include_str!("../../src/solver/inprocessing/congruence/rup_probing.rs"),
        include_str!("../../src/solver/inprocessing/decompose.rs"),
        include_str!("../../src/solver/inprocessing/deduplicate.rs"),
        include_str!("../../src/solver/inprocessing/factorize.rs"),
        include_str!("../../src/solver/inprocessing/htr.rs"),
        include_str!("../../src/solver/inprocessing/pass_runner.rs"),
        include_str!("../../src/solver/inprocessing/probe.rs"),
        include_str!("../../src/solver/inprocessing/sbva.rs"),
        include_str!("../../src/solver/inprocessing/subsume.rs"),
        include_str!("../../src/solver/inprocessing/sweep.rs"),
        include_str!("../../src/solver/inprocessing/transred.rs"),
        include_str!("../../src/solver/inprocessing/vivify/mod.rs"),
        include_str!("../../src/solver/inprocessing/vivify/tier.rs"),
        include_str!("../../src/solver/inprocessing/vivify/analysis.rs"),
    ]
    .join("")
}

fn clause_db_source() -> String {
    [
        include_str!("../../src/solver/mod.rs"),
        include_str!("../../src/solver/clause_add.rs"),
        include_str!("../../src/solver/clause_add_internal.rs"),
        include_str!("../../src/solver/clause_add_theory.rs"),
    ]
    .join("")
}

#[test]
fn proof_add_kind_has_three_variants() {
    let source = include_str!("../../src/proof_manager.rs");
    let body = block_body(source, "pub(crate) enum ProofAddKind {");

    assert_eq!(count_occurrences(body, "Derived,"), 1);
    assert_eq!(count_occurrences(body, "Axiom,"), 1);
    assert!(
        body.contains("TrustedTransform,"),
        "missing TrustedTransform (#4609)"
    );
}

#[test]
fn add_clause_db_checked_decoupling_contract_is_preserved() {
    let source = clause_db_source();
    let theory_source = include_str!("../../src/solver/clause_add_theory.rs");
    let unscoped_helper = without_whitespace(block_body(
        theory_source,
        "fn add_unscoped_theory_clause_db(",
    ));

    assert!(
        source.contains("self.add_clause_db_checked(literals, learned, learned, &[])")
            && source.contains("fn add_clause_db_checked("),
        "add_clause_db must route through add_clause_db_checked"
    );
    assert!(
        source.contains("if forward_check_derived {")
            && source.contains("checker.add_derived(literals);")
            && source.contains("checker.add_original(literals);"),
        "forward checker classification split must remain explicit"
    );
    assert!(
        unscoped_helper.contains("self.add_clause_db_checked(literals,true,false,&[])"),
        "unscoped theory clauses must use forward_check_derived=false"
    );
    assert_eq!(
        count_occurrences(
            theory_source,
            "self.add_unscoped_theory_clause_db(&literals)"
        ),
        2,
        "unit and multi-literal theory lemmas must share the unscoped axiom path"
    );
    assert_eq!(
        count_occurrences(theory_source, "self.add_unscoped_theory_clause_db(&clause)"),
        2,
        "theory propagation clauses must share the unscoped axiom path"
    );
    assert_eq!(
        count_occurrences(theory_source, "self.add_clause_db_checked("),
        1,
        "theory clauses must not bypass the audited unscoped helper"
    );
}

#[test]
fn inprocessing_derived_emit_add_mapping() {
    let src = inprocessing_source();
    for (needle, expected) in [
        // BVE empty-resolvent path now uses mark_empty_clause_with_hints
        // instead of direct proof_emit_add — count dropped from 1 to 0.
        ("proof_emit_add(&[], &hints, ProofAddKind::Derived)", 0usize),
        (
            "proof_emit_add_prechecked(resolvent, &hints, ProofAddKind::Derived)",
            2,
        ),
        // HTR binary: probe-based LRAT hints (#5419)
        ("proof_emit_add(&[lit0, lit1], &htr_hints, htr_kind)", 1),
        // Congruence equivalence binaries: probe-based LRAT hints (#5419)
        (
            "proof_emit_add(&[lhs.negated(), rhs], fwd_hints, ProofAddKind::Derived)",
            1,
        ),
        (
            "proof_emit_add(&[lhs, rhs.negated()], bwd_hints, ProofAddKind::Derived)",
            1,
        ),
    ] {
        assert_eq!(
            count_occurrences(&src, needle),
            expected,
            "drifted: `{needle}`"
        );
    }
}

#[test]
fn inprocessing_axiom_emit_add_mapping() {
    let src = inprocessing_source();
    // After #4594 (commit 56af3a57d): all ProofAddKind::Axiom eliminated from
    // inprocessing. Congruence uses Derived with probe-based hints (#5419).
    // Guard against Axiom creeping back.
    assert_eq!(
        count_occurrences(&src, "ProofAddKind::Axiom"),
        0,
        "ProofAddKind::Axiom must not appear in inprocessing (#4594)"
    );
    // Congruence equivalence binaries: Derived with collected hints (#5419).
    // Pattern covered by inprocessing_derived_emit_add_mapping.
}

#[test]
fn inprocessing_trusted_transform_emit_add_mapping() {
    let factorize = without_whitespace(include_str!("../../src/solver/inprocessing/factorize.rs"));
    let sbva = without_whitespace(include_str!("../../src/solver/inprocessing/sbva.rs"));

    // Factorization has two distinct TrustedTransform sites: an LRAT
    // admission check for unproved dividers and the DRAT emission helper.
    // The former is side-effect-free and deliberately rejects until a
    // checker-visible divider proof is available; it is not a duplicate emit.
    for (needle, expected) in [
        (
            "preflight_forward_lrat_add_with_planned_ids(\
             divider,&[],ProofAddKind::TrustedTransform,planned_visible_ids,)",
            1usize,
        ),
        (
            "proof_emit_add(clause,&[],ProofAddKind::TrustedTransform)",
            1,
        ),
    ] {
        let needle = without_whitespace(needle);
        assert_eq!(
            count_occurrences(&factorize, &needle),
            expected,
            "factorization mapping drifted: `{needle}`"
        );
    }
    assert_eq!(
        count_occurrences(&factorize, "ProofAddKind::TrustedTransform"),
        2,
        "factorization must keep one TrustedTransform preflight and one emit"
    );

    // The blocked and quotient clauses now carry signed Derived witnesses.
    // Reintroducing their former empty-hint TrustedTransform preflights would
    // weaken the fail-closed LRAT transaction contract.
    for needle in [
        "preflight_forward_lrat_add_signed_with_planned_ids(\
         &app.blocked_clause,&sidecar.blocked_signed_lrat_hints,\
         ProofAddKind::Derived,planned_visible_ids,)",
        "preflight_forward_lrat_add_signed_with_planned_ids(\
         quotient,&signed_hints,ProofAddKind::Derived,planned_visible_ids,)",
    ] {
        let needle = without_whitespace(needle);
        assert_eq!(
            count_occurrences(&factorize, &needle),
            1,
            "factorization signed Derived mapping drifted: `{needle}`"
        );
    }

    // SBVA's definition, proof-only blocked clause, and tail clauses are
    // separate DRAT transaction steps and therefore three legitimate emits.
    for needle in [
        "proof_emit_add(&app.definition_clause,&[],ProofAddKind::TrustedTransform,)",
        "proof_emit_add(&app.blocked_clause,&[],ProofAddKind::TrustedTransform)",
        "proof_emit_add(tail,&[],ProofAddKind::TrustedTransform)",
    ] {
        assert_eq!(
            count_occurrences(&sbva, needle),
            1,
            "SBVA mapping drifted: `{needle}`"
        );
    }
    assert_eq!(
        count_occurrences(&sbva, "ProofAddKind::TrustedTransform"),
        3,
        "SBVA must emit exactly its three documented DRAT transaction steps"
    );
}

#[test]
fn decompose_hint_gated_kind_selection() {
    let src = inprocessing_source();
    assert!(
        count_occurrences(&src, "proof_emit_add(new, &hints, kind)") >= 1,
        "decompose rewritten-clause add must stay hint-gated"
    );
}

#[test]
fn otfs_uses_trusted_transform() {
    let otfs = include_str!("../../src/solver/otfs.rs");
    assert_eq!(
        count_occurrences(
            otfs,
            "proof_emit_add(&new_lits, &hints, ProofAddKind::TrustedTransform)"
        ),
        1,
        "OTFS strengthen add must use TrustedTransform (#4609)"
    );
}
