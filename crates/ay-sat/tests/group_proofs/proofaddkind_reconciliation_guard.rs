// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Source-grep guard: detect unintentional drift in ProofAddKind assignments
// across inprocessing, OTFS, and the clause-DB interface.

#![allow(clippy::panic)]

fn count_occurrences(source: &str, needle: &str) -> usize {
    source.match_indices(needle).count()
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
        source.contains("self.add_clause_db_checked(&literals, true, false, &[])"),
        "theory lemma path must use forward_check_derived=false"
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
    let src = inprocessing_source();
    for (needle, expected) in [
        (
            "preflight_forward_lrat_add(divider, &[], ProofAddKind::TrustedTransform)",
            1usize,
        ),
        (
            "proof_emit_add(&app.blocked_clause, &[], ProofAddKind::TrustedTransform)",
            1,
        ),
        (
            "preflight_forward_lrat_add(quotient, &[], ProofAddKind::TrustedTransform)",
            1,
        ),
        (
            "proof_emit_add(clause, &[], ProofAddKind::TrustedTransform)",
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
