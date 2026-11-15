// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #semantic-token census — what the closed-sentence mint holds, measured.
//!
//! `checked-semantic-certificate-unrendered` names, by its wording, a checked
//! derivation that only lacks a writer. These tests pin the instrument that
//! tests that name: the census must (a) count the token's leaf obligations,
//! (b) pair the sealed root with the parsed assertion at its own index and
//! say when the authored text names declared symbols the sealed root cannot,
//! and (c) change nothing about the verdict, the admission or the decline.

use super::*;
use crate::executor::{ProofDeclineMechanism, SemanticTokenCensus, SemanticTokenSource};

/// keymaera `intersection-example-simple` in miniature. The authored root
/// names two declared constants (`A`, `B`) and re-binds a third (`ts`, which
/// is declared AND quantified, exactly as the corpus files do). Its consequent
/// is `(or (= 2 2) …)`, which term construction folds to `true`, so the
/// implication folds to `true` and the sealed root is
/// `(not (exists ((ts Real)) true))` — a sentence nobody asserted.
const FOLDED_KEYMAERA: &str = concat!(
    "(set-logic NRA)\n",
    "(declare-fun A () Real)\n",
    "(declare-fun B () Real)\n",
    "(declare-fun ts () Real)\n",
    "(assert (not (exists ((ts Real)) ",
    "(=> (and (= A 0) (= A 2) (> B 0)) (or (= 2 2) (= B 2))))))\n",
    "(check-sat)\n",
);

/// The same sealed root, this time literally authored: no declared symbol
/// anywhere in the file.
const AUTHORED_RESIDUE: &str = concat!(
    "(set-logic NRA)\n",
    "(assert (not (exists ((ts Real)) true)))\n",
    "(check-sat)\n",
);

fn solve(script: &str, retain_parsed: bool) -> Executor {
    // The QSAT route and the qlra lane (#qlra-nested-cegqi) refute both
    // fixtures first, through the consequence replay; this census pins the
    // exact semantic mint behind them.
    let _no_qlra = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_cegqi: true,
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let commands = parse(script).expect("script parses");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(retain_parsed);
    let out = exec.execute_all(&commands).expect("script executes");
    assert_eq!(out, vec!["unsat"], "both fixtures refute");
    exec
}

fn census_of(exec: &Executor) -> &SemanticTokenCensus {
    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::CheckedSemanticCertificateUnrendered),
        "the fixture must publish through the exact semantic mint, or the census tests nothing",
    );
    exec.last_semantic_token_census()
        .expect("the semantic mint records its census when it publishes")
}

/// The corpus shape: declared symbols in the authored text, none in the
/// sealed root. The census must call that a construction residue, must not
/// count the re-bound `ts` as a free mention, and must find nothing but leaf
/// obligations behind the token.
#[test]
fn a_folded_keymaera_root_is_reported_as_a_construction_residue() {
    let exec = solve(FOLDED_KEYMAERA, true);
    let census = census_of(&exec);
    assert_eq!(census.kind, "closed-sentence");
    assert_eq!(census.authored_source, SemanticTokenSource::Aligned);
    assert!(
        census.authored_walk_complete,
        "the walk models every node of this fixture"
    );
    assert_eq!(
        census.authored_symbols, 2,
        "A and B are free in the authored text; ts is declared but re-bound and must not count"
    );
    assert_eq!(census.sealed_root_is_construction_residue(), Some(true));
    assert_eq!(census.authored_head, "not");
    assert_eq!(census.sealed_root_head, "not");
    assert!(
        census.sealed_root_surface.contains("exists")
            && census.sealed_root_surface.contains("true"),
        "the sealed root is the folded residue, got {:?}",
        census.sealed_root_surface
    );
    assert!(census.obligations >= 1);
    assert!(
        census.is_leaf_only(),
        "every obligation is a single-leaf instrument"
    );
    assert!(
        census.authored_nodes > census.sealed_root_nodes,
        "the authored tree ({}) is larger than what survived construction ({})",
        census.authored_nodes,
        census.sealed_root_nodes
    );
}

/// The one shape a renderer could honestly serve: the sealed root IS the
/// authored sentence. The census must not call it a residue.
#[test]
fn a_literally_authored_residue_is_not_reported_as_a_residue() {
    let exec = solve(AUTHORED_RESIDUE, true);
    let census = census_of(&exec);
    assert_eq!(census.authored_source, SemanticTokenSource::Aligned);
    assert_eq!(census.authored_symbols, 0);
    assert!(census.authored_walk_complete);
    assert_eq!(census.sealed_root_is_construction_residue(), Some(false));
}

/// Retention off keeps no authored text; the census must say so rather than
/// answer the authored-scope question on nothing.
#[test]
fn retention_off_marks_the_authored_comparison_unavailable() {
    let exec = solve(FOLDED_KEYMAERA, false);
    let census = census_of(&exec);
    assert_eq!(census.authored_source, SemanticTokenSource::RetentionOff);
    assert_eq!(census.sealed_root_is_construction_residue(), None);
    // The sealed-root half of the census does not need authored text.
    assert_eq!(census.sealed_root_head, "not");
    assert!(census.obligations >= 1);
}

/// The instrument is write-only: the same fixture publishes the same verdict,
/// the same admission and the same decline with or without authored text.
#[test]
fn the_census_changes_no_verdict_admission_or_decline() {
    let with_text = solve(FOLDED_KEYMAERA, true);
    let without_text = solve(FOLDED_KEYMAERA, false);
    for exec in [&with_text, &without_text] {
        assert_eq!(
            exec.last_proof_decline(),
            Some(ProofDeclineMechanism::CheckedSemanticCertificateUnrendered)
        );
        assert_eq!(
            exec.last_command_unsat_admission_tag(),
            Some("checked-exact-closed-sentence")
        );
        assert!(
            exec.last_proof().is_none(),
            "the lane nulls the proof by design"
        );
    }
}

/// The residue predicate is definitive only in the negative direction.
#[test]
fn residue_predicate_is_definitive_only_when_symbols_are_present() {
    let mut census = SemanticTokenCensus {
        kind: "closed-sentence",
        authored_source: SemanticTokenSource::Aligned,
        authored_symbols: 3,
        authored_walk_complete: false,
        ..SemanticTokenCensus::default()
    };
    assert_eq!(
        census.sealed_root_is_construction_residue(),
        Some(true),
        "symbols found by an incomplete walk are still symbols the sealed root lacks"
    );
    census.authored_symbols = 0;
    assert_eq!(
        census.sealed_root_is_construction_residue(),
        None,
        "an incomplete walk that found nothing proves nothing"
    );
    census.authored_walk_complete = true;
    assert_eq!(census.sealed_root_is_construction_residue(), Some(false));
    for source in [
        SemanticTokenSource::NotApplicable,
        SemanticTokenSource::RetentionOff,
        SemanticTokenSource::Misaligned,
        SemanticTokenSource::RootNotInOriginals,
    ] {
        census.authored_source = source;
        census.authored_symbols = 3;
        assert_eq!(
            census.sealed_root_is_construction_residue(),
            None,
            "{source:?}"
        );
    }
}

/// Every source tag is greppable and distinct — a census cuts on them.
#[test]
fn source_tags_are_distinct_and_kebab_case() {
    let sources = [
        SemanticTokenSource::NotApplicable,
        SemanticTokenSource::RetentionOff,
        SemanticTokenSource::Misaligned,
        SemanticTokenSource::RootNotInOriginals,
        SemanticTokenSource::Aligned,
    ];
    let mut tags: Vec<&str> = sources.iter().map(|s| s.tag()).collect();
    for tag in &tags {
        assert!(
            tag.bytes().all(|b| b.is_ascii_lowercase() || b == b'-'),
            "{tag}"
        );
    }
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(tags.len(), sources.len());
}

/// Corpus `AUFBVDTLIA ... rec-fun-ijcar2016 ... BitsTricks.scala-7.smt2-3` in
/// miniature: the macro `f` is eliminated, leaving one closed sentence whose
/// VALIDITY the lane proves by refuting its negation in a nested re-solve.
const TRUST_RESOLVED_SENTENCE: &str = concat!(
    "(set-logic ALL)\n",
    "(declare-fun f ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))\n",
    "(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) ",
    "(= (f x n) (bvand x (bvshl (_ bv1 32) n)))))\n",
    "(assert (not (forall ((n (_ BitVec 32)) (x (_ BitVec 32))) ",
    "(or (not (bvslt n (_ bv32 32))) ",
    "(not (= (f (bvor x (bvshl (_ bv1 32) n)) n) (_ bv0 32))) ",
    "(bvslt n (_ bv0 32))))))\n",
    "(check-sat)\n",
);

/// A closed-sentence theorem is exactly as strong as its weakest nested
/// refutation (2026-09-24 fp-strings fix-up; the audit the verifier's E1
/// asked for).
///
/// The nested re-solve behind this fixture's one obligation is accepted
/// because its proof's strict check fails ONLY at a `trust` step — the
/// deferred-discharge entry condition, a fresh-executor re-solve of the same
/// code. Before the fix-up the theorem published as
/// `checked-exact-closed-sentence` ("an independently checked semantic
/// certificate") with `nested_negation_refuted=1 nested_trust_refuted=0`,
/// measured on the corpus file itself (`--phase-trace`: "reconfirm ACCEPTED:
/// re-solve proof rejected only for a trust-kind step"). It is now admitted
/// on `discharged-trust` and the census counts the obligation as trust.
///
/// If AY's nested proof of this sentence ever becomes strictly checkable, the
/// obligation turns checked and so does the admission; update the pin then,
/// with the phase trace that shows it.
#[test]
fn a_closed_sentence_over_a_trust_refutation_is_a_discharged_trust_admission() {
    let commands = parse(TRUST_RESOLVED_SENTENCE).expect("script parses");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(true);
    let out = exec.execute_all(&commands).expect("script executes");
    assert_eq!(out, vec!["unsat"]);
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("discharged-trust"),
        "a closed sentence whose nested refutation rests on a trust step is not \
         an independently checked semantic certificate"
    );
    assert!(!exec.last_command_unsat_was_exact_semantically_verified());
    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::ExactExpansionOverDischargedTrust)
    );
    let census = exec
        .last_semantic_token_census()
        .expect("the semantic mint records its census when it publishes");
    assert_eq!(census.kind, "closed-sentence");
    assert_eq!(
        (
            census.obligations,
            census.nested_refuted,
            census.nested_negation_refuted,
            census.nested_trust_refuted,
        ),
        (1, 0, 0, 1),
        "the one nested obligation is counted by the authority it was accepted on"
    );
}

/// The class is transitive (E1b, the 2026-09-28 fp-strings verifier): a probe
/// that PUBLISHED on this theorem must seal into an enclosing certificate as
/// trust, not as checked. `UnsatCertificate::probe_authority` reads an exact
/// theorem over a trust refutation as `DischargedTrust`; without that arm the
/// token below, which `command_admission` already admits as
/// `discharged-trust`, would carry `Checked` into the certificate that seals
/// it. No solver-level input was found to reach it through a sealing theorem,
/// so it is pinned on the token, minted the way `checked_isolated_solve` mints
/// a probe's: a public solve, the publication funnel, the one-shot token.
#[test]
fn a_probe_publishing_on_a_theorem_over_a_trust_refutation_seals_as_trust() {
    use crate::executor::unsat_cert::ProbeUnsatAuthority;
    let assertions = TRUST_RESOLVED_SENTENCE.replace("(check-sat)\n", "");
    let commands = parse(&assertions).expect("script parses");
    let mut probe = Executor::new();
    probe.set_retain_parsed_assertions(true);
    probe
        .execute_all(&commands)
        .expect("declarations and assertions load");
    probe.begin_public_solve(false);
    probe.bind_unsat_query_assumptions(&[]);
    let raw = probe.check_sat().expect("the probe solve completes");
    assert!(raw.is_unsat(), "{raw:?}");
    let published = probe.certify_unsat_for_publication(raw, &[]);
    assert!(published.is_unsat(), "{published:?}");
    let census = probe
        .last_semantic_token_census()
        .expect("the closed-sentence mint records its census");
    assert_eq!(
        (census.kind, census.nested_trust_refuted),
        ("closed-sentence", 1),
        "the token is the closed-sentence theorem over one trust refutation"
    );
    let token = probe
        .take_unsat_certificate()
        .expect("the published verdict's one-shot certificate");
    assert!(!token.exact_semantic_verified());
    assert_eq!(
        token.probe_authority(),
        ProbeUnsatAuthority::DischargedTrust,
        "an exact theorem that seals a trust refutation reads as trust when a \
         probe that published on it is sealed in turn"
    );
}
