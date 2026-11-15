// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The guarded collapse keeps the measurably smaller certified derivation of
//! an anchored authored root (`rederive.rs`).

use super::super::super::GuardedCollapseStage;
use super::super::{bounded_source, source};
use super::*;

/// `bv_partition_source`'s exception-coverage fixture: the named interval
/// partition lane and, since 73810d00d, the complete blast both certify its
/// one authored root.
const PARTITION: &str = include_str!("../../../../../../tests/fixtures/partition_coverage.smt2");

/// An absorption law no named arithmetic lane recognizes; the complete blast
/// certifies it.
const ABSORPTION: &str = "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= (bvand x (bvor x y)) x)))
(check-sat)";

/// `guarded_mask_tls.smt2` narrowed to eight bits. The arithmetic recognizer
/// accepts the root, but its lemma prints through the same complete blast
/// (267,080 bytes either way at 64 bits; 36,226 here), so re-deriving it
/// would change nothing but the internal lemma kind.
const NARROW_GUARDED_MASK: &str = "(set-logic QF_BV)
(declare-const A (_ BitVec 8))
(declare-const G (_ BitVec 8))
(assert (and (= (bvand #x07 (bvadd A G)) #x00)
  (not (= (bvadd A G) (bvadd (bvand #xf0 (bvadd A G)) (bvand #x08 (bvadd A G)))))))
(check-sat)";

fn solved(problem: &str) -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let results = executor
        .execute_all(&ay_frontend::parse(problem).unwrap())
        .unwrap();
    assert_eq!(
        results.first().map(String::as_str),
        Some("unsat"),
        "{results:?}"
    );
    executor
}

/// The raw authored root the guarded collapse anchors, and its negation.
fn anchored_root(executor: &mut Executor) -> (TermId, TermId) {
    let parsed = executor.ctx.assertions_parsed()[0].clone();
    let assertion = source::expand(&executor.ctx, &parsed).expect("declaration-bounded source");
    assert_eq!(bounded_source(&assertion), Some(false), "no array read");
    let root = executor
        .raw_intern_ground_bv_surface(&assertion)
        .expect("raw-interned authored root");
    let negated = executor.ctx.terms.mk_not_raw(root);
    (root, negated)
}

/// The kind of the lemma that refutes exactly `(cl negated)`.
fn refutation_kind(proof: &Proof, negated: TermId) -> Option<TheoryLemmaKind> {
    proof.steps.iter().find_map(|step| match step {
        ProofStep::TheoryLemma { kind, clause, .. } if clause.as_slice() == [negated] => {
            Some(*kind)
        }
        _ => None,
    })
}

fn published_document(executor: &Executor) -> String {
    let document = executor
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("requested proof")
        .expect("the published proof renders");
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{} bytes with an unproved step",
        document.len()
    );
    document
}

#[test]
fn a_publishable_complete_blast_yields_to_the_smaller_partition_document() {
    let mut executor = solved(PARTITION);
    let (root, negated) = anchored_root(&mut executor);
    let published = executor.last_proof().cloned().expect("requested proof");
    assert!(proof_already_assumes(&published, root));
    assert_eq!(
        refutation_kind(&published, negated),
        Some(TheoryLemmaKind::ArithClauseTautology)
    );
    let document = published_document(&executor);
    assert!(
        !document.contains("@ay_cbb_") && document.contains(":rule poly_simp"),
        "the complete blast displaced the partition lane ({} bytes)",
        document.len()
    );

    // The incumbent the planner meets: since 73810d00d the complete blast
    // makes `assume root`, `BvBitBlast (not root)` publishable.
    let blast = anchored_refutation(root, negated, TheoryLemmaKind::BvBitBlast);
    assert!(executor.authored_cascade_publishable(&blast));
    let named = anchored_refutation(root, negated, TheoryLemmaKind::ArithClauseTautology);
    let named_len = executor
        .clean_render_len(&named)
        .expect("the partition lane renders clean under the choice cap");
    assert!(executor
        .clean_render_len(&blast)
        .is_none_or(|blast_len| named_len < blast_len));
    for stage in [GuardedCollapseStage::Cascade, GuardedCollapseStage::Final] {
        let mut proof = blast.clone();
        assert!(
            executor.promote_bv_guarded_collapse(&mut proof, stage),
            "{stage:?}"
        );
        assert_eq!(
            refutation_kind(&proof, negated),
            Some(TheoryLemmaKind::ArithClauseTautology),
            "{stage:?}"
        );
    }
}

#[test]
fn a_root_no_named_lane_recognizes_keeps_its_complete_blast() {
    let mut executor = solved(ABSORPTION);
    let (root, negated) = anchored_root(&mut executor);
    assert!(!ay_proof::recognize_arith_clause_tautology(
        &executor.ctx.terms,
        &[negated]
    ));
    let blast = anchored_refutation(root, negated, TheoryLemmaKind::BvBitBlast);
    assert!(executor.authored_cascade_publishable(&blast));
    for stage in [GuardedCollapseStage::Cascade, GuardedCollapseStage::Final] {
        let mut proof = blast.clone();
        assert!(
            !executor.promote_bv_guarded_collapse(&mut proof, stage),
            "{stage:?}"
        );
        assert_eq!(format!("{:?}", proof.steps), format!("{:?}", blast.steps));
    }
}

#[test]
fn a_recognized_root_whose_lane_is_no_smaller_keeps_its_complete_blast() {
    let mut executor = solved(NARROW_GUARDED_MASK);
    let (root, negated) = anchored_root(&mut executor);
    assert!(ay_proof::recognize_arith_clause_tautology(
        &executor.ctx.terms,
        &[negated]
    ));
    let blast = anchored_refutation(root, negated, TheoryLemmaKind::BvBitBlast);
    let named = anchored_refutation(root, negated, TheoryLemmaKind::ArithClauseTautology);
    assert!(executor.authored_cascade_publishable(&blast));
    let blast_len = executor
        .clean_render_len(&blast)
        .expect("the blast renders clean");
    assert!(executor
        .clean_render_len(&named)
        .is_some_and(|named_len| named_len >= blast_len));
    for stage in [GuardedCollapseStage::Cascade, GuardedCollapseStage::Final] {
        let mut proof = blast.clone();
        assert!(
            !executor.promote_bv_guarded_collapse(&mut proof, stage),
            "{stage:?}"
        );
        assert_eq!(format!("{:?}", proof.steps), format!("{:?}", blast.steps));
    }
}

#[test]
fn a_larger_certified_document_never_replaces_a_smaller_one() {
    // At eight bits both documents fit the choice cap, so the comparison
    // below is decided by measured size alone.
    let mut executor = solved(&PARTITION.replace(" 32)", " 8)"));
    let (root, negated) = anchored_root(&mut executor);
    let blast = anchored_refutation(root, negated, TheoryLemmaKind::BvBitBlast);
    let named = anchored_refutation(root, negated, TheoryLemmaKind::ArithClauseTautology);
    let blast_len = executor
        .clean_render_len(&blast)
        .expect("the blast fits the cap");
    let named_len = executor
        .clean_render_len(&named)
        .expect("the lane fits the cap");
    assert!(named_len < blast_len, "{named_len} >= {blast_len}");
    // The same two certified proofs with their roles swapped: the order in
    // which they arrive decides nothing, and an equal document is no reason
    // to re-anchor.
    assert!(executor.rederivation_publishes_smaller(&blast, &named));
    assert!(!executor.rederivation_publishes_smaller(&named, &blast));
    assert!(!executor.rederivation_publishes_smaller(&named, &named));
}
