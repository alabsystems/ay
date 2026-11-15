// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #evidence-stage-3 — the attribution vocabulary, and the closer that feeds it.
//!
//! These are census invariants, not solver behaviour. A corpus scan buckets on
//! `ProofDeclineMechanism::tag`, so two mechanisms sharing a tag silently merge
//! two populations with different remedies — which is the exact defect this
//! stage exists to remove, reintroduced one level up.

use ay_core::{Proof, ProofStep, Sort, Symbol, TermStore, TheoryLemmaKind};

use crate::executor::proof_resolution::empty_clause::{derive_empty_via_trust_lemma, TrustClosure};
use crate::executor::ProofDeclineMechanism as M;
use crate::executor::{SatReconstructionOutcome as R, SatReconstructionRecord, TrustClosureCensus};

fn every_mechanism() -> Vec<M> {
    vec![
        M::AuthoredSourceRootUnbounded,
        M::AuthoredSourceAggregateBudget,
        M::AuthoredSourceRootCount,
        M::PreprocessorFoldToFalseUnrecorded,
        M::AuthoredSurfaceOverridePlanUnbounded,
        M::InputSyntaxRewriteSourceBudget,
        M::CheckedSemanticCertificateUnrendered,
        M::ExactExpansionOverDischargedTrust,
        M::AuthoredSubsetUnrendered,
        M::QuantifierArtifactFirewall,
        M::AssumeFamilyTrustClosure,
        M::DerivedLeafTrustClosure {
            verified_finite_enum_witness: false,
        },
        M::DerivedLeafTrustClosure {
            verified_finite_enum_witness: true,
        },
        M::TerminalTrustStepOnPath,
        M::PrinterRuleWithoutExternalSpelling,
        M::AletheEmissionWorkBudget,
        M::UndeclarableProofSymbols,
        M::PinnedCheckerSurfaceUnsupported,
        M::ProofSurfaceBridgeMissing,
        M::StaleAuthenticatedExportScope,
        M::CertificateWriteFailed,
        M::NonPortableGroundEvaluate,
        M::AuthoredAssumeSurfaceUnavailable,
        M::AuthoredSourceAuthorityInvalid,
        M::RetentionOffWithoutAuthoredText,
        M::ForallInstanceSurfaceConflict,
        M::ProofAssemblyStopped,
        M::NoDerivationRecorded,
    ]
}

/// Distinct mechanisms must not collide in the census tag space.
///
/// The whole value of stage 3 is that a corpus scan can RANK the residual, and
/// it ranks by this string. A duplicate tag would merge two populations whose
/// remedies have nothing in common and the merge would be invisible — the same
/// failure the two original poisons had, one abstraction level higher.
#[test]
fn every_decline_mechanism_has_its_own_tag() {
    let mechanisms = every_mechanism();
    let mut tags: Vec<&'static str> = mechanisms.iter().map(|m| m.tag()).collect();
    tags.sort_unstable();
    let mut unique = tags.clone();
    unique.dedup();
    assert_eq!(
        unique.len(),
        mechanisms.len(),
        "two decline mechanisms share a census tag: {tags:?}",
    );
}

/// A tag a shell scan cannot cut on is not a census tag.
#[test]
fn decline_tags_are_kebab_case_and_greppable() {
    for mechanism in every_mechanism() {
        let tag = mechanism.tag();
        assert!(!tag.is_empty(), "empty tag");
        assert!(
            tag.bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-'),
            "tag {tag:?} is not kebab-case ASCII, so `mechanism=([\\w-]+)` cannot capture it",
        );
        assert!(
            !mechanism.explanation().is_empty(),
            "mechanism {tag} has no explanation, so the line says a name and nothing else",
        );
    }
}

/// The finite-enum bit is the whole point of the derived-leaf split.
///
/// "The closer had nothing to reconstruct" and "the closer declined while a
/// self-verified refutation of the same query sat in a field beside it" are a
/// weeks-long producer project and a routing fix respectively. If they share a
/// tag the census cannot tell them apart, which is where QF_UFDT `vlsat3` sat
/// for the whole campaign.
#[test]
fn the_derived_leaf_split_reaches_the_census() {
    let without = M::DerivedLeafTrustClosure {
        verified_finite_enum_witness: false,
    };
    let with = M::DerivedLeafTrustClosure {
        verified_finite_enum_witness: true,
    };
    assert_ne!(without.tag(), with.tag());
    assert_ne!(without.explanation(), with.explanation());
    assert!(
        with.tag().contains("enum-witness"),
        "the tag must name what was in hand, not merely differ: {}",
        with.tag(),
    );
}

/// The closer reports the strict-checkable closures as such.
///
/// `false` as a derived leaf closes through Alethe's own `false` rule plus one
/// resolution — every step re-derivable — so recording a decline there would
/// label a checkable refutation unevidenced.
#[test]
fn a_false_leaf_closure_is_not_a_decline() {
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    let false_term = terms.mk_bool(false);
    proof.add_step(ProofStep::TheoryLemma {
        theory: String::from("Core"),
        kind: TheoryLemmaKind::Generic,
        clause: vec![false_term],
        farkas: None,
        lia: None,
    });
    assert_eq!(
        derive_empty_via_trust_lemma(&mut terms, &mut proof),
        TrustClosure::DerivedFalseLeaf,
        "a derived `false` leaf closes without any trust claim",
    );
}

/// Nothing to close over is not a decline either: this closer did not run.
#[test]
fn an_empty_proof_reports_no_leaves() {
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    assert_eq!(
        derive_empty_via_trust_lemma(&mut terms, &mut proof),
        TrustClosure::NoLeaves,
    );
}

/// The assume-family route restates the solve's own verdict, and says so.
///
/// This is the mechanism behind the largest single bucket the census could not
/// name. It must not be confused with the derived-leaf route: over
/// assume-family leaves a `Generic` head is honest (the solver did answer UNSAT
/// about exactly that set); over derived leaves it would be false in every
/// model, which is why the two carry different tags and different repairs.
#[test]
fn an_assume_family_closure_reports_a_trust_head() {
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    let p = terms.mk_app(Symbol::named("closure_probe_p"), Vec::new(), Sort::Bool);
    proof.add_step(ProofStep::Assume(p));
    assert_eq!(
        derive_empty_via_trust_lemma(&mut terms, &mut proof),
        TrustClosure::AssumeFamilyTrustHead,
    );
}

// #closer-population. The census below is the instrument that told the
// campaign what `assume-family-trust-closure` actually is; these are its
// vocabulary invariants, on the same terms as the tag tests above.

/// Distinct reconstruction outcomes must not collide in the census tag space.
#[test]
fn every_reconstruction_outcome_has_its_own_kebab_case_tag() {
    let outcomes = [
        R::NoTrace,
        R::TraceWithoutEmptyClause,
        R::NoVariableMap,
        R::ScopeAssumptionsRejected,
        R::ManagerDeclinedTrace,
        R::ReconstructionShort,
        R::Reconstructed,
    ];
    let mut tags: Vec<&'static str> = outcomes.iter().map(|o| o.tag()).collect();
    tags.sort_unstable();
    let unique_len = {
        let mut u = tags.clone();
        u.dedup();
        u.len()
    };
    assert_eq!(unique_len, outcomes.len(), "tags collide: {tags:?}");
    for tag in tags {
        assert!(
            tag.bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-'),
            "tag {tag:?} is not kebab-case ASCII, so a census cannot cut on it",
        );
    }
}

/// The high-water mark must not let a CONSUMED trace read as an absent one.
///
/// `try_derive_empty_via_sat_resolution` takes the clause trace and does not
/// restore it on every path, and the empty-clause pipeline runs twice on some
/// queries. A last-write-wins record would then report `no-trace` for a query
/// that held a full propositional refutation — turning a translation gap into a
/// claim that AY never reasoned at all, which is the exact misreading this
/// instrument exists to prevent.
#[test]
fn a_later_traceless_attempt_cannot_erase_an_earlier_refutation() {
    let mut record = SatReconstructionRecord::default();
    record.keep_furthest(SatReconstructionRecord {
        outcome: Some(R::ReconstructionShort),
        trace_entries: 85_869,
        trace_has_empty: true,
        mapped_vars: 257,
        untranslatable_entries: 85_536,
        proof_work_exhausted: false,
        trace_truncated: false,
        // The `destroyed_*` fields arrived on main after this literal was
        // written, which left the `--lib` test target uncompilable; defaulting
        // them keeps the case exactly the one it was asserting.
        ..Default::default()
    });
    record.keep_furthest(SatReconstructionRecord {
        outcome: Some(R::NoTrace),
        ..Default::default()
    });
    assert_eq!(record.outcome, Some(R::ReconstructionShort));
    assert_eq!(record.trace_entries, 85_869);

    // …and a further attempt is kept when it genuinely gets further.
    record.keep_furthest(SatReconstructionRecord {
        outcome: Some(R::Reconstructed),
        trace_entries: 12,
        trace_has_empty: true,
        ..Default::default()
    });
    assert_eq!(record.outcome, Some(R::Reconstructed));
}

/// The two predicates a census reads must not be the same question.
///
/// `is_assumptions_only` is about the PROOF (nothing but authored assumptions
/// in it); `has_propositional_refutation` is about the clause trace beside it.
/// Measured together they separate "AY has nothing to write down" from "AY has
/// a refutation it cannot express in terms", and the two have opposite
/// remedies.
#[test]
fn the_census_predicates_answer_different_questions() {
    let nothing = TrustClosureCensus {
        steps: 22,
        assumes: 22,
        ..Default::default()
    };
    assert!(nothing.is_assumptions_only());
    assert!(!nothing.has_propositional_refutation());

    let unexpressed = TrustClosureCensus {
        steps: 22,
        assumes: 22,
        reconstruction: SatReconstructionRecord {
            outcome: Some(R::ReconstructionShort),
            trace_entries: 85_869,
            trace_has_empty: true,
            ..Default::default()
        },
        ..Default::default()
    };
    assert!(unexpressed.is_assumptions_only());
    assert!(
        unexpressed.has_propositional_refutation(),
        "an assumptions-only proof beside a complete clause trace is a \
         TRANSLATION gap, and must not read as an absence of reasoning",
    );

    // A trace that never reached the empty clause is not a refutation.
    let partial = TrustClosureCensus {
        reconstruction: SatReconstructionRecord {
            outcome: Some(R::TraceWithoutEmptyClause),
            trace_entries: 89,
            trace_has_empty: false,
            ..Default::default()
        },
        ..Default::default()
    };
    assert!(!partial.has_propositional_refutation());
}

/// A theory lemma in the proof is derivation, so the proof is not assumptions
/// only — the closer had something to resolve against and could not chain it.
#[test]
fn a_recorded_theory_lemma_makes_the_proof_more_than_its_assumptions() {
    let with_lemma = TrustClosureCensus {
        steps: 37,
        assumes: 28,
        theory_lemmas: 9,
        typed_theory_lemmas: 9,
        ..Default::default()
    };
    assert!(!with_lemma.is_assumptions_only());
}
