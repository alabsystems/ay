// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The P4 labels (evidence policy, 2026-10-02): stable spellings, nested
//! propagation, and the weakest-refutation rule for sealing theorems.

use super::{
    CorroborationMethod, CorroborationSource, UnsatCorroboration, UnsatEvidence, UnsatEvidenceLevel,
};
use crate::executor::{Strengthening, StrengtheningSet};

#[test]
fn labels_have_stable_spellings() {
    assert_eq!(UnsatEvidenceLevel::E0.tag(), "E0");
    assert_eq!(UnsatEvidenceLevel::E1.tag(), "E1");
    assert_eq!(UnsatEvidenceLevel::E2.tag(), "E2");
    assert_eq!(CorroborationMethod::Resolve.tag(), "resolve");
    assert_eq!(CorroborationMethod::Entailment.tag(), "entailment");
    assert_eq!(
        CorroborationMethod::StandaloneTautology.tag(),
        "standalone-tautology"
    );
    assert_eq!(CorroborationSource::Direct.tag(), "direct");
    assert_eq!(
        CorroborationSource::NestedAuthoredSubset.tag(),
        "nested:authored-subset"
    );
    assert_eq!(
        CorroborationSource::NestedRmDomainExpansion.tag(),
        "nested:rm-domain-expansion"
    );
    assert_eq!(
        CorroborationSource::NestedClosedSentence.tag(),
        "nested:closed-sentence"
    );
}

#[test]
fn the_levels_order_e0_below_e1_below_e2() {
    assert!(UnsatEvidenceLevel::E0 < UnsatEvidenceLevel::E1);
    assert!(UnsatEvidenceLevel::E1 < UnsatEvidenceLevel::E2);
}

#[test]
fn a_corroborated_refutation_is_e1_and_names_its_arm() {
    let tautology = UnsatEvidence::corroborated(UnsatCorroboration::standalone_tautology());
    assert_eq!(tautology.level(), UnsatEvidenceLevel::E1);
    let corroboration = tautology.corroboration().expect("arm");
    assert_eq!(
        corroboration.method(),
        CorroborationMethod::StandaloneTautology
    );
    assert_eq!(corroboration.source(), CorroborationSource::Direct);
    assert_eq!(corroboration.disabled().tags(), "none");

    let lnh = StrengtheningSet::EMPTY.with(Strengthening::LnhSymmetry);
    let resolve = UnsatCorroboration::resolve(lnh);
    assert_eq!(resolve.method(), CorroborationMethod::Resolve);
    assert_eq!(resolve.disabled(), lnh);
    assert!(
        resolve.explanation().contains("E1"),
        "the sentence must say what the re-solve is worth"
    );
}

/// The 23 files that printed no corroboration line on D7 were nested probes:
/// the label must carry the probe's arm, renamed to where it ran.
#[test]
fn nesting_keeps_the_arm_and_names_the_probe() {
    let inner = UnsatEvidence::corroborated(UnsatCorroboration::resolve(StrengtheningSet::EMPTY));
    let outer = inner.nested(CorroborationSource::NestedAuthoredSubset);
    assert_eq!(outer.level(), UnsatEvidenceLevel::E1);
    let corroboration = outer.corroboration().expect("propagated");
    assert_eq!(corroboration.method(), CorroborationMethod::Resolve);
    assert_eq!(
        corroboration.source(),
        CorroborationSource::NestedAuthoredSubset
    );
    assert_eq!(
        UnsatEvidence::CHECKED.nested(CorroborationSource::NestedRmDomainExpansion),
        UnsatEvidence::CHECKED,
        "a checked probe stays checked and gains no corroboration"
    );
}

/// A theorem that seals several refutations is as strong as the weakest, and
/// still names a corroboration when any of them rests on one.
#[test]
fn a_sealing_theorem_takes_its_weakest_refutation() {
    let corroborated = UnsatEvidence::corroborated(UnsatCorroboration::standalone_tautology());
    let combined = UnsatEvidence::CHECKED.weakest(corroborated);
    assert_eq!(combined, corroborated);
    assert_eq!(corroborated.weakest(UnsatEvidence::CHECKED), corroborated);
    assert_eq!(
        UnsatEvidence::CHECKED
            .weakest(UnsatEvidence::RE_DERIVED)
            .level(),
        UnsatEvidenceLevel::E1
    );
    assert_eq!(
        UnsatEvidence::RE_DERIVED
            .weakest(UnsatEvidence::RAW)
            .level(),
        UnsatEvidenceLevel::E0
    );
    assert_eq!(
        UnsatEvidence::CHECKED.weakest(UnsatEvidence::CHECKED),
        UnsatEvidence::CHECKED
    );
}
