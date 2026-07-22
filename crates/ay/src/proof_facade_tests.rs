// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn proof_types_accessible_through_facade() {
    let _: fn() -> crate::ProofAcceptanceMode = || crate::ProofAcceptanceMode::Strict;
    let _: fn() -> Option<crate::StrictProofVerdict> = || None;
    let _: fn() -> Result<(), crate::ProofAcceptanceError> = || Ok(());
    let _: fn() -> Option<crate::ProofQuality> = || None;
    let _: fn() -> Option<crate::PartialProofCheck> = || None;
    let _: fn() -> Option<crate::UnsatProofArtifact> = || None;
    let _: fn() -> Option<Result<crate::ProofQuality, crate::ProofCheckError>> = || None;
}

#[test]
fn proof_types_accessible_through_api_module() {
    let _: fn() -> crate::api::ProofAcceptanceMode = || crate::api::ProofAcceptanceMode::Strict;
    let _: fn() -> Option<crate::api::StrictProofVerdict> = || None;
    let _: fn() -> Result<(), crate::api::ProofAcceptanceError> = || Ok(());
    let _: fn() -> Option<crate::api::ProofQuality> = || None;
    let _: fn() -> Option<crate::api::PartialProofCheck> = || None;
    let _: fn() -> Option<crate::api::UnsatProofArtifact> = || None;
    let _: fn() -> Option<Result<crate::api::ProofQuality, crate::api::ProofCheckError>> = || None;
}

#[test]
fn proof_types_accessible_through_prelude() {
    let _: fn() -> crate::prelude::ProofAcceptanceMode =
        || crate::prelude::ProofAcceptanceMode::Strict;
    let _: fn() -> Option<crate::prelude::StrictProofVerdict> = || None;
    let _: fn() -> Result<(), crate::prelude::ProofAcceptanceError> = || Ok(());
    let _: fn() -> Option<crate::prelude::ProofQuality> = || None;
    let _: fn() -> Option<crate::prelude::PartialProofCheck> = || None;
    let _: fn() -> Option<crate::prelude::UnsatProofArtifact> = || None;
    let _: fn() -> Option<Result<crate::prelude::ProofQuality, crate::prelude::ProofCheckError>> =
        || None;
}

#[test]
fn proof_internals_types_accessible() {
    let _: fn() -> Option<crate::proof_internals::ProofId> = || None;
    let _: fn() -> Option<crate::proof_internals::TermId> = || None;
    let _: fn() -> Option<crate::proof_internals::Proof> = || None;
    let _: fn() -> Option<crate::proof_internals::AletheRule> = || None;
    let _: fn() -> Option<crate::proof_internals::TheoryLemmaKind> = || None;
    let _: fn() -> Option<crate::proof_internals::FarkasAnnotation> = || None;
    let _: fn() -> Option<crate::proof_internals::Sort> = || None;
    let _ = crate::proof_internals::quote_symbol as fn(&str) -> String;
}

#[test]
fn export_alethe_accessible_through_proof_internals() {
    let _ = crate::proof_internals::export_alethe
        as fn(&crate::proof_internals::Proof, &crate::proof_internals::TermStore) -> String;
}

#[test]
#[allow(deprecated)]
fn translate_types_accessible() {
    let _: fn() -> Option<crate::translate::TranslationContext<String>> = || None;
    let _: fn() -> Option<crate::translate::TranslationSession<'static, String>> = || None;
    let _: fn() -> Option<crate::translate::TranslationState<String>> = || None;
}

#[test]
fn executor_companion_types_accessible() {
    let _: fn() -> Option<crate::executor::Context> = || None;
    let _: fn() -> Option<crate::executor::Proof> = || None;
    let _: fn() -> Option<crate::executor::TermStore> = || None;
    let _: crate::executor::Result<()> = Ok(());
}

#[test]
fn formula_stats_accessible_through_root_api_and_prelude() {
    let _: fn() -> Option<crate::FormulaStats> = || None;
    let _: fn() -> Option<crate::api::FormulaStats> = || None;
    let _: fn() -> Option<crate::prelude::FormulaStats> = || None;
    let _ = crate::collect_formula_stats as fn(&[crate::Command]) -> crate::FormulaStats;
    let _ = crate::api::collect_formula_stats as fn(&[crate::Command]) -> crate::api::FormulaStats;
    let _ = crate::prelude::collect_formula_stats
        as fn(&[crate::Command]) -> crate::prelude::FormulaStats;
}
