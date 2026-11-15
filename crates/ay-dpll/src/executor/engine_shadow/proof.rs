// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--engine-shadow-proofs=DIR`: the recording run's request, and the one
//! check of each assembled refutation (see the parent module's docs).

use std::time::Instant;

use ay_cdclt::KernelProof;
use ay_core::{TermId, TermStore};

use super::super::Executor;

/// A recording run's input: the authored assertions, and where the Alethe
/// documents go.
pub(super) struct ProofRequest<'a> {
    dir: &'a str,
    /// File stem for this check's document.
    stem: String,
    overrides: Option<ay_core::kani_compat::DetHashMap<TermId, String>>,
    surfaces: super::super::proof_authored_assume_spelling::AuthoredExportSurfaces,
    /// The executor's dialect: the document is rendered in it and its
    /// round trip reads the rule vocabulary of that dialect's checker.
    dialect: ay_proof::AletheDialect,
}

impl Executor {
    /// A recording run's request: the problem's own spelling of each
    /// assertion (the term layer rewrites at construction: `mk_and`
    /// flattens, numerals are coerced), so each `assume` prints as the
    /// problem states it. Planned before the store is cloned; planning may
    /// intern terms.
    pub(super) fn engine_shadow_proof_request<'d>(&mut self, dir: &'d str) -> ProofRequest<'d> {
        let mut overrides = self.proof_export_term_overrides().unwrap_or_default();
        if let Ok((_, authored)) = self.prepare_surface_overrides() {
            overrides.extend(authored);
        }
        ProofRequest {
            dir,
            stem: format!("{}-{}", std::process::id(), self.engine_shadow.checks),
            overrides: (!overrides.is_empty()).then_some(overrides),
            surfaces: self.authored_export_surfaces(),
            dialect: self.alethe_dialect(),
        }
    }
}

/// Check the assembled refutation once (AY's strict checker over every step,
/// then the document round-trip), write the Alethe document, and describe
/// both in the row's `proof` object.
pub(super) fn check_and_write(
    store: &TermStore,
    assertions: &[TermId],
    proof: &KernelProof,
    request: &ProofRequest<'_>,
    deadline: Option<Instant>,
) -> serde_json::Value {
    let stats = &proof.stats;
    let strict_started = Instant::now();
    let mut in_time = |_: usize, _: usize| deadline.is_none_or(|d| Instant::now() < d);
    let strict = match ay_proof::check_proof_strict_with_context_and_progress(
        &proof.proof,
        store,
        None,
        None,
        Some(assertions),
        &mut in_time,
    ) {
        Ok(_) => "ok".to_string(),
        Err(error) => format!("{error:?}"),
    };
    let strict_seconds = strict_started.elapsed().as_secs_f64();
    let printed = ay_proof::with_alethe_dialect(request.dialect, || {
        ay_proof::try_export_alethe_with_authored_surfaces(
            &proof.proof,
            store,
            assertions,
            request.overrides.as_ref(),
            request.surfaces.channels(),
            None,
        )
    });
    let (document, file) = match printed {
        Ok(text) => {
            let scope = ay_proof::ProblemScope::from_symbols(ay_proof::problem_scope_symbol_names(
                store, assertions,
            ));
            let document =
                match ay_proof::check_alethe_document_in_dialect(&text, &scope, request.dialect) {
                    Ok(_) => "ok".to_string(),
                    Err(defect) => defect.to_string(),
                };
            let path = std::path::Path::new(request.dir).join(format!("{}.alethe", request.stem));
            let file = match std::fs::write(&path, text) {
                Ok(()) => Some(path.display().to_string()),
                Err(error) => {
                    tracing::warn!(%error, "engine shadow: cannot write the proof");
                    None
                }
            };
            (document, file)
        }
        Err(error) => (format!("not printed: {error}"), None),
    };
    serde_json::json!({
        "status": "assembled",
        "strict": strict,
        "strict_seconds": strict_seconds,
        "document": document,
        "file": file,
        "steps": stats.steps,
        "assumes": stats.assumes,
        "clausification": stats.clausification,
        "theory_lemmas": stats.theory_lemmas,
        "theory_kinds": stats.theory_kinds,
        "resolutions": stats.resolutions,
        "holes": stats.holes,
        "unjustified": stats.unjustified,
        "trace_entries": stats.trace_entries,
        "derived_by_hints": stats.derived_by_hints,
        "derived_by_search": stats.derived_by_search,
    })
}
