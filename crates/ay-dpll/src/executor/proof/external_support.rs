// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A live seal for one unchanged proof and its checked native-premise transport.
//! Digests disclose bytes; literal proof, source, declaration, and entry identity
//! checks retain authority. The ordinary UNSAT admission scope remains complete.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermEntryStamp;
use ay_core::{AletheRule, Proof, ProofStep, TermId};
use ay_proof::{AletheDialect, CarcaraSurface};
use sha2::{Digest, Sha256};

use crate::api::{ExternalProofAssumption, ExternalProofSupport};
use crate::executor::commands::CheckedExternalSupportProblem;
use crate::executor::Executor;

use super::check::check_bounded_with_executor_progress;
use super::native_source_scope::NativeProofSourceScope;

mod payload;

const MAX_SUPPORT_WORK: usize = 250_000_000;
const MAX_SUPPORT_BYTES: usize = 512 * 1024 * 1024;
const MAX_SUPPORT_PAYLOAD: usize = 262_144;
const MAX_SUPPORT_TEXT: usize = 32 * 1024 * 1024;
const MAX_SUPPORT_RENDER_WORK: u64 = 2_000_000;

pub(crate) struct CheckedExternalProofSupport {
    proof: Proof,
    source: Arc<NativeProofSourceScope>,
    proof_entries: Vec<(TermId, TermEntryStamp)>,
    overrides: Option<DetHashMap<TermId, String>>,
    dialect: AletheDialect,
    problem: CheckedExternalSupportProblem,
    alethe: String,
    surface: CarcaraSurface,
    disclosure: ExternalProofSupport,
}

impl CheckedExternalProofSupport {
    pub(crate) fn proof_text(&self) -> &str {
        &self.alethe
    }

    pub(crate) fn problem_text(&self) -> &str {
        self.problem.text()
    }

    pub(crate) fn surface(&self) -> &CarcaraSurface {
        &self.surface
    }

    pub(crate) fn disclosure(&self) -> &ExternalProofSupport {
        &self.disclosure
    }

    fn is_current(
        &self,
        executor: &Executor,
        proof: &Proof,
        overrides: Option<&DetHashMap<TermId, String>>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> bool {
        payload::preflight(proof, progress).is_some()
            && self.proof == *proof
            && self.dialect == executor.alethe_dialect()
            && self.overrides.as_ref() == overrides
            && self.source.is_current_after_proof_growth(executor)
            && self.problem.is_current(executor)
            && self.proof_entries.iter().all(|(term, entry)| {
                progress(1, 0) && executor.ctx.terms.entry_stamp(*term) == Some(*entry)
            })
    }
}

impl Executor {
    /// Prepare at the publication gate, before self-check can discard an UNSAT.
    /// Every reader revalidates the literal proof; a repair refreshes this pair
    /// rather than retaining the previous document's support authority.
    pub(crate) fn prepare_external_proof_support(&self) {
        let _ = self.checked_external_proof_support_for_current_proof();
    }

    pub(crate) fn checked_external_proof_support_for_current_proof(
        &self,
    ) -> Option<Arc<CheckedExternalProofSupport>> {
        let proof = self.last_proof.as_ref()?;
        if self.last_unsat_proof_reconstruction_suppressed
            || self.native_proof_source_scope.is_none()
        {
            self.checked_external_proof_support.borrow_mut().take();
            return None;
        }
        let cached = self.checked_external_proof_support.borrow().clone();
        let checked = check_bounded_with_executor_progress(
            self,
            MAX_SUPPORT_WORK,
            MAX_SUPPORT_BYTES,
            |progress| {
                if payload::preflight(proof, progress).is_none()
                    || self.ctx.datatype_iter().next().is_some()
                {
                    return Ok(None);
                }
                // The positively native source excludes datatype contexts, so
                // no invented datatype-field overrides are possible. Borrow
                // the actual remaining channel before any map/string copy.
                let overrides = self.last_proof_term_overrides.as_ref();
                if overrides.is_some_and(|table| !table.is_empty()) {
                    return Ok(None);
                }
                // Ordinary exports retain their complete source transport.
                if self
                    .problem_and_proof_surface(proof, overrides)
                    .is_supported()
                {
                    return Ok(None);
                }
                if let Some(cached) = cached {
                    if cached.is_current(self, proof, overrides, progress) {
                        return Ok(Some(cached));
                    }
                }
                // Preserve None versus Some(empty) without copying unused
                // capacity from the caller's empty override table.
                let overrides = overrides.map(|_| DetHashMap::default());
                Ok(prepare(self, proof, overrides, progress).map(Arc::new))
            },
        )
        .ok()
        .flatten();
        *self.checked_external_proof_support.borrow_mut() = checked.clone();
        checked
    }
}

/// Borrowed payload admission shared by optional presentation codecs. It
/// grants none of the checked support/subset authority defined in this module.
pub(super) fn preflight_presentation_payload(
    proof: &Proof,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    payload::preflight(proof, progress)
}

fn prepare(
    executor: &Executor,
    proof: &Proof,
    overrides: Option<DetHashMap<TermId, String>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<CheckedExternalProofSupport> {
    let source = executor.native_proof_source_scope.as_ref()?;
    payload::preflight(proof, progress)?;
    if !source.is_current_after_proof_growth(executor)
        || source.roots().is_empty()
        || !has_terminal_empty_clause(proof)
    {
        return None;
    }
    // Native source capture excludes defined functions and datatype contexts.
    // The first independent walk authenticates the WHOLE unchanged document
    // against the FULL frozen query, before any premise is selected.
    let checked = ay_proof::check_proof_strict_with_typed_context_and_progress(
        proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
        Some(source.roots()),
        progress,
    )
    .ok()?;
    if !checked.is_complete() {
        return None;
    }
    let (assumptions, selected, proof_terms) = select_assumptions(source, proof, progress)?;
    let checked = ay_proof::check_proof_strict_with_typed_context_and_progress(
        proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
        Some(&selected),
        progress,
    )
    .ok()?;
    if !checked.is_complete() {
        return None;
    }
    let problem = executor.render_external_support_problem(
        &selected,
        &proof_terms,
        source,
        overrides.as_ref(),
    )?;
    if !problem.surface().is_supported() {
        return None;
    }
    let (rendered, dialect_report) = executor.in_alethe_dialect(|| {
        ay_proof::capture_alethe_dialect_report(|| {
            ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                proof,
                &executor.ctx.terms,
                &selected,
                overrides.as_ref(),
                Some(MAX_SUPPORT_RENDER_WORK),
            )
        })
    });
    let alethe = rendered.ok()?;
    let surface = ay_proof::carcara_proof_surface(proof, &executor.ctx.terms, overrides.as_ref())
        .with_dialect_report(&dialect_report);
    if !surface.is_supported()
        || alethe.contains(":rule hole")
        || alethe.contains(":rule trust")
        || alethe.len() > MAX_SUPPORT_TEXT
        || problem.text().len() > MAX_SUPPORT_TEXT
        || !progress(
            alethe.len().checked_add(problem.text().len())?,
            alethe.len().checked_add(problem.text().len())?,
        )
    {
        return None;
    }
    let proof_entries = proof_terms
        .iter()
        .map(|term| Some((*term, executor.ctx.terms.entry_stamp(*term)?)))
        .collect::<Option<Vec<_>>>()?;
    let disclosure = ExternalProofSupport {
        full_typed_query_sha256: source.full_typed_query_sha256(),
        declaration_context_sha256: source.declaration_context_sha256(),
        original_assertion_count: source.roots().len(),
        assumptions,
        proof_sha256: Sha256::digest(alethe.as_bytes()).into(),
        supported_problem_sha256: Sha256::digest(problem.text().as_bytes()).into(),
    };
    if !source.is_current_after_proof_growth(executor) || !problem.is_current(executor) {
        return None;
    }
    Some(CheckedExternalProofSupport {
        proof: proof.clone(),
        source: source.clone(),
        proof_entries,
        overrides,
        dialect: executor.alethe_dialect(),
        problem,
        alethe,
        surface,
        disclosure,
    })
}

fn has_terminal_empty_clause(proof: &Proof) -> bool {
    match proof.steps.last() {
        Some(ProofStep::Resolution { clause, .. }) => clause.is_empty(),
        Some(ProofStep::Step { rule, clause, .. }) => {
            *rule != AletheRule::ArrayExtDiffIntro && clause.is_empty()
        }
        _ => false,
    }
}

type SelectedAssumptions = (Vec<ExternalProofAssumption>, Vec<TermId>, Vec<TermId>);

fn select_assumptions(
    source: &NativeProofSourceScope,
    proof: &Proof,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<SelectedAssumptions> {
    let mut earliest = DetHashMap::default();
    for (index, &root) in source.roots().iter().enumerate() {
        if !progress(1, std::mem::size_of::<(TermId, usize)>()) {
            return None;
        }
        earliest.entry(root).or_insert(index);
    }
    let mut assumptions = Vec::new();
    let mut selected_indices = Vec::new();
    let mut proof_terms = Vec::new();
    let mut seen_terms = DetHashSet::default();
    let mut anchors = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let index = u32::try_from(index).ok()?;
        while anchors.last().is_some_and(|end| *end < index) {
            anchors.pop();
        }
        let terms = match step {
            ProofStep::Assume(term) => {
                if !anchors.is_empty() {
                    return None;
                }
                let original_assertion_index = *earliest.get(term)?;
                assumptions.push(ExternalProofAssumption {
                    proof_step: index,
                    original_assertion_index,
                });
                selected_indices.push(original_assertion_index);
                std::slice::from_ref(term)
            }
            ProofStep::Resolution { clause, pivot, .. } => {
                if seen_terms.insert(*pivot) {
                    proof_terms.push(*pivot);
                }
                clause.as_slice()
            }
            ProofStep::TheoryLemma { clause, .. } => clause.as_slice(),
            ProofStep::Step { clause, args, .. } => {
                for &term in args {
                    if seen_terms.insert(term) {
                        proof_terms.push(term);
                    }
                }
                clause.as_slice()
            }
            ProofStep::Anchor { end_step, .. } => {
                anchors.push(end_step.0);
                &[]
            }
            _ => return None,
        };
        if !progress(terms.len().checked_add(1)?, terms.len().checked_mul(16)?) {
            return None;
        }
        for &term in terms {
            if seen_terms.insert(term) {
                proof_terms.push(term);
            }
        }
    }
    if assumptions.is_empty() {
        return None;
    }
    selected_indices.sort_unstable();
    selected_indices.dedup();
    let selected = selected_indices
        .into_iter()
        .map(|index| source.roots()[index])
        .collect();
    Some((assumptions, selected, proof_terms))
}

#[cfg(test)]
mod tests;
