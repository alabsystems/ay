// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-source resolution for reachable Alethe `assume` steps.

use super::*;

/// The authenticated presentation of one reachable native assumption.
pub(super) enum ReachableAuthoredSource {
    /// The root already has an exact problem row in canonical identity form.
    Identity(TermId),
    /// Re-render the parsed source row as an assume-scoped override. The final
    /// bit permits an exact common duplicate spelling to replace a stale
    /// earlier-pass spelling for the same root.
    Parsed(TermId, FrontendTerm, bool),
    /// An authored premise this presentation-only pass has nothing to restore
    /// for. This is not an authority failure: the root keeps the rendering an
    /// earlier replacement pass installed.
    ///
    /// This covers current-query assumptions, which have no `(assert ...)`
    /// source row, and exact source spellings the Alethe printer cannot confine
    /// to their own `assume`. Clearing the latter can erase a folded authored
    /// conjunction that an earlier pass correctly installed.
    Untouched,
}

/// Why exact source resolution did not produce an Alethe presentation.
pub(super) enum AuthoredSourceResolutionFailure {
    /// Native proof authority or its aligned provenance ledger is invalid.
    InvalidAuthority,
    /// Native authority is valid, but no one exact Alethe spelling is justified.
    AletheSurfaceUnavailable,
}

/// Single-pass summary of all authored rows that elaborate to one root.
struct RootSourceRows {
    first_index: usize,
    count: usize,
    first_surface: Option<String>,
    all_surfaces_identical: bool,
    identity_authenticated: bool,
}

impl RootSourceRows {
    fn new(index: usize, source: &FrontendTerm, canonical_surface: &str) -> RootSourceRows {
        let surface = authored_surface(source);
        RootSourceRows {
            first_index: index,
            count: 1,
            identity_authenticated: surface
                .as_deref()
                .is_none_or(|surface| surface == canonical_surface),
            first_surface: surface,
            all_surfaces_identical: true,
        }
    }

    fn observe(&mut self, source: &FrontendTerm, canonical_surface: &str) {
        self.count = self.count.saturating_add(1);
        let surface = authored_surface(source);
        self.identity_authenticated |= surface
            .as_deref()
            .is_none_or(|surface| surface == canonical_surface);
        self.all_surfaces_identical &= surface.is_some() && surface == self.first_surface;
    }
}

/// `None` denotes a native-API assertion sentinel. Its exact exported problem
/// spelling is the canonical identity, so it authenticates identity directly.
fn authored_surface(source: &FrontendTerm) -> Option<String> {
    let source = proof_surface_syntax::strip_frontend_annotations(source);
    if matches!(
        source,
        FrontendTerm::Symbol(name) if name == NATIVE_API_ASSERTION_PLACEHOLDER
    ) {
        None
    } else {
        Some(proof_surface_syntax::format_frontend_term(source))
    }
}

impl Executor {
    /// Authenticate each reachable root against immutable source provenance.
    ///
    /// A repeated canonical root is presentation-safe in exactly two cases:
    /// one source row is already the canonical identity spelling, or all rows
    /// have the same noncanonical spelling and the printer can confine that
    /// spelling to its own `assume`. Anything else withholds only Alethe. The
    /// checked native proof and its portable bundle do not depend on choosing a
    /// presentation among semantically equal source rows.
    pub(super) fn resolve_reachable_authored_sources(
        &self,
        roots: &[TermId],
    ) -> Result<Vec<ReachableAuthoredSource>, AuthoredSourceResolutionFailure> {
        use AuthoredSourceResolutionFailure::{AletheSurfaceUnavailable, InvalidAuthority};

        let parsed = self.ctx.assertions_parsed();
        let originals = self.proof_original_problem_assertions_slice();
        if originals.len() != parsed.len() || originals.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS {
            return Err(InvalidAuthority);
        }
        if !crate::executor::proof_trust_surgery_surface_audit::surface_sources_have_bounded_work(
            parsed.iter(),
        ) || !proof_surface_syntax::surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            roots.iter().copied(),
        ) {
            return Err(InvalidAuthority);
        }
        if self.last_proof_rebuild_originals.len() > MAX_REBUILD_AUTHORITY_ROWS
            || self.last_proof_raw_original_assertions.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
        {
            return Err(InvalidAuthority);
        }

        let reachable: DetHashSet<TermId> = roots.iter().copied().collect();
        let mut rows: DetHashMap<TermId, RootSourceRows> = DetHashMap::default();
        let mut canonical_surfaces: DetHashMap<TermId, String> = DetHashMap::default();
        for (index, (&original, source)) in originals.iter().zip(parsed).enumerate() {
            if !reachable.contains(&original) {
                continue;
            }
            let canonical_surface = canonical_surfaces
                .entry(original)
                .or_insert_with(|| ay_proof::format_term_alethe(&self.ctx.terms, original));
            rows.entry(original)
                .and_modify(|summary| summary.observe(source, canonical_surface))
                .or_insert_with(|| RootSourceRows::new(index, source, canonical_surface));
        }

        let rebuild_authority: DetHashSet<TermId> =
            self.last_proof_rebuild_originals.iter().copied().collect();
        let raw_originals: DetHashSet<TermId> = self
            .last_proof_raw_original_assertions
            .iter()
            .copied()
            .collect();
        // This is exactly the current-query assumption ledger used by the
        // proof export scope. An over-cap ledger disables only this arm.
        let query_assumptions: DetHashSet<TermId> = match self.last_assumptions.as_deref() {
            Some(assumptions) if assumptions.len() <= MAX_AUTHORED_ORIGINAL_INDEX_ROWS => {
                assumptions.iter().copied().collect()
            }
            _ => DetHashSet::default(),
        };

        let mut sources = Vec::with_capacity(roots.len());
        for &root in roots {
            let Some(summary) = rows.get(&root) else {
                if rebuild_authority.contains(&root) && raw_originals.contains(&root) {
                    sources.push(ReachableAuthoredSource::Identity(root));
                    continue;
                }
                if query_assumptions.contains(&root) {
                    sources.push(ReachableAuthoredSource::Untouched);
                    continue;
                }
                return Err(InvalidAuthority);
            };
            let source = &parsed[summary.first_index];
            if summary.count > 1 {
                if summary.identity_authenticated {
                    sources.push(ReachableAuthoredSource::Identity(root));
                } else if summary.all_surfaces_identical
                    && authored_surface_is_assume_confinable(&self.ctx.terms, root, source)
                {
                    sources.push(ReachableAuthoredSource::Parsed(root, source.clone(), true));
                } else {
                    return Err(AletheSurfaceUnavailable);
                }
                continue;
            }
            if authored_surface(source).is_none() {
                sources.push(ReachableAuthoredSource::Identity(root));
            } else if authored_surface_is_assume_confinable(&self.ctx.terms, root, source) {
                sources.push(ReachableAuthoredSource::Parsed(root, source.clone(), false));
            } else {
                sources.push(ReachableAuthoredSource::Untouched);
            }
        }
        Ok(sources)
    }

    /// Native proof access remains independent; this wrapper is exclusively
    /// for Alethe text and its paired exact-problem transport.
    pub(in crate::executor::proof) fn last_proof_with_authenticated_alethe_surface(
        &self,
    ) -> Option<&Proof> {
        let proof = self.last_proof()?;
        if self.last_proof_has_finite_enum_sidecar() {
            return Some(proof);
        }
        if !self.ctx.retains_parsed_assertions() {
            return None;
        }
        let roots = reachable_authored_assume_roots(proof)?;
        if roots.is_empty() || self.resolve_reachable_authored_sources(&roots).is_ok() {
            Some(proof)
        } else {
            None
        }
    }
}
