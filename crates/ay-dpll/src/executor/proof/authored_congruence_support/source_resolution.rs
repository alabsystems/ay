// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-source resolution for reachable Alethe `assume` steps.

use super::*;
use crate::executor::proof_repair::proof_trust_surgery::surface_terms::expand_surface_lets;
use crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;

/// Total rows the provenance-mismatch fallback may clone/hash while
/// reconstructing its exact export-scope authority. Charge rows before
/// deduplication so repeated assumptions cannot hide allocation work.
const MAX_RECOVERED_EXPORT_SCOPE_ROWS: usize = MAX_AUTHORED_ORIGINAL_INDEX_ROWS;

/// The authenticated presentation of one reachable native assumption.
pub(super) enum ReachableAuthoredSource {
    /// The root already has an exact problem row in canonical identity form.
    Identity(TermId),
    /// Re-render the parsed source row as an assume-scoped override. The final
    /// bit permits an exact common duplicate spelling to replace a stale
    /// earlier-pass spelling for the same root.
    Parsed(TermId, FrontendTerm, bool),
    /// A separately authenticated parsed `let` row whose capture-safe
    /// expansion is exactly this raw proof root. Unlike generic raw-source
    /// authority, this retains the source `let` spelling so the printer emits
    /// its certified elimination bridge before the expanded root is used.
    ExpandedLet(TermId, String),
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
    /// A root any of whose source rows already carries the canonical identity
    /// spelling publishes that canonical text with no override at all — the
    /// row IS the authentication, at any row count.
    ///
    /// A repeated canonical root with no such row is presentation-safe in
    /// exactly one further case: all its rows carry the same noncanonical
    /// spelling and the printer can confine that spelling to its own `assume`.
    /// Anything else withholds only Alethe. The checked native proof and its
    /// portable bundle do not depend on choosing a presentation among
    /// semantically equal source rows.
    pub(super) fn resolve_reachable_authored_sources(
        &self,
        roots: &[TermId],
    ) -> Result<Vec<ReachableAuthoredSource>, AuthoredSourceResolutionFailure> {
        use AuthoredSourceResolutionFailure::{AletheSurfaceUnavailable, InvalidAuthority};

        let parsed = self.ctx.assertions_parsed();
        let provenance_originals = self.proof_original_problem_assertions_slice();
        // Bound every borrowed ledger before the provenance-mismatch fallback
        // can clone a Context row or materialize/hash the export scope.
        if parsed.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
            || provenance_originals.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
            || self.last_proof_rebuild_originals.len() > MAX_REBUILD_AUTHORITY_ROWS
            || self.last_proof_raw_original_assertions.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
            || self.last_proof_expanded_let_sources.len() > MAX_PROVENANCE_REPAIR_TERMS
        {
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

        let originals = if provenance_originals.len() != parsed.len() {
            // A public `check-sat-assuming` query may deliberately keep only
            // its base assertions in proof provenance while moving other
            // still-authored rows into the exactly bound assumption slice.
            // The parsed ledger remains aligned with Context's immutable
            // concrete-authored ledger, not with that narrower base. Recover
            // the alignment from those source-owned rows only; never zip
            // parsed text against the mutable solver assertion stack.
            let proof_problem_assertions = self
                .proof_problem_assertion_provenance
                .as_ref()
                .map_or(provenance_originals, |provenance| {
                    provenance.problem_assertions.as_slice()
                });
            let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
            proof_problem_assertions
                .len()
                .checked_add(provenance_originals.len())
                .and_then(|rows| rows.checked_add(self.last_proof_rebuild_originals.len()))
                .and_then(|rows| rows.checked_add(assumptions.len()))
                .filter(|rows| *rows <= MAX_RECOVERED_EXPORT_SCOPE_ROWS)
                .ok_or(InvalidAuthority)?;
            if proof_problem_assertions.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
                || assumptions.len() > MAX_AUTHORED_ORIGINAL_INDEX_ROWS
            {
                return Err(InvalidAuthority);
            }
            let Some(concrete_authored) =
                self.ctx.concrete_authored_assertion_terms_aligned_bounded(
                    MAX_AUTHORED_ORIGINAL_INDEX_ROWS,
                )
            else {
                return Err(InvalidAuthority);
            };

            // This fallback is presentation-only, but keep its authority
            // boundary explicit: every proof root that can select one of the
            // recovered source rows must already belong to the exact strict
            // problem scope (base, bound assumptions, or authenticated
            // rebuild roots). An inactive/popped authored row therefore
            // cannot lend its spelling to a solver-generated assumption.
            let mut authorized: DetHashSet<TermId> = DetHashSet::default();
            authorized.extend(proof_problem_assertions.iter().copied());
            authorized.extend(provenance_originals.iter().copied());
            authorized.extend(self.last_proof_rebuild_originals.iter().copied());
            authorized.extend(assumptions.iter().copied());
            if !self.boolean_constant_premises_authored().1 {
                authorized.remove(&self.ctx.terms.false_term());
            }
            if roots.iter().any(|root| !authorized.contains(root)) {
                return Err(InvalidAuthority);
            }
            std::borrow::Cow::Owned(concrete_authored)
        } else {
            std::borrow::Cow::Borrowed(provenance_originals)
        };

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
        let mut expanded_let_sources: DetHashMap<TermId, String> = DetHashMap::default();
        for (root, source_index, source_surface) in &self.last_proof_expanded_let_sources {
            let Some(source) = parsed.get(*source_index) else {
                return Err(InvalidAuthority);
            };
            let source = proof_surface_syntax::strip_frontend_annotations(source);
            if !matches!(source, FrontendTerm::Let(..))
                || proof_surface_syntax::format_frontend_term(source) != *source_surface
            {
                return Err(InvalidAuthority);
            }
            let Some(expanded) = expand_surface_lets(source, &std::collections::HashMap::new())
            else {
                return Err(InvalidAuthority);
            };
            let expanded = proof_surface_syntax::strip_frontend_annotations(&expanded);
            if proof_surface_syntax::format_frontend_term(expanded)
                != ay_proof::format_term_alethe(&self.ctx.terms, *root)
                || self
                    .last_proof_term_overrides
                    .as_ref()
                    .and_then(|overrides| overrides.get(root))
                    .is_some_and(|override_surface| override_surface != source_surface)
            {
                return Err(InvalidAuthority);
            }
            if expanded_let_sources
                .insert(*root, source_surface.clone())
                .is_some_and(|previous| previous != *source_surface)
            {
                return Err(InvalidAuthority);
            }
        }
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
            let summary = rows.get(&root);
            if let Some(surface) = expanded_let_sources.get(&root) {
                if !rebuild_authority.contains(&root) || !raw_originals.contains(&root) {
                    return Err(InvalidAuthority);
                }
                // A direct canonical row is sufficient problem authority for
                // this proof root, so it supersedes the presentation-only
                // `let` bridge. Validate the bridge's independent grants
                // first so malformed metadata cannot hide behind that row.
                if !summary.is_some_and(|summary| summary.identity_authenticated) {
                    sources.push(ReachableAuthoredSource::ExpandedLet(root, surface.clone()));
                    continue;
                }
            }
            let Some(summary) = summary else {
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
            // Identity authentication is a property of the ROWS, not of how
            // many there are. One row that already spells the root exactly as
            // the Alethe printer renders it is the problem file's own evidence
            // for canonical text, whether or not other rows elaborate to the
            // same root. Re-deriving that spelling as an override would carry
            // no provenance the printer does not already have, and the entry
            // is not inert: `restored_authored_override_map` compares it
            // against whatever an earlier pass recorded for the same root and
            // declines the WHOLE reconstruction on any disagreement, so a root
            // the problem file spells canonically could cost the query its
            // entire external proof. Removing instead publishes the canonical
            // text that row authenticates.
            //
            // This also subsumes the native-API sentinel, whose exported
            // problem spelling IS the canonical identity: `authored_surface`
            // reports `None` for it and `RootSourceRows` already folds that
            // into `identity_authenticated`.
            if summary.identity_authenticated {
                sources.push(ReachableAuthoredSource::Identity(root));
                continue;
            }
            if summary.count > 1 {
                if summary.all_surfaces_identical
                    && authored_surface_is_assume_confinable(&self.ctx.terms, root, source)
                {
                    sources.push(ReachableAuthoredSource::Parsed(root, source.clone(), true));
                } else {
                    return Err(AletheSurfaceUnavailable);
                }
                continue;
            }
            if authored_surface_is_assume_confinable(&self.ctx.terms, root, source) {
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
