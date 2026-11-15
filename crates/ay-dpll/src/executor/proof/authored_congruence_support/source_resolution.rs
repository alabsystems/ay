// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-source resolution for reachable Alethe `assume` steps.

use super::*;
use crate::executor::proof_repair::proof_trust_surgery::surface_terms::expand_surface_lets;
use crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;

#[path = "source_resolution/canonical_render.rs"]
mod canonical_render;

#[path = "source_resolution/identity_surfaces.rs"]
mod identity_surfaces;

#[path = "source_resolution/nullary_macro.rs"]
mod nullary_macro;

#[cfg(test)]
#[path = "source_resolution/tests.rs"]
mod tests;

/// Total rows the provenance-mismatch fallback may clone/hash while
/// reconstructing its exact export-scope authority. Charge rows before
/// deduplication so repeated assumptions cannot hide allocation work.
const MAX_RECOVERED_EXPORT_SCOPE_ROWS: usize = MAX_AUTHORED_ORIGINAL_INDEX_ROWS;

/// The authenticated presentation of one reachable native assumption.
pub(super) enum ReachableAuthoredSource {
    /// The root already has an exact problem row in canonical identity form:
    /// some source row's own text IS the Alethe printer's canonical rendering,
    /// so publishing that rendering publishes what the problem wrote. Only
    /// this grant licenses the whole-root canonical seal.
    Identity(TermId),
    /// The root is authenticated by the RAW-source ledgers alone
    /// (`last_proof_rebuild_originals` + `last_proof_raw_original_assertions`),
    /// with no source row claiming its canonical text. That grant is about the
    /// root's TERM, not its spelling: the fold-to-false promoters raw-rebuild a
    /// premise whose authored surface — an author-named binder, a `(_ bvN W)`
    /// literal — is carried by DESCENDANT overrides, and the canonical
    /// rendering is exactly the text those overrides exist to avoid. Treated
    /// like `Identity` when clearing a stale root entry, never sealed.
    RawIdentity(TermId),
    /// Re-render the parsed source row as an assume-scoped override. The final
    /// bit permits an exact common duplicate spelling to replace a stale
    /// earlier-pass spelling for the same root.
    Parsed(TermId, FrontendTerm, bool),
    /// A separately authenticated parsed `let` row whose capture-safe
    /// expansion is exactly this raw proof root. Unlike generic raw-source
    /// authority, this retains the source `let` spelling so the printer emits
    /// its certified elimination bridge before the expanded root is used.
    ExpandedLet(TermId, String),
    /// A single source row whose top-level connective elaboration FOLDED away
    /// (`(or (< x 3) false)` interns as `(< x 3)`): the head comparison cannot
    /// confine it, so it is `Untouched` unless the Alethe printer derives the
    /// canonical unit from that exact spelling with checked steps
    /// (`ay_proof::folded_authored_assume_bridge_is_supported`). The restoring
    /// pass renders the spelling exactly as it would install it and asks, then
    /// re-judges it against the finished map (`confined_spelling.rs`).
    Folded(TermId, FrontendTerm),
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

impl ReachableAuthoredSource {
    /// The root whose CANONICAL text a source row authenticates, if any.
    ///
    /// Only such a root may be pinned by the whole-root seal: a `RawIdentity`
    /// grant is evidence about the root's TERM, and sealing it would publish
    /// the very canonical rendering its descendant overrides exist to replace.
    pub(super) fn canonical_row_root(&self) -> Option<TermId> {
        match self {
            ReachableAuthoredSource::Identity(root) => Some(*root),
            _ => None,
        }
    }
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
        }
    }

    fn observe(&mut self, source: &FrontendTerm, canonical_surface: &str) {
        self.count = self.count.saturating_add(1);
        let surface = authored_surface(source);
        self.identity_authenticated |= surface
            .as_deref()
            .is_none_or(|surface| surface == canonical_surface);
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
    /// Preflight a replacement without changing presentation or proof state.
    /// A candidate that would suppress source restoration must not preempt the
    /// existing reconstruction and its independently checked recovery paths.
    pub(in crate::executor::proof) fn candidate_authored_surface_is_available(
        &self,
        proof: &Proof,
    ) -> bool {
        let Some(roots) = reachable_authored_assume_roots(proof) else {
            return false;
        };
        if roots.is_empty() {
            return true;
        }
        if !self.ctx.retains_parsed_assertions() {
            return !self.is_producing_proofs() && !self.proof_artifact_required;
        }
        self.resolve_reachable_authored_sources(&roots).is_ok()
    }

    /// Authenticate each reachable root against immutable source provenance.
    ///
    /// A root any of whose source rows already carries the canonical identity
    /// spelling authenticates that canonical text, at any row count. The
    /// final restoration pass adds a whole-root entry only if descendant
    /// overrides would otherwise change that text.
    ///
    /// A repeated canonical root with no such row is presentation-safe when
    /// the printer can confine its FIRST row's spelling to its own `assume`:
    /// every row is a premise of the problem, so that spelling binds exactly
    /// whether or not the other rows spell it the same way. Anything else
    /// withholds only Alethe. The checked native proof and its
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
        // A root authenticated by both raw-source ledgers needs no rendering
        // unless it also owns a parsed row or an expanded-let receipt. Keep
        // those grants independent of the canonical spelling chosen below.
        let rebuild_authority: DetHashSet<TermId> =
            self.last_proof_rebuild_originals.iter().copied().collect();
        let raw_originals: DetHashSet<TermId> = self
            .last_proof_raw_original_assertions
            .iter()
            .copied()
            .collect();
        // An unaligned ledger may recover rows later, so every root in that
        // case must remain in the canonical rendering batch.
        let row_owners: DetHashSet<TermId> = if provenance_originals.len() == parsed.len() {
            provenance_originals.iter().copied().collect()
        } else {
            roots.iter().copied().collect()
        };
        // With only exact raw premises, no parsed row is selected or rendered.
        // Both independent grants are still required, and an expanded-let
        // receipt or an unaligned source ledger must take the ordinary audit.
        // Pricing unused parsed trees here would refuse a bounded ground
        // reconstruction solely because the generic source collector is smaller.
        if provenance_originals.len() == parsed.len()
            && self.last_proof_expanded_let_sources.is_empty()
            && !roots.is_empty()
            && roots.len() <= MAX_AUTHORED_ORIGINAL_INDEX_ROWS
            && roots.iter().all(|root| {
                rebuild_authority.contains(root)
                    && raw_originals.contains(root)
                    && !row_owners.contains(root)
            })
        {
            return Ok(roots
                .iter()
                .copied()
                .map(ReachableAuthoredSource::RawIdentity)
                .collect());
        }
        let priced = roots.iter().copied().filter(|root| {
            !(rebuild_authority.contains(root)
                && raw_originals.contains(root)
                && !row_owners.contains(root))
        });
        if !crate::executor::proof_trust_surgery_surface_audit::surface_sources_have_bounded_work(
            parsed.iter(),
        ) {
            return Err(InvalidAuthority);
        }
        let canonical_surfaces = canonical_render::render(
            &self.ctx.terms,
            priced.chain(
                self.last_proof_expanded_let_sources
                    .iter()
                    .map(|(root, _, _)| *root),
            ),
        )
        .ok_or(InvalidAuthority)?;

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
        for (index, (&original, source)) in originals.iter().zip(parsed).enumerate() {
            if !reachable.contains(&original) {
                continue;
            }
            let canonical_surface = canonical_surfaces.get(&original).ok_or(InvalidAuthority)?;
            rows.entry(original)
                .and_modify(|summary| summary.observe(source, canonical_surface))
                .or_insert_with(|| RootSourceRows::new(index, source, canonical_surface));
        }

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
                != *canonical_surfaces.get(root).ok_or(InvalidAuthority)?
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
        let mut definitions = None;
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
                    sources.push(ReachableAuthoredSource::RawIdentity(root));
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
            // entire external proof. Remove the stale root entry first; the
            // final restoration pass separately seals against descendant
            // spellings introduced anywhere in the completed source map.
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
                // Rows that spell the root DIFFERENTLY (`(= x (- 2.5))` and
                // `(= x -2.5)`, g06) are each a premise of the problem, and
                // pinned Carcara matches an `assume` against any one of
                // them; the proof assumes the root once. So the first row's
                // spelling, confined to its own `assume` exactly as a common
                // spelling is, is as exact a binding as a common one. It used
                // to withhold the whole surface, and an explicit `--proof
                // FILE` then lost the verdict (#8821).
                if self.authored_row_is_assume_confinable(root, source, &mut definitions) {
                    sources.push(ReachableAuthoredSource::Parsed(root, source.clone(), true));
                } else {
                    return Err(AletheSurfaceUnavailable);
                }
                continue;
            }
            let resolved = self.single_authored_row_source(root, source, &mut definitions)?;
            sources.push(self.folded_row_candidate(root, source, resolved));
        }
        Ok(sources)
    }

    /// A single row the head comparison left `Untouched` is a fold candidate
    /// ([`ReachableAuthoredSource::Folded`]), unless it names a nullary macro
    /// (the definition bridge's) or its root is a constant (shared by every
    /// assertion that folds to it).
    fn folded_row_candidate(
        &self,
        root: TermId,
        source: &FrontendTerm,
        resolved: ReachableAuthoredSource,
    ) -> ReachableAuthoredSource {
        match resolved {
            ReachableAuthoredSource::Untouched
                if !matches!(self.ctx.terms.get(root), TermData::Const(_))
                    && !nullary_macro::row_names_nullary_macro(&self.ctx, source) =>
            {
                ReachableAuthoredSource::Folded(root, source.clone())
            }
            resolved => resolved,
        }
    }

    /// Native proof access remains independent; this wrapper is exclusively
    /// for Alethe text and its paired exact-problem transport.
    pub(in crate::executor::proof) fn last_proof_with_authenticated_alethe_surface(
        &self,
    ) -> Option<&Proof> {
        let proof = self.last_proof()?;
        self.proof_has_authenticated_alethe_surface(proof)
            .then_some(proof)
    }

    /// Whether `proof` has an authenticated Alethe surface: a finite-enum
    /// sidecar, or retained source text that resolves every reachable
    /// authored `assume` to one exact spelling.
    pub(in crate::executor) fn proof_has_authenticated_alethe_surface(
        &self,
        proof: &Proof,
    ) -> bool {
        if self.last_proof_has_finite_enum_sidecar() {
            return true;
        }
        if !self.ctx.retains_parsed_assertions() {
            return false;
        }
        reachable_authored_assume_roots(proof).is_some_and(|roots| {
            roots.is_empty() || self.resolve_reachable_authored_sources(&roots).is_ok()
        })
    }
}
