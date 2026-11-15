// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unbounded-population. The census taken at the moment
//! `authored-source-root-unbounded` is recorded, and the one hard question it
//! has to get right: WHICH canonical term the refused parsed root elaborated
//! to.
//!
//! The first version of this census read `ctx.assertions[index]` and was
//! WRONG. See [`authored_canonical_roots`] for what that stack actually is by
//! the time the assembly gate runs, and what is read instead.

use ay_core::TermId;

use super::{parsed_root_shape, term_kind, CanonicalShapeMemo, SourceRootCensus};
use crate::executor::Executor;

/// `first_canonical*` was read from the immutable public-query epoch.
pub(super) const SOURCE_QUERY_EPOCH: &str = "epoch";
/// `first_canonical*` was read from the installed proof source provenance.
pub(super) const SOURCE_PROOF_PROVENANCE: &str = "provenance";
/// No pre-split stack is index-aligned with the parsed stack on this query,
/// so NO canonical root is reported and the shape fields stay at zero.
pub(super) const SOURCE_UNAVAILABLE: &str = "unavailable";

impl Executor {
    /// Census the parsed roots at the moment `authored-source-root-unbounded`
    /// is recorded. Read-only over the parsed stack; the walk is linear in it.
    #[must_use]
    pub(in crate::executor) fn source_root_census(&self) -> SourceRootCensus {
        use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
            surface_source_work_probe_as, SurfaceWorkModel,
        };
        let roots = self.ctx.assertions_parsed();
        let authored = self.authored_canonical_roots(roots.len());
        let mut census = SourceRootCensus {
            roots: u32::try_from(roots.len()).unwrap_or(u32::MAX),
            solve_window_roots: u32::try_from(self.ctx.assertions.len()).unwrap_or(u32::MAX),
            authored_roots: authored.as_ref().map_or(0, |(stack, _)| {
                u32::try_from(stack.len()).unwrap_or(u32::MAX)
            }),
            first_canonical_source: authored.as_ref().map_or(SOURCE_UNAVAILABLE, |(_, tag)| tag),
            first_canonical_kind: SOURCE_UNAVAILABLE,
            ..Default::default()
        };
        for (index, root) in roots.iter().enumerate() {
            // The build pass's own model: the bound whose refusal this census
            // explains (`proof_source_decline`).
            match surface_source_work_probe_as(root, SurfaceWorkModel::Traversal) {
                Ok(work) => {
                    census.bounded_roots_work =
                        census.bounded_roots_work.saturating_add(work as u64);
                }
                Err(refusal) => {
                    let shape = parsed_root_shape(root);
                    if census.refused_roots == 0 {
                        census.refusal = Some(refusal);
                        census.first_refused = shape;
                        if let Some(&canonical) =
                            authored.as_ref().and_then(|(stack, _)| stack.get(index))
                        {
                            let mut memo = CanonicalShapeMemo::default();
                            census.first_canonical = memo.shape(&self.ctx.terms, canonical);
                            census.first_canonical_kind = term_kind(&self.ctx.terms, canonical);
                        }
                    }
                    if shape.nodes > census.largest_refused.nodes {
                        census.largest_refused = shape;
                    }
                    census.refused_roots = census.refused_roots.saturating_add(1);
                }
            }
        }
        census
    }

    /// The ELABORATED AUTHORED ROOTS as they stood before `check-sat`'s
    /// in-place passes, index-aligned with `assertions_parsed()`.
    ///
    /// **Not `ctx.assertions`.** That stack is the solve-time window: by the
    /// time the assembly gate runs, preprocessing has rewritten it in place and
    /// `FlattenAnd` has split a top-level conjunction into one entry per
    /// conjunct, so `ctx.assertions[i]` names the i-th formula the SOLVER sees,
    /// not the i-th root the author wrote. Reading it is what made the first
    /// version of this census report a bare `var` or `(not v)` as the root of
    /// single-assertion problems AY answers `unsat` — a root of that shape is
    /// satisfiable, so it cannot have been the root, and the "38% of
    /// source-root declines are elaborator folds" reading built on it was
    /// withdrawn.
    ///
    /// Two stacks survive the split, in preference order:
    ///
    /// 1. the immutable public-query epoch, bound by
    ///    `bind_materialized_public_query` AFTER command elaboration has
    ///    materialized every authored root and BEFORE any solver-owned
    ///    transformation may enter the query — the exact authored vector the
    ///    certificate authenticator itself compares against, and deliberately
    ///    sourced from there rather than from `ctx.assertions` for this same
    ///    reason;
    /// 2. the proof source provenance, installed from that same vector at the
    ///    public-solve boundary, for a query whose epoch was dropped.
    ///
    /// Index alignment is CHECKED, not assumed: a stack of a different length
    /// than the parsed one cannot be positionally matched to it, and a wrong
    /// root is worse than no root, so the census reports none. The tag it
    /// returns travels to the disclosure line, so a reader can always see which
    /// stack (if any) a `first_canonical*` number came from.
    fn authored_canonical_roots(&self, parsed_len: usize) -> Option<(Vec<TermId>, &'static str)> {
        if parsed_len == 0 {
            return None;
        }
        if let Some(epoch) = self.unsat_query_epoch_authored_assertions() {
            if epoch.len() == parsed_len {
                return Some((epoch, SOURCE_QUERY_EPOCH));
            }
        }
        let provenance = self.proof_problem_assertion_provenance.as_ref()?;
        let originals = &provenance.original_problem_assertions;
        (originals.len() == parsed_len).then(|| (originals.clone(), SOURCE_PROOF_PROVENANCE))
    }
}
