// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deny-only identity of one authenticated native BV proof-producing offer.

use crate::executor::{Executor, QueryAuthorityEpoch};
use ay_core::{term::TermEntryStamp, TermId};
use ay_frontend::SourceContextStamp;

#[derive(Clone)]
pub(in crate::executor) struct NativeBvRefutationScope {
    epoch: QueryAuthorityEpoch,
    source: SourceContextStamp,
    roots: Vec<TermId>,
    entries: Vec<TermEntryStamp>,
    assumptions: Vec<TermId>,
}

impl NativeBvRefutationScope {
    // At most 64 retained scopes, each with at most 64 roots/entry stamps/
    // assumptions. Precharge worst-case comparisons and bounded clones to the
    // query's SAME source envelope, before any scope lookup/allocation.
    pub(in crate::executor) const CAPTURE_WORK: usize = 64 * (64 * 3 + 16);

    pub(in crate::executor) fn capture(executor: &Executor) -> Option<Self> {
        if ay_core::resource::check_stop_requested()
            || !executor
                .proof_source_work
                .spend_canonical_scan_work(Self::CAPTURE_WORK)
        {
            return None;
        }
        let roots = executor
            .authenticated_unsat_query_roots_for_internal_certificate()
            .or_else(|| {
                // A named-core redirect leaves its tracking assumptions in
                // the solver slot after restoring the public assertion stack.
                // The existing getter authenticates each tracking term and
                // returns only the original, assumption-free epoch roots.
                executor.authenticated_plain_query_assertions_after_named_core_redirect()
            })?;
        let entries = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()?;
        // Also retain the actual tracking slot as deny-only retry identity.
        // Neither getter grants those terms any additional premise authority.
        let assumptions = executor.last_assumptions.clone().unwrap_or_default();
        if ay_core::resource::check_stop_requested() {
            return None;
        }
        Some(Self {
            epoch: executor.query_authority_epoch.clone(),
            source: executor.ctx.source_context_stamp(),
            roots,
            entries,
            assumptions,
        })
    }

    pub(in crate::executor) fn roots(&self) -> &[TermId] {
        &self.roots
    }

    pub(in crate::executor) fn matches(&self, other: &Self) -> bool {
        self.epoch.is_same_epoch(&other.epoch)
            && self.source == other.source
            && self.roots == other.roots
            && self.entries == other.entries
            && self.assumptions == other.assumptions
    }
}
