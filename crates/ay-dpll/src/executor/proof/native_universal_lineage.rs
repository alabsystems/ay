// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source receipts for native universal instantiation. A receipt authorizes
//! only the original universal as a premise, never an instance or a witness.
//! The existing strict checker still re-derives every substitution and checks
//! the finished document against the complete original query.

mod admission;
mod budget;
mod diagnostics;
mod instances;
mod offers;
#[cfg(test)]
mod tests;
mod witnesses;

use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{Sort, TermData, TermId};
use ay_frontend::SourceContextStamp;

use crate::executor::{Executor, QueryAuthorityEpoch};

pub(in crate::executor) use budget::NativeUniversalBudget;
pub(in crate::executor) use witnesses::NativeUniversalWitness;

const MAX_ROOTS: usize = 128;

/// Planning receipt, minted only from the opaque original query and positive
/// native insertion records. All fields are private and no decoder mints one.
#[derive(Debug)]
pub(in crate::executor) struct NativeUniversalSource {
    epoch: QueryAuthorityEpoch,
    context: SourceContextStamp,
    roots: Box<[TermId]>,
    entries: Box<[TermEntryStamp]>,
    prefix: TermStoreSnapshotStamp,
    metadata: u64,
    depth: usize,
}

impl NativeUniversalSource {
    pub(in crate::executor) fn capture(exec: &Executor) -> Option<Self> {
        exec.charge_native_universal(64, 512)?;
        let (epoch, context, roots) = exec.bounded_plain_unsat_query_scope(MAX_ROOTS)?;
        exec.charge_native_universal(
            roots.len().checked_mul(3)?,
            roots.len().checked_mul(
                (std::mem::size_of::<TermId>() + std::mem::size_of::<TermEntryStamp>())
                    .checked_mul(4)?,
            )?,
        )?;
        if roots.is_empty()
            || roots != exec.proof_original_problem_assertions_slice()
            || !exec
                .ctx
                .native_authored_originals_match_bounded(roots, MAX_ROOTS)
        {
            return None;
        }
        // The scan is borrowed and pays expanded edges and raw payload before
        // copying roots, binder names, signatures, or substitution data.
        admission::terms(exec, roots)?;
        if roots
            .iter()
            .any(|&root| exec.ctx.terms.sort(root) != &Sort::Bool)
        {
            return None;
        }
        let entries = roots
            .iter()
            .map(|&r| exec.ctx.terms.entry_stamp(r))
            .collect::<Option<Box<[_]>>>()?;
        Some(Self {
            epoch,
            context,
            roots: roots.into(),
            entries,
            prefix: exec.ctx.terms.snapshot_stamp(),
            metadata: exec.ctx.terms.checker_visible_metadata_generation(),
            depth: exec.ctx.scope_depth(),
        })
    }

    pub(in crate::executor) fn is_current(&self, exec: &Executor) -> bool {
        if exec
            .charge_native_universal(self.roots.len().saturating_mul(4), 0)
            .is_none()
            || !self.prefix.is_append_only_prefix_of(&exec.ctx.terms)
            || self.metadata != exec.ctx.terms.checker_visible_metadata_generation()
            || self.depth != exec.ctx.scope_depth()
        {
            return false;
        }
        let Some((epoch, context, roots)) = exec.bounded_plain_unsat_query_scope(MAX_ROOTS) else {
            return false;
        };
        self.epoch.is_same_epoch(&epoch)
            && self.context == context
            && self.roots.as_ref() == roots
            && roots == exec.proof_original_problem_assertions_slice()
            && exec
                .ctx
                .native_authored_originals_match_bounded(roots, MAX_ROOTS)
            && roots
                .iter()
                .zip(&self.entries)
                .all(|(&root, &entry)| exec.ctx.terms.entry_stamp(root) == Some(entry))
    }

    pub(in crate::executor) fn roots(&self) -> &[TermId] {
        &self.roots
    }

    pub(in crate::executor) fn admits(&self, exec: &Executor, root: TermId) -> bool {
        self.is_current(exec)
            && self.roots.contains(&root)
            && matches!(exec.ctx.terms.get(root), TermData::Forall(..))
    }
}

impl Executor {
    pub(in crate::executor) fn charge_native_universal(
        &self,
        work: usize,
        bytes: usize,
    ) -> Option<()> {
        let Ok(original) = ay_core::resource::current_check_stop() else {
            let _ = self.native_universal_budget.borrow_mut().charge(0, 0, true);
            return None;
        };
        let stopped = super::assembly_observations::observe()
            || self.certification_stop().is_some()
            || self.term_memory_exceeded()
            || self.solve_interrupt_is_set()
            || original.as_ref().is_some_and(|stop| stop())
            || ay_core::resource::current_guard()
                .as_ref()
                .is_some_and(|guard| guard.poll().is_some());
        if self.native_universal_budget.borrow().needs_controls() {
            // One owned Certify poller per external query, not a freshly
            // allocated guard/deadline at every visited source occurrence.
            self.native_universal_budget
                .borrow_mut()
                .charge(1024, 8192, stopped)?;
            let guard = self
                .assembly_certify
                .upgrade()
                .unwrap_or_else(|| self.proof_assembly_certify_node());
            let deadline = crate::executor::solve_deadline::DeadlinePoll::new(
                self.certification_deadline.clone(),
            );
            self.native_universal_budget
                .borrow_mut()
                .bind_controls(guard, deadline);
        }
        self.native_universal_budget
            .borrow_mut()
            .charge(work, bytes, stopped)
    }

    pub(in crate::executor) fn admit_native_universal_terms(&self, roots: &[TermId]) -> Option<()> {
        admission::terms(self, roots)
    }
}
