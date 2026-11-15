// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's counted WORK, beside its conflicts.
//!
//! ## Why
//!
//! A candidate lemma that unit propagation decides (`unit.rs`) never reaches
//! the solver and spends no conflict, and a solver call is charged at least
//! one (`solve.rs`) whatever its local problem's size. Building those local
//! problems (`proof/local.rs`) and propagating over them was counted by
//! nothing but the candidates themselves (`max_lemma_calls`, at least two a
//! gate) and the clock. Measured 2026-10-07: the strict checker's sweep of
//! the commuted SMULL row `gen/chain016` read 553M literals over 7,793
//! candidates in 88 s (test profile) and spent 42,164 of its 200,000
//! conflicts.
//!
//! ## What is counted
//!
//! Each candidate attempt is charged the literals of its local problem and
//! every literal its unit propagation reads; its solver call, if any, is
//! charged its conflicts as before. Once the allowance is spent the sweep
//! attempts no candidate (`prove`, `out_of_budget`) and starts no solver
//! call, its closing refutation included (`solve.rs`), so it declines, and
//! a split visits no further node. The allowance is checked before each
//! attempt, so a sweep reads at most one candidate's problem past it. A
//! split's leaf core sweeps spend the split's allowance (`split/leaf.rs`),
//! and the strict checker's sweep only what its split left
//! (`bv_blast_solver/sweep.rs`). The printer's sweeps keep no work cap
//! (`SweepLimits::standalone`).
//!
//! ## What is not
//!
//! The count is a ceiling, not a model of time. A solver call is charged its
//! conflicts, not its propagations or its refutation's validation, which is
//! where a sweep over wide, unmatched multipliers spends its time; nor are a
//! candidate's search for a cone too large to be local, a split node's
//! propagation over its pool, or the leaf solves a split falls back on. Each
//! is bounded by another count — candidates, conflicts, nodes — and by the
//! clock. A sweep's count is deterministic, but a split that its deadline
//! ends leaves the sweep after it an allowance that depends on when.

use super::proof::Local;
use super::unit::unit_refutation_counted;
use super::*;

/// What a sweep spent of its [`SweepLimits`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Spent {
    /// Conflicts its solver calls spent.
    pub(crate) conflicts: u64,
    /// Literals its candidate attempts read.
    pub(crate) work: u64,
}

impl Sweep<'_, '_> {
    /// Whether the sweep must attempt nothing more: the caller stopped it, or
    /// its candidates, conflicts, work or time ran out.
    pub(super) fn out_of_budget(&mut self) -> bool {
        if !self.stopped && !(self.keep_going)() {
            self.stopped = true;
        }
        self.stopped
            || self.lemma_calls >= self.max_lemma_calls
            || self.conflicts_left == 0
            || self.out_of_work()
            || Instant::now() >= self.deadline
    }

    /// Whether the candidates have read the whole allowance.
    pub(super) fn out_of_work(&self) -> bool {
        self.work_read >= self.work_cap
    }

    /// Unit propagation over one candidate's `local` problem (`unit.rs`),
    /// charged the problem's literals and the literals propagation read.
    pub(super) fn propagate_candidate(&mut self, local: &Local) -> Option<Vec<usize>> {
        let built: u64 = local.clauses.iter().map(|clause| clause.len() as u64).sum();
        let (used, read) = unit_refutation_counted(&local.clauses, local.global.len());
        self.work_read = self.work_read.saturating_add(built.saturating_add(read));
        used
    }

    /// What the sweep has spent of `limits`: its conflicts, and every literal
    /// its candidates read, the one that crossed the cap included.
    pub(super) fn spent(&self, limits: SweepLimits) -> Spent {
        Spent {
            conflicts: limits.total_conflicts.saturating_sub(self.conflicts_left),
            work: self.work_read,
        }
    }
}
