// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[derive(Default)]
pub(super) struct Counts {
    pub checks: AtomicUsize,
    pub extracts: AtomicUsize,
    pub unsets: AtomicUsize,
    pub drops: AtomicUsize,
}

pub(super) struct SatTheory {
    counts: Arc<Counts>,
}

impl SatTheory {
    pub(super) fn new(counts: &Arc<Counts>) -> Self {
        Self {
            counts: Arc::clone(counts),
        }
    }
    fn set_terms(&mut self, _: &ay_core::TermStore) {}
    pub(super) fn unset_terms(&mut self) {
        self.counts.unsets.fetch_add(1, Ordering::SeqCst);
    }
}

impl Drop for SatTheory {
    fn drop(&mut self) {
        self.counts.drops.fetch_add(1, Ordering::SeqCst);
    }
}

impl TheorySolver for SatTheory {
    fn assert_literal(&mut self, _: TermId, _: bool) {}
    fn check(&mut self) -> TheoryResult {
        self.counts.checks.fetch_add(1, Ordering::SeqCst);
        TheoryResult::Sat
    }
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }
    fn push(&mut self) {}
    fn pop(&mut self) {}
    fn reset(&mut self) {}
}

pub(super) fn setup() -> Executor {
    let mut exec = Executor::new();
    let end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    exec.solve_deadline.set(Some(end));
    let commands = ay_frontend::parse("(set-logic QF_UF)(declare-const p Bool)(assert p)")
        .expect("parse unchanged Boolean fixture");
    for command in &commands {
        exec.execute(command).expect("elaborate fixture");
    }
    exec
}

impl Executor {
    pub(super) fn checked_lra_lazy(
        &mut self,
        extracts: &std::cell::Cell<usize>,
        error: QueryError,
    ) -> ExecResult<SolveResult> {
        solve_incremental_split_loop_pipeline!(self,
            tag: "CheckedExtractLazy",
            persistent_sat_field: persistent_sat,
            create_theory: ay_lra::LraSolver::new(&self.ctx.terms),
            extract_models: |_theory| {
                extracts.set(extracts.get() + 1);
                Err::<TheoryModels, _>(error)
            },
            max_splits: 16,
            pre_theory_import: |_theory, _lc, _hc, _ds| {},
            post_theory_export: |_theory| {
                (vec![], Default::default(), Default::default())
            }
        )
    }

    pub(super) fn checked_lra_assumptions(
        &mut self,
        extracts: &std::cell::Cell<usize>,
        error: QueryError,
    ) -> ExecResult<SolveResult> {
        solve_incremental_assume_split_loop_pipeline!(self,
            tag: "CheckedExtractAssumptions",
            persistent_sat_field: persistent_sat,
            assumptions: &[],
            create_theory: ay_lra::LraSolver::new(&self.ctx.terms),
            extract_models: |_theory| {
                extracts.set(extracts.get() + 1);
                Err::<TheoryModels, _>(error)
            },
            max_splits: 16,
            pre_theory_import: |_theory, _lc, _hc, _ds| {},
            post_theory_export: |_theory| {
                (vec![], Default::default(), Default::default())
            }
        )
    }

    pub(super) fn checked_mock_incremental(
        &mut self,
        counts: &Arc<Counts>,
        mut extract: impl FnMut() -> std::result::Result<TheoryModels, QueryError>,
    ) -> ExecResult<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "CheckedExtract",
            create_theory: SatTheory { counts: Arc::clone(counts) },
            extract_models: |_theory| {
                counts.extracts.fetch_add(1, Ordering::SeqCst);
                extract()
            },
            track_theory_stats: false,
            set_unknown_on_error: false
        )
    }

    pub(super) fn checked_mock_persistent(
        &mut self,
        counts: &Arc<Counts>,
        mut extract: impl FnMut() -> std::result::Result<TheoryModels, QueryError>,
    ) -> ExecResult<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "CheckedExtractPersistent",
            create_theory: SatTheory { counts: Arc::clone(counts) },
            extract_models: |_theory| {
                counts.extracts.fetch_add(1, Ordering::SeqCst);
                extract()
            },
            track_theory_stats: false,
            set_unknown_on_error: false,
            persistent_theory: true
        )
    }

    pub(super) fn checked_lra_split(
        &mut self,
        extracts: &std::cell::Cell<usize>,
        error: QueryError,
    ) -> ExecResult<SolveResult> {
        solve_incremental_split_loop_pipeline!(self,
            tag: "CheckedExtractLra",
            persistent_sat_field: persistent_sat,
            create_theory: ay_lra::LraSolver::new(&self.ctx.terms),
            extract_models: |_theory| {
                extracts.set(extracts.get() + 1);
                Err::<TheoryModels, _>(error)
            },
            max_splits: 16,
            pre_theory_import: |_theory, _lc, _hc, _ds| {},
            post_theory_export: |_theory| {
                (vec![], Default::default(), Default::default())
            },
            persistent_theory: true,
            eager_extension: true
        )
    }

    pub(super) fn checked_lra_eager(
        &mut self,
        extracts: &std::cell::Cell<usize>,
        error: QueryError,
    ) -> ExecResult<SolveResult> {
        solve_incremental_split_loop_pipeline!(self,
            tag: "CheckedExtractEager",
            persistent_sat_field: persistent_sat,
            create_theory: ay_lra::LraSolver::new(&self.ctx.terms),
            extract_models: |_theory| {
                extracts.set(extracts.get() + 1);
                Err::<TheoryModels, _>(error)
            },
            max_splits: 16,
            pre_theory_import: |_theory, _lc, _hc, _ds| {},
            post_theory_export: |_theory| {
                (vec![], Default::default(), Default::default())
            },
            eager_extension: true
        )
    }
}
