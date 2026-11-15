// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::fixture::{Counts, SatTheory};
use super::*;
use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;
use std::cell::Cell;
use std::sync::{atomic::Ordering, Arc};

fn observed<'a, T>(calls: &Cell<usize>, value: &'a T) -> &'a T {
    calls.set(calls.get() + 1);
    value
}

#[test]
fn shared_refusal_pops_frame_without_evaluating_placeholder_maps_or_model() {
    let mut exec = Executor::new();
    let mut sat = ay_sat::Solver::new(0);
    sat.push();
    let counts = Arc::new(Counts::default());
    let mut theory = SatTheory::new(&counts);
    let mut timing = crate::dpll_support::SplitLoopTimingStats::default();
    let ttv = DetHashMap::<TermId, u32>::default();
    let vtt = DetHashMap::<u32, TermId>::default();
    let maps = Cell::new(0);
    let models = Cell::new(0);
    let cleanups = Cell::new(0);
    let model = Vec::<bool>::new();
    let result: ExecResult<SolveResult> = 'shared: loop {
        pipeline_store_sat_model!('shared, exec, sat,
            observed(&models, &model).clone(),
            observed(&maps, &ttv), observed(&maps, &vtt), 0,
            timing, theory, _theory,
            Err::<TheoryModels, _>(QueryError::Exhausted),
            pre_store: {
                cleanups.set(cleanups.get() + 1);
                let _ = sat.pop();
            }
        );
    };
    assert_terminal(result, QueryError::Exhausted);
    assert_eq!(sat.scope_depth(), 0);
    assert_eq!(cleanups.get(), 1);
    assert_eq!(maps.get(), 0);
    assert_eq!(models.get(), 0);
    assert_eq!(timing.store_model, std::time::Duration::ZERO);
    assert!(exec.last_model.is_none());
    assert!(exec.last_result().is_none());
}

#[test]
fn shared_refusal_unsets_terms_before_return_without_model_storage() {
    let mut exec = Executor::new();
    let sat = ay_sat::Solver::new(0);
    let counts = Arc::new(Counts::default());
    let mut theory = SatTheory::new(&counts);
    let mut timing = crate::dpll_support::SplitLoopTimingStats::default();
    let ttv = DetHashMap::<TermId, u32>::default();
    let vtt = DetHashMap::<u32, TermId>::default();
    let result: ExecResult<SolveResult> = 'shared: loop {
        pipeline_store_sat_model!('shared, exec, sat, Vec::<bool>::new(),
            ttv, vtt, 0, timing, theory, _theory,
            Err::<TheoryModels, _>(QueryError::Invalid("array closure not prepared")),
            pre_store: { theory.unset_terms(); }
        );
    };
    assert_terminal(result, QueryError::Invalid("array closure not prepared"));
    assert_eq!(sat.scope_depth(), 0);
    assert_eq!(counts.unsets.load(Ordering::SeqCst), 1);
    assert_eq!(timing.store_model, std::time::Duration::ZERO);
    assert!(exec.last_model.is_none());
    assert!(exec.last_result().is_none());
}
