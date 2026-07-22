// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Scripted fake stepper for unit testing the scheduler.
struct ScriptedStepper {
    steps: Vec<Option<ChcEngineResult>>,
    index: usize,
}

impl ScriptedStepper {
    fn new(steps: Vec<Option<ChcEngineResult>>) -> Self {
        Self { steps, index: 0 }
    }
}

impl StepwiseTrl for ScriptedStepper {
    fn do_step(&mut self) -> Option<ChcEngineResult> {
        if self.index < self.steps.len() {
            let result = self.steps[self.index].take();
            self.index += 1;
            result
        } else {
            Some(ChcEngineResult::Unknown)
        }
    }
}

#[test]
fn test_interleaved_alternates_forward_backward() {
    // Both sides return None for 3 steps each, then forward returns Unknown,
    // backward returns Safe.
    let fwd = ScriptedStepper::new(vec![
        None,                           // step 1: forward, no result
        None,                           // step 3: forward, no result
        None,                           // step 5: forward, no result
        Some(ChcEngineResult::Unknown), // step 7: forward exhausted
    ]);
    let bwd = ScriptedStepper::new(vec![
        None, // step 2: backward, no result
        None, // step 4: backward, no result
        None, // step 6: backward, no result
        // Phase 2: backward runs solo after forward exhausts
        Some(ChcEngineResult::Safe(
            crate::pdr::model::InvariantModel::new(),
        )),
    ]);
    let mut interleaved = InterleavedTrl::new(fwd, bwd);
    let result = interleaved.solve();
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "Expected Safe when backward succeeds after forward exhausts: got {result:?}"
    );
}

#[test]
fn test_interleaved_returns_immediately_on_active_safe() {
    let fwd = ScriptedStepper::new(vec![
        None,
        Some(ChcEngineResult::Safe(
            crate::pdr::model::InvariantModel::new(),
        )), // forward finds Safe on step 3
    ]);
    let bwd = ScriptedStepper::new(vec![
        None, // step 2
             // backward should never get step 4
    ]);
    let mut interleaved = InterleavedTrl::new(fwd, bwd);
    let result = interleaved.solve();
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "Expected immediate Safe from forward: got {result:?}"
    );
}

#[test]
fn test_interleaved_returns_immediately_on_passive_unsafe() {
    use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let fwd = ScriptedStepper::new(vec![
        None, // step 1: forward
        None, // step 3: forward
    ]);
    let bwd = ScriptedStepper::new(vec![
        // step 2: backward finds Unsafe
        Some(ChcEngineResult::Unsafe(Counterexample::new(vec![
            CounterexampleStep::new(crate::predicate::PredicateId(0), FxHashMap::default()),
        ]))),
    ]);
    let mut interleaved = InterleavedTrl::new(fwd, bwd);
    let result = interleaved.solve();
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Expected immediate Unsafe from backward: got {result:?}"
    );
}

#[test]
fn test_interleaved_fallback_passive_runs_to_completion_on_unknown() {
    // Forward returns Unknown on step 1. Backward then runs solo.
    let fwd = ScriptedStepper::new(vec![
        Some(ChcEngineResult::Unknown), // step 1: forward exhausted immediately
    ]);
    let bwd = ScriptedStepper::new(vec![
        None,                           // solo step 1
        None,                           // solo step 2
        Some(ChcEngineResult::Unknown), // solo step 3: also exhausted
    ]);
    let mut interleaved = InterleavedTrl::new(fwd, bwd);
    let result = interleaved.solve();
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "Expected Unknown when both sides exhaust: got {result:?}"
    );
}
