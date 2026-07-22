// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External-boundary canary for #6315 step-mode matching.

use ay_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
use ay_dpll::{DpllT, SolveStepResult};
use ay_sat::SatResult;

#[derive(Clone, Copy)]
struct DummyTheory;

impl TheorySolver for DummyTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {}
}

fn handle_step_result(result: SolveStepResult) -> SatResult {
    match result {
        SolveStepResult::Done(result) => result,
        SolveStepResult::NeedBoundRefinements(_reqs) => SatResult::Unknown,
        SolveStepResult::NeedSplit(_split) => SatResult::Unknown,
        SolveStepResult::NeedDisequalitySplit(_split) => SatResult::Unknown,
        SolveStepResult::NeedExpressionSplit(_split) => SatResult::Unknown,
        SolveStepResult::NeedStringLemma(_lemma) => SatResult::Unknown,
        SolveStepResult::NeedModelEquality(_req) => SatResult::Unknown,
        SolveStepResult::NeedModelEqualities(_reqs) => SatResult::Unknown,
        _ => SatResult::Unknown,
    }
}

#[test]
fn test_solve_step_non_exhaustive_canary_6315() {
    let mut dpll = DpllT::new(1, DummyTheory);

    let result = dpll.solve_step().expect("dummy solve_step should succeed");

    match handle_step_result(result) {
        SatResult::Sat(model) => assert_eq!(model.len(), 1, "expected one SAT model value"),
        other => panic!("expected SAT result from dummy theory, got {other:?}"),
    }
}
