// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private malformed-producer guards. Public round trips and budget/stop tests
//! live in tests/bounded_native_input.rs and compile against the public API.

use crate::api::{
    Logic, NativeReplayExportBudget as Budget, NativeReplayExportError as Error,
    NativeReplayExportLimits as Limits, NativeReplayMetadata, Solver,
};
use ay_core::TermId;

#[test]
fn bounded_native_input_invalid_internal_root_refuses_without_indexing_arena() {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    solver
        .executor
        .context_mut()
        .assertions
        .push(TermId(u32::MAX));
    let mut budget = Budget::new(Limits::new(16 << 20, 8 << 20, 4 << 20, 128));
    assert_eq!(
        solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut budget,
            &mut |_, _| true
        ),
        Err(Error::InvalidTerm { term: u32::MAX })
    );
    assert_eq!(budget.usage().output_bytes, 0);
}

#[test]
fn bounded_native_input_overflowed_owned_charge_refuses_even_with_max_allowance() {
    let mut budget = Budget::new(Limits::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX));
    let mut progress = |_, _| true;
    let mut meter = super::meter::Meter {
        budget: &mut budget,
        progress: &mut progress,
    };
    assert!(
        meter.charge(usize::MAX, 0).is_err(),
        "saturated arithmetic is not an exact admissible bound"
    );
    assert_eq!(meter.budget.usage().work, 0);
}
