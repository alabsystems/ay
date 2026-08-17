// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// What the caller's solver looked like at the instant grounding succeeded,
/// recorded before `install_grounded_model` pops the tentative scope.
/// `scoped_bounds` is the only field a pop actually changes, so it distinguishes
/// grounding over live refinement bounds from grounding into a clean relaxation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct GroundingProbe {
    pub(super) successes: usize,
    pub(super) tentative_scopes: u32,
    pub(super) scoped_bounds: usize,
    pub(super) tangent_lemmas: u64,
}

std::thread_local! {
    pub(super) static TEST_PROBE: std::cell::Cell<GroundingProbe> =
        const { std::cell::Cell::new(GroundingProbe {
            successes: 0,
            tentative_scopes: 0,
            scoped_bounds: 0,
            tangent_lemmas: 0,
        }) };
}

pub(super) fn reset_test_successes() {
    TEST_PROBE.with(|slot| slot.set(GroundingProbe::default()));
}

pub(super) fn test_successes() -> usize {
    TEST_PROBE.with(std::cell::Cell::get).successes
}

pub(super) fn test_probe() -> GroundingProbe {
    TEST_PROBE.with(std::cell::Cell::get)
}
