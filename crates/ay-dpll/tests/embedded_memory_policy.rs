// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consumer-boundary tests for host-owned process memory policy.

use ay_dpll::api::{Logic, Solver};

#[test]
fn constructing_solver_does_not_arm_a_process_global_memory_limit() {
    // Integration tests compile ay-dpll as a normal dependency, so this proves
    // the behavior downstream consumers receive (unlike an in-crate cfg(test)
    // assertion). A library constructor must not silently bind the whole host
    // process to AY's embedded default.
    ay_sys::set_process_memory_limit(0);
    let _solver = Solver::new(Logic::QfLia);
    assert_eq!(ay_sys::get_process_memory_limit(), 0);
}
