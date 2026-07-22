// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod clique_dense_specialist_census;
mod preprocessing_stats;
mod random3sat;
mod stric_bmc_ibm_10;

/// Spawn a background thread that sets `solver`'s interrupt flag after `secs`.
/// Returns the shared flag for use with `solve_interruptible`.
fn setup_timeout(solver: &mut Solver, secs: u64) -> Arc<AtomicBool> {
    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let f = flag.clone();
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_secs(secs));
        f.store(true, Ordering::Relaxed);
    });
    flag
}

/// Solve with a timeout via `solve_interruptible`. Spawns a background
/// interrupt thread and returns the raw `SatResult`.
fn solve_with_timeout(solver: &mut Solver, secs: u64) -> SatResult {
    let interrupt = setup_timeout(solver, secs);
    let flag = interrupt;
    solver
        .solve_interruptible(move || flag.load(Ordering::Relaxed))
        .into_inner()
}
