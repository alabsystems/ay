// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Public pseudo-Boolean API and installed solver facade.
//!
//! Solver implementation lives in `ay-pb-core`, which deliberately has no
//! dependency on an embedding MILP engine. This leaf preserves the historical
//! `ay_pb` API and binary while injecting AY's MILP optimum prover per portfolio
//! call.

#![forbid(unsafe_code)]

mod milp_lane;
pub mod opt_fallback;

// Preserve every root-level type, function, and public module from the former
// monolithic crate. The explicit `portfolio`/`dev_tools` modules below shadow
// their glob-imported core counterparts only to install the leaf-owned engine.
pub use ay_pb_core::*;

/// Portfolio API with the leaf-owned MILP upgrade explicitly injected.
pub mod portfolio {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    use ay_pb_core::{PbInstance, PbObjective, PbSolution};

    pub use ay_pb_core::portfolio::*;

    use ay_pb_core::portfolio::{
        solve_optimization_portfolio_parallel_with_upgrade as core_solve_parallel_with_upgrade,
        solve_optimization_portfolio_with_timings_and_upgrade as core_solve_with_timings_and_upgrade,
        solve_optimization_portfolio_with_upgrade as core_solve_with_upgrade,
        solve_wbo_reduced_optimization_portfolio_parallel_with_upgrade as core_solve_wbo_parallel_with_upgrade,
    };

    use crate::milp_lane::AY_MILP_UPGRADE;

    pub fn solve_optimization_portfolio(
        instance: &PbInstance,
        objective: &PbObjective,
        timeout_dur: Option<Duration>,
        start: Instant,
        term_flag: &AtomicBool,
        on_improve: &mut dyn FnMut(i128, &[bool]),
    ) -> PbSolution {
        core_solve_with_upgrade(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            on_improve,
            &AY_MILP_UPGRADE,
        )
    }

    pub fn solve_optimization_portfolio_with_timings(
        instance: &PbInstance,
        objective: &PbObjective,
        timeout_dur: Option<Duration>,
        start: Instant,
        term_flag: &AtomicBool,
        on_improve: &mut dyn FnMut(i128, &[bool]),
    ) -> PbPortfolioOutcome {
        core_solve_with_timings_and_upgrade(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            on_improve,
            &AY_MILP_UPGRADE,
        )
    }

    pub fn solve_optimization_portfolio_parallel(
        instance: &Arc<PbInstance>,
        objective: &PbObjective,
        timeout_dur: Option<Duration>,
        start: Instant,
        term_flag: &AtomicBool,
        on_improve: &mut dyn FnMut(i128, &[bool]),
    ) -> PbSolution {
        core_solve_parallel_with_upgrade(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            on_improve,
            &AY_MILP_UPGRADE,
        )
    }

    pub fn solve_wbo_reduced_optimization_portfolio_parallel(
        instance: &Arc<PbInstance>,
        objective: &PbObjective,
        timeout_dur: Option<Duration>,
        start: Instant,
        term_flag: &AtomicBool,
        on_improve: &mut dyn FnMut(i128, &[bool]),
    ) -> PbSolution {
        core_solve_wbo_parallel_with_upgrade(
            instance,
            objective,
            timeout_dur,
            start,
            term_flag,
            on_improve,
            &AY_MILP_UPGRADE,
        )
    }
}

/// Developer probes with the same leaf-owned MILP engine as the production
/// portfolio. Other developer helpers are re-exported unchanged from core.
#[cfg(feature = "dev-tools")]
#[doc(hidden)]
pub mod dev_tools {
    use ay_pb_core::PbInstance;

    pub use ay_pb_core::dev_tools::*;

    use crate::milp_lane::AY_MILP_UPGRADE;

    pub fn run_probe(
        instance: &PbInstance,
        engine: ProbeEngine,
        config: ProbeConfig,
        should_stop: &dyn Fn() -> bool,
        on_improve: &mut dyn FnMut(i128, &[bool]),
    ) -> Result<ProbeOutcome, DevToolError> {
        run_probe_with_upgrade(
            instance,
            engine,
            config,
            should_stop,
            on_improve,
            &AY_MILP_UPGRADE,
        )
    }
}
