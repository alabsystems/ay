// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::sync::atomic::AtomicBool;

use super::{SolveArgs, SAT_COMPETITION_WRAPPER_ENV};

/// Latched before executor construction so proof-cycle shedding cannot race.
pub(crate) static COMPETITION_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

/// Whether a benchmark harness requested competition behavior.
fn competition_env_active() -> bool {
    const SIGNALS: &[&str] = &[
        SAT_COMPETITION_WRAPPER_ENV,
        "AY_COMPETITION",
        "AY_SAT_COMPETITION_PROFILE",
        "AY_SAT_PROFILE_ID",
    ];
    SIGNALS
        .iter()
        .any(|name| env::var(name).is_ok_and(|value| !value.trim().is_empty()))
}

/// Competition mode disables optional batteries, never soundness defaults.
pub(crate) fn competition_mode(args: &SolveArgs) -> bool {
    args.competition || competition_env_active()
}
