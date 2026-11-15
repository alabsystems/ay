// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thread-local fault injection for the probes a published `sat` rests on
//! (mutation tests for the `discharged-trust` refusal).
//!
//! The threat this simulates is a WRONG refutation that only a fresh executor
//! running the same code vouches for (`discharged-trust`): a same-engine
//! defect re-derives the same wrong `unsat`. Each guard forges one probe
//! family, whatever the query:
//!
//! * [`ForgedTrustGuard::model_check_refutations`]: every refutation probe of
//!   the model check (`Executor::checked_model_check_solve_classified`). Its
//!   confirm solve is a separate entry point and is never forged.
//! * [`ForgedTrustGuard::sat_authority_probes`]: every sat-authority probe
//!   (`Executor::checked_sat_authority_ground_solve`): the publication gate's
//!   confirming obligations and the SAT-certificate producers' refutations.
//!
//! A forged UNSAT is judged by `CheckedIsolatedMode::admits_discharged_trust`,
//! the rule `CheckedIsolatedMode::admits_unsat` applies to a real token of
//! that class (`checked_isolated_mode::tests` pins the two together on a real
//! one).

use std::cell::Cell;

thread_local! {
    /// `Some(n)` inside a model-check guard: `n` probes forged so far.
    static MODEL_CHECK_REFUTATIONS: Cell<Option<usize>> = const { Cell::new(None) };
    /// `Some(n)` inside a sat-authority guard: `n` probes forged so far.
    static SAT_AUTHORITY_PROBES: Cell<Option<usize>> = const { Cell::new(None) };
}

type Seam = &'static std::thread::LocalKey<Cell<Option<usize>>>;

/// Panic-safe scope forging one probe family on this thread. Thread-local
/// state keeps parallel tests isolated.
pub(in crate::executor) struct ForgedTrustGuard {
    seam: Seam,
    previous: Option<usize>,
}

impl ForgedTrustGuard {
    fn install(seam: Seam) -> Self {
        let previous = seam.with(|state| state.replace(Some(0)));
        Self { seam, previous }
    }

    /// Forge every refutation probe of the model check.
    pub(in crate::executor) fn model_check_refutations() -> Self {
        Self::install(&MODEL_CHECK_REFUTATIONS)
    }

    /// Forge every sat-authority probe.
    pub(in crate::executor) fn sat_authority_probes() -> Self {
        Self::install(&SAT_AUTHORITY_PROBES)
    }

    /// How many probes this scope has forged: zero means the fixture never
    /// reached one, so it proves nothing.
    pub(in crate::executor) fn forged(&self) -> usize {
        self.seam.with(|state| state.get().unwrap_or(0))
    }
}

impl Drop for ForgedTrustGuard {
    fn drop(&mut self) {
        self.seam.with(|state| state.set(self.previous));
    }
}

fn forge(seam: Seam) -> bool {
    seam.with(|state| match state.get() {
        Some(forged) => {
            state.set(Some(forged.saturating_add(1)));
            true
        }
        None => false,
    })
}

/// Whether to forge this model-check refutation probe (counting it when so).
pub(in crate::executor) fn forge_model_check_refutation() -> bool {
    forge(&MODEL_CHECK_REFUTATIONS)
}

/// Whether to forge this sat-authority probe (counting it when so).
pub(in crate::executor) fn forge_sat_authority_probe() -> bool {
    forge(&SAT_AUTHORITY_PROBES)
}
