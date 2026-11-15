// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Census of the guarded ENUMERATIVE lane's structural gate
//! (#quantifier-guarded-enumerative).
//!
//! The gate decides, per eligible universal, whether the lane enumerates it
//! (`quant_unit_authority::quantifier_guarded_enumerative_enabled`). Its own
//! answer is the only direct evidence of what it decided: a final verdict is
//! not, because other routes can decide the same query. Measured: the
//! ground-first fallback (#qe-ground-first) refutes the kill-switch binary's
//! matcher-produced fixture by deciding it WITHOUT its trigger-carrying axiom,
//! on a disposable probe whose E-matcher therefore produced nothing, so there
//! the lane is correctly the only route. That `unsat` is right and says
//! nothing about this executor's gate, which declined.
//!
//! Observation only: no verdict path reads these keys. They count the gate
//! decisions recorded in the statistics a check-sat publishes.
//! `last_statistics` restarts at every public check-sat and at every internal
//! re-solve (`prepare_check_sat_internal_state`), so the count is that of the
//! solve whose statistics are published. A disposable probe executor, the
//! ground-first probe among them, counts in its own statistics, and those do
//! not cross back.

use crate::executor::Executor;
use crate::quant_unit_authority::{quantifier_guarded_enumerative_enabled, EnumerativeAdmission};

/// Eligible universals (triggerless, not entailed, enumerable) whose gate was
/// consulted.
const CONSULTED_KEY: &str = "quantifier.guarded_enumerative.consulted";
/// Of those, the universals the gate admitted to enumeration.
const ADMITTED_KEY: &str = "quantifier.guarded_enumerative.admitted";

impl Executor {
    /// Ask the gate for one eligible universal and record its answer.
    pub(super) fn guarded_enumerative_gate(&mut self, admission: EnumerativeAdmission) -> bool {
        let admitted = quantifier_guarded_enumerative_enabled(admission);
        let statistics = &mut self.last_statistics;
        for (key, by) in [(CONSULTED_KEY, 1), (ADMITTED_KEY, u64::from(admitted))] {
            let prior = statistics.get_int(key).unwrap_or(0);
            statistics.set_int(key, prior.saturating_add(by));
        }
        admitted
    }
}
