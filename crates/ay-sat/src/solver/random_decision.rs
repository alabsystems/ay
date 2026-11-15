// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random decision sequences (focused mode only): CaDiCaL's schedule by
//! default, Kissat 4.0.4's under `--sat-randec-kissat` (`decide.c:57-124`).

use super::*;

impl Solver {
    /// Start a new random decision burst. Sets burst length and schedules
    /// the next burst using CaDiCaL's phase * ln(phase) interval growth.
    pub(crate) fn start_random_sequence(&mut self) {
        let count = self.cold.random_decision_phases + 1;
        self.cold.random_decision_phases = count;
        if ay_core::sat_ab_switches().randec_kissat == Some(true) {
            // Kissat decide.c:57-84: length trunc(10 log10(n + 9)) conflicts,
            // next limit conflicts + trunc(500 log10(n + 9)).
            let l = ((count + 9) as f64).log10();
            self.cold.randomized_deciding = ((10.0 * l) as u64).max(1);
            self.cold.next_random_decision = self.num_conflicts.saturating_add((500.0 * l) as u64);
            return;
        }

        // Burst length: RANDEC_LENGTH * ln(count + 10)
        let length = (RANDEC_LENGTH * ((count + 10) as f64).ln()) as u64;
        self.cold.randomized_deciding = length.max(1);

        // Schedule next burst: conflicts + phases * ln(phases) * RANDEC_INT
        let phases = self.cold.random_decision_phases as f64;
        let delta = phases * phases.ln();
        self.cold.next_random_decision = self
            .num_conflicts
            .saturating_add((delta * RANDEC_INT) as u64);
    }

    /// Check if a random decision should be made. Returns a random unassigned
    /// variable if we are in a random burst, or starts one if the conflict
    /// threshold is reached. CaDiCaL only enables this in focused mode.
    pub(super) fn next_random_decision(&mut self) -> Option<Variable> {
        // Only inject random decisions in focused mode (CaDiCaL: randecfocused=1, randecstable=0)
        if self.stable_mode {
            return None;
        }

        let kissat = ay_core::sat_ab_switches().randec_kissat == Some(true);
        if kissat {
            // Kissat decide.c:86-124: a running sequence continues; a new one
            // starts at level 0 once the conflict limit (first 500) is reached.
            if self.cold.randomized_deciding == 0 {
                let limit = if self.cold.random_decision_phases == 0 {
                    500
                } else {
                    self.cold.next_random_decision
                };
                if self.num_conflicts < limit || self.decision_level > 0 {
                    return None;
                }
                self.start_random_sequence();
            }
        } else if self.num_conflicts < self.cold.next_random_decision {
            // Not yet time for random decisions
            return None;
        }

        // Start a new random burst if not already in one
        if !kissat && self.cold.randomized_deciding == 0 {
            // CaDiCaL decide.cpp:80: delay random burst start if too deep.
            // `level > assumptions.size()` — with no assumptions, only level 0.
            if self.decision_level > 0 {
                return None;
            }
            self.start_random_sequence();
        }

        // Pick a random unassigned, non-eliminated variable using LCG seeded from decisions
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return None;
        }
        let mut rng = Random::new(self.num_decisions);
        for _ in 0..num_vars {
            let idx = rng.pick(num_vars);
            if !self.var_is_assigned(idx) && !self.var_lifecycle.is_removed(idx) {
                self.stats.random_decisions += 1;
                return Some(Variable(idx as u32));
            }
        }
        // All sampled vars are assigned or eliminated; fall through to normal decision
        None
    }

    /// Decrement the random decision burst counter on conflict.
    /// Called from conflict analysis paths to end the burst after enough conflicts.
    #[inline]
    pub(super) fn on_conflict_random_decision(&mut self) {
        self.poll_process_memory_limit();
        if self.cold.randomized_deciding > 0 {
            self.cold.randomized_deciding -= 1;
        }
    }
}
