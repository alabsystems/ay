// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Kitten {
    /// Create a new kitten sub-solver.
    pub(crate) fn new() -> Self {
        Self {
            num_internal_vars: 0,
            values: Vec::new(),
            phases: Vec::new(),
            rng_state: 1,
            vars: Vec::new(),
            marks: Vec::new(),
            links: Vec::new(),
            queue_first: INVALID,
            queue_last: INVALID,
            queue_search: INVALID,
            queue_stamp: 0,
            unassigned: 0,
            clause_data: Vec::new(),
            end_original: 0,
            watches: Vec::new(),
            trail: Vec::new(),
            propagated: 0,
            level: 0,
            status: 0,
            inconsistent: INVALID,
            ext_to_int: Vec::new(),
            int_to_ext: Vec::new(),
            analyzed: Vec::new(),
            assumptions: Vec::new(),
            units: Vec::new(),
            clause_buf: Vec::new(),
            resolved: Vec::new(),
            track_antecedents: false,
            failed: Vec::new(),
            failing: INVALID,
            core: Vec::new(),
            ticks: 0,
            ticks_limit: u64::MAX,
            conflicts: 0,
            decisions: 0,
            propagations: 0,
        }
    }

    /// Clear all clauses, assignments, learned state. Keeps allocated memory.
    pub(crate) fn clear(&mut self) {
        self.assumptions.clear();
        self.core.clear();
        self.clause_buf.clear();
        self.clause_data.clear();
        self.trail.clear();
        self.units.clear();

        for w in &mut self.watches {
            w.clear();
        }

        // Unmap external variables.
        for &eidx in &self.int_to_ext {
            let ei = eidx as usize;
            if ei < self.ext_to_int.len() {
                self.ext_to_int[ei] = 0;
            }
        }
        self.int_to_ext.clear();

        // Reset per-variable arrays.
        self.phases.iter_mut().for_each(|v| *v = 0);
        self.values.iter_mut().for_each(|v| *v = 0);
        self.vars.iter_mut().for_each(|v| *v = Var::default());
        self.marks.iter_mut().for_each(|v| *v = 0);
        self.failed.iter_mut().for_each(|v| *v = false);

        self.num_internal_vars = 0;
        self.end_original = 0;
        self.propagated = 0;
        self.level = 0;
        self.status = 0;
        self.inconsistent = INVALID;
        self.failing = INVALID;
        self.queue_first = INVALID;
        self.queue_last = INVALID;
        self.queue_search = INVALID;
        self.queue_stamp = 0;
        self.unassigned = 0;
        self.conflicts = 0;
        self.decisions = 0;
        self.propagations = 0;
        // Match CaDiCaL's `kitten_clear()`: a fresh local environment should
        // not restart phase randomization from the same seed every time.
        self.rng_state = Self::advance_random(self.rng_state);
    }

    /// Enable antecedent tracking for clausal core extraction.
    pub(crate) fn enable_antecedent_tracking(&mut self) {
        self.track_antecedents = true;
    }

    /// Set tick-based effort limit relative to the current tick count.
    pub(crate) fn set_ticks_limit(&mut self, limit: u64) {
        self.ticks_limit = self.ticks.saturating_add(limit);
    }

    /// Get current tick count.
    pub(crate) fn current_ticks(&self) -> u64 {
        self.ticks
    }

    /// Randomize decision phases for future branching.
    ///
    /// CaDiCaL sweep treats each kitten SAT call as a fresh random simulation.
    /// The first decision bit comes from the low bit of the generator state,
    /// which makes repeated calls deterministically explore different models.
    pub(crate) fn randomize_phases(&mut self) {
        let mut random = 0u64;
        let mut available = 0u32;
        let mut rng_state = self.rng_state;
        for phase in &mut self.phases {
            if available == 0 {
                rng_state = Self::advance_random(rng_state);
                random = rng_state;
                available = u64::BITS;
            }
            *phase = (random & 1) as u8;
            random >>= 1;
            available -= 1;
        }
        self.rng_state = rng_state;
    }

    /// Invert all cached decision phases.
    #[allow(dead_code)]
    pub(crate) fn flip_phases(&mut self) {
        for phase in &mut self.phases {
            *phase ^= 1;
        }
    }

    fn advance_random(state: u64) -> u64 {
        state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407)
    }
}
