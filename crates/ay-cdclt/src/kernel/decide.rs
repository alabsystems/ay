// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When the kernel has anything to do, and which phases it suggests (design
//! §3.2 `can_propagate`, `seed_phase_hints_dual`; §3.8).

use ay_sat::{Literal, SolverContext};

use super::clauses::sat_lit;

use super::Kernel;

impl Kernel<'_> {
    /// Whether the trail holds a theory atom the plug-ins have not seen. A run
    /// of purely Boolean assignments (Tseitin structure) gives them nothing.
    pub(super) fn new_atom_on_trail(&self, sat: &dyn SolverContext) -> bool {
        let trail = sat.trail();
        let from = self.trail_pos.max(self.scan_pos.get()).min(trail.len());
        let found = trail[from..].iter().any(|lit| {
            let var = lit.variable().index();
            self.atoms.entry(var).is_some() || self.hub_var.get(var).is_some_and(|&w| w != 0)
        });
        self.scan_pos.set(trail.len());
        found
    }

    /// Theory-aware branching (design §3.8, an engine option): every other
    /// decision, the first plug-in hint whose atom is unassigned. The lanes
    /// alternate the same way, leaving VSIDS the other half.
    pub(super) fn theory_decision(&self, sat: &dyn SolverContext) -> Option<Literal> {
        if !self.theory_branching {
            return None;
        }
        let count = self.decision_calls.get();
        self.decision_calls.set(count.wrapping_add(1));
        if count % 2 != 0 {
            return None;
        }
        self.plugins.iter().find_map(|plugin| {
            let (atom, phase) = plugin.decision_hint()?;
            let lit = sat_lit(self.atoms.var_of(atom)?, phase);
            sat.lit_value(lit).is_none().then_some(lit)
        })
    }

    /// Write each unassigned atom's plug-in phase into both phase arrays (the
    /// saved phase and, for stable mode, the target phase). Skipped while every
    /// plug-in reports an unchanged phase epoch: the answers would be the same.
    pub(super) fn seed_phases(&self, phase: &mut [i8], target: &mut [i8], vals: &[i8]) {
        let epoch = self
            .plugins
            .iter()
            .map(|p| p.phase_epoch())
            .try_fold(0u64, |acc, e| {
                e.map(|e| acc.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(e))
            });
        if epoch.is_some() && self.seeded_epoch.get() == epoch {
            return;
        }
        self.seeded_epoch.set(epoch);
        for (var, entry) in self.atoms.owned() {
            if vals.get(var * 2).is_some_and(|&v| v != 0) {
                continue;
            }
            let Some(plugin) = self.plugins.get(usize::from(entry.owner)) else {
                continue;
            };
            let Some(p) = plugin.phase(entry.term) else {
                continue;
            };
            let v = if p { 1 } else { -1 };
            if let Some(slot) = phase.get_mut(var) {
                *slot = v;
            }
            if let Some(slot) = target.get_mut(var) {
                *slot = v;
            }
        }
    }
}
