// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! RUP probes for proof steps alone, which leave the search as they found it.
//!
//! A run without a proof never probes congruence's hyper-ternary binaries,
//! equivalence edges or ladder rungs. A probe through `search_propagate` moves
//! watches, swaps watched literals in the arena, refreshes blockers, drops
//! stale watchers, saves phases and charges search ticks, and every later pass
//! sizes its budget from those ticks and walks those watch lists: one probe
//! made the whole run differ from the run without a proof (the posture screen,
//! competition/proof-posture-parity/LEDGER.md). These probes assign on the
//! trail, so the VeriPB hint walk reads their reasons as it always did, but
//! propagate by reading the watch lists, never changing them.

use super::super::super::*;
use crate::kani_compat::{DetHashMap, DetHashSet};

/// The watches a frozen probe moves, kept beside the solver's lists: literal
/// index to the clauses to visit when that literal is falsified, each
/// (literal, clause) pair once.
#[derive(Default)]
struct ProbeWatches {
    by_lit: DetHashMap<usize, Vec<usize>>,
    placed: DetHashSet<(usize, usize)>,
}

impl ProbeWatches {
    fn watch(&mut self, lit: Literal, off: usize) {
        if self.placed.insert((lit.index(), off)) {
            self.by_lit.entry(lit.index()).or_default().push(off);
        }
    }
}

impl Solver {
    /// Whether clause `lits` is RUP, with its annotated-RUP hint ids read off
    /// the probe's contradiction (`veripb_clause_probe_hints`; `None` when
    /// hints are off or unreadable). The negation of each literal is assumed
    /// at its own level and propagated by `frozen_propagate`; `rungs` are
    /// unwatched clauses (XOR ladder rungs) it propagates through as well.
    /// Watch lists, arena, blockers, phases, ticks and counters are left as
    /// they were: every assignment is made at its decision level and undone.
    #[track_caller]
    pub(super) fn frozen_rup_probe(
        &mut self,
        lits: &[Literal],
        rungs: &[usize],
    ) -> (bool, Option<Vec<u64>>) {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: clause RUP probe must start at level 0"
        );
        // Root propagation still pending is the search's own work, done here
        // as by every RUP probe (congruence's callers leave none pending).
        if self.probe_has_root_conflict() {
            return (true, None);
        }
        // No phase, two-stage clause score or chronological level comes out of
        // the probe: with chronological assignment off, a rung unit at root
        // is assigned at the probe's level, never fixed at level 0.
        let saved = (
            self.suppress_phase_saving,
            self.chrono_enabled,
            self.two_stage_clause_management,
            self.two_stage_warm,
        );
        self.suppress_phase_saving = true;
        self.chrono_enabled = false;
        self.two_stage_clause_management = false;
        self.two_stage_warm = false;
        let mut moved = ProbeWatches::default();
        let mut outcome = (false, None);
        for &lit in lits {
            match self.lit_value(lit.negated()) {
                Some(false) => {
                    outcome = (true, self.veripb_clause_probe_hints(lits, None, Some(lit)));
                    break;
                }
                Some(true) => {}
                None => {
                    let head = self.trail.len();
                    self.decision_level += 1;
                    self.trail_lim.push(head);
                    self.enqueue(lit.negated(), None);
                    if let Some(conflict) = self.frozen_propagate(head, rungs, &mut moved) {
                        outcome = (
                            true,
                            self.veripb_clause_probe_hints(lits, Some(conflict), None),
                        );
                        break;
                    }
                }
            }
        }
        self.backtrack_without_phase_saving(0);
        (
            self.suppress_phase_saving,
            self.chrono_enabled,
            self.two_stage_clause_management,
            self.two_stage_warm,
        ) = saved;
        outcome
    }

    /// Unit propagation of the trail from `head` to fixpoint. Each watcher of
    /// a falsified literal whose blocker is not true has its clause scanned
    /// whole by `frozen_visit`, as are `rungs` first; the clauses `moved`
    /// watches on the falsified literal follow. Returns the falsified clause.
    fn frozen_propagate(
        &mut self,
        mut head: usize,
        rungs: &[usize],
        moved: &mut ProbeWatches,
    ) -> Option<ClauseRef> {
        for &off in rungs {
            if let Some(conflict) = self.frozen_visit(off, moved) {
                return Some(conflict);
            }
        }
        while head < self.trail.len() {
            let false_lit = self.trail[head].negated();
            head += 1;
            let extra = moved.by_lit.remove(&false_lit.index()).unwrap_or_default();
            for k in 0..self.watches.len_of(false_lit) {
                // The blocker is a literal of the clause: true, it satisfies it.
                if self.lit_val(self.watches.blocker(false_lit, k)) > 0 {
                    continue;
                }
                let off = self.watches.clause_ref(false_lit, k).0 as usize;
                if let Some(conflict) = self.frozen_visit(off, moved) {
                    return Some(conflict);
                }
            }
            for off in extra {
                if let Some(conflict) = self.frozen_visit(off, moved) {
                    return Some(conflict);
                }
            }
        }
        None
    }

    /// One clause of `frozen_propagate`: skipped when dead (whatever kind of
    /// watcher names it, so a stale binary watcher cannot propagate through a
    /// deleted clause) or satisfied; returned when every literal is false;
    /// its one open literal assigned with it as the reason; with two or more
    /// open, watched on two of them in `moved`, where BCP would move its watch.
    fn frozen_visit(&mut self, off: usize, moved: &mut ProbeWatches) -> Option<ClauseRef> {
        if off >= self.arena.len() || self.arena.is_dead(off) {
            return None;
        }
        let mut open: [Option<Literal>; 2] = [None, None];
        for i in 0..self.arena.len_of(off) {
            let lit = self.arena.literal(off, i);
            match self.lit_val(lit) {
                v if v > 0 => return None,
                0 if open[0].is_none() => open[0] = Some(lit),
                0 if open[1].is_none() => open[1] = Some(lit),
                _ => {}
            }
        }
        let clause = ClauseRef(off as u32);
        match open {
            [None, _] => Some(clause),
            [Some(unit), None] => {
                self.enqueue(unit, Some(clause));
                None
            }
            [Some(a), Some(b)] => {
                moved.watch(a, off);
                moved.watch(b, off);
                None
            }
        }
    }
}
