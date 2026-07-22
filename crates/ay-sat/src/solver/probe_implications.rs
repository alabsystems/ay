// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public propagate-only probing: assume one literal at a fresh decision
//! level, run BCP (no search, no learning), report which watched literals
//! became false, and restore level 0. Built for MaxSAT AM1 strengthening
//! (#maxsat-am1-probe): unit-propagation-derived implications are logically
//! valid, so `probe=T ⇒ watch=F` edges give a sound selector conflict graph
//! even when no direct binary clause connects the pair (protein family:
//! 64 selectors behind 2.5M binaries, zero direct selector-selector edges).

use super::*;

/// Result of a single [`Solver::probe_implications_false`] call.
#[derive(Debug, Default)]
pub struct ProbeImplications {
    /// The probe literal is false in every model (assuming it propagated to
    /// a conflict, or it was already assigned false at level 0). The CALLER
    /// decides what to do with this fact (e.g. `add_clause(¬probe)`); this
    /// probe records nothing.
    pub failed: bool,
    /// Watched literals that became FALSE under the probe assumption
    /// (excluding the probe itself). Empty when `failed`.
    pub falsified: Vec<Literal>,
}

impl Solver {
    /// Assume `probe` at a fresh decision level, unit-propagate, and report
    /// which of `watch` became false. State is restored (backtrack to level
    /// 0) before returning; heuristic state (phases, brancher bumps) may
    /// move, and the incremental assumption cache is invalidated.
    ///
    /// Soundness of consumers: every reported implication is derived by unit
    /// propagation from the clause database, hence logically valid. `failed`
    /// means `¬probe` is entailed. A formula already UNSAT at level 0
    /// reports `failed: true` with no implications.
    ///
    /// CONTRACT (#maxsat-am1-probe): watches attach in the SOLVE prologue,
    /// so this is only meaningful AFTER at least one `solve*` call, and it
    /// does NOT see clauses added since that solve (their watches and unit
    /// enqueues are deferred to the next prologue). Callers needing
    /// pre-solve or mid-stream probing must first drive a real solve — an
    /// instantly-interrupted warmup solve is NOT safe (measured: it corrupts
    /// subsequent incremental solves; the ay-maxsat cross-check nets caught
    /// wrong optima). A first-class attach-only prologue is future work.
    pub fn probe_implications_false(
        &mut self,
        probe: Literal,
        watch: &[Literal],
    ) -> ProbeImplications {
        let mut out = ProbeImplications::default();
        // The probe replays trail work between solves; the assumption-prefix
        // cache must not survive it.
        self.cold.assumption_cache_valid = false;

        if self.has_empty_clause {
            out.failed = true;
            return out;
        }
        // A finished SAT solve can leave the model on the trail above level
        // 0; probes must judge entailment from the level-0 fixpoint only.
        if self.decision_level() > 0 {
            self.backtrack(0);
        }
        if self.propagate_check_unsat() {
            out.failed = true;
            return out;
        }

        let var_idx = probe.variable().index();
        if var_idx >= self.num_vars || self.var_lifecycle.is_removed(var_idx) {
            return out;
        }
        if self.var_is_assigned(var_idx) {
            out.failed = self.lit_value(probe) == Some(false);
            return out;
        }

        self.decide(probe);
        if self.search_propagate().is_some() {
            self.backtrack(0);
            out.failed = true;
            return out;
        }
        for &w in watch {
            if w != probe && self.lit_value(w) == Some(false) {
                out.falsified.push(w);
            }
        }
        self.backtrack(0);
        out
    }
}

#[cfg(test)]
mod tests {
    use crate::{Literal, Solver};

    /// Post-solve probing (the supported regime: watches are attached by the
    /// solve prologue) reports chain implications and failed literals.
    #[test]
    fn probe_reports_chain_implications_after_solve() {
        let mut solver = Solver::new(7);
        let lit = |i: i32| Literal::from(i);
        // 1 → 4 → ¬2, 1 → 5 → ¬3 (conflicts only via chains), and a
        // failed-literal seed: 6 → 4 plus 6 → ¬4.
        for (a, mid, b) in [(1, 4, 2), (1, 5, 3)] {
            solver.add_clause(vec![lit(-a), lit(mid)]);
            solver.add_clause(vec![lit(-mid), lit(-b)]);
        }
        solver.add_clause(vec![lit(-6), lit(4)]);
        solver.add_clause(vec![lit(-6), lit(-4)]);
        assert!(matches!(
            solver.solve().into_inner(),
            crate::SatResult::Sat(_)
        ));

        let watch = [lit(1), lit(2), lit(3)];
        let r = solver.probe_implications_false(lit(1), &watch);
        assert!(!r.failed, "assuming 1 must not conflict");
        let mut got = r.falsified.clone();
        got.sort_unstable();
        assert_eq!(got, vec![lit(2), lit(3)], "chains 1⇒¬2 and 1⇒¬3");

        // Failed-literal detection: a probe that propagates to conflict.
        // 6 → 4 and 6 → ¬4 were in the database before the solve, so
        // assuming 6 conflicts.
        let r = solver.probe_implications_false(lit(6), &[lit(1)]);
        assert!(r.failed, "6 forces 4 and ¬4 — must report failed");
    }
}
