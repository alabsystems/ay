// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scratch-state lucky probes (kissat lucky.c) for the EARLY lucky phase.
//!
//! Implements kissat's exact probe set — constant all-true / all-false
//! (lucky.c `no_all_negative_clauses` / `no_all_positive_clauses`), then the
//! four directional sweeps (forward/backward x false/true) with full
//! propagation and single-flip repair — on a standalone counting-propagation
//! engine that reads the clause arena IMMUTABLY.
//!
//! Why not probe with the solver's own `decide()` + `search_propagate()`?
//! Because BCP permanently mutates state that is invisible to `backtrack()`:
//! watch-list order, per-clause saved search positions and clause literal
//! order (`swap_literals`). A measured 81ms failed in-solver probe on
//! e3bd4a39 (191K vars / 13M clauses) perturbed the subsequent search from
//! 9.7K conflicts (0.7s) to 185K conflicts (35s). The scratch engine cannot
//! corrupt or perturb the solver by construction: on failure it is simply
//! dropped.
//!
//! Verdict safety: a successful probe yields a full model that is verified
//! against every active clause here, then again by `finalize_sat_model` and
//! `verify_external_model` (the model gate). A buggy probe can only waste
//! (budget-bounded) time, never emit a wrong verdict. UNSAT is never derived
//! here — failed probes just fall through to normal preprocessing + CDCL.

use super::*;
use std::time::{Duration, Instant};

/// Throttle for wall-clock deadline / interrupt checks inside the hot loops.
const LUCKY_SCRATCH_CHECK_INTERVAL: usize = 4096;

/// The kissat lucky probe order (lucky.c:307-393).
#[derive(Clone, Copy, Debug)]
enum LuckyProbe {
    ConstantTrue,
    ConstantFalse,
    Sweep { assign_true: bool, forward: bool },
}

const LUCKY_PROBE_ORDER: [LuckyProbe; 6] = [
    LuckyProbe::ConstantTrue,
    LuckyProbe::ConstantFalse,
    LuckyProbe::Sweep {
        assign_true: false,
        forward: true,
    },
    LuckyProbe::Sweep {
        assign_true: true,
        forward: true,
    },
    LuckyProbe::Sweep {
        assign_true: false,
        forward: false,
    },
    LuckyProbe::Sweep {
        assign_true: true,
        forward: false,
    },
];

/// Why a probe stopped without producing a model.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProbeStop {
    /// Both polarities of some variable conflicted — try the next probe.
    Conflict,
    /// Per-probe wall budget exhausted — try the next probe.
    Deadline,
    /// External interrupt — abandon lucky entirely.
    Interrupted,
}

/// Standalone counting-propagation engine over an immutable clause arena.
///
/// Per active clause `c`: `n_false[c]` counts falsified literals and
/// `n_sat[c]` counts satisfied literals under the scratch assignment. A
/// clause with `n_sat == 0 && n_false == len` is a conflict; with
/// `n_sat == 0 && n_false == len - 1` it forces its single unassigned
/// literal. Undo is exact: decrement the same counters in reverse trail
/// order, so resetting to the root state is O(work done).
struct LuckyScratch {
    num_vars: usize,
    /// Arena word offsets of active clauses, indexed by dense clause id.
    clause_off: Vec<u32>,
    /// CSR occurrence lists: `occ[occ_start[lit] .. occ_start[lit + 1]]` are
    /// the dense clause ids containing `lit` (indexed by `Literal::index()`).
    occ_start: Vec<u32>,
    occ: Vec<u32>,
    n_false: Vec<u32>,
    n_sat: Vec<u32>,
    /// Per-variable assignment: 1 true, -1 false, 0 unassigned.
    vals: Vec<i8>,
    trail: Vec<Literal>,
    /// Trail entries below `qhead` have their counter effects applied.
    qhead: usize,
    /// Trail prefix holding the solver's level-0 assignments; probes never
    /// undo below this.
    root_len: usize,
    deadline: Instant,
}

impl LuckyScratch {
    /// Build occurrence lists over all active clauses. Returns `None` when
    /// the formula exceeds u32 indexing (never on competition inputs: a
    /// 1.4 GB CNF stays well under 4.3 G literals/words).
    fn build(arena: &ClauseArena, num_vars: usize) -> Option<Self> {
        let num_lits = num_vars.checked_mul(2)?;
        let mut counts = vec![0u32; num_lits];
        let mut clause_off: Vec<u32> = Vec::new();
        let mut total: u64 = 0;
        for off in arena.indices() {
            if !arena.is_active(off) {
                continue;
            }
            let lits = arena.literals(off);
            if lits.is_empty() {
                continue;
            }
            if off > u32::MAX as usize {
                return None;
            }
            clause_off.push(off as u32);
            for &lit in lits {
                let idx = lit.index();
                if idx >= num_lits {
                    // Malformed literal — refuse to probe rather than risk OOB.
                    return None;
                }
                counts[idx] += 1;
                total += 1;
            }
        }
        if total > u32::MAX as u64 || clause_off.len() > u32::MAX as usize {
            return None;
        }

        // Prefix sums -> occ_start; reuse `counts` as per-literal cursors.
        let mut occ_start = vec![0u32; num_lits + 1];
        let mut acc: u32 = 0;
        for (i, &c) in counts.iter().enumerate() {
            occ_start[i] = acc;
            acc += c;
        }
        occ_start[num_lits] = acc;
        let mut cursor = occ_start.clone();
        let mut occ = vec![0u32; total as usize];
        for (dense, &off) in clause_off.iter().enumerate() {
            for &lit in arena.literals(off as usize) {
                let cur = &mut cursor[lit.index()];
                occ[*cur as usize] = dense as u32;
                *cur += 1;
            }
        }

        let n_clauses = clause_off.len();
        Some(Self {
            num_vars,
            clause_off,
            occ_start,
            occ,
            n_false: vec![0u32; n_clauses],
            n_sat: vec![0u32; n_clauses],
            vals: vec![0i8; num_vars],
            trail: Vec::new(),
            qhead: 0,
            root_len: 0,
            deadline: Instant::now(),
        })
    }

    #[inline]
    fn occ_range(&self, lit: Literal) -> std::ops::Range<usize> {
        let i = lit.index();
        self.occ_start[i] as usize..self.occ_start[i + 1] as usize
    }

    /// Signed value of `lit` under the scratch assignment: 1 true, -1 false,
    /// 0 unassigned.
    #[inline]
    fn lit_val(&self, lit: Literal) -> i8 {
        let v = self.vals[lit.variable().index()];
        if lit.is_positive() {
            v
        } else {
            -v
        }
    }

    #[inline]
    fn assign(&mut self, lit: Literal) {
        debug_assert_eq!(self.vals[lit.variable().index()], 0);
        self.vals[lit.variable().index()] = if lit.is_positive() { 1 } else { -1 };
        self.trail.push(lit);
    }

    /// Seed the root state from the solver's level-0 assignments and apply
    /// their counter effects. The solver is at a BCP fixpoint, so this cannot
    /// derive anything new; a conflict here would mean inconsistent input
    /// state, in which case we refuse to probe (fail closed).
    fn init_root(&mut self, arena: &ClauseArena, solver_vals: &[i8]) -> bool {
        for v in 0..self.num_vars {
            let val = solver_vals[v * 2];
            if val > 0 {
                self.assign(Literal::positive(Variable(v as u32)));
            } else if val < 0 {
                self.assign(Literal::negative(Variable(v as u32)));
            }
        }
        // Generous deadline for the root replay: it is O(root occurrences).
        self.deadline = Instant::now() + Duration::from_mins(1);
        let ok = matches!(self.propagate(arena, &|| false), Ok(()));
        self.root_len = self.trail.len();
        ok && self.qhead == self.trail.len()
    }

    /// Propagate all queued assignments. `Err(stop)` on conflict, deadline or
    /// interrupt. Counter effects of a trail entry are applied atomically
    /// (both loops complete even when a conflict is detected mid-clause-list)
    /// so `undo_to` can treat every entry below `qhead` as fully applied.
    fn propagate(
        &mut self,
        arena: &ClauseArena,
        is_interrupted: &dyn Fn() -> bool,
    ) -> Result<(), ProbeStop> {
        let mut processed_since_check = 0usize;
        while self.qhead < self.trail.len() {
            processed_since_check += 1;
            if processed_since_check >= LUCKY_SCRATCH_CHECK_INTERVAL {
                processed_since_check = 0;
                if is_interrupted() {
                    return Err(ProbeStop::Interrupted);
                }
                if Instant::now() >= self.deadline {
                    return Err(ProbeStop::Deadline);
                }
            }
            let lit = self.trail[self.qhead];

            // Satisfy loop first so unit detection below sees fresh n_sat.
            for k in self.occ_range(lit) {
                let c = self.occ[k] as usize;
                self.n_sat[c] += 1;
            }

            // Falsify loop: count, detect conflicts and units.
            let mut conflict = false;
            let not_lit = lit.negated();
            for k in self.occ_range(not_lit) {
                let c = self.occ[k] as usize;
                self.n_false[c] += 1;
                if self.n_sat[c] > 0 || conflict {
                    continue;
                }
                let off = self.clause_off[c] as usize;
                let lits = arena.literals(off);
                let len = lits.len() as u32;
                if self.n_false[c] >= len {
                    // Complete this literal's counter effects, then stop.
                    conflict = true;
                } else if self.n_false[c] + 1 == len {
                    // n_false counts PROCESSED false literals, so exactly one
                    // literal of the clause is still unprocessed. It is
                    // either unassigned (a genuine unit — assign it),
                    // enqueued-true awaiting processing (clause satisfied —
                    // n_sat will catch up; do nothing), or enqueued-false
                    // (the clause is already all-false under vals — conflict
                    // now rather than when the queue reaches it).
                    let mut unit = None;
                    let mut pending_true = false;
                    for &l in lits {
                        match self.lit_val(l) {
                            0 => {
                                unit = Some(l);
                                break;
                            }
                            v if v > 0 => {
                                pending_true = true;
                                break;
                            }
                            _ => {}
                        }
                    }
                    match unit {
                        Some(l) => self.assign(l),
                        None if pending_true => {}
                        // All literals false under vals — real conflict.
                        None => conflict = true,
                    }
                }
            }
            self.qhead += 1;
            if conflict {
                return Err(ProbeStop::Conflict);
            }
        }
        Ok(())
    }

    /// Exact undo of all trail entries at or above `pos`. Entries below
    /// `qhead` had counter effects applied — reverse them; entries at or
    /// above `qhead` were only enqueued.
    fn undo_to(&mut self, pos: usize) {
        debug_assert!(pos >= self.root_len);
        for i in (pos..self.trail.len()).rev() {
            let lit = self.trail[i];
            if i < self.qhead {
                for k in self.occ_range(lit) {
                    let c = self.occ[k] as usize;
                    self.n_sat[c] -= 1;
                }
                for k in self.occ_range(lit.negated()) {
                    let c = self.occ[k] as usize;
                    self.n_false[c] -= 1;
                }
            }
            self.vals[lit.variable().index()] = 0;
        }
        self.trail.truncate(pos);
        self.qhead = self.qhead.min(pos);
    }

    fn reset_to_root(&mut self) {
        self.undo_to(self.root_len);
        self.qhead = self.root_len;
    }

    /// Kissat lucky.c:11-80: if no clause is "all negative" (resp. "all
    /// positive") under the root assignment, then extending the root with
    /// all-true (resp. all-false) satisfies every clause. Pure read-only
    /// scan; no propagation needed (propagations under the constant
    /// assignment can only assign the chosen polarity — proof in lucky.c).
    fn run_constant(
        &self,
        arena: &ClauseArena,
        all_true: bool,
        is_interrupted: &dyn Fn() -> bool,
    ) -> Result<Vec<bool>, ProbeStop> {
        for (i, &off) in self.clause_off.iter().enumerate() {
            if i % LUCKY_SCRATCH_CHECK_INTERVAL == 0 {
                if is_interrupted() {
                    return Err(ProbeStop::Interrupted);
                }
                if Instant::now() >= self.deadline {
                    return Err(ProbeStop::Deadline);
                }
            }
            if self.n_sat[i] > 0 {
                continue; // satisfied by the root assignment
            }
            let saved = arena
                .literals(off as usize)
                .iter()
                .any(|&lit| lit.is_positive() == all_true && self.lit_val(lit) >= 0);
            if !saved {
                return Err(ProbeStop::Conflict);
            }
        }
        Ok(self.model_with_default(all_true))
    }

    /// Kissat lucky.c:82-305: directional sweep. Assign every unassigned
    /// variable to `assign_true` in index order (`forward`) or reverse order,
    /// propagating fully after each assignment. On conflict, undo the last
    /// assignment and try the opposite polarity once (single-flip repair);
    /// if that also conflicts, the probe fails.
    fn run_sweep(
        &mut self,
        arena: &ClauseArena,
        assign_true: bool,
        forward: bool,
        is_interrupted: &dyn Fn() -> bool,
    ) -> Result<Vec<bool>, ProbeStop> {
        let make = |v: usize, positive: bool| {
            if positive {
                Literal::positive(Variable(v as u32))
            } else {
                Literal::negative(Variable(v as u32))
            }
        };
        let mut steps = 0usize;
        let sweep_one = |this: &mut Self, v: usize| -> Result<(), ProbeStop> {
            if this.vals[v] != 0 {
                return Ok(());
            }
            let pos = this.trail.len();
            this.assign(make(v, assign_true));
            match this.propagate(arena, is_interrupted) {
                Ok(()) => Ok(()),
                Err(ProbeStop::Conflict) => {
                    this.undo_to(pos);
                    this.assign(make(v, !assign_true));
                    this.propagate(arena, is_interrupted)
                }
                Err(stop) => Err(stop),
            }
        };
        if forward {
            for v in 0..self.num_vars {
                steps += 1;
                if steps.is_multiple_of(LUCKY_SCRATCH_CHECK_INTERVAL) && is_interrupted() {
                    return Err(ProbeStop::Interrupted);
                }
                sweep_one(self, v)?;
            }
        } else {
            for v in (0..self.num_vars).rev() {
                steps += 1;
                if steps.is_multiple_of(LUCKY_SCRATCH_CHECK_INTERVAL) && is_interrupted() {
                    return Err(ProbeStop::Interrupted);
                }
                sweep_one(self, v)?;
            }
        }
        debug_assert_eq!(self.qhead, self.trail.len());
        Ok(self.model_with_default(assign_true))
    }

    /// Current scratch assignment as a model; unassigned variables (only
    /// possible for the constant probes) default to `default_true`.
    fn model_with_default(&self, default_true: bool) -> Vec<bool> {
        (0..self.num_vars)
            .map(|v| match self.vals[v] {
                0 => default_true,
                val => val > 0,
            })
            .collect()
    }

    /// Defensive final check: every active clause satisfied by `model`.
    fn verify_model(&self, arena: &ClauseArena, model: &[bool]) -> bool {
        self.clause_off.iter().all(|&off| {
            arena.literals(off as usize).iter().any(|&lit| {
                let v = lit.variable().index();
                v < model.len() && (model[v] == lit.is_positive())
            })
        })
    }
}

impl Solver {
    /// Run kissat's lucky probe set on a scratch engine. Returns a fully
    /// verified satisfying model, or `None` if every probe failed / timed
    /// out / was interrupted. Never mutates solver state.
    pub(super) fn lucky_scratch_probe(
        &self,
        per_probe_budget: Duration,
        total_budget: Duration,
    ) -> Option<Vec<bool>> {
        let mut eng = LuckyScratch::build(&self.arena, self.num_vars)?;
        if !eng.init_root(&self.arena, &self.vals) {
            return None;
        }
        // #lucky-total-cap: bound the WHOLE probe sequence, not just each
        // probe. The per-probe budget scales with clause count (~1s/M), so on
        // a 22M-clause giant two FAILING sweeps burned 43.8s of a 120s solve
        // budget — flipping three near-budget main-track solves back to
        // timeouts (measured: ddf9620 sat@105s -> unknown; lucky_ms=43770).
        // Successful probes are FAST (<=1.6s measured on 63M clauses), so a
        // small total cap keeps every win and turns the failure tax into
        // noise. Failures typically die in ms via conflicts; the cap only
        // bites pathological all-probes-slow cases.
        let overall_deadline = Instant::now() + total_budget;
        let is_interrupted = || self.is_interrupted();
        for probe in LUCKY_PROBE_ORDER {
            if self.is_interrupted() {
                return None;
            }
            let remaining = overall_deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                tracing::debug!("lucky (scratch): total budget exhausted, falling through");
                return None;
            }
            eng.deadline = Instant::now() + per_probe_budget.min(remaining);
            let outcome = match probe {
                LuckyProbe::ConstantTrue => eng.run_constant(&self.arena, true, &is_interrupted),
                LuckyProbe::ConstantFalse => eng.run_constant(&self.arena, false, &is_interrupted),
                LuckyProbe::Sweep {
                    assign_true,
                    forward,
                } => eng.run_sweep(&self.arena, assign_true, forward, &is_interrupted),
            };
            match outcome {
                Ok(model) => {
                    if eng.verify_model(&self.arena, &model) {
                        tracing::info!(?probe, "lucky (scratch): satisfying assignment found");
                        return Some(model);
                    }
                    // Engine bug — fail closed: abandon lucky, let normal
                    // search handle the instance.
                    tracing::warn!(
                        ?probe,
                        "lucky (scratch): model failed self-verification; abandoning lucky"
                    );
                    debug_assert!(false, "lucky scratch model failed self-verification");
                    return None;
                }
                Err(ProbeStop::Interrupted) => return None,
                Err(ProbeStop::Conflict) | Err(ProbeStop::Deadline) => {
                    eng.reset_to_root();
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add(solver: &mut Solver, clause: &[i32]) {
        let lits: Vec<Literal> = clause.iter().map(|&d| Literal::from_dimacs(d)).collect();
        assert!(solver.add_clause(lits), "clause {clause:?} rejected");
    }

    fn probe(solver: &Solver) -> Option<Vec<bool>> {
        solver.lucky_scratch_probe(Duration::from_secs(5), Duration::from_secs(10))
    }

    #[test]
    fn scratch_constant_true_and_false() {
        // Every clause has a positive literal => all-true model.
        let mut s = Solver::new(3);
        add(&mut s, &[1, 2]);
        add(&mut s, &[-1, 3]);
        assert_eq!(probe(&s), Some(vec![true, true, true]));

        // Every clause has a negative literal => all-false model.
        let mut s = Solver::new(3);
        add(&mut s, &[-1, -2]);
        add(&mut s, &[1, -3]);
        assert_eq!(probe(&s), Some(vec![false, false, false]));
    }

    #[test]
    fn scratch_forward_false_propagates() {
        // (1 v 2) kills constant-false, (-1 v -2) kills constant-true; the
        // forward-false sweep succeeds: x1=F propagates x2=T via (1 v 2).
        let mut s = Solver::new(2);
        add(&mut s, &[1, 2]);
        add(&mut s, &[-1, -2]);
        assert_eq!(probe(&s), Some(vec![false, true]));
    }

    #[test]
    fn scratch_forward_false_single_flip_repair() {
        // Forward-false conflicts on x1 ((1 v 2) forces 2, (1 v -2) then
        // conflicts) and repairs by flipping x1 to true.
        let mut s = Solver::new(2);
        add(&mut s, &[1, 2]);
        add(&mut s, &[1, -2]);
        add(&mut s, &[-1, -2]); // also kills constant-true
        let model = probe(&s).expect("flip repair must find a model");
        assert!(model[0], "x1 must be flipped to true");
        assert!(!model[1]);
    }

    #[test]
    fn scratch_pending_true_is_not_a_conflict() {
        // Regression: deciding x1=F propagates x2=T and x3=T in one batch.
        // While x2 is processed, clause (-2 v 3) reaches n_false == len-1
        // with x3 still enqueued-but-unprocessed (pending true). The engine
        // must treat the clause as satisfied, not as a defensive conflict —
        // the original code failed the whole forward-false sweep here.
        let mut s = Solver::new(4);
        add(&mut s, &[1, 2]);
        add(&mut s, &[1, 3]);
        add(&mut s, &[-2, 3]);
        add(&mut s, &[-1, -4]); // kills constant-true
        assert_eq!(probe(&s), Some(vec![false, true, true, false]));
    }

    #[test]
    fn scratch_all_probes_fail_returns_none() {
        // Gadgets: c1..c4 force var1 true (kills forward-false at var2),
        // c5..c8 force var4 false (kills forward-true at var5),
        // c9/c10 kill both constant probes,
        // c11..c14 force var15 true (kills backward-false at var14),
        // c15..c18 force var12 false (kills backward-true at var11).
        let mut s = Solver::new(15);
        for c in [
            [1, 2, 3],
            [1, 2, -3],
            [1, -2, 3],
            [1, -2, -3],
            [-4, 5, 6],
            [-4, 5, -6],
            [-4, -5, 6],
            [-4, -5, -6],
            [7, 8, 9],
            [-7, -8, -9],
            [15, 14, 13],
            [15, 14, -13],
            [15, -14, 13],
            [15, -14, -13],
            [-12, 11, 10],
            [-12, 11, -10],
            [-12, -11, 10],
            [-12, -11, -10],
        ] {
            add(&mut s, &c);
        }
        assert_eq!(probe(&s), None, "every scratch probe must fail");
    }

    #[test]
    fn scratch_probe_never_mutates_solver() {
        let mut s = Solver::new(15);
        add(&mut s, &[1, 2, 3]);
        add(&mut s, &[-1, -2, -3]);
        add(&mut s, &[1, -2, 3]);
        let vals_before = s.vals.clone();
        let trail_before = s.trail.clone();
        let decisions_before = s.num_decisions;
        let props_before = s.num_propagations;
        let _ = probe(&s);
        assert_eq!(s.vals, vals_before);
        assert_eq!(s.trail, trail_before);
        assert_eq!(s.num_decisions, decisions_before);
        assert_eq!(s.num_propagations, props_before);
        assert_eq!(s.decision_level, 0);
    }

    #[test]
    fn scratch_respects_root_units() {
        // Unit clause fixes x1=true at level 0; probes must honor it.
        let mut s = Solver::new(2);
        add(&mut s, &[1]);
        add(&mut s, &[-1, -2]);
        let model = probe(&s).expect("model expected");
        assert!(model[0], "root unit must be honored");
    }
}
