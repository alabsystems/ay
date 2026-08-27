// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover `B - k*A = c`, optionally guarded by `mode = g`, for every
    /// predicate that has a fact clause and a self-loop.
    pub(in crate::pdr::solver) fn discover_guarded_scaled_equalities(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if !self.predicate_has_facts(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: guarded-eq: pred {} skipped (no facts)",
                        pred.id.index()
                    );
                }
                continue;
            }
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };
            // Two arguments are enough for the unguarded form; a guarded one
            // additionally needs the mode argument.
            if canonical_vars.len() < 2 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: guarded-eq: pred {} skipped (arity {} < 2)",
                        pred.id.index(),
                        canonical_vars.len()
                    );
                }
                continue;
            }

            // `None` first: the unconditional equality is always in scope, and
            // is the form case-split branches need once the mode is specialized
            // away.
            let mut guards: Vec<Option<ModeGuard>> = vec![None];
            guards.extend(self.mode_guard_candidates(pred.id).into_iter().map(Some));
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: guarded-eq: pred {} — 1 unguarded + {} mode guard(s)",
                    pred.id.index(),
                    guards.len() - 1
                );
            }

            let (mut alive, budget_start, budget) =
                self.guarded_equality_init_candidates(pred.id, &canonical_vars, &guards);
            if alive.is_empty() {
                continue;
            }
            self.refine_guarded_equalities(pred.id, &mut alive, &budget_start, budget);
            self.emit_guarded_equalities(pred.id, &canonical_vars, &alive);
        }
    }

    /// PHASE 1 — candidates that hold at INIT.
    ///
    /// `c` is forced by the fact clause (`c = B_init - k * A_init`), so
    /// there is no scan over candidate constants. The init check is
    /// ABSOLUTE: facts only, no frame assumption, so a candidate that
    /// survives here genuinely holds on every initial state.
    fn guarded_equality_init_candidates(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        guards: &[Option<ModeGuard>],
    ) -> (
        Vec<GuardedEquality>,
        ay_core::time::Instant,
        std::time::Duration,
    ) {
        let init_values = self.get_init_values(predicate);
        let scale_factors = self.guarded_equality_scale_factors();
        let budget_start = ay_core::time::Instant::now();
        let budget = std::time::Duration::from_secs(2);

        let mut alive: Vec<GuardedEquality> = Vec::new();
        'candidates: for guard in guards {
            let guard_idx = guard.map(|guard| guard.idx);
            for (i, var_a) in canonical_vars.iter().enumerate() {
                if Some(i) == guard_idx || !matches!(var_a.sort, ChcSort::Int) {
                    continue;
                }
                for (j, var_b) in canonical_vars.iter().enumerate() {
                    if Some(j) == guard_idx || i == j || !matches!(var_b.sort, ChcSort::Int) {
                        continue;
                    }
                    let (Some(a0), Some(b0)) = (
                        init_values
                            .get(&var_a.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min),
                        init_values
                            .get(&var_b.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min),
                    ) else {
                        continue;
                    };
                    for &k in &scale_factors {
                        if budget_start.elapsed() >= budget || self.is_cancelled() {
                            break 'candidates;
                        }
                        let Some(scaled) = k.checked_mul(a0) else {
                            continue;
                        };
                        let Some(c) = b0.checked_sub(scaled) else {
                            continue;
                        };
                        let cand = GuardedEquality {
                            guard: *guard,
                            a_idx: i,
                            b_idx: j,
                            k,
                            c,
                        };
                        if self.guarded_equality_init_valid(predicate, cand) {
                            alive.push(cand);
                        }
                    }
                }
            }
        }
        (alive, budget_start, budget)
    }

    /// PHASE 2 — HOUDINI. Drop every candidate not preserved ASSUMING THE
    /// WHOLE SURVIVING SET, and repeat to a fixpoint.
    ///
    /// This is the part that has to be a group decision rather than a
    /// per-candidate one. `J = 1 => D - 2*C = 0` is not preserved on its
    /// own — its step leaves a residual `B - A` — and is preserved exactly
    /// when `A = B` is also assumed (#1411). Checking candidates one at a
    /// time therefore rejects the pair that carries the proof, and the
    /// obvious repair of assuming the whole of frame 1 instead is WORSE
    /// THAN WRONG: frame 1 holds other unproven candidates, and leaning on
    /// them admitted `C = A` and `D = 2*A` here — both false, since
    /// `C = n(n+1)/2` and `D = n(n+1)` against `A = n` agree only for
    /// `n <= 1`.
    ///
    /// The fixpoint of this loop is sound WITHOUT any frame assumption:
    /// every survivor holds at init (phase 1) and every survivor's step is
    /// discharged using only other survivors, so the CONJUNCTION is
    /// inductive by simultaneous induction. Nothing outside the set is
    /// assumed, so no unproven frame lemma can leak in.
    fn refine_guarded_equalities(
        &mut self,
        predicate: PredicateId,
        alive: &mut Vec<GuardedEquality>,
        budget_start: &ay_core::time::Instant,
        budget: std::time::Duration,
    ) {
        let mut rounds = 0;
        loop {
            rounds += 1;
            if rounds > GUARDED_EQ_MAX_HOUDINI_ROUNDS
                || budget_start.elapsed() >= budget
                || self.is_cancelled()
            {
                alive.clear();
                break;
            }
            let assumption: Vec<GuardedEquality> = alive.clone();
            let mut survivors = Vec::with_capacity(alive.len());
            let mut dropped = false;
            for cand in alive.iter() {
                if self.guarded_equality_preserved_given(predicate, *cand, &assumption) {
                    survivors.push(*cand);
                } else {
                    dropped = true;
                }
            }
            *alive = survivors;
            if !dropped || alive.is_empty() {
                break;
            }
        }
    }

    /// PHASE 3 — emit the jointly-inductive survivors.
    fn emit_guarded_equalities(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        alive: &[GuardedEquality],
    ) {
        for cand in alive {
            let lemma = Self::guarded_scaled_equality_expr(canonical_vars, *cand);
            if self.frames.len() > 1 && self.frames[1].contains_lemma(predicate, &lemma) {
                continue;
            }
            if self.config.verbose {
                let guard = match cand.guard {
                    None => "(unguarded)".to_string(),
                    Some(guard) => {
                        format!("{} = {} =>", canonical_vars[guard.idx].name, guard.value)
                    }
                };
                safe_eprintln!(
                    "PDR: Discovered scaled equality for pred {}: {} {} - {}*{} = {}",
                    predicate.index(),
                    guard,
                    canonical_vars[cand.b_idx].name,
                    cand.k,
                    canonical_vars[cand.a_idx].name,
                    cand.c
                );
            }
            self.add_discovered_invariant(predicate, lemma, 1);
        }
    }
}
