// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3-optimized 1UIP conflict analysis (#8569 Gap 5).
//!
//! Pure 1UIP analysis stripped of all features unnecessary for IC3 queries:
//! - No OTFS (on-the-fly subsumption) accounting
//! - No tick accounting (search_ticks)
//! - No clause bumping (bump_clause)
//! - No streaming UNSAT core marking
//! - No LRAT chain collection (already disabled by set_ic3_mode)
//! - No JIT conflict processing (IC3 conflicts are 2-10 literals; JIT
//!   overhead dominates for such tiny clauses)
//! - No ghost literal guards (disabled by set_ic3_mode)
//! - No solver_log! calls
//! - No IBCL stats
//! - No bumpreason decision rate tracking
//!
//! The IC3 inner loop calls `analyze_conflict_ic3` instead of the shared
//! `analyze_conflict`, and `finalize_conflict_analysis_ic3` instead of
//! `finalize_conflict_analysis`. Together these eliminate ~50% of the
//! per-conflict overhead for the typical IC3 conflict (3-8 literals,
//! 1-3 resolution steps).
//!
//! The 1UIP scheme is the published CDCL conflict-analysis algorithm
//! (Marques-Silva & Sakallah, GRASP, 1996; Moskewicz et al., Chaff,
//! DAC 2001; Een & Sorensson, "An Extensible SAT-solver", SAT 2003).

use super::*;

impl Solver {
    /// IC3-optimized 1UIP conflict analysis (#8569 Gap 5).
    ///
    /// Stripped version of `analyze_conflict` for IC3 workloads. Produces
    /// the same ConflictResult but skips OTFS, tick accounting, clause
    /// bumping, streaming core marking, JIT processing, ghost guards,
    /// and logging.
    ///
    /// SAFETY: Caller must ensure `ic3_mode` is set (which guarantees
    /// `lrat_enabled=false`, `ghost_guard_needed=false`, `chrono_enabled=false`).
    ///
    /// Returns `None` on trail exhaustion (same semantics as `analyze_conflict`).
    pub(super) fn analyze_conflict_ic3(
        &mut self,
        conflict_ref: ClauseRef,
    ) -> Option<ConflictResult> {
        self.conflict.clear(&mut self.var_data);

        debug_assert!(
            self.decision_level > 0,
            "BUG: IC3 conflict analysis called at decision level 0"
        );

        let mut counter: u32 = 0;
        let mut p: Option<Literal> = None;
        let mut index = self.trail.len();

        let mut current_clause_offset = conflict_ref.0 as usize;
        let mut current_clause_len = self.arena.len_of(current_clause_offset);

        loop {
            let clause_len = current_clause_len;

            // Process literals in the current clause (conflict or reason).
            // Pure 1UIP: no OTFS accounting, no tick accounting, no clause bumping.
            for i in 0..clause_len {
                let lit = self.arena.literal_at(current_clause_offset, i);
                if let Some(p_lit) = p {
                    if lit == p_lit {
                        continue;
                    }
                }

                let var_idx = lit.variable().index();
                let var_level = self.var_data[var_idx].level;

                if !self.conflict.is_seen(var_idx, &self.var_data) {
                    self.conflict.mark_seen(var_idx, &mut self.var_data);

                    debug_assert!(
                        var_level <= self.decision_level,
                        "BUG: IC3 analyzed literal var={} at level {} exceeds decision level {}",
                        var_idx,
                        var_level,
                        self.decision_level,
                    );

                    if var_level > 0 {
                        self.track_level_seen(var_level, var_idx);
                    }

                    if var_level == self.decision_level {
                        counter += 1;
                    } else if var_level > 0 {
                        self.conflict.add_to_learned(lit);
                    }
                    // Level-0 literals: no LRAT collection needed (disabled).
                }
            }

            // Backward scan for the next seen literal at the current level.
            let trail_len = self.trail.len();
            if index > trail_len {
                index = trail_len;
            }
            if index == 0 {
                self.stats.trail_exhaustion_bailouts += 1;
                self.conflict.clear(&mut self.var_data);
                self.clear_level_seen();
                return None;
            }
            loop {
                index -= 1;
                let trail_lit = self.trail[index];
                let var_idx = trail_lit.variable().index();
                if self.conflict.is_seen(var_idx, &self.var_data)
                    && self.var_data[var_idx].level == self.decision_level
                {
                    p = Some(trail_lit);
                    break;
                }
                if index == 0 {
                    self.stats.trail_exhaustion_bailouts += 1;
                    self.conflict.clear(&mut self.var_data);
                    self.clear_level_seen();
                    return None;
                }
            }

            debug_assert!(
                counter > 0,
                "BUG: IC3 analysis counter underflow before resolving {p:?} \
                 (counter={counter}, decision_level={})",
                self.decision_level,
            );
            if counter == 0 {
                // Release-mode guard: prevent u32 underflow.
                self.stats.trail_exhaustion_bailouts += 1;
                self.conflict.clear(&mut self.var_data);
                self.clear_level_seen();
                return None;
            }
            counter -= 1;

            if counter == 0 {
                break; // Found 1UIP
            }

            // Resolve with the reason clause of the current literal.
            let p_var = p
                .expect("IC3 conflict analysis: p set for reason lookup")
                .variable();

            let reason_kind = self.var_reason_kind(p_var.index());
            match reason_kind {
                ReasonKind::Decision => {
                    self.conflict.add_to_learned(
                        p.expect("IC3 conflict analysis: p for decision").negated(),
                    );
                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::BinaryLiteral(reason_lit) => {
                    // Binary literal reason: resolve inline without arena access.
                    let var_idx = reason_lit.variable().index();
                    let var_level = self.var_data[var_idx].level;

                    if !self.conflict.is_seen(var_idx, &self.var_data) {
                        self.conflict.mark_seen(var_idx, &mut self.var_data);

                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        }

                        if var_level == self.decision_level {
                            counter += 1;
                        } else if var_level > 0 {
                            self.conflict.add_to_learned(reason_lit);
                        }
                    }

                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::LazyTheory(_lazy_idx) => {
                    // Should not occur in IC3 mode (no theory extension).
                    debug_assert!(
                        false,
                        "BUG: LazyTheory reason in IC3 conflict analysis (var={}, lazy_idx={})",
                        p.map_or(0, |l| l.variable().index()),
                        _lazy_idx,
                    );
                    self.conflict
                        .add_to_learned(p.expect("IC3: p for lazy decision").negated());
                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::Clause(reason_ref) => {
                    // No bump_clause, no mark_streaming_core, no tick accounting.
                    current_clause_offset = reason_ref.0 as usize;
                    current_clause_len = self.arena.len_of(current_clause_offset);
                }
            }
        }

        let uip = p.expect("IC3 conflict analysis: 1UIP found").negated();
        Some(self.finalize_conflict_analysis_ic3(uip))
    }

    /// IC3-optimized finalization of conflict analysis (#8569 Gap 5).
    ///
    /// Stripped version of `finalize_conflict_analysis` that skips:
    /// - LRAT chain computation
    /// - IBCL stats
    /// - Bumpreason decision rate tracking
    ///
    /// Keeps: minimization, level_seen clear, variable bumping, watch reordering.
    fn finalize_conflict_analysis_ic3(&mut self, uip: Literal) -> ConflictResult {
        self.conflict.set_asserting_literal(uip);

        let lbd = self.conflict.compute_lbd(&self.var_data);

        if self.shrink_enabled {
            self.shrink_and_minimize_learned_clause();
        } else {
            self.minimize_learned_clause();
        }

        self.clear_level_seen();
        self.bump_reason_literals();
        self.bump_analyzed_variables();

        let backtrack_level = self.conflict.compute_backtrack_level(&self.var_data);
        let mut result = self.conflict.get_result(backtrack_level, lbd);

        crate::conflict::reorder_for_watches(
            &mut result.learned_clause,
            &self.var_data,
            backtrack_level,
        );

        self.debug_assert_learned_clause_invariants(uip, backtrack_level, &result.learned_clause);
        result
    }

    /// Verify that an IC3 learned clause is structurally valid (#8661).
    ///
    /// This is a debug-only self-check that catches domain-BCP-induced
    /// soundness bugs. It runs after conflict analysis but before backtrack,
    /// so the full trail state is still available.
    ///
    /// Checks performed:
    /// 1. **All literals falsified**: every literal in the learned clause
    ///    must be false under the current assignment (pre-backtrack).
    ///    The UIP literal (index 0) is at the current decision level;
    ///    all other literals are at lower levels.
    ///
    /// 2. **No duplicate variables**: each variable appears at most once
    ///    in the learned clause.
    ///
    /// 3. **Level ordering**: the UIP literal must be at the current
    ///    decision level. All other literals must be at strictly lower
    ///    levels (1UIP invariant).
    ///
    /// 4. **Domain coverage audit** (when domain restriction is active):
    ///    check whether any literal in the learned clause references a
    ///    non-domain variable. If so, log a diagnostic — this is the
    ///    suspected root cause of IC3 soundness bugs (#8661). Non-domain
    ///    variables in learned clauses are not inherently wrong (the
    ///    conflict may involve non-domain propagation chains), but in
    ///    IC3 mode with domain BCP, they signal that the domain was
    ///    incomplete w.r.t. the transition relation.
    ///
    /// 5. **Reason chain audit**: for each non-UIP literal in the learned
    ///    clause, verify that it was a decision or has a valid reason clause
    ///    in the clause database.
    #[cfg(debug_assertions)]
    pub(super) fn verify_ic3_learned_clause(
        &self,
        learned_clause: &[Literal],
        _conflict_ref: ClauseRef,
    ) {
        if learned_clause.is_empty() {
            return;
        }

        let dl = self.decision_level;

        // Check 1: All literals must be falsified under the current assignment.
        for (idx, &lit) in learned_clause.iter().enumerate() {
            let val = self.lit_val(lit);
            debug_assert!(
                val < 0,
                "BUG(#8661): IC3 learned clause literal {:?} (var={}, idx={}) \
                 is not falsified (val={}) at decision level {}. \
                 Learned clause: {:?}",
                lit,
                lit.variable().index(),
                idx,
                val,
                dl,
                learned_clause
                    .iter()
                    .map(|l| (l.variable().index(), l.is_positive(), self.lit_val(*l)))
                    .collect::<Vec<_>>(),
            );
        }

        // Check 2: No duplicate variables.
        {
            let mut seen_vars = Vec::with_capacity(learned_clause.len());
            for &lit in learned_clause {
                let vi = lit.variable().index();
                debug_assert!(
                    !seen_vars.contains(&vi),
                    "BUG(#8661): IC3 learned clause contains duplicate variable {} \
                     in clause {:?}",
                    vi,
                    learned_clause
                        .iter()
                        .map(|l| (l.variable().index(), l.is_positive()))
                        .collect::<Vec<_>>(),
                );
                seen_vars.push(vi);
            }
        }

        // Check 3: Level ordering — UIP at current level, others below.
        {
            let uip = learned_clause[0];
            let uip_level = self.var_data[uip.variable().index()].level;
            debug_assert!(
                uip_level == dl,
                "BUG(#8661): IC3 learned clause UIP {:?} (var={}) at level {} \
                 but decision level is {}",
                uip,
                uip.variable().index(),
                uip_level,
                dl,
            );

            for &lit in &learned_clause[1..] {
                let level = self.var_data[lit.variable().index()].level;
                debug_assert!(
                    level < dl,
                    "BUG(#8661): IC3 learned clause non-UIP literal {:?} (var={}) \
                     at level {} which is not below decision level {}. \
                     UIP={:?} at level {}",
                    lit,
                    lit.variable().index(),
                    level,
                    dl,
                    uip,
                    uip_level,
                );
            }
        }

        // Check 4: Domain coverage audit.
        if let Some(ref domain) = self.active_domain {
            let mut non_domain_count = 0u32;
            for &lit in learned_clause {
                let vi = lit.variable().index();
                if vi < domain.len() && !domain[vi] {
                    non_domain_count += 1;
                }
            }
            if non_domain_count > 0 {
                // Log diagnostic. Non-domain variables in learned clauses under
                // domain-restricted BCP indicate the domain is incomplete w.r.t.
                // the clause set. This is the primary suspect for #8661.
                //
                // NOTE: This is NOT an assertion failure — non-domain variables
                // can appear in learned clauses when the conflict involves reason
                // clauses that mix domain and non-domain literals. The domain BCP
                // skips propagation of non-domain watched literals, but conflict
                // analysis follows reason clauses regardless of domain membership.
                // The learned clause is still a valid consequence of the formula.
                //
                // However, if the domain is supposed to be complete (as in IC3
                // with a correct cone-of-influence computation), non-domain vars
                // in learned clauses suggest a domain computation bug upstream.
                eprintln!(
                    "[IC3-VERIFY] WARNING: learned clause contains {} non-domain \
                     variable(s) out of {} total literals (dl={}). \
                     Non-domain vars: {:?}",
                    non_domain_count,
                    learned_clause.len(),
                    dl,
                    learned_clause
                        .iter()
                        .filter(|l| {
                            let vi = l.variable().index();
                            vi < domain.len() && !domain[vi]
                        })
                        .map(|l| (l.variable().index(), l.is_positive()))
                        .collect::<Vec<_>>(),
                );
            }
        }

        // Check 5: Reason chain audit — every non-decision literal should
        // have a valid reason clause. Decision literals (including the UIP
        // if it was a decision) have no reason.
        for &lit in learned_clause {
            let vi = lit.variable().index();
            let level = self.var_data[vi].level;
            if level == 0 {
                // Level-0 assignments have reasons from initial propagation,
                // which may have been garbage-collected. Skip.
                continue;
            }
            let reason = self.var_data[vi].reason;
            if reason == NO_REASON {
                // NO_REASON with level > 0 means this was a decision.
                // Decisions in learned clauses are valid (they become the
                // UIP or are below the backtrack level).
                continue;
            }
            if is_binary_literal_reason(reason) {
                // Binary literal reason (jump reason #8034) — the reason
                // is encoded as a literal, not a clause reference. The
                // binary clause is implicit. This is valid.
                continue;
            }
            if is_clause_reason(reason) {
                // Verify the reason clause exists and is not garbage.
                let reason_off = reason as usize;
                let is_garbage =
                    self.arena.is_garbage(reason_off) || self.arena.is_pending_garbage(reason_off);
                debug_assert!(
                    !is_garbage,
                    "BUG(#8661): IC3 learned clause literal {lit:?} (var={vi}, level={level}) \
                     has garbage reason clause {reason} — conflict analysis used a \
                     deleted clause in the resolution chain",
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Literal, Solver, Variable};

    fn var(i: u32) -> Variable {
        Variable::new(i)
    }
    fn pos(i: u32) -> Literal {
        Literal::positive(var(i))
    }
    fn neg(i: u32) -> Literal {
        Literal::negative(var(i))
    }

    /// Verify that IC3 conflict analysis produces UNSAT on a simple conflict.
    #[test]
    fn ic3_conflict_analysis_basic_unsat() {
        let mut s = Solver::new(4);
        s.set_ic3_mode();
        // (x0 | x1) & (!x0 | !x1) & (x0 | !x1)
        // Only solution: x0=true, x1=false.
        // Assume x1=true -> conflict.
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![neg(0), neg(1)]);
        s.add_clause(vec![pos(0), neg(1)]);

        let result = s.solve_incremental_ic3(&[pos(1)]);
        assert!(result.is_unsat(), "expected UNSAT with x1=true");
    }

    /// Verify that IC3 conflict analysis produces SAT when satisfiable.
    #[test]
    fn ic3_conflict_analysis_basic_sat() {
        let mut s = Solver::new(4);
        s.set_ic3_mode();
        // (x0 | x1) & (!x0 | !x1) & (x0 | !x1)
        // Only solution: x0=true, x1=false.
        // Assume x0=true -> SAT (consistent with the only solution).
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![neg(0), neg(1)]);
        s.add_clause(vec![pos(0), neg(1)]);

        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(result.is_sat(), "expected SAT with x0=true");
    }

    /// IC3 conflict analysis on a deeper conflict requiring multiple
    /// resolution steps. Tests the binary reason and clause reason paths.
    #[test]
    fn ic3_conflict_analysis_multi_resolution() {
        let mut s = Solver::new(6);
        s.set_ic3_mode();
        // Implication chain: x0 -> x1 -> x2 -> x3 -> x4
        // Plus: !x0 | !x4 (conflict when x0=true propagates to x4=true)
        s.add_clause(vec![neg(0), pos(1)]); // x0 -> x1
        s.add_clause(vec![neg(1), pos(2)]); // x1 -> x2
        s.add_clause(vec![neg(2), pos(3)]); // x2 -> x3
        s.add_clause(vec![neg(3), pos(4)]); // x3 -> x4
        s.add_clause(vec![neg(0), neg(4)]); // !x0 | !x4

        // Assuming x0=true should propagate x1..x4=true, then conflict on !x0|!x4.
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_unsat(),
            "expected UNSAT: x0=true propagates chain to x4=true, conflicting with !x0|!x4"
        );
    }

    /// Alternating SAT/UNSAT queries to verify state is properly reset
    /// between IC3 incremental calls.
    #[test]
    fn ic3_conflict_analysis_alternating_queries() {
        let mut s = Solver::new(4);
        s.set_ic3_mode();
        // x0 XOR x1: exactly one of x0, x1 is true.
        s.add_clause(vec![pos(0), pos(1)]); // at least one true
        s.add_clause(vec![neg(0), neg(1)]); // at most one true

        for _ in 0..100 {
            // x0=true, x1=true -> UNSAT (both true violates XOR)
            let r1 = s.solve_incremental_ic3(&[pos(0), pos(1)]);
            assert!(r1.is_unsat(), "expected UNSAT: both true");

            // x0=true -> SAT (x1=false forced)
            let r2 = s.solve_incremental_ic3(&[pos(0)]);
            assert!(r2.is_sat(), "expected SAT: x0=true, x1=false");

            // x0=false, x1=false -> UNSAT (both false violates "at least one")
            let r3 = s.solve_incremental_ic3(&[neg(0), neg(1)]);
            assert!(r3.is_unsat(), "expected UNSAT: both false");

            // x1=true -> SAT (x0=false forced)
            let r4 = s.solve_incremental_ic3(&[pos(1)]);
            assert!(r4.is_sat(), "expected SAT: x1=true, x0=false");
        }
    }

    /// Stress test: many IC3 solves exercising the IC3 conflict analysis path.
    #[test]
    fn ic3_conflict_analysis_stress() {
        let mut s = Solver::new(10);
        s.set_ic3_mode();

        // Build a small transition system.
        for i in 0..9u32 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);
        s.add_clause(vec![neg(9), pos(0)]);

        // Run many solves with varying assumptions.
        for iteration in 0..500 {
            let assume_var = (iteration % 10) as u32;
            let result = s.solve_incremental_ic3(&[pos(assume_var)]);
            assert!(result.is_sat(), "iteration {iteration}: expected SAT");
        }
    }

    /// IC3 conflict analysis with domain restriction, exercising the
    /// domain-aware BCP path that the IC3 analysis must handle.
    #[test]
    fn ic3_conflict_analysis_with_domain() {
        let mut s = Solver::new(8);
        s.set_ic3_mode();

        // Build formula: chain x0->x1->...->x6, plus conflict clause.
        for i in 0..6u32 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![neg(0), neg(6)]); // conflict: x0 -> ... -> x6, but !x0|!x6

        // Set domain to first 4 variables.
        s.set_domain(&[var(0), var(1), var(2), var(3)]);

        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_unsat(),
            "expected UNSAT with domain restriction: x0=true propagates to conflict"
        );

        // Without the conflicting assumption, should be SAT.
        let result2 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(result2.is_sat(), "expected SAT with x0=false");
    }
}
