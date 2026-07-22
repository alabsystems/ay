// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) solving loop for IncrementalPdrContext (#6358).
//!
//! SAT from the SAT solver triggers a LIA theory check. If the theory confirms
//! SAT, a model is extracted and returned. If the theory finds a conflict, a
//! theory lemma (blocking clause) is added to the SAT solver and the DPLL(T)
//! loop re-solves.

use super::theory::TheoryLoopResult;
use super::{take_tseitin, IncrementalPdrContext};
use crate::smt::context::SmtContext;
use crate::smt::incremental::IncrementalCheckResult;
use crate::smt::types::SmtValue;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{TermId, TermStore};
use std::collections::BTreeMap;

/// Maximum DPLL(T) iterations (theory conflict + re-solve cycles).
const MAX_DPLL_T_ITERATIONS: usize = 1_000_000;

impl IncrementalPdrContext {
    /// Check satisfiability at a given frame level with DPLL(T) theory integration.
    ///
    /// Activates lemmas at levels >= `level` by assuming `NOT act_k` for k >= level.
    /// The `assumptions` are per-query expressions (proof obligations).
    ///
    /// Returns:
    /// - `Unsat` if the SAT solver proves UNSAT (definitely blocked).
    /// - `Sat(model)` if SAT and theory-consistent.
    /// - `Unknown` if theory check is inconclusive or times out.
    ///
    /// Convenience wrapper used by tests. Production code uses
    /// `check_sat_at_level_with_activations()` via `PredicatePropSolver`.
    #[cfg(test)]
    pub(crate) fn check_sat_at_level(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        self.check_sat_at_level_seeded(level, assumptions, timeout, None)
    }

    /// Seeded variant: install `phase_seed_model` on the owned `SmtContext` for the
    /// duration of the query so that theory split handlers can bias SAT variable
    /// phases toward the predecessor model.
    ///
    /// Convenience wrapper used by tests. Production code uses
    /// `check_sat_at_level_with_activations()` via `PredicatePropSolver`.
    #[cfg(test)]
    pub(crate) fn check_sat_at_level_seeded(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        timeout: Option<std::time::Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        self.check_sat_at_level_with_activations(
            level,
            assumptions,
            &[],
            &[],
            timeout,
            phase_seed_model,
        )
    }

    /// Full query entrypoint with query-family activation control.
    ///
    /// In addition to level activation (frame lemma scoping) and per-query
    /// assumptions (proof obligations), this method accepts:
    ///
    /// - `active_query_acts`: query activation variables whose guarded segments
    ///   should be active (assumed as `NOT act_var`).
    /// - `inactive_query_acts`: query activation variables whose guarded segments
    ///   should be inactive (assumed as `act_var`).
    ///
    /// This is the Spacer `prop_solver` pattern generalized: one persistent solver
    /// per predicate selects which clause/fact/init background segments are relevant
    /// to each query via activation assumptions, without allocating separate solver
    /// instances per query family.
    pub(crate) fn check_sat_at_level_with_activations(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        active_query_acts: &[u32],
        inactive_query_acts: &[u32],
        timeout: Option<std::time::Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        // Install seed model on own_smt for the duration of the query.
        let prev_seed = self.own_smt.phase_seed_model.take();
        self.own_smt.phase_seed_model = phase_seed_model.cloned();
        let result = self.check_sat_at_level_inner_with_activations(
            level,
            assumptions,
            active_query_acts,
            inactive_query_acts,
            timeout,
        );
        self.own_smt.phase_seed_model = prev_seed;
        result
    }

    /// Inner implementation with query-family activation control.
    ///
    /// `active_query_acts` are assumed as `NOT act_var` (segment active).
    /// `inactive_query_acts` are assumed as `act_var` (segment deactivated).
    fn check_sat_at_level_inner_with_activations(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        active_query_acts: &[u32],
        inactive_query_acts: &[u32],
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        if !self.finalized || self.background_conversion_budget_exceeded {
            return IncrementalCheckResult::Unknown;
        }

        let start = ay_core::time::Instant::now();
        self.own_smt.reset_conversion_budget();

        // Fast path: detect contradictory assumptions via equality propagation.
        let assumption_refs: Vec<&ChcExpr> = assumptions.iter().collect();
        let mut propagated_equalities: FxHashMap<String, i128> = FxHashMap::default();
        let contradiction = SmtContext::collect_int_equalities_with_closure(
            &assumption_refs,
            &mut propagated_equalities,
        );
        if contradiction {
            return IncrementalCheckResult::Unsat;
        }
        // #5877: Collect BV var=const equalities for BV-native PDR mode.
        let mut propagated_bv_equalities: FxHashMap<String, (u128, u32)> = FxHashMap::default();

        // Convert assumption expressions to TermIds (using own_smt).
        // #6358: Use static namespace strings for the common case (0-3 assumptions)
        // to avoid format! allocation per query.
        static NAMESPACES: [&str; 4] = ["q0", "q1", "q2", "q3"];
        let mut assumption_terms = Vec::with_capacity(assumptions.len());
        let mut namespace_buf = String::new();
        for (idx, a) in assumptions.iter().enumerate() {
            let namespace: &str = if idx < NAMESPACES.len() {
                NAMESPACES[idx]
            } else {
                namespace_buf.clear();
                use std::fmt::Write;
                let _ = write!(namespace_buf, "q{idx}");
                &namespace_buf
            };
            let normalized = SmtContext::preprocess_incremental_assumption(a, namespace);
            SmtContext::collect_int_var_const_equalities(&normalized, &mut propagated_equalities);
            SmtContext::collect_bv_var_const_equalities(&normalized, &mut propagated_bv_equalities);

            match normalized {
                ChcExpr::Bool(true) => continue,
                ChcExpr::Bool(false) => return IncrementalCheckResult::Unsat,
                _ => assumption_terms.push(self.own_smt.convert_expr(&normalized)),
            }
        }

        if self.own_smt.conversion_budget_exceeded() {
            return IncrementalCheckResult::Unknown;
        }

        // Encode assumption terms via Tseitin.
        if self.tseitin_state.is_none() {
            return IncrementalCheckResult::Unknown;
        }
        let mut tseitin = take_tseitin(&mut self.tseitin_state, &self.own_smt.terms, self.num_vars);

        let extra_activation_count = active_query_acts.len() + inactive_query_acts.len();
        let mut sat_assumptions: Vec<ay_sat::Literal> = Vec::with_capacity(
            assumption_terms.len() + self.level_act_vars.len() + extra_activation_count,
        );

        for &term in &assumption_terms {
            let encoded = tseitin.encode_assertion(term);
            self.sat.ensure_num_vars(tseitin.num_vars() as usize);
            for clause in &encoded.def_clauses {
                let lits: Vec<ay_sat::Literal> = clause
                    .0
                    .iter()
                    .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                    .collect();
                self.sat.add_clause_global(lits);
            }
            sat_assumptions.push(ay_sat::Literal::from_dimacs(encoded.root_lit));
        }

        // Save Tseitin state (term_to_var/var_to_term are read from self.tseitin_state
        // inside the DPLL(T) loop so that theory-generated split atoms are visible).
        self.num_vars = tseitin.num_vars();
        self.tseitin_state = Some(tseitin.into_state());

        // Build level activation assumptions.
        self.ensure_level(level);
        for (k, &act_var) in self.level_act_vars.iter().enumerate() {
            let sat_var = ay_sat::Variable::new(act_var - 1);
            if k >= level {
                sat_assumptions.push(ay_sat::Literal::negative(sat_var));
            } else {
                sat_assumptions.push(ay_sat::Literal::positive(sat_var));
            }
        }

        // Build query-family activation assumptions (#6358).
        // Active segments: assume NOT act_var (the guarded clause is satisfied).
        for &act_var in active_query_acts {
            let sat_var = ay_sat::Variable::new(act_var - 1);
            sat_assumptions.push(ay_sat::Literal::negative(sat_var));
        }
        // Inactive segments: assume act_var (the guarded clause is trivially true).
        for &act_var in inactive_query_acts {
            let sat_var = ay_sat::Variable::new(act_var - 1);
            sat_assumptions.push(ay_sat::Literal::positive(sat_var));
        }

        // DPLL(T) loop: SAT check → theory check → conflict clause → re-solve.
        self.run_dpll_t_loop(
            &sat_assumptions,
            &propagated_equalities,
            &propagated_bv_equalities,
            assumptions,
            timeout,
            start,
        )
    }

    /// Core DPLL(T) loop: SAT → theory check → conflict → re-solve.
    ///
    /// The term_to_var/var_to_term maps are read fresh from `self.tseitin_state`
    /// on each iteration so that theory-generated split atoms (from
    /// `get_or_alloc_theory_var`) are visible to subsequent theory checks.
    fn run_dpll_t_loop(
        &mut self,
        sat_assumptions: &[ay_sat::Literal],
        propagated_equalities: &FxHashMap<String, i128>,
        propagated_bv_equalities: &FxHashMap<String, (u128, u32)>,
        assumptions: &[ChcExpr],
        timeout: Option<std::time::Duration>,
        start: ay_core::time::Instant,
    ) -> IncrementalCheckResult {
        let mut split_count: usize = 0;

        loop {
            if let Some(t) = timeout {
                if start.elapsed() >= t {
                    return IncrementalCheckResult::Unknown;
                }
            }
            if TermStore::global_memory_exceeded() {
                return IncrementalCheckResult::Unknown;
            }

            let should_stop = || {
                timeout.is_some_and(|t| start.elapsed() >= t) || TermStore::global_memory_exceeded()
            };
            let sat_result = self
                .sat
                .solve_with_assumptions_interruptible(sat_assumptions, should_stop);

            match sat_result.result() {
                ay_sat::AssumeResult::Unsat(_core, _) => {
                    return IncrementalCheckResult::Unsat;
                }
                ay_sat::AssumeResult::Sat(model) => {
                    // Read live term↔var maps from Tseitin state so that atoms
                    // allocated by theory splits in prior iterations are visible.
                    let (term_to_var, var_to_term) = self.snapshot_var_maps();

                    let theory_result = self.check_theory_and_extract_model(
                        model,
                        &term_to_var,
                        &var_to_term,
                        propagated_equalities,
                        propagated_bv_equalities,
                        assumptions,
                        timeout.map(|t| {
                            t.checked_sub(start.elapsed())
                                .unwrap_or(std::time::Duration::from_millis(1))
                        }),
                    );

                    match theory_result {
                        TheoryLoopResult::Sat(values) => {
                            return IncrementalCheckResult::Sat(values);
                        }
                        TheoryLoopResult::Unsat => {
                            return IncrementalCheckResult::Unsat;
                        }
                        TheoryLoopResult::ConflictAdded => {
                            split_count += 1;
                            if split_count > MAX_DPLL_T_ITERATIONS {
                                return IncrementalCheckResult::Unknown;
                            }
                            continue;
                        }
                        TheoryLoopResult::Unknown => {
                            return IncrementalCheckResult::Unknown;
                        }
                    }
                }
                ay_sat::AssumeResult::Unknown => return IncrementalCheckResult::Unknown,
                #[allow(unreachable_patterns)]
                _ => return IncrementalCheckResult::Unknown,
            }
        }
    }

    /// Build fresh term↔var snapshots from the current Tseitin state.
    ///
    /// Called inside the DPLL(T) loop (not before it) so that atoms allocated
    /// by `get_or_alloc_theory_var` during previous theory conflict iterations
    /// are included in the maps.
    fn snapshot_var_maps(&self) -> (BTreeMap<TermId, u32>, BTreeMap<u32, TermId>) {
        if let Some(state) = &self.tseitin_state {
            (state.term_to_var.clone(), state.var_to_term.clone())
        } else {
            (BTreeMap::new(), BTreeMap::new())
        }
    }
}
