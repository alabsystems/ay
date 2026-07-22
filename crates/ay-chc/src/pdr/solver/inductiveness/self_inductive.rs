// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Self-inductiveness checks for PDR blocking lemmas.
//!
//! Contains `is_self_inductive_blocking` (cached) and its uncached
//! implementation. Self-inductiveness verifies that a lemma L is preserved
//! by ALL transitions starting from ANY L-satisfying state, not just from init.

use super::super::PdrSolver;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Whether any clause defining `predicate` is a self-loop (the predicate
    /// appears in its own body).
    ///
    /// When this is false, `is_self_inductive_blocking_uncached` rejects every
    /// lemma vacuously (#8578 anti-vacuous guard: no self-loop clause was
    /// checked). Callers that can prove preservation via the incoming edges
    /// instead (`is_entry_inductive`, relative induction) use this to
    /// distinguish "no self-loop to check" from "self-loop preservation
    /// genuinely fails".
    pub(in crate::pdr::solver) fn predicate_has_self_loop_clause(
        &self,
        predicate: PredicateId,
    ) -> bool {
        self.problem.clauses_defining(predicate).any(|clause| {
            clause
                .body
                .predicates
                .iter()
                .any(|(body_pred, _)| *body_pred == predicate)
        })
    }

    /// Check if a blocking formula is "self-inductive" - meaning the lemma NOT(blocking)
    /// is inductive relative to itself: L /\ T => L'.
    ///
    /// This is stricter than is_inductive_blocking at level 1, which only checks:
    /// init /\ T => L'
    ///
    /// For counter variables, init might have x=0, and one transition gives x=1,
    /// both satisfying L: x<6. But L /\ T can reach x=7 after 7 steps.
    ///
    /// This check verifies that starting from ANY state satisfying L (not just init),
    /// transitions preserve L. This catches blocking lemmas that are 1-inductive
    /// but not truly inductive (not k-inductive for all k).
    ///
    /// BUG FIX for #685: Blocking lemmas were only checked at level 1, allowing
    /// unsound lemmas like (pc=0 AND x=6) to block reachable states.
    pub(in crate::pdr::solver) fn is_self_inductive_blocking(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
    ) -> bool {
        let cache_key = (predicate, blocking_formula.structural_hash());
        let current_frame1_revision = self
            .frames
            .get(1)
            .map_or(0, |f| f.predicate_lemma_revision(predicate));

        if let Some((cached_expr, cached_frame1_revision, cached_result)) =
            self.caches.self_inductive_cache.get(&cache_key)
        {
            // Collision safety (#2860): verify expression matches before using cached result.
            if cached_expr == blocking_formula && *cached_frame1_revision == current_frame1_revision
            {
                return *cached_result;
            }
        }

        let result = self.is_self_inductive_blocking_uncached(blocking_formula, predicate);

        // Store with expression for collision detection (#2860)
        self.insert_self_inductive_cache_entry(
            cache_key,
            (blocking_formula.clone(), current_frame1_revision, result),
        );
        result
    }

    /// P0 (model-checker-consumer wishlist 2026-07-17 item 2.3): whether this blocking
    /// formula's self-inductiveness was ever accepted via the forward-sample
    /// fallback (heuristic, unsound-by-construction on nonlinear queries).
    /// Tainted lemmas must never contribute to `individually_inductive` /
    /// whole-model verification skips. Conservative: the taint persists even
    /// if a later re-check proves the same formula by real SMT — that only
    /// forces full verification, never a wrong skip.
    pub(in crate::pdr::solver) fn lemma_sample_tainted(
        &self,
        predicate: PredicateId,
        blocking_formula: &ChcExpr,
    ) -> bool {
        self.caches
            .sample_accepted_taint
            .contains(&(predicate, blocking_formula.structural_hash()))
    }

    /// Uncached implementation of is_self_inductive_blocking.
    ///
    /// Used directly in apply_lemma_hints to avoid caching Unknown results from
    /// timeout-driven SMT calls (issue #2255). Hints are optional, so treating a
    /// timeout as Unknown and rejecting is sound, but we must not cache this as a
    /// definitive "not self-inductive" result.
    pub(in crate::pdr::solver) fn is_self_inductive_blocking_uncached(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
    ) -> bool {
        let lemma = ChcExpr::not(blocking_formula.clone());

        // Check: lemma /\ T /\ blocking_on_head is UNSAT
        // This verifies: for all states s satisfying L, T(s, s') => L(s')
        let mut result = true;
        // #8578: Track whether any self-loop clause was actually checked.
        // Predicates with no self-loops (acyclic CFG nodes) pass vacuously,
        // which is unsound for the `individually_inductive` flag.
        let mut checked_any_self_loop = false;

        // Collect clauses first to end the immutable borrow before calling check_parts
        // which needs &mut self. Includes clause index for incremental context keying.
        let clauses: Vec<_> = self
            .problem
            .clauses_defining_with_index(predicate)
            .map(|(i, c)| (i, c.clone()))
            .collect();
        for (clause_index, clause) in &clauses {
            // #2887: Check cancellation between SMT queries in clause loop.
            if self.is_cancelled() {
                return false;
            }
            if clause.body.predicates.is_empty() {
                // Fact clause - init check is done separately
                continue;
            }

            // For hyperedges: only relevant if any body predicate is a self-loop.
            // If no body predicate equals the head predicate, this clause doesn't
            // contribute to self-inductiveness (it's an incoming edge, not a self-loop).
            if clause.body.predicates.len() > 1 {
                let has_self_loop = clause
                    .body
                    .predicates
                    .iter()
                    .any(|(bp, _)| *bp == predicate);
                if !has_self_loop {
                    // No self-loop in this hyperedge - skip it
                    continue;
                }
                checked_any_self_loop = true;
                // #1852 Phase 0: Try UNSAT-sufficient check for hyperedge self-loops
                // For is_self_inductive_blocking, we check not(blocking_formula) is preserved
                if let Some(hyperedge_query) =
                    self.build_hyperedge_inductive_query(clause, predicate, &lemma)
                {
                    match self.check_hyperedge_inductive_query(
                        predicate,
                        *clause_index,
                        &hyperedge_query,
                    ) {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // UNSAT means self-inductive even with weak assumptions - continue
                            continue;
                        }
                        SmtResult::Sat(_) => {
                            if hyperedge_query.missing_product_state {
                                // SAT but we dropped constraints - inconclusive, be conservative
                                if self.config.verbose {
                                    safe_eprintln!("PDR: is_self_inductive_blocking hyperedge SAT but missing product-state");
                                }
                                result = false;
                                break;
                            }
                            // SAT with no missing constraints - truly not self-inductive
                            result = false;
                            break;
                        }
                        SmtResult::Unknown => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_self_inductive_blocking hyperedge check unknown"
                                );
                            }
                            result = false;
                            break;
                        }
                    }
                } else {
                    // Couldn't build query - be conservative
                    if self.config.verbose {
                        safe_eprintln!("PDR: is_self_inductive_blocking being conservative for hyperedge with self-loop");
                    }
                    result = false;
                    break;
                }
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // blocking_on_head = blocking_formula applied to head (post-state)
            let blocking_on_head = match self.apply_to_args(predicate, blocking_formula, head_args)
            {
                Some(e) => e,
                None => {
                    result = false;
                    break;
                }
            };

            // lemma_on_body = lemma applied to body (pre-state)
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Self-loop only - for transitions from other predicates, skip
                continue;
            }
            checked_any_self_loop = true;
            let lemma_on_body = match self.apply_to_args(predicate, &lemma, body_args) {
                Some(e) => e,
                None => {
                    result = false;
                    break;
                }
            };

            // Query: lemma_on_body /\ clause_constraint /\ blocking_on_head
            // If SAT, then there's a transition from a lemma-satisfying state to a blocked state
            // => lemma is NOT self-inductive
            fn check_parts(solver: &mut PdrSolver, query_parts: Vec<ChcExpr>) -> Option<bool> {
                let query = solver.bound_int_vars(ChcExpr::and_all(query_parts));

                // #8660 Phase 2b: ROW-expand `select(store(...))` (incl. symbolic
                // ITE form) before simplification so self-inductiveness queries
                // reduce to LIA+ITE. Mirrors the expansion applied in
                // inductiveness/insertion/retry.rs Phase 2.
                let row_expanded = query.expand_select_store_symbolic();
                // Fix #967: Use equality propagation + ITE case-split fallback like other PDR queries.
                // This avoids spurious Unknown results on ITE-heavy transitions (e.g., mode dispatch).
                let simplified = row_expanded.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    return Some(false);
                }

                let (smt_result, _) = PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &simplified,
                );
                match smt_result {
                    SmtResult::Sat(_) => Some(true),
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // Cross-check UNSAT results to catch false negatives from
                        // the internal solver. This is especially important for
                        // array formulas (#8675) where the internal DPLL(T) or
                        // executor may return incorrect UNSAT results.
                        // P0 (model-checker-consumer wishlist item 2): also cross-check BV
                        // problems — the internal BV theory path has produced
                        // wrong verdicts (wishlist item 1), and self-inductive
                        // lemmas feed model admission. Executor SAT overturns
                        // the UNSAT; executor Unknown keeps it (non-strict
                        // results never justify verification skips on BV —
                        // the strict check in strict_self.rs additionally
                        // REQUIRES executor confirmation there).
                        let needs_cross_check = solver.problem_is_integer_arithmetic
                            || simplified.contains_array_ops()
                            || solver.problem.has_bv_sorts();
                        if needs_cross_check {
                            let propagated = FxHashMap::default();
                            let cross_timeout = std::time::Duration::from_millis(500);
                            let cross_result = solver.smt.check_sat_via_executor(
                                &simplified,
                                &propagated,
                                cross_timeout,
                            );
                            if matches!(cross_result, SmtResult::Sat(_)) {
                                if solver.config.verbose {
                                    safe_eprintln!(
                                        "PDR: is_self_inductive_blocking false-UNSAT cross-check hit executor SAT"
                                    );
                                }
                                return Some(true);
                            }
                        }
                        Some(false)
                    }
                    SmtResult::Unknown => {
                        // #3121: When the query contains mod/div, the LIA solver may
                        // return Unknown. Try eliminating mod operations (converting to
                        // pure LIA with auxiliary quotient/remainder variables) and retry.
                        // This matches the pattern used in verify_model (verification.rs).
                        if simplified.contains_mod_or_div() {
                            let mod_free = simplified.eliminate_mod();
                            solver.smt.reset();
                            let mod_retry_timeout = std::time::Duration::from_secs(2);
                            let retry_result = solver
                                .smt
                                .check_sat_with_timeout(&mod_free, mod_retry_timeout);
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_self_inductive_blocking mod-elimination retry: {:?}",
                                    match &retry_result {
                                        SmtResult::Sat(_) => "SAT",
                                        SmtResult::Unsat
                                        | SmtResult::UnsatWithCore(_)
                                        | SmtResult::UnsatWithFarkas(_) => "UNSAT",
                                        SmtResult::Unknown => "Unknown",
                                    }
                                );
                            }
                            match retry_result {
                                SmtResult::Sat(_) => return Some(true),
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => return Some(false),
                                SmtResult::Unknown => {}
                            }
                        }
                        None
                    }
                }
            }

            // #6358: Per-predicate prop_solver for self-inductiveness.
            // Pure-LIA: one solve via prop_solver, no double-solve fallback.
            let mut sat = if self.incremental_pdr_enabled() {
                let seg_key = super::super::prop_solver::SegmentKey::Inductiveness {
                    clause_index: *clause_index,
                };
                let prop = super::super::core::ensure_prop_solver_split(
                    &mut self.prop_solvers,
                    &self.frames,
                    predicate,
                );
                prop.register_segment(seg_key, &clause_constraint);
                let check_timeout = self
                    .smt
                    .current_timeout()
                    .or(Some(std::time::Duration::from_secs(2)));
                let assumptions = [lemma_on_body.clone(), blocking_on_head.clone()];
                let incr_result = prop.check_inductiveness(
                    self.frames.len(),
                    *clause_index,
                    &assumptions,
                    check_timeout,
                    None,
                );

                match incr_result {
                    crate::smt::IncrementalCheckResult::Unsat => {
                        continue;
                    }
                    // Pure-LIA: SAT is trusted (no ITE/mod/div).
                    crate::smt::IncrementalCheckResult::Sat(_) => true,
                    crate::smt::IncrementalCheckResult::Unknown => {
                        // Unknown: fall through to non-incremental check_parts.
                        let base_parts = vec![
                            lemma_on_body.clone(),
                            clause_constraint.clone(),
                            blocking_on_head.clone(),
                        ];
                        match check_parts(self, base_parts) {
                            Some(true) => true,
                            Some(false) => false,
                            None => {
                                // When SMT returns Unknown due to nonlinear multiplication,
                                // fall back to forward simulation.
                                if clause_constraint.contains_nonlinear_mul()
                                    || blocking_on_head.contains_nonlinear_mul()
                                    || lemma_on_body.contains_nonlinear_mul()
                                {
                                    let init_samples = self.sample_init_models(predicate, 5);
                                    let forward = self.simulate_forward_samples_from_init_samples(
                                        predicate,
                                        &init_samples,
                                        20,
                                    );
                                    let all_samples: Vec<_> =
                                        init_samples.iter().chain(forward.iter()).collect();
                                    let all_satisfy = all_samples.len() >= 5
                                        && all_samples.iter().all(|model| {
                                            let smt_model: FxHashMap<String, SmtValue> = model
                                                .iter()
                                                .map(|(k, v)| (k.clone(), SmtValue::Int(*v)))
                                                .collect();
                                            matches!(
                                                crate::expr::evaluate_expr(&lemma, &smt_model),
                                                Some(SmtValue::Bool(true))
                                            )
                                        });
                                    if all_satisfy {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                            "PDR: is_self_inductive_blocking UNKNOWN (nonlinear) but {}/{} forward samples satisfy lemma {} — accepting",
                                            all_samples.len(),
                                            all_samples.len(),
                                            lemma
                                        );
                                        }
                                        // P0 taint (wishlist item 2.3): sample-based
                                        // acceptance is heuristic evidence, not proof.
                                        // Mark it so this lemma can never grant the
                                        // `individually_inductive` verification skip.
                                        self.caches.sample_accepted_taint.insert((
                                            predicate,
                                            blocking_formula.structural_hash(),
                                        ));
                                        false // treat as UNSAT (inductive)
                                    } else {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: is_self_inductive_blocking UNKNOWN: lemma {}",
                                                lemma
                                            );
                                        }
                                        result = false;
                                        break;
                                    }
                                } else {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: is_self_inductive_blocking UNKNOWN: lemma {}",
                                            lemma
                                        );
                                    }
                                    result = false;
                                    break;
                                }
                            }
                        }
                    }
                }
            } else {
                // Non-incremental path (incremental_pdr_enabled()=false).
                let base_parts = vec![
                    lemma_on_body.clone(),
                    clause_constraint.clone(),
                    blocking_on_head.clone(),
                ];
                match check_parts(self, base_parts) {
                    Some(true) => true,
                    Some(false) => false,
                    None => {
                        if clause_constraint.contains_nonlinear_mul()
                            || blocking_on_head.contains_nonlinear_mul()
                            || lemma_on_body.contains_nonlinear_mul()
                        {
                            let init_samples = self.sample_init_models(predicate, 5);
                            let forward = self.simulate_forward_samples_from_init_samples(
                                predicate,
                                &init_samples,
                                20,
                            );
                            let all_samples: Vec<_> =
                                init_samples.iter().chain(forward.iter()).collect();
                            let all_satisfy = all_samples.len() >= 5
                                && all_samples.iter().all(|model| {
                                    let smt_model: FxHashMap<String, SmtValue> = model
                                        .iter()
                                        .map(|(k, v)| (k.clone(), SmtValue::Int(*v)))
                                        .collect();
                                    matches!(
                                        crate::expr::evaluate_expr(&lemma, &smt_model),
                                        Some(SmtValue::Bool(true))
                                    )
                                });
                            if all_satisfy {
                                // P0 taint (wishlist item 2.3): sample-based
                                // acceptance is heuristic evidence, not proof.
                                // Mark it so this lemma can never grant the
                                // `individually_inductive` verification skip.
                                self.caches
                                    .sample_accepted_taint
                                    .insert((predicate, blocking_formula.structural_hash()));
                                false // treat as UNSAT (inductive)
                            } else {
                                result = false;
                                break;
                            }
                        } else {
                            result = false;
                            break;
                        }
                    }
                }
            };

            if sat && self.frames.len() > 1 {
                let mut strengthened_parts = vec![lemma_on_body, clause_constraint.clone()];
                for frame_lemma in &self.frames[1].lemmas {
                    if frame_lemma.predicate == predicate {
                        if let Some(applied) =
                            self.apply_to_args(predicate, &frame_lemma.formula, body_args)
                        {
                            strengthened_parts.push(applied);
                        }
                    }
                }
                strengthened_parts.push(blocking_on_head);

                match check_parts(self, strengthened_parts) {
                    Some(true) => {
                        sat = true;
                    }
                    Some(false) => {
                        sat = false;
                    }
                    None => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: is_self_inductive_blocking UNKNOWN (strengthened): lemma {}",
                                lemma
                            );
                        }
                        result = false;
                        break;
                    }
                }
            }

            if sat {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: is_self_inductive_blocking FAILED: lemma {} not self-inductive",
                        lemma
                    );
                }
                result = false;
                break;
            }
        }

        // #8578: Vacuous truth is not sufficient. If no self-loop clause
        // was actually checked, this predicate's lemma has not been proven
        // self-inductive — it just has no self-transitions to violate.
        result && checked_any_self_loop
    }
}
