// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma management: frame insertion, clause splitting, disequality generalization.
//!
//! All lemma writes to PDR frames flow through `add_lemma_to_frame_impl`.
//! - `add_lemma_to_frame`: insertion with cross-predicate propagation
//! - `add_lemma_to_frame_no_propagation`: insertion without propagation (used by propagation worklist)
//! - `add_blocking_lemma`: insertion + restart accounting + disequality generalization

use super::{
    caches, ChcExpr, ChcOp, ChcSort, ChcVar, FxHashSet, Lemma, PdrSolver, PredicateId, SmtResult,
};
use crate::pdr::lemma_sanitize::{lemma_sanitize_enabled, sanitize_lemma_opt, LEMMA_NODE_SOFT_CAP};

impl PdrSolver {
    /// Add a lemma to the frame at the specified level.
    ///
    /// Also tracks disequality lemmas (`distinct var const`) to detect enumeration patterns.
    /// Shared frame insertion path for lemma writes.
    ///
    /// Handles level consistency checks and optional cross-predicate propagation.
    fn add_lemma_to_frame_impl(
        &mut self,
        mut lemma: Lemma,
        level: usize,
        propagate_to_users: bool,
    ) {
        // INVARIANT: Frame level bounds check — soundness-critical, must not be
        // disabled in release builds (see #3095).
        assert!(
            level < self.frames.len(),
            "BUG: Adding lemma to non-existent frame level {} (only {} frames)",
            level,
            self.frames.len()
        );
        // INVARIANT: Lemma level must match where it's being added — a mismatch
        // would place the lemma in the wrong frame, producing unsound invariants.
        assert!(
            lemma.level == level,
            "BUG: Lemma level {} doesn't match target frame level {}",
            lemma.level,
            level
        );

        // Sanitize the lemma formula at admission: EXACT simplification only
        // (false ∨ X ≡ X, true ∧ X ≡ X, provably-constant linear atoms folded).
        // Counters the giant-compound-lemma pathology on the reve/llreve/
        // rust-horn family (push_lemmas SIGSEGV/SIGBUS). Kill-switch:
        // AY_PDR_LEMMA_SANITIZE=0.
        if lemma_sanitize_enabled() {
            if let Some(sanitized) = sanitize_lemma_opt(&lemma.formula) {
                let nodes_before = lemma.formula.node_count(usize::MAX);
                let nodes_after = sanitized.node_count(usize::MAX);
                tracing::debug!(
                    target: "ay_chc::pdr::lemma_sanitize",
                    nodes_before,
                    nodes_after,
                    level,
                    "PDR lemma sanitized at admission"
                );
                lemma.formula = sanitized;
                // Recompute derived data: the cached structural hash must stay
                // consistent with the rewritten formula (frame dedup keys on it).
                lemma.formula_hash = lemma.formula.structural_hash();
            }
            // Soft cap telemetry (observability only in this increment).
            let node_count = lemma.formula.node_count(LEMMA_NODE_SOFT_CAP + 1);
            if node_count > LEMMA_NODE_SOFT_CAP {
                tracing::warn!(
                    target: "ay_chc::pdr::lemma_sanitize",
                    node_count,
                    level,
                    "PDR lemma exceeds soft node cap after sanitization"
                );
            }
        }

        // #6047: Reject lemmas containing non-canonical array-sorted variables.
        // Non-canonical array variables (clause-local, MBP-introduced) that appear
        // outside of `select` context cannot participate in PDR convergence.
        // Canonical array vars are allowed — cubes now constrain them via
        // select(arr, idx) = val from the model (#6047 array cube support).
        {
            let canonical_names: FxHashSet<String> = self
                .canonical_vars(lemma.predicate)
                .map(|vars| vars.iter().map(|v| v.name.clone()).collect())
                .unwrap_or_default();
            let has_noncanonical_array_var = lemma.formula.vars().iter().any(|v| {
                matches!(v.sort, ChcSort::Array(_, _)) && !canonical_names.contains(&v.name)
            });
            if has_noncanonical_array_var {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #6047 Dropping lemma for pred {:?} — contains non-canonical \
                         array-sorted variable. Formula: {}.",
                        lemma.predicate,
                        lemma.formula
                    );
                }
                return;
            }
        }

        // #5877: Clause splitting for BV lemmas.
        //
        // When a lemma's invariant formula is AND(c1, c2, ..., cn), split into n
        // individual clause lemmas. Each clause ci is stored as a separate Lemma
        // in the frame and pushed independently during propagation.
        //
        // This matches Z3 Spacer's architecture where each lemma stores a single
        // clause (spacer_context.h:121-198, spacer_context.cpp:2091-2122).
        //
        // The Lemma.formula field stores the invariant (positive form). BV-native
        // PDR produces multi-clause conjunctions via try_simplify_bv_native_lemma
        // which returns NOT(AND(clauses)) as a blocking formula; after
        // NOT(NOT(AND(clauses))) = AND(clauses), the lemma formula is a conjunction.
        //
        // Gated on !problem_is_pure_lia to avoid impacting the well-tested LIA path.
        // LIA lemmas are typically single clauses already.
        if !self.problem_is_pure_lia {
            let conjuncts = lemma.formula.collect_conjuncts();
            if conjuncts.len() > 1 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #5877 Splitting {}-conjunct lemma for pred {:?} into \
                         individual clause lemmas at level {}",
                        conjuncts.len(),
                        lemma.predicate,
                        level,
                    );
                }
                // Add each conjunct as a separate clause lemma.
                // Dedup is handled by Frame::add_lemma's hash-based check.
                for conjunct in conjuncts {
                    let clause_lemma = Lemma::new(lemma.predicate, conjunct, level);
                    // Recurse through add_lemma_to_frame_impl so each clause
                    // gets the array-var filter, prop_solver assertion, and
                    // cross-predicate propagation. The recursion terminates because
                    // each ci is a single clause (not AND(...)).
                    self.add_lemma_to_frame_impl(clause_lemma, level, propagate_to_users);
                }
                return;
            }
        }

        // Capture predicate/formula before lemma is consumed by frame add.
        let lemma_pred = lemma.predicate;
        let lemma_formula = lemma.formula.clone();
        self.frames[level].add_lemma(lemma);

        // #6358: Assert lemma to the per-predicate prop_solver.
        // The prop_solver keeps a single persistent SAT context per predicate with
        // activation-guarded segments for all query families. Lemmas are asserted
        // once and gated by level activation literals.
        // Uses ensure_prop_solver for correct lemma backfill on lazy creation.
        if self.incremental_pdr_enabled() {
            let prop = self.ensure_prop_solver(lemma_pred);
            prop.assert_lemma_at_level(&lemma_formula, level);
        }

        // Cross-predicate propagation: translate through connecting clauses to
        // parent predicates. Matches Z3 Spacer add_lemma_core → m_use pattern.
        // Reference: z3/src/muz/spacer/spacer_context.cpp:981-983
        if propagate_to_users && level > 0 {
            self.propagate_lemma_to_users(lemma_pred, &lemma_formula, level);
        }
    }

    /// Insert a lemma into a frame and trigger cross-predicate propagation.
    ///
    /// This is the low-level insertion path. It does NOT affect restart
    /// accounting or clear fixed-point detection state. Use `add_blocking_lemma`
    /// for lemmas from POB resolution that should influence restart dynamics.
    ///
    /// # Design (#2459 Phase 1, #2439)
    ///
    /// Z3 Spacer's `add_lemma_core` is the single choke-point for all lemma
    /// insertions. It always triggers cross-predicate propagation via
    /// `m_use[i]->add_lemma_from_child`. This method is AY's equivalent.
    pub(in crate::pdr::solver) fn add_lemma_to_frame(&mut self, lemma: Lemma, level: usize) {
        self.add_lemma_to_frame_impl(lemma, level, true);
    }

    /// Insert a lemma into a frame without invoking cross-predicate propagation.
    ///
    /// Used by the propagation worklist itself to avoid nested recursive
    /// propagation calls while still routing frame writes through the same
    /// insertion choke-point (#2459 Phase 1).
    pub(in crate::pdr::solver) fn add_lemma_to_frame_no_propagation(
        &mut self,
        lemma: Lemma,
        level: usize,
    ) {
        self.add_lemma_to_frame_impl(lemma, level, false);
    }

    /// Insert a blocking lemma: frame insertion + cross-predicate propagation
    /// + restart accounting + fixed-point invalidation.
    ///
    /// Use this for lemmas from POB resolution (blocking learned lemmas).
    /// Non-blocking insertions (discovery, push, propagation) should use
    /// `add_lemma_to_frame` directly.
    ///
    /// # Design (#2459 Phase 1, #2439)
    ///
    /// Factored from the original `add_lemma` to separate restart accounting
    /// (which should only apply to blocking lemmas) from frame insertion
    /// (which all lemmas need). The disequality generalization logic lives
    /// here because it's specific to blocking lemmas.
    ///
    /// When 10+ disequalities for the same variable are accumulated, attempts to generalize
    /// to a bound lemma (e.g., `var > max(values)`) to prevent exponential constraint growth.
    /// See #1677 and the development design notes.
    pub(in crate::pdr::solver) fn add_blocking_lemma(&mut self, lemma: Lemma, level: usize) {
        // #1677: Track disequality lemmas for enumeration detection
        // A disequality lemma has form `(distinct var const)` = `ChcOp::Ne(Var(v), Int(c))`
        const DISEQ_GENERALIZATION_THRESHOLD: usize = 10;
        const DISEQ_MAX_TRACKED: usize = 50; // Stop tracking after this many to prevent unbounded growth

        if let Some((var_name, const_val)) = Self::extract_disequality(&lemma.formula) {
            // #1677: Lemma subsumption: skip value-specific disequalities that are already implied
            // by the existing frame constraint. This prevents distinct-chain blowups where we
            // keep adding redundant `distinct x N` lemmas.
            if self.frame_implies_formula(level, lemma.predicate, &lemma.formula) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping subsumed disequality lemma for {} at level {}: {}",
                        var_name,
                        level,
                        lemma.formula
                    );
                }
                return;
            }

            let key = (lemma.predicate, var_name.clone(), level);

            // Evict entire map if key count exceeds cap (#2673)
            if self.caches.diseq_values.len() >= caches::PdrCacheStore::diseq_values_cap()
                && !self.caches.diseq_values.contains_key(&key)
            {
                self.caches.diseq_values.clear();
            }

            // First pass: add the value and check if we've reached threshold
            let (should_generalize, stop_tracking) = {
                let values = self.caches.diseq_values.entry(key.clone()).or_default();
                if values.len() < DISEQ_MAX_TRACKED && !values.contains(&const_val) {
                    values.push(const_val);
                }
                (
                    values.len() >= DISEQ_GENERALIZATION_THRESHOLD,
                    values.len() >= DISEQ_MAX_TRACKED,
                )
            };

            // Second pass: attempt generalization if threshold reached
            // Only attempt at specific counts to avoid repeated failed attempts.
            // Use exponential backoff: attempt at 10, 20, 40, 50 (cap) values.
            let values_count = self.caches.diseq_values.get(&key).map_or(0, Vec::len);
            let should_attempt = values_count == DISEQ_GENERALIZATION_THRESHOLD
                || values_count == 20
                || values_count == 40
                || values_count == DISEQ_MAX_TRACKED;
            if should_generalize && should_attempt {
                // Try to generalize: if all values < some bound, use `var > max(values)`
                // Example: `distinct x 1, distinct x 3, ... distinct x 15` → lemma `x > 15`
                if let Some(generalized) =
                    self.try_generalize_disequalities(lemma.predicate, &var_name, level)
                {
                    let num_values = self.caches.diseq_values.get(&key).map_or(0, Vec::len);
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Disequality generalization for {} at level {}: {} values -> {}",
                            var_name,
                            level,
                            num_values,
                            generalized
                        );
                    }
                    // Add the generalized lemma instead of the point disequality
                    let gen_lemma = Lemma::new(lemma.predicate, generalized, level);
                    self.add_lemma_to_frame(gen_lemma, level);
                    self.pdr_trace_step("Running", Some("LearnLemma"), None);
                    tracing::info!(
                        action = "LearnLemma",
                        level,
                        frames = self.frames.len(),
                        kind = "disequality_generalization",
                        "PDR learned generalized blocking lemma"
                    );
                    // Clear the tracked values since we've generalized
                    self.caches.diseq_values.remove(&key);
                    // Blocking-specific: restart accounting + fixed-point invalidation
                    self.obligations.fixed_point_pob_seen.clear();
                    self.restart.lemmas_since_restart += 1;
                    return;
                }
            }

            // Check cap separately - must happen even when we don't attempt generalization
            if stop_tracking {
                // Generalization failed and we've hit the cap - stop tracking to prevent
                // unbounded memory growth and repeated failed generalization attempts.
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Disequality tracking capped for {} at level {}: {} values, no inductive generalization found",
                        var_name,
                        level,
                        DISEQ_MAX_TRACKED
                    );
                }
                self.caches.diseq_values.remove(&key);
            }
        }

        // Mark existing frame lemmas for this predicate as "used" — they
        // participated in the inductiveness check that proved this blocking
        // lemma. This ensures active lemmas survive GC. (#8601)
        let blocking_pred = lemma.predicate;
        if level < self.frames.len() {
            for existing in &mut self.frames[level].lemmas {
                if existing.predicate == blocking_pred {
                    existing.mark_used();
                }
            }
        }

        self.add_lemma_to_frame(lemma, level);
        self.pdr_trace_step("Running", Some("LearnLemma"), None);
        tracing::info!(
            action = "LearnLemma",
            level,
            frames = self.frames.len(),
            "PDR learned blocking lemma"
        );
        // Blocking-specific: restart accounting + fixed-point invalidation
        self.obligations.fixed_point_pob_seen.clear();
        self.restart.lemmas_since_restart += 1;
    }

    /// Legacy entry point — routes to `add_blocking_lemma`.
    ///
    /// All production callers have been migrated (#2459 Phase 1):
    /// - Blocking context: `add_blocking_lemma` (restart accounting + propagation)
    /// - Discovery context: `add_lemma_to_frame` (propagation only)
    ///
    /// Retained for test code compatibility.
    #[cfg(test)]
    pub(in crate::pdr::solver) fn add_lemma(&mut self, lemma: Lemma, level: usize) {
        self.add_blocking_lemma(lemma, level);
    }

    /// Extract a variable name and constant from a disequality lemma.
    /// Returns Some((var_name, const_val)) for `(distinct var const)` = `Ne(Var(v), Int(c))`
    fn extract_disequality(formula: &ChcExpr) -> Option<(String, i128)> {
        if let ChcExpr::Op(ChcOp::Ne, args) = formula {
            if args.len() == 2 {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) => return Some((v.name.clone(), *c)),
                    (ChcExpr::Int(c), ChcExpr::Var(v)) => return Some((v.name.clone(), *c)),
                    _ => {}
                }
            }
        }
        None
    }

    /// Try to generalize accumulated disequalities to a bound lemma.
    /// Returns Some(bound_lemma) if generalization is possible and valid.
    fn try_generalize_disequalities(
        &mut self,
        pred: PredicateId,
        var_name: &str,
        level: usize,
    ) -> Option<ChcExpr> {
        let key = (pred, var_name.to_string(), level);
        let values = self.caches.diseq_values.get(&key)?;

        if values.is_empty() {
            return None;
        }

        // Find min and max of tracked values
        let min_val = *values.iter().min()?;
        let max_val = *values.iter().max()?;

        // Get the canonical variable for this predicate
        let canonical_vars = self.canonical_vars(pred)?;
        let var = canonical_vars.iter().find(|v| v.name == var_name)?.clone();

        // Heuristic: Check if all values are positive - use `var > max` bound
        // This handles the common case of excluding specific positive values
        if min_val >= 0 {
            let candidate = ChcExpr::gt(ChcExpr::var(var.clone()), ChcExpr::int(max_val));
            // Verify the candidate lemma is inductive before using it.
            // Note: `is_*_inductive_blocking` takes a blocking formula, and checks inductiveness
            // of `NOT(blocking)`. Our candidate is already a lemma, so pass `NOT(candidate)`.
            let blocking = ChcExpr::not(candidate.clone());
            if self.is_self_inductive_blocking(&blocking, pred)
                || self.is_inductive_blocking(&blocking, pred, level)
            {
                return Some(candidate);
            }
        }

        // Heuristic: Check if all values are negative - use `var < min` bound
        if max_val <= 0 {
            let candidate = ChcExpr::lt(ChcExpr::var(var.clone()), ChcExpr::int(min_val));
            let blocking = ChcExpr::not(candidate.clone());
            if self.is_self_inductive_blocking(&blocking, pred)
                || self.is_inductive_blocking(&blocking, pred, level)
            {
                return Some(candidate);
            }
        }

        // Heuristic: Try both bounds (var < min OR var > max) for mixed values
        // This handles cases where values span both sides of zero
        let lower_bound = ChcExpr::lt(ChcExpr::var(var.clone()), ChcExpr::int(min_val));
        let upper_bound = ChcExpr::gt(ChcExpr::var(var), ChcExpr::int(max_val));
        let candidate = ChcExpr::or(lower_bound, upper_bound);
        let blocking = ChcExpr::not(candidate.clone());
        if self.is_self_inductive_blocking(&blocking, pred)
            || self.is_inductive_blocking(&blocking, pred, level)
        {
            return Some(candidate);
        }

        None
    }

    /// Check if the current frame constraint at `level` implies `formula`.
    ///
    /// Used as a subsumption filter for value-specific disequality lemmas to prevent
    /// frame constraint explosion on enumeration-heavy benchmarks (#1677).
    fn frame_implies_formula(
        &mut self,
        level: usize,
        pred: PredicateId,
        formula: &ChcExpr,
    ) -> bool {
        let Some(frame_constraint) = self.cumulative_frame_constraint(level, pred) else {
            return false;
        };

        // Check: frame ∧ ¬formula is UNSAT means frame implies formula
        let query = self.bound_int_vars(ChcExpr::and(
            frame_constraint,
            ChcExpr::not(formula.clone()),
        ));

        // #7984: Use persistent executor backend for integer arithmetic.
        match self.check_sat_via_executor_backend(&query) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => true,
            SmtResult::Sat(_) => false,
            SmtResult::Unknown => {
                // #6047: Removed array fallback. Executor adapter handles
                // array queries natively. Unknown means we can't prove
                // frame implies formula.
                false
            }
        }
    }

    /// Filter a formula to only keep conjuncts that reference canonical vars
    pub(in crate::pdr::solver) fn filter_to_canonical_vars(
        &self,
        formula: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> ChcExpr {
        super::filter_to_canonical_vars(formula, canonical_vars)
    }

    pub(in crate::pdr) fn bound_int_vars(&self, query: ChcExpr) -> ChcExpr {
        // NOTE: Model-biasing heuristics can be added here, but should not change
        // satisfiability or risk non-termination in the SMT backend.
        query
    }
}
