// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR strengthen loop: process proof obligations to block bad states.
//!
//! Extracted from `solve.rs` for file size management. The `strengthen()` method
//! is the core obligation-processing loop called from the main PDR solve loop.

use super::{
    cube, BlockResult, ChcExpr, ChcOp, ChcSort, FxHashMap, FxHashSet, HornClause, Lemma, PdrSolver,
    PredicateId, ProofObligation, ReachFact, ReachFactId, StrengthenResult,
};

impl PdrSolver {
    /// Strengthen the current frame by blocking bad states
    pub(in crate::pdr::solver) fn strengthen(&mut self) -> StrengthenResult {
        // Precondition: current level is valid (#4757).
        debug_assert!(
            self.frames.len() >= 2,
            "BUG: strengthen requires at least 2 frames, got {}",
            self.frames.len()
        );

        // Reset per-strengthen overflow tracking (#2983).
        self.obligations.overflowed = false;

        let current_level = self.frames.len() - 1;
        self.tracing.query_level = Some(current_level);

        // #6366: Use structural_hash for POB dedup instead of full ChcExpr clone.
        // This avoids O(expr_size) allocation per enqueue. Hash collisions are benign
        // (duplicate POBs dropped → completeness, not soundness).
        let mut enqueued: FxHashSet<(PredicateId, usize, u64)> = FxHashSet::default();
        let key = |p: &ProofObligation| (p.predicate, p.level, p.state.structural_hash());

        // #1293: Check if a POB is query-derived (created from query or has a query-derived ancestor).
        // Fixed-point verification creates POBs that are NOT query-derived. If such a POB reaches
        // init, that's NOT a valid UNSAFE witness - it just means the state is reachable.
        let is_query_derived = |p: &ProofObligation| {
            if p.query_clause.is_some() {
                return true;
            }
            let mut cur = p.parent.as_deref();
            while let Some(parent) = cur {
                if parent.query_clause.is_some() {
                    return true;
                }
                cur = parent.parent.as_deref();
            }
            false
        };

        // Track level-0 states that have been checked and found not to be init.
        // These are blocked locally but not added to frames (so we can find
        // longer predecessor chains).
        let mut blocked_at_level_0: Vec<(PredicateId, ChcExpr)> = Vec::new();

        // #1293/#1326: Track non-query POBs that reached init. These are reachable states but NOT
        // valid CEX witnesses. Don't re-enqueue them to prevent infinite loops.
        // Key: (predicate, level, state) - must be level-aware to avoid cross-level
        // contamination. When a non-query POB reaches init, we mark the entire parent chain.
        // Uses full ChcExpr instead of hash for collision safety (#6158).
        let mut non_query_reached_init: FxHashSet<(PredicateId, usize, ChcExpr)> =
            FxHashSet::default();

        // Track (parent_level, predecessor_predicate, predecessor_state) triples that led to Unknown results.
        // When a parent re-discovers the same predecessor, we need to find a different one.
        let mut unknown_predecessors: Vec<(usize, PredicateId, ChcExpr)> = Vec::new();

        // Track point-blocking lemmas at each level to detect degeneration into enumeration.
        // When too many point blocks are added at any level, the algorithm is likely
        // enumerating individual states rather than finding general lemmas.
        // Key: level, Value: count of point-blocking lemmas added at that level
        // See #759: MBP soundness fix causes PDR to produce more point cubes
        let mut point_blocks_per_level: FxHashMap<usize, usize> = FxHashMap::default();
        const MAX_POINT_BLOCKS_PER_LEVEL: usize = 25;

        // Clone queries (with clause indices) to avoid borrow issues with self
        let queries: Vec<(usize, HornClause)> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_query())
            .map(|(i, c)| (i, c.clone()))
            .collect();

        for (query_clause_index, query) in &queries {
            // #1518: Handle hyperedge queries via must-summary intersection
            // This handles both:
            // 1. Direct hyperedge queries (multiple body predicates)
            // 2. Indirect hyperedge queries (single body predicate defined by hyperedge clause)
            if let Some(cex) = self.check_hyperedge_unsafe(query, *query_clause_index) {
                return StrengthenResult::Unsafe(cex);
            }

            // Skip direct hyperedge queries - can only be handled via must-summary intersection above
            if query.body.predicates.len() != 1 {
                continue;
            }

            let (pred_id, args) = &query.body.predicates[0];
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let bad_state = match self.constraint_to_canonical_state(*pred_id, args, &constraint) {
                Some(s) => s,
                None => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Failed to convert query constraint to canonical state"
                        );
                    }
                    self.pdr_trace_conservative_fail(
                        "strengthen_query_to_canonical_state_failed",
                        serde_json::json!({
                            "query_clause_index": query_clause_index,
                            "predicate": pred_id.index(),
                        }),
                        None,
                    );
                    return StrengthenResult::Unknown;
                }
            };
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Create obligation for bad state {} at level {}",
                    bad_state,
                    current_level
                );
            }
            let pob = ProofObligation::new(*pred_id, bad_state, current_level)
                .with_query_clause(*query_clause_index);
            if enqueued.insert(key(&pob)) {
                self.push_obligation(pob);
            }
        }

        // Process proof obligations
        let mut processed = 0usize;
        while let Some(pob) = self.pop_obligation() {
            enqueued.remove(&key(&pob));
            processed += 1;

            // Check cancellation or memory budget (#2769)
            if self.is_cancelled() {
                if self.config.verbose {
                    safe_eprintln!("PDR: Cancelled during strengthen()");
                }
                self.pdr_trace_conservative_fail(
                    "strengthen_cancelled",
                    serde_json::json!({
                        "processed_obligations": processed,
                        "max_obligations": self.config.max_obligations,
                    }),
                    Some(&pob),
                );
                return StrengthenResult::Unknown;
            }

            if processed > self.config.max_obligations {
                if self.config.verbose {
                    safe_eprintln!("PDR: Exceeded {} obligations", self.config.max_obligations);
                }
                self.pdr_trace_conservative_fail(
                    "strengthen_obligation_limit",
                    serde_json::json!({
                        "processed_obligations": processed,
                        "max_obligations": self.config.max_obligations,
                    }),
                    Some(&pob),
                );
                return StrengthenResult::Unknown;
            }

            // #1326: Early skip for non-query POBs that are already in non_query_reached_init.
            // These were previously discovered to lead to init via a non-query path (not a valid CEX).
            // CRITICAL: Never skip query-derived POBs as those may be valid counterexamples.
            let pob_key = (pob.predicate, pob.level, pob.state.clone());
            if !is_query_derived(&pob) && non_query_reached_init.contains(&pob_key) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping non-query POB already in reached-init set (pred={} level={})",
                        pob.predicate.index(),
                        pob.level
                    );
                }
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Processing obligation ({}, {}) at level {}",
                    pob.predicate.index(),
                    pob.state,
                    pob.level
                );
            }
            self.tracing.active_pob = Some((pob.predicate.index(), pob.level, pob.depth));
            self.pdr_trace_step("Running", Some("BlockObligation"), Some(&pob));
            tracing::info!(
                action = "BlockObligation",
                predicate = pob.predicate.index(),
                level = pob.level,
                frames = self.frames.len(),
                "PDR processing proof obligation"
            );

            // Spacer optimization: Check if POB intersects with a must-reachable state
            // SOUNDNESS: Only use this for early counterexample detection at the query level.
            // For intermediate levels, finding one reachable point doesn't mean the entire
            // POB should be skipped - we still need to try to block it.
            if pob.level == current_level {
                if let Some(rf_id) = self.check_must_reachability(&pob) {
                    // SOUNDNESS (agenda #6 MAY-POB): may-pobs must NEVER enter
                    // counterexample reconstruction. A may-pob that intersects
                    // a must-reachable state is unblockable — drop it silently
                    // (GSpacer's drop rule for unblockable may-pobs).
                    if pob.is_may() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Dropping may-pob intersecting must-reachable state (pred={} level={})",
                                pob.predicate.index(),
                                pob.level
                            );
                        }
                        continue;
                    }
                    if self.config.verbose {
                        let rf = self.reachability.reach_facts.get(rf_id);
                        safe_eprintln!(
                            "PDR: POB intersects must-reachable state at query level: {}",
                            rf.map(|r| r.state.to_string()).unwrap_or_default()
                        );
                    }
                    // Query state intersects with must-reachable - counterexample found.
                    // If reach facts were pruned (#2809), fall through to normal blocking.
                    if let Some(cex) = self.build_cex_from_reach_facts(rf_id, pob.query_clause) {
                        return StrengthenResult::Unsafe(cex);
                    }
                }
            }

            // NOTE: pob passed mutably to allow storing smt_model from already-blocked check (#801)
            let mut pob = pob;
            match self.block_obligation_with_local_blocked(
                &mut pob,
                &blocked_at_level_0,
                &unknown_predecessors,
            ) {
                BlockResult::Blocked(lemma) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Blocked with lemma {} at level {}",
                            lemma.formula,
                            pob.level
                        );
                    }

                    // Record blocked state for convex closure analysis
                    self.record_blocked_state_for_convex(pob.predicate, &pob.state);
                    let blocked_state_count = self
                        .caches
                        .blocked_states_for_convex
                        .get(&pob.predicate)
                        .map_or(0, std::collections::VecDeque::len);
                    let has_bv_vars = self.canonical_vars(pob.predicate).is_some_and(|vars| {
                        vars.iter()
                            .any(|var| matches!(var.sort, ChcSort::BitVec(_)))
                    });
                    if has_bv_vars
                        && blocked_state_count == Self::BV_DISCOVERY_RERUN_BLOCKED_STATE_THRESHOLD
                    {
                        self.rerun_bv_range_invariants_for_pred(pob.predicate);
                    }

                    // At level 0, we're checking if a state intersects init.
                    // If not, the state is not an initial state, but it might
                    // still be reachable via a longer path. Track locally.
                    if pob.level == 0 {
                        // MAY-POB (agenda #6): a may child blocked at level 0 only
                        // confirms a speculative cube misses init. Don't let
                        // best-effort may work consume the level-0 enumeration
                        // budget (which degrades the result to Unknown when hit).
                        if pob.is_may() {
                            continue;
                        }
                        blocked_at_level_0.push((pob.predicate, pob.state.clone()));

                        // Detect degeneration into point enumeration: when we've blocked
                        // too many level-0 states without making progress, the algorithm
                        // is likely enumerating values infinitely (e.g., x != 0, x != -1,
                        // x != -2, ...). Return Unknown to avoid infinite loops.
                        // Use a smaller limit (50) because each blocked state adds to the
                        // exclusion clause, causing exponential slowdown in SMT queries.
                        const MAX_LEVEL0_BLOCKED: usize = 50;
                        if blocked_at_level_0.len() > MAX_LEVEL0_BLOCKED {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Exceeded {} blocked level-0 states, returning Unknown to avoid infinite enumeration",
                                    MAX_LEVEL0_BLOCKED
                                );
                            }
                            self.pdr_trace_conservative_fail(
                                "strengthen_level0_blocked_state_limit",
                                serde_json::json!({
                                    "blocked_level0_states": blocked_at_level_0.len(),
                                    "limit": MAX_LEVEL0_BLOCKED,
                                    "predicate": pob.predicate.index(),
                                }),
                                Some(&pob),
                            );
                            return StrengthenResult::Unknown;
                        }

                        // For mixed summaries: also add to frame[0] so may-summaries
                        // at level 0 reflect blocked states
                        if self.config.use_mixed_summaries {
                            let mut l = lemma.clone();
                            l.level = 0;
                            self.add_lemma_to_frame(l.clone(), 0);
                            // Also add to frame[1] so the lemma participates in the inductive
                            // invariant construction (frame[0] is not used in the final model).
                            let mut l1 = lemma.clone();
                            l1.level = 1;
                            // #2459: Hint/invariant context — use add_lemma_to_frame
                            // for cross-predicate propagation without restart accounting.
                            self.add_lemma_to_frame(l1.clone(), 1);
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Added lemma to frame[0]: pred={}, formula={}",
                                    l.predicate.index(),
                                    l.formula
                                );
                                let fc = self.frames[0].get_predicate_constraint(l.predicate);
                                safe_eprintln!(
                                    "PDR: frame[0] constraint for pred {} = {:?}",
                                    l.predicate.index(),
                                    fc
                                );
                                safe_eprintln!(
                                    "PDR: Added lemma to frame[1]: pred={}, formula={}",
                                    l1.predicate.index(),
                                    l1.formula
                                );
                            }
                        }
                        continue;
                    }
                    // At level 1+, add lemma to the frame and propagate to related predicates
                    let lvl = pob.level.min(self.frames.len() - 1);

                    // For cyclic SCCs, try simultaneous strengthening first
                    // This breaks cyclic dependencies by strengthening all SCC predicates together
                    if let Some(scc_lemmas) =
                        self.try_scc_strengthening(pob.predicate, &lemma.formula, lvl)
                    {
                        // Successfully verified joint inductiveness - add all SCC lemmas
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: SCC strengthening succeeded, adding {} lemmas at level {}",
                                scc_lemmas.len(),
                                lvl
                            );
                        }
                        for (pred, translated_formula) in scc_lemmas {
                            let scc_lemma = Lemma::new(pred, translated_formula, lvl);
                            // #2459: Blocking context — SCC lemmas from POB resolution.
                            self.add_blocking_lemma(scc_lemma, lvl);
                        }
                        // Don't add the original lemma separately - it's included in scc_lemmas
                        continue;
                    }

                    // Standard single-predicate strengthening (existing code)
                    // #2459: Blocking context — POB resolution.
                    let mut l = lemma.clone();
                    l.level = lvl;
                    self.add_blocking_lemma(l.clone(), lvl);

                    // Track point-blocking lemmas to detect degeneration.
                    // Fix #963: Check the LEMMA's blocking formula, not the POB state.
                    // The lemma is `Not(blocking_formula)`, so extract the inner formula
                    // and check if that is a point cube.
                    //
                    // Why this matters: generalization may produce a non-point blocking_formula
                    // even when pob.state was a point cube, so counting by pob.state causes
                    // false positives (premature Unknown when generalization succeeded).
                    if let Some(canonical_vars) = self.canonical_vars(pob.predicate) {
                        // Extract blocking formula from lemma: lemma.formula = Not(blocking_formula)
                        let is_point_blocking = if let ChcExpr::Op(ChcOp::Not, args) = &l.formula {
                            args.len() == 1
                                && cube::is_point_cube_for_vars(&args[0], canonical_vars)
                        } else {
                            false
                        };
                        // MAY-POB (agenda #6): best-effort may work must not
                        // trip the point-enumeration degradation (Unknown).
                        if is_point_blocking && !pob.is_may() {
                            // Feed concretize tracker (#4782): detect convergence stalls early
                            // so Reachable POBs at this (pred, level) can be concretized.
                            self.record_point_block_for_concretize(pob.predicate, lvl);

                            let count = point_blocks_per_level.entry(lvl).or_insert(0);
                            *count += 1;
                            if *count > MAX_POINT_BLOCKS_PER_LEVEL {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Exceeded {} point-blocking lemmas at level {}, returning Unknown to avoid infinite enumeration",
                                        MAX_POINT_BLOCKS_PER_LEVEL,
                                        lvl
                                    );
                                }
                                self.pdr_trace_conservative_fail(
                                    "strengthen_point_blocking_limit",
                                    serde_json::json!({
                                        "level": lvl,
                                        "point_block_count": *count,
                                        "limit": MAX_POINT_BLOCKS_PER_LEVEL,
                                        "predicate": pob.predicate.index(),
                                    }),
                                    Some(&pob),
                                );
                                return StrengthenResult::Unknown;
                            }
                        }
                    }

                    // Try convex closure generalization after adding enough data points
                    // This can discover additional constraints from patterns in blocked states
                    let cc_lemmas = self.try_convex_closure_generalization(pob.predicate, lvl);
                    for cc_lemma in cc_lemmas {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Adding convex closure lemma at level {}: {}",
                                lvl,
                                cc_lemma.formula
                            );
                        }
                        // #2459: Blocking context — convex closure from POB resolution.
                        self.add_blocking_lemma(cc_lemma, lvl);
                    }

                    // MAY-POB promotion (agenda #6): a blocked may-pob re-queues
                    // one level higher (one unit of gas) until its lemma has been
                    // re-verified up to the level global guidance asked for.
                    // Verdict-neutral: each promoted copy goes through the normal
                    // blocking machinery.
                    if let Some(promoted) =
                        pob.may_promotion_after_block(lvl, self.frames.len() - 1)
                    {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Promoting blocked may-pob to level {} (desired {}, gas {})",
                                promoted.level,
                                promoted.desired_level,
                                promoted.gas
                            );
                        }
                        if enqueued.insert(key(&promoted)) {
                            self.push_obligation(promoted);
                        }
                    }
                }
                BlockResult::AlreadyBlocked => {
                    // State is already blocked by existing frame constraint.
                    // No new lemma needed - the frame already blocks this state.
                    // IMPORTANT: Do NOT add to blocked_at_level_0 here - that would
                    // create point exclusions for states already covered by general lemmas.
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: State already blocked by existing lemma at level {}",
                            pob.level
                        );
                    }

                    // POB Push (#1269): When a POB is blocked, push it to verify blocking
                    // at higher levels. This propagates lemmas faster and discovers
                    // fixed points earlier. Reference: Z3 Spacer spacer_context.cpp:3532-3540
                    let max_level = self.frames.len().saturating_sub(1);
                    if self.config.use_pob_push
                        && pob.level < max_level
                        && pob.depth < self.config.push_pob_max_depth
                    {
                        // Create pushed POB at next level
                        let mut pushed_pob = pob.clone();
                        pushed_pob.level += 1;
                        pushed_pob.depth += 1; // Track push count to respect max_depth
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: POB push - blocked at level {}, pushing to level {} (depth {})",
                                pob.level, pushed_pob.level, pushed_pob.depth
                            );
                        }
                        // Re-queue pushed POB (normal priority - not front)
                        if enqueued.insert(key(&pushed_pob)) {
                            self.push_obligation(pushed_pob);
                        }
                    }
                }
                BlockResult::Reachable(predecessor) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Reachable via predecessor ({}, {})",
                            predecessor.predicate.index(),
                            predecessor.state
                        );
                    }
                    if pob.level == 0 {
                        // Reached initial state - counterexample found

                        // #1275 Phase 3: Create reach fact FIRST to get ID for backed must-summary.
                        // This enables AND-node witnesses for hyperedge clauses.
                        let mut instances = predecessor.smt_model.clone();
                        cube::extract_equalities_from_formula(&predecessor.state, &mut instances);
                        let Some(premise_rf_id) = Self::insert_reach_fact_bounded(
                            &mut self.reachability,
                            self.config.verbose,
                            ReachFact {
                                id: ReachFactId(0),
                                predicate: pob.predicate,
                                level: 0,
                                state: predecessor.state.clone(),
                                incoming_clause: Some(predecessor.clause_index),
                                premises: vec![],
                                instances,
                            },
                        ) else {
                            self.pdr_trace_conservative_fail(
                                "strengthen_reach_fact_saturated",
                                serde_json::json!({
                                    "predicate": pob.predicate.index(),
                                    "level": pob.level,
                                }),
                                Some(&pob),
                            );
                            return StrengthenResult::Unknown;
                        };

                        // Add to must summaries as BACKED (proven reachable via backward search)
                        self.add_must_summary_backed(
                            pob.predicate,
                            0,
                            predecessor.state.clone(),
                            premise_rf_id,
                        );
                        // Add to reach solver for fast short-circuit in future queries
                        self.reachability.reach_solvers.add_backed(
                            pob.predicate,
                            premise_rf_id,
                            predecessor.state.clone(),
                        );

                        // Progress derivation if this POB is part of one
                        if let Some(deriv_id) = pob.derivation_id {
                            if let Some(head_rf_id) =
                                self.try_progress_derivation(deriv_id, premise_rf_id)
                            {
                                // Derivation complete - check if head is a query predicate
                                if let Some(head_rf) = self.reachability.reach_facts.get(head_rf_id)
                                {
                                    let head_is_query = queries
                                        .iter()
                                        .flat_map(|(_, q)| q.body.predicates.iter())
                                        .any(|(pred, _)| *pred == head_rf.predicate);
                                    if head_is_query {
                                        // Find the query clause for this predicate
                                        let query_clause = queries
                                            .iter()
                                            .find(|(_, q)| {
                                                q.body
                                                    .predicates
                                                    .iter()
                                                    .any(|(p, _)| *p == head_rf.predicate)
                                            })
                                            .map(|(idx, _)| *idx);
                                        // Build CEX from complete derivation (AND-node witness).
                                        // If reach facts were pruned (#2809), fall through.
                                        if let Some(cex) = self
                                            .build_cex_from_reach_facts(head_rf_id, query_clause)
                                        {
                                            return StrengthenResult::Unsafe(cex);
                                        }
                                    }
                                }
                            } else {
                                // Derivation not complete - enqueue next premise POB (#2283)
                                // After try_progress_derivation, the derivation's `active` index
                                // points to the next premise that needs to be satisfied.
                                if let Some(deriv) = self.reachability.derivations.get(deriv_id) {
                                    if let Some(premise) = deriv.active_premise() {
                                        // Extract state from premise summary (May = over-approx)
                                        let next_state = match &premise.summary {
                                            crate::pdr::derivation::PremiseSummary::May(expr) => {
                                                expr.clone()
                                            }
                                            crate::pdr::derivation::PremiseSummary::Must => {
                                                // Should not happen - active premise should be May
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: Unexpected Must summary for active premise in derivation {:?}",
                                                        deriv_id
                                                    );
                                                }
                                                continue;
                                            }
                                        };

                                        // Create POB for the next premise at level 0
                                        // (we're processing level-0 POBs here, so next premise also at level 0)
                                        let next_pob =
                                            ProofObligation::new(premise.predicate, next_state, 0)
                                                .with_derivation_id(deriv_id);

                                        // Optionally set query_clause from derivation if available
                                        let next_pob = if let Some(qc) = deriv.query_clause {
                                            next_pob.with_query_clause(qc)
                                        } else {
                                            next_pob
                                        };

                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Derivation {:?} - enqueueing next premise POB (pred={} level=0)",
                                                deriv_id,
                                                premise.predicate.index()
                                            );
                                        }

                                        // Enqueue with dedup check
                                        if enqueued.insert(key(&next_pob)) {
                                            self.push_obligation(next_pob);
                                        }
                                    }
                                }
                            }
                            continue;
                        }

                        // #1293/#1326: POBs created from fixed-point verification are NOT query-derived.
                        // Reaching init for such POBs is not a sound UNSAFE witness - it just means
                        // the state is reachable, not that it leads to the bad query.
                        // We mark the ENTIRE parent chain to prevent re-enqueueing any POB on this
                        // derivation path (mirrors Z3/Spacer's reach_facts propagation).
                        //
                        // MAY-POB (agenda #6): may-pobs never carry a query_clause, so
                        // is_query_derived is already false for the whole may lineage;
                        // the explicit is_may() check is belt-and-braces so a reachable
                        // may-pob is ALWAYS dropped silently here, never returned as a
                        // counterexample (GSpacer drop rule; soundness-critical).
                        if pob.is_may() || !is_query_derived(&pob) {
                            // Track this POB and all ancestors to prevent re-enqueueing
                            non_query_reached_init.insert((
                                pob.predicate,
                                pob.level,
                                pob.state.clone(),
                            ));
                            // Mark entire parent chain at their respective levels
                            let mut cur = pob.parent.as_deref();
                            while let Some(p) = cur {
                                non_query_reached_init.insert((
                                    p.predicate,
                                    p.level,
                                    p.state.clone(),
                                ));
                                cur = p.parent.as_deref();
                            }
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Reached init for non-query POB (pred={} level=0); marked chain",
                                    pob.predicate.index()
                                );
                            }
                            // Continue processing other obligations - this POB is not a CEX
                            continue;
                        }

                        // #1510: For hyperedge clauses, a POB may be query-derived but for an
                        // intermediate predicate (not the query predicate itself). E.g., for
                        // P(x) ∧ Q(y) → R(x,y) with query on R, tracing back may create a POB
                        // for Q. Reaching init for Q proves Q is reachable, but does NOT prove
                        // R violates the safety property. We must only return UNSAFE when the
                        // POB's predicate IS a query predicate.
                        // #1520: Check ALL body predicates, not just the first
                        let is_query_pred = queries
                            .iter()
                            .flat_map(|(_, q)| q.body.predicates.iter())
                            .any(|(pred, _)| *pred == pob.predicate);
                        if !is_query_pred {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Reached init for intermediate hyperedge POB (pred={} level=0); \
                                    not returning Unsafe (not query predicate)",
                                    pob.predicate.index()
                                );
                            }
                            // Don't return Unsafe - this is just reachability for a non-query predicate
                            // Continue processing to find actual counterexamples
                            continue;
                        }

                        // SOUNDNESS (agenda #6): counterexample construction is
                        // must-pob-only; may-pobs were dropped above.
                        debug_assert!(
                            !pob.is_may(),
                            "BUG: may-pob must never reach counterexample construction"
                        );
                        let pob_with_clause = pob
                            .clone()
                            .with_incoming_clause(predecessor.clause_index)
                            .with_smt_model(predecessor.smt_model);
                        return StrengthenResult::Unsafe(self.build_cex(&pob_with_clause));
                    }
                    // MAY-POB gas discipline (agenda #6): descending to a
                    // predecessor costs gas; an exhausted may-pob is dropped
                    // silently instead of descending (GSpacer decrements gas
                    // per child and concretizes/drops at zero — we drop).
                    if pob.is_may() && pob.gas == 0 {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Dropping out-of-gas may-pob (pred={} level={})",
                                pob.predicate.index(),
                                pob.level
                            );
                        }
                        continue;
                    }

                    // POB concretization (#4782): attempt before consuming the model.
                    // When the parent POB is in a stuck pattern (too many point-blocks
                    // at this predicate+level), concretize it using the predecessor's
                    // model values. The concretized POB is stronger (implies the original)
                    // and may lead to better generalization.
                    let concretized_parent =
                        self.try_concretize_pob(&pob, &Some(predecessor.smt_model.clone()));

                    // Push child obligation to lower level
                    // Use depth-first order: process child before re-checking parent
                    //
                    // The predecessor.smt_model is the model for the transition from
                    // predecessor's state to pob's state. This model should be on
                    // parent_for_chain (which represents pob in the derivation) because
                    // it contains the variable bindings for the transition clause.
                    let parent_for_chain = pob
                        .clone()
                        .with_incoming_clause(predecessor.clause_index)
                        .with_smt_model(predecessor.smt_model.clone());
                    let mut child_pob = ProofObligation::new(
                        predecessor.predicate,
                        predecessor.state,
                        pob.level - 1,
                    )
                    .with_parent(parent_for_chain)
                    .with_smt_model(predecessor.smt_model);

                    // MAY-POB lineage (agenda #6): children inherit the may kind
                    // (and pay one unit of gas) so the entire lineage stays out of
                    // counterexample reconstruction. Derivation tracking is
                    // must-pob machinery (it can feed hyperedge CEX construction)
                    // and is deliberately NOT propagated on may lineages.
                    if pob.is_may() {
                        pob.gas = pob.gas.saturating_sub(1);
                        child_pob.kind = pob.kind;
                        child_pob.gas = pob.gas;
                    } else if let Some(deriv_id) = predecessor.derivation_id {
                        // #1275: Propagate derivation_id to child POBs for hyperedge tracking.
                        child_pob = child_pob.with_derivation_id(deriv_id);
                    }

                    // #1293/#1326: Skip if child would be a non-query POB that already reached init.
                    // Processing such POBs is pointless - they're reachable but not CEX witnesses.
                    // CRITICAL: Only skip non-query obligations - never skip query-derived ones,
                    // as those could be valid counterexample paths.
                    let child_key = (
                        child_pob.predicate,
                        child_pob.level,
                        child_pob.state.clone(),
                    );
                    if !is_query_derived(&child_pob) && non_query_reached_init.contains(&child_key)
                    {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Skipping non-query child that already reached init (pred={} level={})",
                                child_pob.predicate.index(),
                                child_pob.level
                            );
                        }
                        // #1340 fix: The parent POB is also transitively reachable from init.
                        // Mark it and DON'T re-enqueue - continuing to find predecessors will
                        // just rediscover the same init-reachable state, causing infinite loops.
                        // The parent isn't a valid CEX witness either (since it reaches init
                        // but not the query), so dropping it is correct.
                        let parent_key = (pob.predicate, pob.level, pob.state.clone());
                        non_query_reached_init.insert(parent_key);
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Parent POB also transitively reached init, dropping (pred={} level={})",
                                pob.predicate.index(),
                                pob.level
                            );
                        }
                        // Don't re-enqueue parent - it's a dead-end
                        continue;
                    }

                    // Queue concretized parent (#4782) if available.
                    // Priority: concretized_parent (front) -> child -> parent (back).
                    // If blocking the concretized version produces a good lemma, it also
                    // blocks the original (concretized implies original).
                    // NOTE: try_concretize_pob is currently a stub returning false.
                    let _ = concretized_parent;

                    // Re-queue parent first (goes to front in DFS mode)
                    if enqueued.insert(key(&pob)) {
                        self.push_obligation_front(pob);
                    }
                    // Then push child (goes in front of parent in DFS mode)
                    // In level-priority mode, level determines order
                    if enqueued.insert(key(&child_pob)) {
                        self.push_obligation_front(child_pob);
                    }
                }
                BlockResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: block_obligation returned Unknown");
                    }
                    // If this POB has a parent, mark this state as an unknown predecessor
                    // at the parent's level so we try to find a different predecessor
                    if let Some(parent) = &pob.parent {
                        unknown_predecessors.push((parent.level, pob.predicate, pob.state.clone()));
                    } else if pob.is_may() {
                        // MAY-POB (agenda #6): an undecidable may-pob is auxiliary
                        // best-effort work — drop it silently. It must never
                        // degrade the strengthen verdict (only unblocked MUST
                        // roots threaten a Safe claim).
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Dropping undecidable may-pob (pred={} level={})",
                                pob.predicate.index(),
                                pob.level
                            );
                        }
                    } else {
                        // Root POB (from query) - if we can't block it, return Unknown.
                        // This is a soundness fix: we cannot claim Safe if we can't block
                        // a state that might reach the bad query.
                        // See #759: MBP regression can cause inability to block states.
                        //
                        // However, for multi-predicate problems we may still be able to discover a
                        // concrete counterexample at a deeper level via must-summary reachability
                        // (Spacer technique). In that case, treating this as immediate Unknown is
                        // unnecessarily incomplete: we can increase the bound (push a new frame)
                        // and let must summaries propagate forward until they intersect the query.
                        //
                        // This path is required for tests like `pdr_hyperedge_unsafe_without_range_weakening`
                        // which intentionally disables mixed summaries but expects must-summary CEX discovery.
                        if self.config.use_must_summaries && !self.obligations.overflowed {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Cannot block root POB {} at level {} (will continue: must-summaries enabled)",
                                    pob.state, pob.level
                                );
                            }
                            return StrengthenResult::Continue;
                        }
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Cannot block root POB {} at level {}, returning Unknown",
                                pob.state,
                                pob.level
                            );
                        }
                        self.pdr_trace_conservative_fail(
                            "strengthen_root_obligation_unblocked",
                            serde_json::json!({
                                "predicate": pob.predicate.index(),
                                "level": pob.level,
                                "state_hash": pob.state.structural_hash(),
                                "must_summaries_enabled": self.config.use_must_summaries,
                            }),
                            Some(&pob),
                        );
                        return StrengthenResult::Unknown;
                    }
                }
            }
        }

        // #2983: If any POBs were dropped due to queue overflow, the obligation
        // exploration is incomplete — we cannot claim Safe.
        if self.obligations.overflowed {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: strengthen would return Safe but obligation queue overflowed; degrading to Unknown"
                );
            }
            self.pdr_trace_conservative_fail(
                "strengthen_obligation_queue_overflow",
                serde_json::json!({
                    "max_obligations": self.config.max_obligations,
                }),
                None,
            );
            return StrengthenResult::Unknown;
        }

        StrengthenResult::Safe
    }
}
