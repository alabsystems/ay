// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-predicate discovered-invariant propagation.
//!
//! Goal: when a predicate P learns a discovered invariant I, attempt to transfer it to
//! predicates that use P in their clause bodies.
//!
//! Initial scope (#1402):
//! - Handle transitions with "linear head args" (head args are variables).
//! - Map source canonical vars to target canonical vars using var=var equalities from the clause.
//! - Only propagate when the translated candidate passes `add_discovered_invariant_impl`.
//!
//! Design: the development design notes

mod translate;

use self::translate::derive_target_var_permutation;
use super::super::PdrSolver;

use crate::expr::walk_linear_expr;
use crate::pdr::frame::Lemma;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::collections::VecDeque;

impl PdrSolver {
    /// Propagate frame[1] discovered invariants to dependent predicates until fixpoint.
    ///
    /// Returns the number of new invariants successfully added.
    ///
    /// # Performance bounds (#2192)
    ///
    /// The worklist size is bounded to prevent performance regression on problems with
    /// many discovered invariants. Each iteration processes one (pred, formula) pair and
    /// potentially adds new items to the worklist. We limit total iterations to avoid
    /// unbounded growth in the startup fixpoint loop.
    pub(in crate::pdr::solver) fn propagate_frame1_invariants_to_users(&mut self) -> usize {
        if self.frames.len() < 2 {
            return 0;
        }

        // Seed the worklist with all current frame[1] lemmas.
        let worklist: VecDeque<(PredicateId, ChcExpr)> = self.frames[1]
            .lemmas
            .iter()
            .map(|l| (l.predicate, l.formula.clone()))
            .collect();

        self.propagate_frame1_invariants_from_worklist(
            worklist,
            1,
            "propagate_frame1_invariants_to_users",
        )
    }

    /// Propagate a newly learned lemma to dependent (parent) predicates at level+1.
    ///
    /// Z3 Spacer uses `next_level(lvl)` (level+1) when propagating to parent predicates:
    /// if child P's invariant holds at level N, parent Q needs it at level N+1
    /// (one more unfolding to reach Q through the connecting clause).
    /// Reference: z3/src/muz/spacer/spacer_context.cpp:981-983 (#2414)
    ///
    /// This is an incremental variant used by `add_lemma()` for blocking-learned lemmas,
    /// avoiding a full rescan of all frame lemmas on each addition.
    pub(in crate::pdr::solver) fn propagate_lemma_to_users(
        &mut self,
        source_pred: PredicateId,
        source_formula: &ChcExpr,
        level: usize,
    ) -> usize {
        // #2414: Use level+1 (Z3's next_level), capped to the last valid frame.
        let target_level = (level + 1).min(self.frames.len().saturating_sub(1)).max(1);
        if self.frames.len() <= target_level {
            return 0;
        }

        let mut worklist = VecDeque::new();
        worklist.push_back((source_pred, source_formula.clone()));

        self.propagate_frame1_invariants_from_worklist(
            worklist,
            target_level,
            "propagate_lemma_to_users",
        )
    }

    /// Translate existing frame[1] affine relations through cross-predicate clauses and
    /// return them as regular lemma hints for startup validation.
    ///
    /// This complements clause-guarded propagation: the translated formula is first
    /// normalized to an affine equality/bound over the target predicate's canonical vars, then
    /// passed through the usual hint inductiveness/entry checks before becoming a frame
    /// lemma. This is the startup path for s_multipl-style target predicates without facts.
    pub(in crate::pdr::solver) fn collect_affine_equality_propagation_hints(
        &self,
    ) -> Vec<crate::lemma_hints::LemmaHint> {
        if self.frames.len() < 2 {
            return Vec::new();
        }

        const SOURCE: &str = "affine-propagation-rel-v1";
        const PRIORITY: u16 = 180;
        const MAX_HINTS_PER_TARGET: usize = 12;

        let candidate_index = self.build_propagation_candidate_index();
        let mut hints = Vec::new();
        let mut per_target: FxHashMap<PredicateId, usize> = FxHashMap::default();

        for lemma in &self.frames[1].lemmas {
            let Some(source_formula) =
                self.normalize_affine_relation_for_target(lemma.predicate, &lemma.formula)
            else {
                continue;
            };
            let Some(candidates) = candidate_index.get(&lemma.predicate) else {
                continue;
            };

            for cand in candidates {
                if per_target.get(&cand.target_pred).copied().unwrap_or(0) >= MAX_HINTS_PER_TARGET {
                    continue;
                }

                let Some((body_args, head_args, constraint)) =
                    self.propagation_candidate_components(lemma.predicate, cand)
                else {
                    continue;
                };
                let Some(translated) = self.translate_invariant_via_clause_mapping(
                    lemma.predicate,
                    cand.target_pred,
                    &source_formula,
                    body_args,
                    head_args,
                    constraint,
                ) else {
                    continue;
                };
                let Some(normalized) =
                    self.normalize_affine_relation_for_target(cand.target_pred, &translated)
                else {
                    continue;
                };

                if self
                    .frames
                    .iter()
                    .any(|frame| frame.contains_lemma(cand.target_pred, &normalized))
                {
                    continue;
                }

                hints.push(crate::lemma_hints::LemmaHint::new(
                    cand.target_pred,
                    normalized,
                    PRIORITY,
                    SOURCE,
                ));
                *per_target.entry(cand.target_pred).or_insert(0) += 1;
            }
        }

        hints.sort_by(|a, b| {
            a.priority
                .cmp(&b.priority)
                .then_with(|| a.predicate.cmp(&b.predicate))
                .then_with(|| a.formula.cmp(&b.formula))
        });
        hints.dedup_by(|a, b| a.predicate == b.predicate && a.formula == b.formula);
        hints
    }

    /// Validate transition-derived affine equality hints at startup until they stop
    /// adding new frame lemmas. This allows newly accepted target equalities to seed
    /// one more propagation round across downstream phase-chain predicates.
    pub(in crate::pdr::solver) fn apply_affine_equality_propagation_hints(&mut self) -> usize {
        const MAX_ROUNDS: usize = 4;

        let mut total_added = 0usize;
        for _ in 0..MAX_ROUNDS {
            if self.is_cancelled() {
                break;
            }

            let hints = self.collect_affine_equality_propagation_hints();
            if hints.is_empty() {
                break;
            }

            let added =
                self.apply_extra_lemma_hints(crate::lemma_hints::HintStage::Startup, &hints);
            total_added += added;
            if added == 0 {
                break;
            }
        }

        total_added
    }

    /// Best-effort cross-predicate frame advancement.
    pub(in crate::pdr::solver) fn try_cross_predicate_propagation(
        &mut self,
        source_pred: PredicateId,
        source_formula: &ChcExpr,
        level: usize,
    ) -> usize {
        if level == 0 || level + 1 >= self.frames.len() {
            return 0;
        }

        let Some(users) = self.caches.predicate_users.get(&source_pred) else {
            return 0;
        };
        if users.is_empty() {
            return 0;
        }

        let target_preds: Vec<PredicateId> = users
            .iter()
            .copied()
            .filter(|pred| *pred != source_pred)
            .collect();
        if target_preds.is_empty() {
            return 0;
        }

        let candidate_lemmas: Vec<Lemma> = self.frames[level]
            .lemmas
            .iter()
            .filter(|lemma| target_preds.contains(&lemma.predicate))
            .filter(|lemma| {
                !self.frames[level + 1].contains_lemma_with_hash(
                    lemma.predicate,
                    &lemma.formula,
                    lemma.formula_hash,
                )
            })
            .cloned()
            .collect();

        let mut pushed_count = 0;
        for lemma in candidate_lemmas {
            if self.is_cancelled() {
                break;
            }

            let blocked_state = match &lemma.formula {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => (*args[0]).clone(),
                positive => ChcExpr::not(positive.clone()),
            };

            let mut can_push = true;
            for (clause_index, clause) in self.problem.clauses_defining_with_index(lemma.predicate)
            {
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                let blocked_on_head =
                    match self.apply_to_args(lemma.predicate, &blocked_state, head_args) {
                        Some(expr) => expr,
                        None => {
                            can_push = false;
                            break;
                        }
                    };

                let mut query_parts = Vec::with_capacity(clause.body.predicates.len() * 2 + 3);
                query_parts.push(
                    clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true)),
                );
                query_parts.push(self.clause_guarded_constraint(
                    lemma.predicate,
                    clause_index,
                    head_args,
                    level,
                ));

                for (body_pred, body_args) in &clause.body.predicates {
                    let frame_constraint = self.frames[level]
                        .get_predicate_constraint(*body_pred)
                        .unwrap_or(ChcExpr::Bool(true));
                    let Some(frame_on_body) =
                        self.apply_to_args(*body_pred, &frame_constraint, body_args)
                    else {
                        can_push = false;
                        break;
                    };
                    query_parts.push(frame_on_body);

                    if *body_pred == source_pred {
                        let Some(source_on_body) =
                            self.apply_to_args(source_pred, source_formula, body_args)
                        else {
                            can_push = false;
                            break;
                        };
                        query_parts.push(source_on_body);
                    }
                }

                if !can_push {
                    break;
                }

                query_parts.push(blocked_on_head);
                let query = ChcExpr::and_all(query_parts);
                let (result, _) =
                    Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
                match result {
                    crate::SmtResult::Unsat
                    | crate::SmtResult::UnsatWithCore(_)
                    | crate::SmtResult::UnsatWithFarkas(_) => {}
                    crate::SmtResult::Sat(_) | crate::SmtResult::Unknown => {
                        can_push = false;
                        break;
                    }
                }
            }

            if !can_push {
                continue;
            }

            let mut pushed = lemma;
            pushed.level = level + 1;
            self.add_lemma_to_frame(pushed.clone(), level + 1);
            pushed_count += 1;

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: cross-predicate push: advanced {} for pred {} to level {} via pred {}",
                    pushed.formula,
                    pushed.predicate.index(),
                    level + 1,
                    source_pred.index(),
                );
            }
        }

        pushed_count
    }

    pub(in crate::pdr::solver) fn normalize_affine_equality_for_target(
        &self,
        predicate: PredicateId,
        expr: &ChcExpr,
    ) -> Option<ChcExpr> {
        self.normalize_affine_relation_for_target(predicate, expr)
            .and_then(|normalized| match normalized {
                ChcExpr::Op(ChcOp::Eq, _) => Some(normalized),
                _ => None,
            })
    }

    fn normalize_affine_relation_for_target(
        &self,
        predicate: PredicateId,
        expr: &ChcExpr,
    ) -> Option<ChcExpr> {
        let target_vars = self.canonical_vars(predicate)?;
        if target_vars.is_empty() {
            return None;
        }

        let (op, lhs, rhs) = match expr {
            ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Le | ChcOp::Ge), args) if args.len() == 2 => {
                (*op, args[0].as_ref(), args[1].as_ref())
            }
            _ => return None,
        };

        let mut name_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
        for (idx, var) in target_vars.iter().enumerate() {
            name_to_idx.insert(var.name.as_str(), idx);
        }

        let (lhs_coeffs, lhs_const) = collect_linear_side(lhs, &name_to_idx, target_vars.len())?;
        let (rhs_coeffs, rhs_const) = collect_linear_side(rhs, &name_to_idx, target_vars.len())?;

        match op {
            ChcOp::Eq => {
                let mut coeffs = vec![0i128; target_vars.len()];
                for idx in 0..target_vars.len() {
                    coeffs[idx] = lhs_coeffs[idx].checked_sub(rhs_coeffs[idx])?;
                }
                let mut constant = rhs_const.checked_sub(lhs_const)?;
                normalize_affine_coefficients(&mut coeffs, &mut constant)?;

                let lhs_expr = build_affine_sum(&coeffs, target_vars)?;
                Some(ChcExpr::eq(lhs_expr, ChcExpr::int(constant)).simplify_constants())
            }
            ChcOp::Ge => {
                normalize_affine_ge(&lhs_coeffs, lhs_const, &rhs_coeffs, rhs_const, target_vars)
            }
            ChcOp::Le => {
                normalize_affine_ge(&rhs_coeffs, rhs_const, &lhs_coeffs, lhs_const, target_vars)
            }
            _ => None,
        }
    }

    fn propagate_frame1_invariants_from_worklist(
        &mut self,
        mut worklist: VecDeque<(PredicateId, ChcExpr)>,
        target_level: usize,
        log_label: &str,
    ) -> usize {
        let mut total_added = 0;

        // #2429: Precompute the propagation candidate index once. The clauses are
        // immutable during propagation, so scanning all clauses per worklist item
        // is redundant. Build a source_pred -> candidates map upfront.
        let candidate_index = self.build_propagation_candidate_index();
        let shared_pattern_index = self.build_shared_variable_pattern_index(&candidate_index);

        // #2192: Bound iterations to avoid performance regression.
        // The worklist propagation is O(lemmas * clauses * SMT_checks) per iteration.
        // With many invariants, this can dominate startup time.
        const MAX_PROPAGATION_ITERATIONS: usize = 100;
        let mut iterations = 0;

        while let Some((source_pred, source_formula)) = worklist.pop_front() {
            if self.is_cancelled() {
                break;
            }
            iterations += 1;
            if iterations > MAX_PROPAGATION_ITERATIONS {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: {}: iteration limit {} reached, {} items remain in worklist",
                        log_label,
                        MAX_PROPAGATION_ITERATIONS,
                        worklist.len()
                    );
                }
                break;
            }
            let candidates = match candidate_index.get(&source_pred) {
                Some(cands) => cands.as_slice(),
                None => continue,
            };
            for cand in candidates {
                let pu = &self.caches.predicate_users;
                assert!(
                    pu.get(&source_pred)
                        .is_some_and(|users| users.contains(&cand.target_pred)),
                    "BUG #2429: propagation candidate index produced non-user edge {} -> {}",
                    source_pred.index(),
                    cand.target_pred.index(),
                );
                let Some((body_args, head_args, constraint)) =
                    self.propagation_candidate_components(source_pred, cand)
                else {
                    continue;
                };
                let Some(transformed) = self.translate_invariant_via_clause_mapping(
                    source_pred,
                    cand.target_pred,
                    &source_formula,
                    body_args,
                    head_args,
                    constraint,
                ) else {
                    continue;
                };

                // #2459 Phase 2+3: Clause-guarded propagation (Z3 rule-tag equivalent).
                //
                // Z3 Spacer uses Boolean rule tags to guard cross-predicate assertions:
                //   tag_i => renamed_lemma
                // AY iterates per-clause, so the tag guard is implicit: store the
                // translated lemma indexed by (target_pred, clause_index) and include
                // it only when that clause is active during blocking/inductiveness.
                //
                // The clause-guarded storage bypasses validation because soundness
                // is guaranteed by two mechanisms:
                // 1. Clause guard: the lemma only applies when the specific clause fires
                //    (Z3 rule-tag equivalent, implicit in AY's per-clause iteration).
                // 2. Level filtering (issue 2536): lemmas are only included at levels where
                //    they are valid (matching Z3's 1..next_level(L) discipline).
                //
                // #2807: The unconditional frame-insertion path (below) checks
                // init-validity. Propagated lemmas may not be globally inductive
                // for the target (they come from cross-predicate transitions), so
                // verify_model() at Safe return sites is the final soundness gate.
                //
                // Reference: z3/src/muz/spacer/spacer_context.cpp:1922-1957
                //
                // #2807: In debug builds, verify that the translated lemma only
                // references variables in the target predicate's canonical namespace.
                // A variable outside this namespace indicates a bug in
                // translate_invariant_via_clause_mapping (e.g., stale source vars
                // leaking through incomplete substitution).
                assert!(
                    {
                        let target_vars = self.canonical_vars(cand.target_pred);
                        match target_vars {
                            Some(tvars) => transformed
                                .vars()
                                .into_iter()
                                .all(|v| tvars.iter().any(|tv| tv.name == v.name)),
                            // No canonical vars — can't validate, assume OK.
                            None => true,
                        }
                    },
                    "BUG #2807: clause-guarded propagated lemma {} for pred {} clause {} \
                     contains variables outside target canonical namespace — \
                     translation error in translate_invariant_via_clause_mapping",
                    transformed,
                    cand.target_pred.index(),
                    cand.clause_index,
                );
                let guarded_key = (cand.target_pred, cand.clause_index);
                // #2536: Check for duplicate formula (ignoring level — keep max level).
                // #2560: Track whether max_level was bumped to re-propagate transitively.
                // #2649: Cap per-key lemma count to prevent SMT query bloat.
                // Multiplicative bound discovery can generate 30+ lemmas per predicate,
                // and including all of them as clause-guarded conjuncts in every
                // blocking/push/inductiveness query creates prohibitive overhead.
                // Z3 Spacer avoids this because rule-tag implications (tag => lemma)
                // are cheaper than direct conjunction in the query formula.
                const MAX_CLAUSE_GUARDED_LEMMAS_PER_KEY: usize = 16;
                let (is_new, level_bumped) = self.upsert_clause_guarded_lemma(
                    guarded_key,
                    transformed.clone(),
                    target_level,
                    MAX_CLAUSE_GUARDED_LEMMAS_PER_KEY,
                );
                if is_new {
                    total_added += 1;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: {}: clause-guarded propagation of {} to pred {} clause {} at level {}",
                            log_label, transformed, cand.target_pred.index(),
                            cand.clause_index, target_level
                        );
                    }
                    // Continue transitive propagation through the worklist.
                    worklist.push_back((cand.target_pred, transformed.clone()));
                } else if level_bumped {
                    // #2560: Re-enqueue for transitive propagation so downstream
                    // clause-guarded copies also get their max_level updated.
                    // Without this, transitive copies (P→Q→R) stay at the old
                    // max_level even after the direct copy (P→Q) is bumped.
                    worklist.push_back((cand.target_pred, transformed.clone()));
                }

                // Predicates that participate in a reversible var-to-var mapping
                // are treated as peers rather than one-way transport edges.
                // For these pairs, try to admit the translated formula through the
                // normal discovered-invariant gate so it can become a regular frame
                // lemma on the target predicate.
                let shares_variable_pattern = shared_pattern_index
                    .get(&source_pred)
                    .is_some_and(|targets| targets.contains(&cand.target_pred));
                if shares_variable_pattern {
                    let had_frame_lemma =
                        self.frames[target_level].contains_lemma(cand.target_pred, &transformed);
                    if !had_frame_lemma
                        && self.add_discovered_invariant_impl(
                            cand.target_pred,
                            transformed.clone(),
                            target_level,
                            false,
                        )
                        && self.frames[target_level].contains_lemma(cand.target_pred, &transformed)
                    {
                        total_added += 1;
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: {}: shared-pattern propagation of {} to pred {} at level {}",
                                log_label,
                                transformed,
                                cand.target_pred.index(),
                                target_level
                            );
                        }
                        worklist.push_back((cand.target_pred, transformed.clone()));
                    }
                }

                // Only predicates with direct fact clauses can safely promote
                // propagated lemmas into unconditional frame invariants.
                // For intermediate predicates, keep propagated lemmas
                // clause-scoped so different incoming transitions do not bleed
                // contradictory constraints into the same frame. (#1398)
                if !self.frames[target_level].contains_lemma(cand.target_pred, &transformed) {
                    let pass_init = if self.predicate_has_facts(cand.target_pred) {
                        let blocking = ChcExpr::not(transformed.clone());
                        self.blocks_initial_states(cand.target_pred, &blocking)
                    } else {
                        // Intermediate predicates (no init facts) get clause-guarded
                        // storage only — not unconditional frame insertion. Inserting
                        // lemmas from different source clauses into the same frame
                        // creates contradictions (frame inconsistency) that prevent
                        // convergence. The clause-guarded path at
                        // `clause_guarded_constraint(pred, clause_idx, ...)` already
                        // stores the lemma with proper clause scoping.
                        // Part of #1398: fixes gj2007_m_1/m_2 frame oscillation.
                        false
                    };

                    if pass_init {
                        // #2807: Note — propagated cross-predicate lemmas added here
                        // are NOT checked for inductiveness. They are init-valid but may
                        // not be self-inductive (the source invariant holds under the
                        // specific clause transition but Q may have other transitions
                        // that violate it). Soundness relies on verify_model() at Safe
                        // return sites to catch false Safe verdicts from non-inductive
                        // frame lemmas. A full inductiveness gate here was tried but
                        // caused regressions (bouncy_two_counters_equality_safe).
                        use crate::pdr::frame::Lemma;
                        let lemma = Lemma::new(cand.target_pred, transformed.clone(), target_level);
                        self.add_lemma_to_frame_no_propagation(lemma, target_level);
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: {}: also added to frame {} for pred {} at level {}",
                                log_label,
                                transformed,
                                cand.target_pred.index(),
                                target_level
                            );
                        }
                    }
                }
            }
        }

        if self.config.verbose && total_added > 0 {
            safe_eprintln!(
                "PDR: {}: added {} clause-guarded invariant(s)",
                log_label,
                total_added
            );
        }

        total_added
    }

    /// Precompute propagation candidates indexed by source predicate (#2429).
    ///
    /// The clause set is immutable during propagation, so we scan all clauses once and
    /// group lightweight candidate descriptors by source predicate.
    fn build_propagation_candidate_index(
        &self,
    ) -> FxHashMap<PredicateId, Vec<PropagationCandidate>> {
        let mut index: FxHashMap<PredicateId, Vec<PropagationCandidate>> = FxHashMap::default();
        for (clause_index, clause) in self.problem.clauses().iter().enumerate() {
            let Some(target_pred) = clause.head.predicate_id() else {
                continue;
            };
            for (body_atom_index, (body_pred, _)) in clause.body.predicates.iter().enumerate() {
                // Skip self-loops (source == target).
                if *body_pred == target_pred {
                    continue;
                }
                index
                    .entry(*body_pred)
                    .or_default()
                    .push(PropagationCandidate {
                        target_pred,
                        clause_index,
                        body_atom_index,
                    });
            }
        }
        index
    }

    fn build_shared_variable_pattern_index(
        &self,
        candidate_index: &FxHashMap<PredicateId, Vec<PropagationCandidate>>,
    ) -> FxHashMap<PredicateId, Vec<PredicateId>> {
        let mut permutations: FxHashMap<(PredicateId, PredicateId), Vec<Vec<usize>>> =
            FxHashMap::default();

        for (source_pred, candidates) in candidate_index {
            for candidate in candidates {
                let Some(permutation) =
                    self.candidate_variable_permutation(*source_pred, candidate)
                else {
                    continue;
                };
                permutations
                    .entry((*source_pred, candidate.target_pred))
                    .or_default()
                    .push(permutation);
            }
        }

        let mut related: FxHashMap<PredicateId, Vec<PredicateId>> = FxHashMap::default();
        for ((source_pred, target_pred), forward_perms) in &permutations {
            let Some(reverse_perms) = permutations.get(&(*target_pred, *source_pred)) else {
                continue;
            };
            if forward_perms.iter().any(|forward| {
                reverse_perms
                    .iter()
                    .any(|reverse| permutations_are_inverse(forward, reverse))
            }) {
                related.entry(*source_pred).or_default().push(*target_pred);
            }
        }

        for targets in related.values_mut() {
            targets.sort_by_key(|pred| pred.index());
            targets.dedup();
        }

        related
    }

    fn propagation_candidate_components(
        &self,
        source_pred: PredicateId,
        candidate: &PropagationCandidate,
    ) -> Option<(&[ChcExpr], &[ChcExpr], Option<&ChcExpr>)> {
        let clause = self.problem.clauses().get(candidate.clause_index)?;
        let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
            return None;
        };
        let (body_pred, body_args) = clause.body.predicates.get(candidate.body_atom_index)?;
        if *body_pred != source_pred {
            return None;
        }
        Some((
            body_args.as_slice(),
            head_args.as_slice(),
            clause.body.constraint.as_ref(),
        ))
    }

    fn candidate_variable_permutation(
        &self,
        source_pred: PredicateId,
        candidate: &PropagationCandidate,
    ) -> Option<Vec<usize>> {
        let source_vars = self.canonical_vars(source_pred)?;
        let target_vars = self.canonical_vars(candidate.target_pred)?;
        if source_vars.len() != target_vars.len() {
            return None;
        }

        let (body_args, head_args, constraint) =
            self.propagation_candidate_components(source_pred, candidate)?;
        if body_args.len() != source_vars.len() || head_args.len() != target_vars.len() {
            return None;
        }

        derive_target_var_permutation(target_vars, body_args, head_args, constraint)
    }

    #[cfg(test)]
    fn build_propagation_candidates(&self, source_pred: PredicateId) -> Vec<PropagationCandidate> {
        // Collect first to avoid borrowing `self.problem` across `&mut self` calls in the loop.
        let mut out = Vec::new();
        for (clause_index, clause) in self.problem.clauses().iter().enumerate() {
            let Some(target_pred) = clause.head.predicate_id() else {
                continue;
            };
            if target_pred == source_pred {
                continue;
            }

            for (body_atom_index, (body_pred, _)) in clause.body.predicates.iter().enumerate() {
                if *body_pred != source_pred {
                    continue;
                }

                out.push(PropagationCandidate {
                    target_pred,
                    clause_index,
                    body_atom_index,
                });
            }
        }
        out
    }
}

fn collect_linear_side(
    expr: &ChcExpr,
    name_to_idx: &FxHashMap<&str, usize>,
    num_vars: usize,
) -> Option<(Vec<i128>, i128)> {
    let mut coeffs = vec![0i128; num_vars];
    let mut constant = 0i128;

    walk_linear_expr(
        expr,
        1i128,
        &mut |mult: i128, n| {
            constant = constant.checked_add(mult.checked_mul(n)?)?;
            Some(())
        },
        &mut |mult: i128, v| {
            let idx = *name_to_idx.get(v.name.as_str())?;
            coeffs[idx] = coeffs[idx].checked_add(mult)?;
            Some(())
        },
    )?;

    Some((coeffs, constant))
}

fn normalize_affine_coefficients(coeffs: &mut [i128], constant: &mut i128) -> Option<()> {
    if coeffs.iter().all(|&c| c == 0) {
        return None;
    }

    fn abs_u128(v: i128) -> u128 {
        v.unsigned_abs()
    }

    let mut g = 0u128;
    for &coeff in coeffs.iter() {
        g = num_integer::gcd(g, abs_u128(coeff));
    }
    g = num_integer::gcd(g, abs_u128(*constant));

    if g > 1 {
        // Fail closed if the gcd itself does not fit i128 (only possible when
        // every value is i128::MIN).
        let g = i128::try_from(g).ok()?;
        if *constant % g == 0 && coeffs.iter().all(|&c| c % g == 0) {
            for coeff in coeffs.iter_mut() {
                *coeff /= g;
            }
            *constant /= g;
        }
    }

    let &first = coeffs.iter().find(|&&coeff| coeff != 0)?;
    if first < 0 {
        if coeffs.iter().any(|&coeff| coeff == i128::MIN) || *constant == i128::MIN {
            return None;
        }
        for coeff in coeffs.iter_mut() {
            *coeff = coeff.checked_neg()?;
        }
        *constant = constant.checked_neg()?;
    }

    Some(())
}

fn normalize_affine_ge(
    lhs_coeffs: &[i128],
    lhs_const: i128,
    rhs_coeffs: &[i128],
    rhs_const: i128,
    target_vars: &[ChcVar],
) -> Option<ChcExpr> {
    debug_assert_eq!(lhs_coeffs.len(), rhs_coeffs.len());
    debug_assert_eq!(lhs_coeffs.len(), target_vars.len());

    let mut coeffs = vec![0i128; target_vars.len()];
    for idx in 0..target_vars.len() {
        coeffs[idx] = lhs_coeffs[idx].checked_sub(rhs_coeffs[idx])?;
    }
    let mut constant = rhs_const.checked_sub(lhs_const)?;
    normalize_affine_bound_coefficients(&mut coeffs, &mut constant)?;

    let lhs_expr = build_affine_sum(&coeffs, target_vars)?;
    Some(ChcExpr::ge(lhs_expr, ChcExpr::int(constant)).simplify_constants())
}

fn normalize_affine_bound_coefficients(coeffs: &mut [i128], constant: &mut i128) -> Option<()> {
    if coeffs.iter().all(|&c| c == 0) {
        return None;
    }

    fn abs_u128(v: i128) -> u128 {
        v.unsigned_abs()
    }

    let mut g = 0u128;
    for &coeff in coeffs.iter() {
        g = num_integer::gcd(g, abs_u128(coeff));
    }
    g = num_integer::gcd(g, abs_u128(*constant));

    if g > 1 {
        // Fail closed if the gcd itself does not fit i128 (only possible when
        // every value is i128::MIN).
        let g = i128::try_from(g).ok()?;
        if *constant % g == 0 && coeffs.iter().all(|&c| c % g == 0) {
            for coeff in coeffs.iter_mut() {
                *coeff /= g;
            }
            *constant /= g;
        }
    }

    Some(())
}

fn build_affine_sum(coeffs: &[i128], vars: &[ChcVar]) -> Option<ChcExpr> {
    debug_assert_eq!(coeffs.len(), vars.len());

    let mut terms = Vec::new();
    for (&coeff, var) in coeffs.iter().zip(vars.iter()) {
        if coeff == 0 {
            continue;
        }
        let term = match coeff {
            1 => ChcExpr::var(var.clone()),
            -1 => ChcExpr::neg(ChcExpr::var(var.clone())),
            _ => ChcExpr::mul(ChcExpr::int(coeff), ChcExpr::var(var.clone())),
        };
        terms.push(term);
    }

    match terms.len() {
        0 => None,
        1 => terms.pop(),
        _ => Some(terms.into_iter().reduce(ChcExpr::add).expect("len > 1")),
    }
}

fn permutations_are_inverse(forward: &[usize], reverse: &[usize]) -> bool {
    if forward.len() != reverse.len() {
        return false;
    }

    for (source_idx, &target_idx) in forward.iter().enumerate() {
        if reverse.get(target_idx).copied() != Some(source_idx) {
            return false;
        }
    }

    true
}

#[derive(Clone, Copy)]
struct PropagationCandidate {
    target_pred: PredicateId,
    /// Index into problem.clauses() that produced this candidate.
    clause_index: usize,
    /// Index into `clause.body.predicates` that matched the source predicate.
    body_atom_index: usize,
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
