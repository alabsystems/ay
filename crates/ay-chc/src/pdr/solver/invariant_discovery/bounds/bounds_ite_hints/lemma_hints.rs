// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Apply lemma hints from registered hint providers and runtime user hints.
    ///
    /// This method collects hints from all registered providers plus any
    /// user-provided hints in `self.config.user_hints`, validates them via
    /// `is_inductive_blocking`, and adds valid hints as lemmas.
    ///
    /// Hints are validated - they are never trusted. A hint that fails
    /// inductiveness or init checks is dropped.
    pub(in crate::pdr::solver) fn apply_lemma_hints(
        &mut self,
        stage: crate::lemma_hints::HintStage,
    ) -> usize {
        if !self.config.use_lemma_hints {
            return 0;
        }

        // BUG FIX #3121: Check cancellation before expensive hint collection.
        // The recurrence analysis in hint providers can take seconds on problems
        // with complex transitions (e.g., dillig02_m with ITE + mod expressions).
        if self.is_cancelled() {
            return 0;
        }

        use crate::lemma_hints::{
            collect_all_hints_with_extra_providers, has_providers, HintRequest,
        };
        use ay_core::kani_compat::DetHashMap as FxHashMap;

        // Fast path: skip if no providers AND no runtime hints/providers
        if !has_providers()
            && self.config.user_hints.is_empty()
            && self.config.user_hint_providers.0.is_empty()
        {
            return 0;
        }

        // Build canonical vars lookup for hint request
        let predicate_vars_clone: FxHashMap<PredicateId, Vec<ChcVar>> =
            self.caches.predicate_vars.clone();
        let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
            predicate_vars_clone.get(&pred).map(Vec::as_slice)
        };

        // Collect hints from all providers (static + runtime) plus user hints
        let req = HintRequest::new(stage, &self.problem, &canonical_vars_fn);
        let hints = collect_all_hints_with_extra_providers(
            &req,
            &self.config.user_hint_providers.0,
            &self.config.user_hints,
        );

        if hints.is_empty() {
            return 0;
        }

        self.apply_collected_lemma_hints(stage, hints)
    }

    /// Apply a pre-collected hint set without invoking registered providers again.
    ///
    /// This is used by startup passes that synthesize dynamic hint candidates from
    /// already-discovered frame lemmas and want to reuse the normal hint validation
    /// pipeline.
    pub(in crate::pdr::solver) fn apply_extra_lemma_hints(
        &mut self,
        stage: crate::lemma_hints::HintStage,
        hints: &[crate::lemma_hints::LemmaHint],
    ) -> usize {
        if !self.config.use_lemma_hints || self.is_cancelled() || hints.is_empty() {
            return 0;
        }

        self.apply_collected_lemma_hints(stage, hints.to_vec())
    }

    fn apply_collected_lemma_hints(
        &mut self,
        stage: crate::lemma_hints::HintStage,
        hints: Vec<crate::lemma_hints::LemmaHint>,
    ) -> usize {
        use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
        use rustc_hash::FxHasher;

        // Bound SMT work for hint validation. Hints are optional, so treating a timeout as
        // `Unknown` and rejecting the hint is sound.
        const HINT_VALIDATION_SMT_TIMEOUT: std::time::Duration =
            std::time::Duration::from_millis(200);
        // Overall wall-clock budget for hint validation: prevents startup starvation when
        // many hints are generated (e.g., 36 mod-sum hints for 5-variable predicates).
        // Each hint can require up to 3 SMT calls x 200ms = 600ms, so 36 hints could
        // consume 21.6s of the 27s solve budget.
        // 2s budget for hint validation. The hints provide critical parity/mod invariants
        // that the brute-force discover_parity_invariants path would take 40s+ to find under
        // portfolio CPU contention. The nonfixpoint deadline in discover_parity_invariants
        // ensures we don't starve even if hint validation takes full 2s (#3121).
        const HINT_VALIDATION_BUDGET: std::time::Duration = std::time::Duration::from_secs(2);
        // Cap on relative-induction (entry-CEGAR) fallthrough attempts per
        // apply pass — see the eligibility comment at the admission site.
        const MAX_RELATIVE_INDUCTION_FALLTHROUGH: usize = 8;
        let mut relative_fallthrough_attempts = 0usize;
        // Genuinely user-supplied hints (relative-induction fallthrough
        // eligibility). Cross-engine lemma-pool transfers are merged into
        // `config.user_hints` too (#7919) but keep their distinguishing
        // source tag — exclude them here.
        let user_hint_keys: FxHashSet<(PredicateId, ChcExpr)> = self
            .config
            .user_hints
            .iter()
            .filter(|hint| hint.source != "lemma_pool_transfer")
            .map(|hint| (hint.predicate, hint.formula.clone()))
            .collect();
        let hint_start = ay_core::time::Instant::now();

        let _hint_smt_timeout = self
            .smt
            .scoped_check_timeout(Some(HINT_VALIDATION_SMT_TIMEOUT));

        if self.config.verbose {
            let user_hint_count = self.config.user_hints.len();
            safe_eprintln!(
                "PDR: apply_lemma_hints received {} hints ({} from user, {} from providers) at {:?}",
                hints.len(),
                user_hint_count,
                hints.len().saturating_sub(user_hint_count),
                stage
            );
        }

        let mut added = 0usize;
        let mut rejected = 0usize;

        // Hints can be jointly self-inductive even when each fails self-inductive check
        // in isolation. Track these candidates and retry as conjunctions per (predicate, source).
        let mut conj_candidates: FxHashMap<(PredicateId, &'static str), Vec<ChcExpr>> =
            FxHashMap::default();

        // Cross-source candidates: track all rejected hints per predicate for cross-combination.
        let mut cross_source_candidates: FxHashMap<PredicateId, Vec<ChcExpr>> =
            FxHashMap::default();

        // #7048: Pre-compute constant variable names per predicate for hint tautology filter.
        // Variables are constant if: (a) unchanged across self-loop transitions
        // (detect_constant_arguments), OR (b) have tight bounds in frame[1]
        // (detect_frame_tight_bound_vars). Both sources are combined.
        // Hints involving ONLY constant variables are tautologies — skip SMT validation.
        //
        // Also: if ALL Int variables of a predicate have tight init bounds (fully
        // determined initial state), skip ALL hints for that predicate. The brute-force
        // discovery passes already find the essential invariants; hints just add
        // redundant reformulations that bloat the frame and slow push queries.
        let mut constant_var_names: FxHashMap<PredicateId, FxHashSet<String>> =
            FxHashMap::default();
        let mut all_init_determined: FxHashSet<PredicateId> = FxHashSet::default();
        for pred in self.problem.predicates() {
            let mut constant_indices = self.detect_constant_arguments(pred.id);
            constant_indices.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

            // Check if ALL Int vars have tight init bounds AND there are enough
            // variables to cause hint bloat (>=4). With fewer variables, hints are
            // few and the overhead is negligible.
            if let Some(cvars) = self.canonical_vars(pred.id) {
                let init_vals = self.get_init_values(pred.id);
                let int_vars: Vec<_> = cvars
                    .iter()
                    .filter(|v| matches!(v.sort, ChcSort::Int))
                    .collect();
                if int_vars.len() >= 4
                    && int_vars
                        .iter()
                        .all(|v| init_vals.get(&v.name).is_some_and(|b| b.min == b.max))
                {
                    all_init_determined.insert(pred.id);
                }

                let names: FxHashSet<String> = constant_indices
                    .iter()
                    .filter_map(|&idx| cvars.get(idx).map(|v| v.name.clone()))
                    .collect();
                if !names.is_empty() {
                    constant_var_names.insert(pred.id, names);
                }
            }
        }

        let hint_count = hints.len();
        let mut skipped_constant = 0usize;
        let mut hints_per_pred: FxHashMap<PredicateId, usize> = FxHashMap::default();
        for (hint_idx, hint) in hints.into_iter().enumerate() {
            // Respect portfolio cancellation: the outer solve loop checks is_cancelled()
            // between discovery passes, but apply_lemma_hints can run for seconds with
            // many SMT calls. Without this check, a cancelled engine grinds through
            // the entire hint validation budget even after the portfolio deadline.
            if self.is_cancelled() {
                break;
            }
            // Check overall time budget before processing each hint.
            if hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: hint validation budget exceeded after {}/{} hints ({:?}), skipping remainder",
                        hint_idx, hint_count, hint_start.elapsed()
                    );
                }
                break;
            }

            // #7048: Skip ALL hints for predicates with fully determined initial state.
            // When all Int vars have tight init bounds, brute-force discovery already
            // found the essential invariants. Hints add redundant reformulations
            // (e.g., mod-sum combinations) that bloat frames and slow push queries.
            if all_init_determined.contains(&hint.predicate) {
                skipped_constant += 1;
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping hint for fully-determined pred {} from '{}'",
                        hint.predicate.index(),
                        hint.source,
                    );
                }
                continue;
            }

            // #7048: Skip hints where all Int variables are constant (unchanged across
            // transitions AND with tight init bounds). These are tautologies.
            if let Some(const_names) = constant_var_names.get(&hint.predicate) {
                let int_vars = hint.formula.vars();
                let int_vars: Vec<_> = int_vars
                    .iter()
                    .filter(|v| matches!(v.sort, ChcSort::Int))
                    .collect();
                if !int_vars.is_empty() && int_vars.iter().all(|v| const_names.contains(&v.name)) {
                    skipped_constant += 1;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Skipping constant-tautology hint from '{}' for pred {}",
                            hint.source,
                            hint.predicate.index(),
                        );
                    }
                    continue;
                }
            }

            if self.config.verbose {
                use std::hash::{Hash, Hasher};
                let formula_str = hint.formula.to_string();
                let mut hasher = FxHasher::default();
                formula_str.hash(&mut hasher);

                let mut chars = formula_str.chars();
                let prefix: String = chars.by_ref().take(200).collect();
                let formula_short = if chars.next().is_some() {
                    format!("{prefix}...")
                } else {
                    prefix
                };

                safe_eprintln!(
                    "PDR: validate_hint {}/{}: stage={:?} source='{}' pred {} hash={:016x} formula={}",
                    hint_idx + 1,
                    hint_count,
                    stage,
                    hint.source,
                    hint.predicate.index(),
                    hasher.finish(),
                    formula_short
                );
            }

            // Validate: hint.formula is the invariant, blocking_formula is NOT(hint.formula)
            let blocking_formula = ChcExpr::not(hint.formula.clone());

            // Determine starting level based on whether predicate has facts
            let start_level = if self.predicate_has_facts(hint.predicate) {
                0
            } else {
                1
            };

            // Try to add at the highest valid level
            let mut best_level: Option<usize> = None;
            for level in start_level..self.frames.len() {
                if hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                    break;
                }
                if self.is_inductive_blocking_uncached(&blocking_formula, hint.predicate, level) {
                    best_level = Some(level);
                }
            }

            if hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: hint validation budget exceeded during hint {}/{} ({:?}), skipping remainder",
                        hint_idx, hint_count, hint_start.elapsed()
                    );
                }
                break;
            }

            if let Some(level) = best_level {
                let self_inductive =
                    self.is_self_inductive_blocking_uncached(&blocking_formula, hint.predicate);
                // Relative-induction admission (model-checker-consumer wishlist item 6): a
                // predicate with NO self-loop clause (multi-BB loop head — the
                // loop closes through other relations) fails the self-inductive
                // check VACUOUSLY (#8578 anti-vacuous guard), even though the
                // hint may be a perfectly good invariant established by its
                // incoming edges. For those predicates the entire preservation
                // content lives on the incoming edges, which is_entry_inductive
                // below checks with predecessor frame context (relative
                // induction). Fall through to that check instead of rejecting.
                //
                // SOUNDNESS: frame lemmas only require 1-step relative
                // induction — is_inductive_blocking already passed at `level`
                // for EVERY defining clause (incl. init), so the frame stays a
                // sound over-approximation of `level`-step reachability. Final
                // Safe verdicts are re-verified by verify_model; admitted
                // lemmas are tagged relative_induction_only so they can never
                // count toward the strict `individually_inductive`
                // verification-skip (#5877) — the strict recomputation in
                // safety_proof_inductive.rs re-runs the anti-vacuous self
                // check and excludes them independently of the tag.
                // Fallthrough eligibility is deliberately NARROW (perf):
                // is_entry_inductive is an Entry-CEGAR hyperedge query, orders
                // of magnitude costlier than the rejection it replaces, and
                // hint sets are re-applied at Startup and every Stuck stage.
                // (a) ONLY user-supplied hints (config.user_hints — the
                //     model-checker-consumer wishlist case: loop invariants forwarded as
                //     LemmaHints) are eligible. Provider-discovered and
                //     lemma_pool_transfer hints (hundreds arrive on retry
                //     stages) keep the old cheap rejection — re-litigating
                //     them under entry induction regressed
                //     pdr_s_multipl_12_safe 45s->126s user CPU.
                // (b) a per-pass attempt cap bounds the added cost.
                // (c) pairs already entry-rejected in an earlier pass are
                //     skipped via the cross-pass memo.
                let relative_induction_only = !self_inductive
                    && user_hint_keys.contains(&(hint.predicate, hint.formula.clone()))
                    && relative_fallthrough_attempts < MAX_RELATIVE_INDUCTION_FALLTHROUGH
                    && !self
                        .caches
                        .entry_induction_rejected_hints
                        .contains(&(hint.predicate, hint.formula.clone()))
                    && !self.predicate_has_self_loop_clause(hint.predicate);
                if relative_induction_only {
                    relative_fallthrough_attempts += 1;
                }
                if !self_inductive && !relative_induction_only {
                    // Genuine self-loop preservation failure: keep the strict
                    // rejection (conjunctive/cross-source retries below may
                    // still combine it into a jointly inductive set).
                    cross_source_candidates
                        .entry(hint.predicate)
                        .or_default()
                        .push(hint.formula.clone());
                    conj_candidates
                        .entry((hint.predicate, hint.source))
                        .or_default()
                        .push(hint.formula);
                    rejected += 1;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Rejected hint from '{}' for pred {}: not self-inductive",
                            hint.source,
                            hint.predicate.index()
                        );
                    }
                    continue;
                }
                if relative_induction_only && self.config.verbose {
                    safe_eprintln!(
                        "PDR: hint from '{}' for pred {} has no self-loop clause; validating under relative (entry) induction",
                        hint.source,
                        hint.predicate.index()
                    );
                }

                if hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                    break;
                }

                if !self.is_entry_inductive(&hint.formula, hint.predicate, level) {
                    if relative_induction_only {
                        // Cross-pass memo: never re-pay the entry-CEGAR query
                        // for a pair already rejected in an earlier apply pass.
                        self.caches
                            .entry_induction_rejected_hints
                            .insert((hint.predicate, hint.formula.clone()));
                        // Preserve the pre-relative-admission bookkeeping: these
                        // hints previously entered the combination retries at
                        // the self-inductive rejection above.
                        cross_source_candidates
                            .entry(hint.predicate)
                            .or_default()
                            .push(hint.formula.clone());
                        conj_candidates
                            .entry((hint.predicate, hint.source))
                            .or_default()
                            .push(hint.formula);
                    }
                    rejected += 1;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Rejected hint '{}' pred {}: not entry-inductive",
                            hint.source,
                            hint.predicate.index(),
                        );
                    }
                    continue;
                }

                const MAX_HINTS_PER_PRED: usize = 10;
                let pred_hint_count = hints_per_pred.entry(hint.predicate).or_insert(0);
                if *pred_hint_count >= MAX_HINTS_PER_PRED {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Skipping hint from '{}' for pred {}: per-pred cap ({}) reached",
                            hint.source,
                            hint.predicate.index(),
                            MAX_HINTS_PER_PRED
                        );
                    }
                    continue;
                }

                if !self.frames[level].contains_lemma(hint.predicate, &hint.formula) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Adding hint from '{}' for pred {} at level {}{}: {}",
                            hint.source,
                            hint.predicate.index(),
                            level,
                            if relative_induction_only {
                                " (relative induction)"
                            } else {
                                ""
                            },
                            hint.formula
                        );
                    }
                    self.add_lemma_to_frame(
                        Lemma::new(hint.predicate, hint.formula, level)
                            .with_relative_induction_only(relative_induction_only),
                        level,
                    );
                    added += 1;
                    *pred_hint_count += 1;
                }
            } else {
                cross_source_candidates
                    .entry(hint.predicate)
                    .or_default()
                    .push(hint.formula);
                rejected += 1;
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejected hint from '{}' for pred {}: not inductive",
                        hint.source,
                        hint.predicate.index()
                    );
                }
            }
        }

        const MAX_CONJ_HINTS: usize = 8;
        for ((predicate, source), mut formulas) in conj_candidates {
            if self.is_cancelled() || hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                break;
            }
            if formulas.len() < 2 {
                continue;
            }

            formulas.sort();
            formulas.dedup();

            if formulas.len() > MAX_CONJ_HINTS {
                formulas.truncate(MAX_CONJ_HINTS);
            }

            let conj_len = formulas.len();
            let conj = ChcExpr::and_vec(formulas);
            let blocking_formula = ChcExpr::not(conj.clone());

            let start_level = usize::from(!self.predicate_has_facts(predicate));
            let mut best_level: Option<usize> = None;
            for level in start_level..self.frames.len() {
                if self.is_inductive_blocking_uncached(&blocking_formula, predicate, level) {
                    best_level = Some(level);
                }
            }

            let Some(level) = best_level else {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Conjunctive hint retry from '{}' for pred {} rejected: not inductive",
                        source,
                        predicate.index()
                    );
                }
                continue;
            };

            if !self.is_self_inductive_blocking_uncached(&blocking_formula, predicate) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Conjunctive hint retry from '{}' for pred {} rejected: not self-inductive",
                        source,
                        predicate.index()
                    );
                }
                continue;
            }

            if self.frames[level].contains_lemma(predicate, &conj) {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Adding conjunctive hint from '{}' for pred {} at level {} ({} conjuncts): {}",
                    source,
                    predicate.index(),
                    level,
                    conj_len,
                    conj
                );
            }
            self.add_lemma_to_frame(Lemma::new(predicate, conj, level), level);
            added += 1;
        }

        const MAX_CROSS_SOURCE_SIZE: usize = 3;
        if self.is_cancelled() || hint_start.elapsed() > HINT_VALIDATION_BUDGET {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: skipping cross-source combination: hint budget exceeded ({:?})",
                    hint_start.elapsed()
                );
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: apply_lemma_hints result: {} added, {} rejected, {} skipped-constant out of {} at {:?}",
                    added,
                    rejected,
                    skipped_constant,
                    hint_count,
                    stage
                );
            }
            return added;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: cross_source_candidates has {} predicates",
                cross_source_candidates.len()
            );
            for (pred, formulas) in &cross_source_candidates {
                safe_eprintln!("PDR:   pred {}: {} formulas", pred.index(), formulas.len());
            }
        }
        for (predicate, mut formulas) in cross_source_candidates {
            if self.is_cancelled() {
                break;
            }
            if formulas.len() < 2 {
                continue;
            }

            formulas.sort();
            formulas.dedup();

            if formulas.len() > 10 {
                formulas.truncate(10);
            }

            if self.config.verbose {
                let formula_strs: Vec<_> = formulas.iter().map(ToString::to_string).collect();
                safe_eprintln!(
                    "PDR: Cross-source combination for pred {}: {} candidates: {:?}",
                    predicate.index(),
                    formulas.len(),
                    formula_strs
                );
            }

            let start_level = usize::from(!self.predicate_has_facts(predicate));

            'pairs: for i in 0..formulas.len() {
                for j in (i + 1)..formulas.len() {
                    if self.is_cancelled() || hint_start.elapsed() > HINT_VALIDATION_BUDGET {
                        break 'pairs;
                    }
                    let pair = vec![formulas[i].clone(), formulas[j].clone()];
                    let conj = ChcExpr::and_vec(pair);
                    let blocking = ChcExpr::not(conj.clone());

                    let mut best_level: Option<usize> = None;
                    for level in start_level..self.frames.len() {
                        if self.is_inductive_blocking_uncached(&blocking, predicate, level) {
                            best_level = Some(level);
                        }
                    }

                    if let Some(level) = best_level {
                        if self.is_self_inductive_blocking_uncached(&blocking, predicate)
                            && !self.frames[level].contains_lemma(predicate, &conj)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Adding cross-source pair hint for pred {} at level {}: {}",
                                    predicate.index(),
                                    level,
                                    conj
                                );
                            }
                            self.add_lemma_to_frame(Lemma::new(predicate, conj, level), level);
                            added += 1;
                        }
                    }
                }
            }

            if formulas.len() >= MAX_CROSS_SOURCE_SIZE {
                'triples: for i in 0..formulas.len() {
                    for j in (i + 1)..formulas.len() {
                        for k in (j + 1)..formulas.len() {
                            if self.is_cancelled() || hint_start.elapsed() > HINT_VALIDATION_BUDGET
                            {
                                break 'triples;
                            }
                            let triple = vec![
                                formulas[i].clone(),
                                formulas[j].clone(),
                                formulas[k].clone(),
                            ];
                            let conj = ChcExpr::and_vec(triple);
                            let blocking = ChcExpr::not(conj.clone());

                            let mut best_level: Option<usize> = None;
                            for level in start_level..self.frames.len() {
                                if self.is_inductive_blocking_uncached(&blocking, predicate, level)
                                {
                                    best_level = Some(level);
                                }
                            }

                            if let Some(level) = best_level {
                                if self.is_self_inductive_blocking_uncached(&blocking, predicate)
                                    && !self.frames[level].contains_lemma(predicate, &conj)
                                {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Adding cross-source triple hint for pred {} at level {}: {}",
                                            predicate.index(),
                                            level,
                                            conj
                                        );
                                    }
                                    self.add_lemma_to_frame(
                                        Lemma::new(predicate, conj, level),
                                        level,
                                    );
                                    added += 1;
                                }
                            }
                        }
                    }
                }
            }
        }

        if self.config.verbose && (added > 0 || rejected > 0) {
            safe_eprintln!(
                "PDR: apply_lemma_hints: {} added, {} rejected",
                added,
                rejected
            );
        }

        added
    }
}
