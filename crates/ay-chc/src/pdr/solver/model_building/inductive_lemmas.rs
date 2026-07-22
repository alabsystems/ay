// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model building from inductiveness-filtered lemmas.
//!
//! Contains `build_model_from_inductive_lemmas` (self-inductive filter)
//! and `build_model_from_entry_inductive_lemmas` (entry-inductive filter).

use super::super::{PdrSolver, PredicateId};
use crate::smt::SmtResult;
use crate::{ChcExpr, InvariantModel, Predicate, PredicateInterpretation};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    fn build_model_from_selected_invariants(
        &self,
        predicates: &[Predicate],
        pred_invariants: &FxHashMap<PredicateId, Vec<ChcExpr>>,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in predicates {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();
            let formulas = pred_invariants.get(&pred.id).cloned().unwrap_or_default();
            let formula = if formulas.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::and_all(formulas)
            };
            let formula = Self::filter_non_canonical_conjuncts(&formula, &vars);
            model.set(pred.id, PredicateInterpretation::new(vars, formula));
        }
        model
    }

    fn invariant_holds_on_selected_model(
        &mut self,
        invariant: &ChcExpr,
        predicate: PredicateId,
        model: &InvariantModel,
    ) -> bool {
        let clauses: Vec<_> = self.problem.clauses_defining(predicate).cloned().collect();

        for clause in &clauses {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };
            let Some(inv_on_head) = self.apply_to_args(predicate, invariant, head_args) else {
                return false;
            };
            let Some(body_under_model) = self.clause_body_under_model(&clause.body, model) else {
                return false;
            };

            let query =
                self.bound_int_vars(ChcExpr::and(body_under_model, ChcExpr::not(inv_on_head)));
            if crate::pdr::cube::is_trivial_contradiction(&query) {
                continue;
            }

            let (result, _) =
                Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
            match result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
            }
        }

        true
    }

    fn prune_entry_model_lemmas(
        &mut self,
        predicates: &[Predicate],
        pred_invariants: &mut FxHashMap<PredicateId, Vec<ChcExpr>>,
    ) {
        loop {
            let model = self.build_model_from_selected_invariants(predicates, pred_invariants);
            let mut to_remove: Vec<(PredicateId, ChcExpr)> = Vec::new();

            for pred in predicates {
                let predicate = pred.id;
                let invariants = pred_invariants.get(&predicate).cloned().unwrap_or_default();
                for invariant in invariants {
                    if !self.invariant_holds_on_selected_model(&invariant, predicate, &model) {
                        to_remove.push((predicate, invariant));
                    }
                }
            }

            if to_remove.is_empty() {
                break;
            }

            for (predicate, invariant) in to_remove {
                if let Some(invariants) = pred_invariants.get_mut(&predicate) {
                    let before = invariants.len();
                    invariants.retain(|candidate| candidate != &invariant);
                    if before != invariants.len() && self.config.verbose {
                        safe_eprintln!(
                            "PDR: build_model_from_entry_inductive_lemmas: filtering model-invalid lemma for pred {}: {}",
                            predicate.index(),
                            invariant
                        );
                    }
                }
            }
        }
    }

    /// Build a model from only inductive lemmas.
    ///
    /// This filters out lemmas that aren't inductive (e.g., optimistic init bounds
    /// like `B > A` that aren't preserved by transitions). Such lemmas can cause
    /// model verification to fail even when the core invariants are correct.
    ///
    /// For each lemma at level L, we check `is_inductive_blocking(formula, predicate, L)`.
    /// Only lemmas that pass this check are included in the model.
    ///
    /// For cyclic SCC predicates, we trust that lemmas were verified when added:
    /// - SCC-strengthened lemmas were jointly verified in try_scc_strengthening
    /// - Other lemmas were verified individually before being added
    ///
    /// We don't re-verify them jointly here because that would combine unrelated
    /// lemmas (e.g., optimistic bounds that aren't init-valid) with SCC lemmas.
    pub(in crate::pdr::solver) fn build_model_from_inductive_lemmas(
        &mut self,
        frame_idx: usize,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();

        // First, collect all predicates and their lemmas to avoid borrow issues
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect all lemmas by predicate (no longer separating SCC vs non-SCC)
        let mut pred_lemmas: FxHashMap<PredicateId, Vec<(ChcExpr, usize, bool)>> =
            FxHashMap::default();

        for pred in &predicates {
            for frame_level in 1..=frame_idx {
                if frame_level >= self.frames.len() {
                    break;
                }
                for lemma in &self.frames[frame_level].lemmas {
                    if lemma.predicate == pred.id {
                        pred_lemmas.entry(pred.id).or_default().push((
                            lemma.formula.clone(),
                            lemma.level,
                            lemma.algebraically_verified,
                        ));
                    }
                }
            }
        }

        // Track which invariants to include for each predicate
        let mut pred_invariants: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        // Process all lemmas with individual inductiveness check
        // For SCC predicates, we also try a relaxed check that assumes other SCC predicates
        // have their lemmas
        for (predicate, lemmas) in pred_lemmas {
            let in_cyclic_scc =
                if let Some(&scc_idx) = self.scc_info.predicate_to_scc.get(&predicate) {
                    let scc = &self.scc_info.sccs[scc_idx];
                    scc.is_cyclic && scc.predicates.len() > 1
                } else {
                    false
                };

            for (invariant, level, algebraically_verified) in lemmas {
                // Check for error-implied invariants first. These have the form:
                // (or (not guard) conclusion) and are syntactically implied by error
                // clauses. They should be included without inductiveness checks.
                // See discover_error_implied_invariants() in invariant_discovery.rs.
                if Self::is_error_implied_invariant(&invariant) {
                    let entry = pred_invariants.entry(predicate).or_default();
                    if !entry.iter().any(|f| f == &invariant) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: build_model_from_inductive_lemmas: including error-implied invariant for pred {}: {}",
                                predicate.index(), invariant
                            );
                        }
                        entry.push(invariant);
                    }
                    continue;
                }

                // Keep algebraically-verified lemmas without re-running strict SMT checks.
                // These lemmas were already validated when inserted into frames (init/entry
                // checks in add_discovered_invariant_impl + algebraic preservation proof),
                // and strict self-inductiveness can reject them spuriously (#3183).
                if algebraically_verified {
                    let entry = pred_invariants.entry(predicate).or_default();
                    if !entry.iter().any(|f| f == &invariant) {
                        entry.push(invariant);
                    }
                    continue;
                }

                // Lemma.formula is the INVARIANT (states to keep).
                // is_inductive_blocking expects the BLOCKING formula (states to block).
                let blocking_formula = ChcExpr::not(invariant.clone());

                // Use is_strictly_self_inductive_blocking - NO frame strengthening.
                // The non-strict version retries with frame[1] lemmas on failure, which
                // allows lemmas that depend on other (potentially non-inductive) frame
                // lemmas to pass. This causes model verification failures on
                // multi-predicate benchmarks (e.g., s_multipl_09) where spurious bounds
                // pass self-inductive checks via frame strengthening but fail
                // inter-predicate transition checks.
                //
                // Part of #2059.
                let _ = level; // Unused now that we use self-inductive check
                if self.is_strictly_self_inductive_blocking(&blocking_formula, predicate) {
                    // #2375: Also check init validity for predicates with facts.
                    // A lemma like `B >= 1` is self-inductive (preserved by B++ transition)
                    // but false at init (B=0). Including it in the model causes
                    // verify_model to fail on init clauses.
                    if self.predicate_has_facts(predicate)
                        && !self.blocks_initial_states(predicate, &blocking_formula)
                    {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: build_model_from_inductive_lemmas: filtering init-invalid lemma for pred {}: {}",
                                predicate.index(), invariant
                            );
                        }
                        // Don't include - it's self-inductive but not init-valid
                    } else {
                        let entry = pred_invariants.entry(predicate).or_default();
                        if !entry.iter().any(|f| f == &invariant) {
                            entry.push(invariant);
                        }
                    }
                    continue;
                }

                // For SCC predicates, try a relaxed check: the lemma may only be inductive
                // when assuming other SCC predicates have their lemmas. This is the case
                // for lemmas added via try_scc_strengthening.
                if in_cyclic_scc {
                    // Check if this lemma holds at init states (for predicates with facts)
                    let init_valid = if self.predicate_has_facts(predicate) {
                        self.blocks_initial_states(predicate, &blocking_formula)
                    } else {
                        true // No facts means no init constraint to satisfy
                    };

                    if init_valid {
                        // Lemma is init-valid, include it (joint inductiveness was verified
                        // when it was added via try_scc_strengthening)
                        let entry = pred_invariants.entry(predicate).or_default();
                        if !entry.iter().any(|f| f == &invariant) {
                            entry.push(invariant);
                        }
                        continue;
                    }
                }

                // Lemma failed all checks - filter it out
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: build_model_from_inductive_lemmas: filtering non-inductive lemma for pred {}: {}",
                        predicate.index(), invariant
                    );
                }
            }
        }

        // Build the final model
        for pred in predicates {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();

            let inductive_formulas = pred_invariants.remove(&pred.id).unwrap_or_default();

            let formula = if inductive_formulas.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::and_all(inductive_formulas)
            };

            // #7146: Filter conjuncts with non-canonical (witness) variables
            let formula = Self::filter_non_canonical_conjuncts(&formula, &vars);

            let interp = PredicateInterpretation::new(vars, formula);
            model.set(pred.id, interp);
        }

        model
    }

    /// Build model from entry-inductive lemmas only.
    ///
    /// More conservative than `build_model_from_inductive_lemmas`: requires each lemma
    /// to be strictly self-inductive AND entry-inductive (preserved by inter-predicate
    /// transitions). This filters out lemmas that are self-inductive on self-loops but
    /// violated by transitions from other predicates.
    ///
    /// Part of #2059.
    pub(in crate::pdr::solver) fn build_model_from_entry_inductive_lemmas(
        &mut self,
        level: usize,
    ) -> InvariantModel {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        let mut pred_invariants: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        for pred in &predicates {
            let predicate = pred.id;

            // Get frame lemmas
            let lemmas: Vec<_> = if level < self.frames.len() {
                self.frames[level]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == predicate)
                    .cloned()
                    .collect()
            } else {
                vec![]
            };

            for lemma in &lemmas {
                // FrameLemma.formula is the INVARIANT (states to keep).
                // The blocking formula is NOT(invariant).
                let invariant = lemma.formula.clone();
                let blocking_formula = ChcExpr::not(invariant.clone());

                // D1 (#5970): Removed strict self-inductiveness filter.
                // Standard IC3/PDR frame convergence proves relative inductiveness
                // (lemma ∧ Frame[k] ∧ T ⟹ lemma'). Requiring strict self-inductiveness
                // (lemma ∧ T ⟹ lemma') filters out valid relatively-inductive lemmas,
                // weakening the model below the inductiveness threshold. Golem uses ALL
                // frame components at the inductive level without filtering.
                // Reference: Golem Spacer.cc:274 getComponents(vid, inductiveLevel).

                // Check 1: init-valid for predicates with facts
                if self.predicate_has_facts(predicate)
                    && !self.blocks_initial_states(predicate, &blocking_formula)
                {
                    continue;
                }

                // Check 2: entry-inductive (preserved by inter-predicate transitions)
                if !self.is_entry_inductive(&invariant, predicate, level) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: build_model_from_entry_inductive_lemmas: filtering non-entry-inductive lemma for pred {}: {}",
                            predicate.index(), invariant
                        );
                    }
                    continue;
                }

                let entry = pred_invariants.entry(predicate).or_default();
                if !entry.iter().any(|f| f == &invariant) {
                    entry.push(invariant);
                }
            }
        }

        self.prune_entry_model_lemmas(&predicates, &mut pred_invariants);

        // Build the final model
        self.build_model_from_selected_invariants(&predicates, &pred_invariants)
    }
}
