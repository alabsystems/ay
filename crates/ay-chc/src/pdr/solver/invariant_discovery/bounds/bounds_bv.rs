// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV/Int range invariant discovery with joint fixpoint (#5877).
//!
//! Discovers mutually-dependent Boolean clause + comparison atom invariants.
//! Works on both BV-native problems (bvsle atoms) and BvToInt-relaxed problems
//! (Int bound atoms). The joint fixpoint loop adds ALL init-valid candidates
//! tentatively, then checks each with the full set present — enabling discovery
//! of clauses like `(A ∨ ¬B)` and `(¬A ∨ V >= 1)` that are only inductive
//! together.

use super::super::super::PdrSolver;
use crate::pdr::frame::Lemma;
use crate::{ChcExpr, ChcOp, ChcSort};
use std::sync::Arc;

const BV_DISCOVERY_SMT_TIMEOUT_SECS: u64 = 1;
const BV_DISCOVERY_BUDGET_SECS: u64 = 3;

impl PdrSolver {
    /// Discover range invariants via joint fixpoint on BV or BvToInt-relaxed problems.
    ///
    /// Generates candidate invariants (BV comparisons for BV-native, Int bounds for
    /// BvToInt-relaxed), Boolean pair clauses, and Bool→comparison implications.
    /// Uses a two-phase approach: Phase 1 tries each candidate individually, Phase 2
    /// runs a joint fixpoint loop for mutually-dependent candidates.
    pub(in crate::pdr::solver) fn discover_bv_range_invariants(&mut self) {
        // #5877: BV self-inductiveness queries need more than the 2s default
        // per-call timeout in check_sat_with_ite_case_split. BV bit-blasting +
        // CDCL routinely exceeds 2s but resolves within 5s. Without this, all
        // discovery candidates are rejected as "not self-inductive" due to
        // Unknown (timeout) being treated as failure.
        let _bv_discovery_timeout = if !self.problem_is_pure_lia {
            Some(
                self.smt
                    .scoped_check_timeout(Some(std::time::Duration::from_secs(
                        BV_DISCOVERY_SMT_TIMEOUT_SECS,
                    ))),
            )
        } else {
            None
        };

        // #5877: Time budget for BV discovery. BV-native problems (not pure LIA)
        // have expensive BV bit-blasting SMT calls. Without a budget, the
        // combinatorial candidate explosion (O(n^2) Bool pairs + O(n*m)
        // Bool→comparison implications) can consume the entire solve timeout
        // before PDR blocking even starts.
        //
        // For BV-native problems, the joint fixpoint discovery is the primary
        // mechanism for finding compact invariants (matching Z3 Spacer's approach).
        // The 500ms budget was too tight — BV bit-blasting + CDCL per candidate
        // routinely needs 10-20ms, and 82+ candidates need testing. Increased to
        // 2s to allow the joint fixpoint to complete at least one round while
        // leaving time for blocking phase.
        let bv_discovery_deadline = if !self.problem_is_pure_lia {
            Some(
                ay_core::time::Instant::now()
                    + std::time::Duration::from_secs(BV_DISCOVERY_BUDGET_SECS),
            )
        } else {
            None
        };

        let predicates = self.problem.predicates().to_vec();
        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if bv_discovery_deadline.map_or(false, |d| ay_core::time::Instant::now() > d) {
                if self.config.verbose {
                    safe_eprintln!("PDR: #5877 BV discovery time budget exhausted, skipping remaining predicates");
                }
                return;
            }
            self.discover_bv_range_invariants_for_pred(pred.id, bv_discovery_deadline);
            if self.is_cancelled() {
                return;
            }
        }
    }

    pub(in crate::pdr::solver) fn rerun_bv_range_invariants_for_pred(
        &mut self,
        pred_id: crate::PredicateId,
    ) {
        let Some(canonical_vars) = self.canonical_vars(pred_id) else {
            return;
        };
        if !canonical_vars
            .iter()
            .any(|var| matches!(var.sort, ChcSort::BitVec(_)))
        {
            return;
        }

        let _bv_discovery_timeout = if !self.problem_is_pure_lia {
            Some(
                self.smt
                    .scoped_check_timeout(Some(std::time::Duration::from_secs(
                        BV_DISCOVERY_SMT_TIMEOUT_SECS,
                    ))),
            )
        } else {
            None
        };
        let deadline = Some(
            ay_core::time::Instant::now()
                + std::time::Duration::from_secs(BV_DISCOVERY_BUDGET_SECS),
        );

        if self.config.verbose {
            safe_eprintln!(
                "PDR: #5877 rerunning BV discovery for pred {} after blocked-state seeds",
                pred_id.index()
            );
        }
        self.discover_bv_range_invariants_for_pred(pred_id, deadline);
    }

    fn discover_bv_range_invariants_for_pred(
        &mut self,
        pred_id: crate::PredicateId,
        bv_discovery_deadline: Option<ay_core::time::Instant>,
    ) {
        let canonical_vars = match self.canonical_vars(pred_id) {
            Some(vars) => vars.to_vec(),
            None => return,
        };

        let bool_vars: Vec<_> = canonical_vars
            .iter()
            .filter(|var| matches!(var.sort, ChcSort::Bool))
            .cloned()
            .collect();

        let has_bv_vars = canonical_vars
            .iter()
            .any(|v| matches!(v.sort, ChcSort::BitVec(_)));
        let comparison_atoms = if has_bv_vars {
            self.extract_bv_candidate_invariants(pred_id, &canonical_vars)
        } else if self.problem_is_pure_lia && !bool_vars.is_empty() {
            self.extract_int_bound_candidates(pred_id, &canonical_vars)
        } else {
            return;
        };

        if comparison_atoms.is_empty() && bool_vars.is_empty() {
            return;
        }

        let mut candidates = comparison_atoms.clone();
        let mut seen_candidates: ay_core::kani_compat::DetHashSet<String> =
            candidates.iter().map(|c| format!("{c}")).collect();

        if has_bv_vars {
            let clause_seeds = self.extract_bv_clause_seeds(pred_id, &canonical_vars);

            for seed in &clause_seeds {
                if (2..=8).contains(&seed.bool_vars.len()) {
                    for i in 0..seed.bool_vars.len() {
                        for j in (i + 1)..seed.bool_vars.len() {
                            for &(neg_i, neg_j) in
                                &[(true, true), (true, false), (false, true), (false, false)]
                            {
                                let lit_i = if neg_i {
                                    ChcExpr::not(ChcExpr::var(seed.bool_vars[i].clone()))
                                } else {
                                    ChcExpr::var(seed.bool_vars[i].clone())
                                };
                                let lit_j = if neg_j {
                                    ChcExpr::not(ChcExpr::var(seed.bool_vars[j].clone()))
                                } else {
                                    ChcExpr::var(seed.bool_vars[j].clone())
                                };
                                let clause =
                                    ChcExpr::Op(ChcOp::Or, vec![Arc::new(lit_i), Arc::new(lit_j)]);
                                let key = format!("{clause}");
                                if seen_candidates.insert(key) {
                                    candidates.push(clause);
                                }
                            }
                        }
                    }
                }

                if !seed.comparison_atoms.is_empty() && seed.bool_vars.len() <= 8 {
                    for bool_var in &seed.bool_vars {
                        for atom in &seed.comparison_atoms {
                            let neg_impl = ChcExpr::Op(
                                ChcOp::Or,
                                vec![
                                    Arc::new(ChcExpr::not(ChcExpr::var(bool_var.clone()))),
                                    Arc::new(atom.clone()),
                                ],
                            );
                            let key = format!("{neg_impl}");
                            if seen_candidates.insert(key) {
                                candidates.push(neg_impl);
                            }
                            let pos_impl = ChcExpr::Op(
                                ChcOp::Or,
                                vec![
                                    Arc::new(ChcExpr::var(bool_var.clone())),
                                    Arc::new(atom.clone()),
                                ],
                            );
                            let key = format!("{pos_impl}");
                            if seen_candidates.insert(key) {
                                candidates.push(pos_impl);
                            }
                        }
                    }
                }
            }
        } else {
            if (2..=8).contains(&bool_vars.len()) {
                for i in 0..bool_vars.len() {
                    for j in (i + 1)..bool_vars.len() {
                        for &(neg_i, neg_j) in
                            &[(true, true), (true, false), (false, true), (false, false)]
                        {
                            let lit_i = if neg_i {
                                ChcExpr::not(ChcExpr::var(bool_vars[i].clone()))
                            } else {
                                ChcExpr::var(bool_vars[i].clone())
                            };
                            let lit_j = if neg_j {
                                ChcExpr::not(ChcExpr::var(bool_vars[j].clone()))
                            } else {
                                ChcExpr::var(bool_vars[j].clone())
                            };
                            candidates.push(ChcExpr::Op(
                                ChcOp::Or,
                                vec![Arc::new(lit_i), Arc::new(lit_j)],
                            ));
                        }
                    }
                }
            }

            if !comparison_atoms.is_empty() && bool_vars.len() <= 8 && comparison_atoms.len() <= 10
            {
                for bool_var in &bool_vars {
                    for atom in &comparison_atoms {
                        candidates.push(ChcExpr::Op(
                            ChcOp::Or,
                            vec![
                                Arc::new(ChcExpr::not(ChcExpr::var(bool_var.clone()))),
                                Arc::new(atom.clone()),
                            ],
                        ));
                        candidates.push(ChcExpr::Op(
                            ChcOp::Or,
                            vec![
                                Arc::new(ChcExpr::var(bool_var.clone())),
                                Arc::new(atom.clone()),
                            ],
                        ));
                    }
                }
            }
        }

        let mut init_valid_candidates = Vec::new();
        let mut phase1_accepted = 0usize;
        let mut phase1_init_valid = 0usize;
        let mut phase1_not_init_valid = 0usize;
        for candidate in &candidates {
            if self.is_cancelled() {
                return;
            }
            if bv_discovery_deadline.map_or(false, |d| ay_core::time::Instant::now() > d) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #5877 BV Phase 1 time budget exhausted for pred {}",
                        pred_id.index()
                    );
                }
                break;
            }

            if self.add_discovered_invariant(pred_id, candidate.clone(), 1) {
                phase1_accepted += 1;
                continue;
            }

            let blocking = ChcExpr::not(candidate.clone());
            if self.blocks_initial_states(pred_id, &blocking) {
                phase1_init_valid += 1;
                init_valid_candidates.push(candidate.clone());
            } else {
                phase1_not_init_valid += 1;
            }
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: BV Phase 1 for pred {}: {} candidates, {} accepted, {} init-valid (for joint), {} not-init-valid",
                pred_id.index(),
                candidates.len(),
                phase1_accepted,
                phase1_init_valid,
                phase1_not_init_valid,
            );
        }

        if init_valid_candidates.is_empty() || self.is_cancelled() {
            return;
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: BV joint fixpoint starting with {} init-valid candidates for pred {}",
                init_valid_candidates.len(),
                pred_id.index()
            );
        }

        let mut accepted = vec![false; init_valid_candidates.len()];
        let frame_lemma_count_before = self.frames.get(1).map_or(0, |frame| frame.lemmas.len());

        for round in 0..10 {
            if self.is_cancelled() {
                break;
            }
            if bv_discovery_deadline.map_or(false, |d| ay_core::time::Instant::now() > d) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #5877 BV Phase 2 time budget exhausted for pred {}",
                        pred_id.index()
                    );
                }
                break;
            }

            let accepted_before = accepted.iter().filter(|a| **a).count();

            for (i, candidate) in init_valid_candidates.iter().enumerate() {
                if !accepted[i] {
                    self.add_lemma_to_frame(Lemma::new(pred_id, candidate.clone(), 1), 1);
                }
            }

            for (i, candidate) in init_valid_candidates.iter().enumerate() {
                if accepted[i] {
                    continue;
                }
                if self.is_cancelled() {
                    break;
                }

                let blocking = ChcExpr::not(candidate.clone());
                if self.is_self_inductive_blocking(&blocking, pred_id) {
                    accepted[i] = true;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: BV joint fixpoint accepted candidate {}: {}",
                            i,
                            candidate,
                        );
                    }
                }
            }

            self.rollback_joint_bv_candidates(
                pred_id,
                frame_lemma_count_before,
                &init_valid_candidates,
                &accepted,
            );

            let accepted_after = accepted.iter().filter(|a| **a).count();
            let new_acceptances = accepted_after - accepted_before;

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: BV joint fixpoint round {}: {} accepted ({} new), {} total candidates",
                    round,
                    accepted_after,
                    new_acceptances,
                    init_valid_candidates.len()
                );
            }

            if new_acceptances == 0 || accepted.iter().all(|a| *a) {
                break;
            }
        }

        if !accepted.iter().any(|accepted| *accepted) {
            if let Some(frame) = self.frames.get_mut(1) {
                frame.truncate_lemmas(frame_lemma_count_before);
            }
        }
    }

    fn rollback_joint_bv_candidates(
        &mut self,
        pred_id: crate::PredicateId,
        frame_lemma_count_before: usize,
        init_valid_candidates: &[ChcExpr],
        accepted: &[bool],
    ) {
        if let Some(frame) = self.frames.get_mut(1) {
            frame.truncate_lemmas(frame_lemma_count_before);
        }
        for (index, candidate) in init_valid_candidates.iter().enumerate() {
            if accepted[index] {
                self.add_lemma_to_frame(Lemma::new(pred_id, candidate.clone(), 1), 1);
            }
        }
    }
}
