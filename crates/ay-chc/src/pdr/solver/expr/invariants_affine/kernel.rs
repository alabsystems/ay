// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel-based affine invariant discovery using ConvexClosure.
//!
//! Contains `discover_affine_invariants_via_kernel` which uses matrix kernel
//! computation over sampled data points to discover linear equalities.

use super::super::super::invariants::discover_conditional_affine_invariants;
use super::super::super::PdrSolver;
use super::super::model_key;
use crate::convex_closure::ConvexClosure;
use crate::ChcSort;
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl PdrSolver {
    /// Discover affine invariants using ConvexClosure kernel computation.
    ///
    /// Supports both predicates with facts (sample init) and derived predicates
    /// without facts (sample entry edges, #1970).
    ///
    /// References: Z3 Spacer's global generalizer (spacer_global_generalizer.cpp:364)
    pub(in crate::pdr::solver) fn discover_affine_invariants_via_kernel(
        &mut self,
        external_budget: Option<std::time::Duration>,
    ) {
        // Wall-clock budget for kernel discovery (#3121). When running under
        // a portfolio or solve_timeout, this pass can dominate startup time
        // due to many SMT sampling queries on benchmarks with mod/ite expressions.
        // If an external budget is provided (remaining nonfixpoint budget), use
        // the minimum of the internal 1500ms default and the external cap. (#5425)
        let kernel_start = ay_core::time::Instant::now();
        let has_cancel = self.config.cancellation_token.is_some();
        let has_timeout = self.config.solve_timeout.is_some();
        let kernel_budget: Option<std::time::Duration> = if has_cancel || has_timeout {
            let internal = std::time::Duration::from_millis(1500);
            match external_budget {
                Some(ext) => Some(internal.min(ext)),
                None => Some(internal),
            }
        } else {
            external_budget
        };

        if self.config.verbose {
            safe_eprintln!(
                "PDR: kernel discovery budget={:?} (cancel={}, timeout={:?})",
                kernel_budget,
                has_cancel,
                self.config.solve_timeout,
            );
        }

        let mut predicates: Vec<_> = self.problem.predicates().to_vec();
        if kernel_budget.is_some() {
            // Spend bounded kernel time on source predicates first. Derived
            // predicates need entry-edge sampling and can consume a branch budget
            // before source equalities, such as dillig12_m's D=2*C, are available.
            predicates.sort_by_key(|pred| (!self.predicate_has_facts(pred.id), pred.id.index()));
        }

        let tiny_kernel_branch = self
            .config
            .solve_timeout
            .is_some_and(|timeout| timeout <= std::time::Duration::from_secs(2));
        let mut added_fact_predicate_invariant = false;

        for pred in &predicates {
            if kernel_budget.is_some()
                && tiny_kernel_branch
                && added_fact_predicate_invariant
                && !self.predicate_has_facts(pred.id)
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Kernel discovery stopping before derived predicates after fact-predicate progress under tiny branch budget"
                    );
                }
                break;
            }

            // Check kernel budget before processing each predicate.
            if let Some(budget) = kernel_budget {
                if kernel_start.elapsed() >= budget {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Kernel discovery budget exhausted ({:?} >= {:?}), skipping remaining predicates",
                            kernel_start.elapsed(),
                            budget
                        );
                    }
                    break;
                }
            }
            let has_facts = self.predicate_has_facts(pred.id);
            // Skip predicates with facts but unrestricted incoming transitions
            if has_facts && self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }
            // Skip predicates without facts if no incoming transitions
            if !has_facts && !self.has_any_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let int_vars: Vec<_> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int))
                .cloned()
                .collect();

            if int_vars.len() < 2 {
                continue;
            }

            let mut models = if has_facts {
                // Predicates WITH facts: sample init + forward simulation (#2042)
                let mut init_models = self.sample_init_models(pred.id, 3);
                let forward =
                    self.simulate_forward_samples_from_init_samples(pred.id, &init_models, 8);
                init_models.extend(forward);
                // Reduce reachable sampling depth when under time pressure (#3121).
                let max_level = if kernel_budget.is_some() { 2 } else { 5 };
                for level in 1..=max_level {
                    init_models.extend(self.sample_reachable_models(pred.id, level, 3));
                }
                init_models
            } else {
                // Predicates WITHOUT facts: sample entry edges (#1970)
                let mut edge_models = Vec::new();
                let max_level = if kernel_budget.is_some() { 2 } else { 3 };
                for level in 1..=max_level {
                    edge_models.extend(self.sample_entry_edge_models(pred.id, level, 5));
                }
                if !edge_models.is_empty() {
                    let forward =
                        self.simulate_forward_samples_from_init_samples(pred.id, &edge_models, 8);
                    edge_models.extend(forward);
                }
                edge_models
            };

            // Dedup models after merging init + forward + reachable samples.
            let mut seen_keys: FxHashSet<String> = FxHashSet::default();
            models.retain(|m| seen_keys.insert(model_key(m)));

            if self.config.verbose {
                let var_names: Vec<_> = int_vars.iter().map(|v| v.name.as_str()).collect();
                safe_eprintln!(
                    "PDR: Kernel discovery for pred {} (has_facts={}): {} unique samples, vars={:?}",
                    pred.id.index(),
                    has_facts,
                    models.len(),
                    var_names
                );
            }

            if models.len() < 2 {
                continue;
            }

            // Build ConvexClosure matrix
            let mut cc = ConvexClosure::new();
            cc.reset(int_vars.clone());

            for model in &models {
                // #2268: Skip samples with missing values. SMT solvers may simplify away
                // variables that are uniquely determined by constraints. Using unwrap_or(0)
                // for those would corrupt the kernel computation with false data points.
                // i128-lockstep: ConvexClosure is i64-based; treat samples with
                // values outside i64 range like incomplete models and skip them
                // (kernel candidates are verified by the admission oracle).
                let values: Option<Vec<i64>> = int_vars
                    .iter()
                    .map(|v| {
                        model
                            .get(&v.name)
                            .copied()
                            .and_then(|n| i64::try_from(n).ok())
                    })
                    .collect();
                match values {
                    Some(vals) => cc.add_data_point(&vals),
                    None => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: kernel discovery - skipping incomplete model (missing variable values)"
                            );
                        }
                    }
                }
            }

            // Compute and extract equalities
            let result = cc.compute();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: kernel for pred {}: {} equalities found: {:?}",
                    pred.id.index(),
                    result.equalities.len(),
                    result
                        .equalities
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                );
            }

            let has_inter = self.has_any_incoming_inter_predicate_transitions(pred.id);
            let mut accepted_eqs: Vec<crate::ChcExpr> = Vec::new();
            let mut rejected_eqs: Vec<crate::ChcExpr> = Vec::new();
            let mut added_this_predicate = false;

            // Phase A pass 1: classify all equalities by transition preservation.
            // This is fast (~7ms per equality) and must complete before any expensive
            // add_discovered_invariant calls. Without this separation, a single slow
            // add (e.g., 6.4s for A=B SCC check when A=B is already in frame under a
            // different structural form) exhausts the kernel budget before D=2C is
            // even checked (#5399).
            for eq in result.equalities.iter() {
                if let Some(budget) = kernel_budget {
                    let elapsed = kernel_start.elapsed();
                    if elapsed >= budget {
                        break;
                    }
                }
                // Dedup: skip equalities already in frame[1].
                if self.frames.len() > 1 && self.frames[1].contains_lemma(pred.id, eq) {
                    accepted_eqs.push(eq.clone());
                    continue;
                }

                // Check transition preservation (fast filter).
                // BUG FIX #2100: also check weakened inequality forms.
                let mut preserved =
                    self.is_chc_expr_preserved_by_transitions(pred.id, eq, &canonical_vars);
                if !preserved && has_inter {
                    if let Some(weakened) = Self::try_weaken_equality_to_inequality(eq) {
                        preserved = weakened.iter().any(|w| {
                            self.is_chc_expr_preserved_by_transitions(pred.id, w, &canonical_vars)
                        });
                    }
                }

                if preserved {
                    accepted_eqs.push(eq.clone());
                } else {
                    rejected_eqs.push(eq.clone());
                }
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: kernel Phase A classify: {} preserved, {} rejected",
                    accepted_eqs.len(),
                    rejected_eqs.len()
                );
            }

            // Phase A pass 2: add transition-preserved equalities to frames.
            // This can be slow (SCC inductiveness checks) but Phase B already has
            // the complete hypothesis set from pass 1.
            for eq in &accepted_eqs {
                if let Some(budget) = kernel_budget {
                    if kernel_start.elapsed() >= budget {
                        break;
                    }
                }
                added_this_predicate |=
                    self.add_discovered_invariant_with_weakening(pred.id, eq.clone(), 1);
            }

            // Phase B: intra-batch relative inductiveness retry (#5399).
            //
            // Some equalities are only relatively inductive: e.g., D=2C requires A=B.
            // If A=B was accepted in Phase A, retry rejected equalities using the
            // accepted equalities as explicit hypotheses. This handles the case where
            // `add_discovered_invariant_with_weakening` weakens A=B to A>=B in the frame,
            // which alone doesn't prove D=2C. The original equality form is needed.
            //
            // Phase B gets its own budget, independent of Phase A pass 2 add time.
            // Pass 2 adds can be very slow (6.4s for SCC re-verification of A=B when
            // a semantically equivalent form is already in the frame), but Phase B
            // only needs fast SMT transition checks (~7ms each). (#5399)
            let phase_b_start = ay_core::time::Instant::now();
            if !accepted_eqs.is_empty() && !rejected_eqs.is_empty() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: kernel Phase B: retrying {} rejected eqs with {} accepted hypotheses",
                        rejected_eqs.len(),
                        accepted_eqs.len(),
                    );
                }
                let mut made_progress = true;
                while made_progress && !rejected_eqs.is_empty() {
                    if let Some(budget) = kernel_budget {
                        if phase_b_start.elapsed() >= budget {
                            break;
                        }
                    }
                    made_progress = false;
                    let mut still_rejected = Vec::new();
                    for eq in rejected_eqs {
                        if let Some(budget) = kernel_budget {
                            if phase_b_start.elapsed() >= budget {
                                still_rejected.push(eq);
                                continue;
                            }
                        }
                        let mut preserved = self.is_chc_expr_preserved_by_transitions_with_hyps(
                            pred.id,
                            &eq,
                            &canonical_vars,
                            &accepted_eqs,
                        );
                        if !preserved && has_inter {
                            if let Some(weakened) = Self::try_weaken_equality_to_inequality(&eq) {
                                preserved = weakened.iter().any(|w| {
                                    self.is_chc_expr_preserved_by_transitions_with_hyps(
                                        pred.id,
                                        w,
                                        &canonical_vars,
                                        &accepted_eqs,
                                    )
                                });
                            }
                        }
                        if preserved {
                            if self.add_discovered_invariant_with_weakening(pred.id, eq.clone(), 1)
                            {
                                added_this_predicate = true;
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Retry accepted kernel invariant for pred {}: {} (relative to {} batch-mates)",
                                        pred.id.index(),
                                        eq,
                                        accepted_eqs.len(),
                                    );
                                }
                                accepted_eqs.push(eq);
                                made_progress = true;
                            } else {
                                still_rejected.push(eq);
                            }
                        } else {
                            still_rejected.push(eq);
                        }
                    }
                    rejected_eqs = still_rejected;
                }
            }

            if has_facts && added_this_predicate {
                added_fact_predicate_invariant = true;
            }

            // (#3121) Skip divisibility and conditional affine phases when under time pressure.
            // These phases involve many SMT preservation checks (each up to 200ms) that can
            // collectively dominate startup time on benchmarks with mod/ite constraints.
            // The kernel equalities above are the primary discovery; these are supplementary.
            if kernel_budget.is_none() {
                // Phase 1 of parity-aware affine synthesis: discover divisibility patterns
                // from sampled values. This supplements kernel-discovered equalities with
                // modular constraints like (var mod 2) = 0.
                //
                // Reference: Z3 Spacer's infer_div_pred (spacer_convex_closure.cpp:254-291)
                // Part of #1615 fix for CHC regression.
                self.discover_divisibility_invariants_from_samples(pred.id, &int_vars, &models);

                // Phase 2 of parity-aware affine synthesis: partitioned kernel synthesis for
                // parity-conditional affine invariants (Phase 2 design: #1945).
                for inv in discover_conditional_affine_invariants(&int_vars, &models) {
                    let inv_expr = inv.to_expr(&int_vars);
                    if self.is_chc_expr_preserved_by_transitions(
                        pred.id,
                        &inv_expr,
                        &canonical_vars,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Kernel-discovered conditional affine invariant for pred {}: {}",
                                pred.id.index(),
                                inv_expr
                            );
                        }
                        // BUG FIX #2100: Use weakening for conditional invariants too
                        self.add_discovered_invariant_with_weakening(pred.id, inv_expr, 1);
                    }
                }
            }
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: discover_affine_invariants_via_kernel took {:?}",
                kernel_start.elapsed()
            );
        }
    }
}
