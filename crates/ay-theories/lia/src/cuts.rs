// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! HNF (Hermite Normal Form) cutting plane methods for LIA.
//!
//! These cuts work on the original constraint matrix, avoiding the slack variable
//! issues that plague Gomory cuts from the simplex tableau.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use tracing::{debug, info};

use crate::hnf;
use crate::{HnfCutKey, LiaSolver, StoredCut};

impl LiaSolver<'_> {
    /// #C7: Mark `key` as a seen HNF cut, trailing it for per-scope undo.
    ///
    /// When a scope is open the key is appended to `seen_hnf_cuts_trail` so
    /// `pop()` removes exactly the keys inserted in the popped scope, restoring
    /// the outer scope's `seen_hnf_cuts` (#3685) without cloning the whole set
    /// on every push. Inserts made at scope depth 0 are permanent and stay off
    /// the trail. Callers must have confirmed the key is absent.
    pub(crate) fn record_seen_hnf_cut(&mut self, key: HnfCutKey) {
        if self.cut_state_scopes.is_empty() {
            self.seen_hnf_cuts.insert(key);
        } else {
            self.seen_hnf_cuts.insert(key.clone());
            self.seen_hnf_cuts_trail.push(key);
        }
    }

    ///
    /// HNF cuts work on the original constraint matrix, avoiding the slack variable
    /// issues that plague Gomory cuts. They're generated when:
    /// 1. The LRA relaxation is SAT with non-integer values
    /// 2. Gomory cuts failed (typically due to slack variables in the tableau)
    ///
    /// Returns true if cuts were generated and added.
    pub(crate) fn try_hnf_cuts(&mut self, _fractional_var: TermId) -> bool {
        // HNF cuts re-enabled after algorithm fixes (#1062):
        // - Floor-before-scale ordering fixed (commit 45ca9412)
        // - Zero diagonal handling fixed (commit 59aad2a6)
        // - Divisibility check added (commit 59aad2a6)
        // - Only processes equalities (not inequalities) to avoid tight-bound bugs
        {
            let debug = self.debug_hnf;

            if self.hnf_iterations >= self.max_hnf_iterations {
                if debug {
                    safe_eprintln!("[HNF] Max iterations reached");
                }
                return false;
            }

            // Dimension gate (#hnf-dimension-gate): the Bareiss determinant
            // threshold is abs_max^6, calibrated for the productive 4-8-row
            // regime; a large matrix deterministically overflows it and
            // yields ZERO cuts after O(m*n) BigInt work (observed: 824x1259
            // from u64 range guards, ~0.7s per rebuild, 41 rebuilds = a 30s
            // timeout). Skip upfront — HNF cuts are a pure optimization.
            let eq_count = self.assertion_view().positive_equalities.len();
            let est_rows = eq_count.saturating_mul(2);
            let view_epoch = self.assertion_view_cache.epoch();
            let (term_to_idx, idx_to_term) = self.build_var_index();
            let n_vars = idx_to_term.len();
            if est_rows > 128 || n_vars > 512 || est_rows.saturating_mul(n_vars) > 32_768 {
                if debug {
                    safe_eprintln!("[HNF] matrix too large ({est_rows}x{n_vars}), skipping");
                }
                return false;
            }
            // Barren-attempt memo: same view epoch + dims already produced
            // zero cuts — do not rebuild the matrix to fail identically.
            if self.hnf_barren_fingerprint == Some((view_epoch, est_rows, n_vars)) {
                if debug {
                    safe_eprintln!("[HNF] barren fingerprint hit, skipping");
                }
                return false;
            }

            // Build HNF cutter from asserted equality constraints
            let mut cutter = hnf::HnfCutter::new();
            for idx in 0..idx_to_term.len() {
                cutter.register_var(idx);
            }

            // Track asserted equalities for soundness checking.
            // We need to reject any HNF cut that contradicts an equality.
            let mut asserted_equalities: Vec<(Vec<(usize, BigInt)>, BigInt)> = Vec::new();

            // Collect equality atom TermIds for proper reason tracking (#5388).
            // All equalities contribute to the HNF constraint matrix, so every
            // HNF cut depends on all of them.
            let mut equality_reasons: Vec<(TermId, bool)> = Vec::new();

            // Collect constraints from asserted literals
            // SOUNDNESS FIX (#1054): Only include explicit equalities, NOT tight inequalities.
            // Tight inequalities from the LP solution may include bounds added during
            // branch-and-bound. HNF cuts derived from those bounds are only valid in that
            // branch, but the cuts were being persisted globally. This caused unsound
            // results when backtracking to explore other branches.
            //
            // Conservative approach: only generate HNF cuts from original equalities.
            // This is less powerful but always sound.
            for &literal in &self.assertion_view().positive_equalities {
                let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                    continue;
                };

                if args.len() != 2 {
                    continue;
                }

                // Only process equalities - skip inequalities for soundness
                if name.as_str() != "=" {
                    continue;
                }

                // Track this equality atom as a reason for all HNF cuts (#5388).
                equality_reasons.push((literal, true));

                // Equality constraint - always tight
                let (var_coeffs, constant) =
                    self.parse_equality_for_hnf(args[0], args[1], &term_to_idx);

                if var_coeffs.is_empty() {
                    continue;
                }

                // Track this equality for soundness checking
                asserted_equalities.push((var_coeffs.clone(), constant.clone()));

                // Add as upper bound constraint (lhs = constant means lhs <= constant)
                cutter.add_constraint(&var_coeffs, constant.clone(), true);
                // And lower bound (lhs >= constant)
                cutter.add_constraint(&var_coeffs, constant, false);
            }

            if !cutter.has_constraints() {
                if debug {
                    safe_eprintln!("[HNF] No equality constraints to generate cuts from");
                }
                return false;
            }

            // Generate cuts
            let cuts = cutter.generate_cuts();

            if cuts.is_empty() {
                if debug {
                    safe_eprintln!("[HNF] No cuts generated");
                }
                self.hnf_barren_fingerprint = Some((view_epoch, est_rows, n_vars));
                return false;
            }

            if debug {
                safe_eprintln!("[HNF] Generated {} cuts", cuts.len());
            }

            // Pre-sort equality coefficients once before the cut loop (#3077).
            // Avoids O(C * E * V * log(V)) redundant clone+sort work.
            let sorted_equalities: Vec<(Vec<(usize, BigInt)>, BigInt)> = asserted_equalities
                .iter()
                .map(|(coeffs, constant)| {
                    let mut sorted = coeffs.clone();
                    sorted.sort_by_key(|(idx, _)| *idx);
                    (sorted, constant.clone())
                })
                .collect();

            // Convert HNF cuts to LRA bounds
            let mut added_any = false;
            let mut cuts_considered = 0usize;
            'cut_loop: for cut in cuts {
                cuts_considered += 1;
                // SOUNDNESS CHECK (#1054): Reject cuts that contradict asserted equalities.
                // If an equality Σ c_i * x_i = B is asserted, we must not add a cut
                // Σ c_i * x_i <= b where b < B, as this would make the system unsound.
                //
                // The HNF algorithm can generate such invalid cuts when the matrix basis
                // selection drops constraints, leading to cuts from a subspace that doesn't
                // respect the full constraint structure.
                let mut cut_coeffs_sorted: Vec<(usize, BigInt)> = cut.coeffs.clone();
                cut_coeffs_sorted.sort_by_key(|(idx, _)| *idx);

                for (eq_coeffs_sorted, eq_constant) in &sorted_equalities {
                    // Check if coefficients match (possibly with scaling)
                    if cut_coeffs_sorted.len() == eq_coeffs_sorted.len() {
                        // Check if they're proportional
                        let mut scale: Option<BigRational> = None;
                        let mut is_proportional = true;

                        for ((cut_idx, cut_coeff), (eq_idx, eq_coeff)) in
                            cut_coeffs_sorted.iter().zip(eq_coeffs_sorted.iter())
                        {
                            if cut_idx != eq_idx {
                                is_proportional = false;
                                break;
                            }
                            if eq_coeff.is_zero() {
                                if !cut_coeff.is_zero() {
                                    is_proportional = false;
                                    break;
                                }
                                continue;
                            }

                            let ratio = BigRational::new(cut_coeff.clone(), eq_coeff.clone());
                            match &scale {
                                None => scale = Some(ratio),
                                Some(s) if *s != ratio => {
                                    is_proportional = false;
                                    break;
                                }
                                Some(_) => {}
                            }
                        }

                        if is_proportional {
                            if let Some(s) = scale {
                                // The cut is: (s * eq_coeffs) * x <= cut.bound
                                // Which is: eq_coeffs * x <= cut.bound / s
                                // The equality requires: eq_coeffs * x = eq_constant
                                // So we need cut.bound / s >= eq_constant, otherwise unsound
                                let scaled_bound = BigRational::from(cut.bound.clone()) / &s;
                                let eq_const_rat = BigRational::from(eq_constant.clone());

                                if s.is_positive() && scaled_bound < eq_const_rat {
                                    // Cut contradicts equality! Skip this cut.
                                    if debug {
                                        safe_eprintln!(
                                        "[HNF] Rejecting cut that contradicts equality: bound {} < {} (scale={})",
                                        scaled_bound, eq_const_rat, s
                                    );
                                    }
                                    continue 'cut_loop;
                                }
                                if s.is_negative() && scaled_bound > eq_const_rat {
                                    // Negated coefficients - reversed inequality direction
                                    if debug {
                                        safe_eprintln!(
                                        "[HNF] Rejecting cut that contradicts equality (negated): bound {} > {} (scale={})",
                                        scaled_bound, eq_const_rat, s
                                    );
                                    }
                                    continue 'cut_loop;
                                }
                            }
                        }
                    }
                }

                // Convert coefficients from term indices to TermIds
                let mut term_coeffs_int: Vec<(TermId, BigInt)> = Vec::new();
                let mut lra_coeffs: Vec<(u32, BigRational)> = Vec::new();
                let mut term_coeffs: Vec<(TermId, BigRational)> = Vec::new();

                for (var_idx, coeff) in &cut.coeffs {
                    let Some(&tid) = idx_to_term.get(*var_idx) else {
                        continue;
                    };
                    term_coeffs_int.push((tid, coeff.clone()));
                    let rational_coeff = BigRational::from(coeff.clone());
                    term_coeffs.push((tid, rational_coeff.clone()));
                    if let Some(&lra_var) = self.lra.term_to_var().get(&tid) {
                        lra_coeffs.push((lra_var, rational_coeff));
                    }
                }

                // Build key using TermIds (stable across theory instances)
                term_coeffs_int.sort_by_key(|(tid, _)| tid.0);
                let key = HnfCutKey {
                    coeffs: term_coeffs_int,
                    bound: cut.bound.clone(),
                };

                if self.seen_hnf_cuts.contains(&key) {
                    continue;
                }

                if lra_coeffs.is_empty() {
                    continue;
                }

                // Create and add the cut as a bound constraint.
                // HNF cuts carry proper reasons from the equality atoms that built
                // the HNF constraint matrix (#5388). This prevents sentinel
                // reasons from creating incomplete conflict explanations.
                let cut_bound = BigRational::from(cut.bound.clone());
                let gomory_cut = ay_lra::GomoryCut {
                    coeffs: lra_coeffs,
                    bound: cut_bound.clone(),
                    is_lower: false, // HNF cuts are upper bounds (Σ coeff*x <= bound)
                    reasons: equality_reasons.clone(),
                    source_term: None,
                };

                self.lra.add_gomory_cut(&gomory_cut, TermId::SENTINEL);
                // HNF cut insertion can tighten a single-var bound —
                // conservatively rescan everything (#C4).
                self.mark_int_bounds_all_dirty();
                added_any = true;
                // #C7: trail the new key for per-scope undo (key is known absent
                // via the `contains` guard above).
                self.record_seen_hnf_cut(key);

                // Store the cut using TermIds for replay after LRA reset.
                // Include reasons so replayed cuts have proper conflict explanations.
                self.learned_cuts.push(StoredCut {
                    coeffs: term_coeffs,
                    bound: cut_bound,
                    is_lower: false,
                    reasons: equality_reasons.clone(),
                });
            }

            if added_any {
                self.hnf_iterations += 1;
                info!(
                    target: "ay::lia",
                    cuts_considered,
                    hnf_iterations = self.hnf_iterations,
                    learned_cuts = self.learned_cuts.len(),
                    "LIA HNF cut round added new cuts"
                );
            } else {
                debug!(
                    target: "ay::lia",
                    cuts_considered,
                    hnf_iterations = self.hnf_iterations,
                    "LIA HNF cut round produced no new cuts"
                );
            }
            added_any
        }
    }

    /// Parse an equality (lhs = rhs) into coefficient/constant form for HNF.
    /// Returns (coefficients, constant) where coefficients maps var_idx -> BigInt.
    fn parse_equality_for_hnf(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> (Vec<(usize, BigInt)>, BigInt) {
        let mut coeffs: HashMap<usize, BigInt> = HashMap::default();
        let mut constant = BigInt::zero();

        let resolve_var = |t: TermId| term_to_idx.get(&t).copied();
        let convert_const = |c: &Constant| -> Option<BigInt> {
            match c {
                Constant::Int(n) => Some(n.clone()),
                Constant::Rational(r) if r.0.denom().is_one() => Some(r.0.numer().clone()),
                _ => None,
            }
        };
        let terms = self.terms;
        let extract_mul_const = |t: TermId| terms.extract_integer_constant(t);

        // Parse lhs with positive sign
        crate::linear_collect::collect_linear_terms(
            self.terms,
            lhs,
            &BigInt::one(),
            &mut coeffs,
            &mut constant,
            &resolve_var,
            &convert_const,
            &extract_mul_const,
            false,
            false,
        );

        // Parse rhs with negative sign (move to LHS)
        crate::linear_collect::collect_linear_terms(
            self.terms,
            rhs,
            &-BigInt::one(),
            &mut coeffs,
            &mut constant,
            &resolve_var,
            &convert_const,
            &extract_mul_const,
            false,
            false,
        );

        // The equation is: Σ(coeff * var) - constant = 0
        // So: Σ(coeff * var) = constant
        constant = -constant;

        // Sort by variable index for deterministic ordering (#2657).
        // HashMap iteration order is nondeterministic.
        // Filter zero coefficients that can arise from cancellation in
        // collect_linear_terms before sorting (#6846).
        let mut coeffs_vec: Vec<_> = coeffs
            .into_iter()
            .filter(|(_, coeff)| !coeff.is_zero())
            .collect();
        coeffs_vec.sort_by_key(|(idx, _)| *idx);
        debug_assert!(
            coeffs_vec.windows(2).all(|w| w[0].0 < w[1].0),
            "BUG: HNF coefficient vector contains duplicate/out-of-order indices"
        );
        (coeffs_vec, constant)
    }
}
