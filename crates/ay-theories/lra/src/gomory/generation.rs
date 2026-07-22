// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Generate Gomory cuts for integer-infeasible basic variables.
    pub fn generate_gomory_cuts(&mut self, integer_vars: &HashSet<TermId>) -> Vec<GomoryCut> {
        // NOTE: Do NOT call move_nonbasic_to_bounds() here.
        // Moving non-basic variables changes basic variable values, potentially
        // violating basic variable bounds and creating an inconsistent LP state.
        // GMI cuts derived from an inconsistent state can be unsound (false UNSAT).
        // Z3 only calls move_non_basic_columns_to_bounds() when no cuts are
        // generated (gomory.cpp:557), not before cut generation.
        // The build_gomory_cut function already checks that each non-basic
        // variable is at a bound (is_at_lower_bound || is_at_upper_bound),
        // rejecting rows where variables are in the interior.

        let debug = debug_gomory();

        if debug {
            safe_eprintln!(
                "[GOMORY] Generating cuts for {} integer vars",
                integer_vars.len()
            );
        }

        let int_var_ids: HashSet<u32> = integer_vars
            .iter()
            .filter_map(|t| self.term_to_var.get(t).copied())
            .collect();

        // Compute per-variable usage count: how many rows reference each
        // variable. Used as tiebreaker in candidate sorting — variables
        // appearing in more constraints have more influence on the feasible
        // region. Reference: Z3 gomory.cpp:403 `usage_in_terms`.
        let mut usage_counts: Vec<usize> = vec![0; self.vars.len()];
        for row in &self.rows {
            for &(var, _) in &row.coeffs {
                if (var as usize) < usage_counts.len() {
                    usage_counts[var as usize] += 1;
                }
            }
        }

        let mut candidates = Vec::new();
        for (row_idx, row) in self.rows.iter().enumerate() {
            let basic_var = row.basic_var;

            if !self.is_integer_var(basic_var, integer_vars, &int_var_ids) {
                continue;
            }

            let basic_value = self.vars[basic_var as usize].value.rational();
            if basic_value.is_integer() {
                continue;
            }

            if !self.is_gomory_cut_target(row, basic_var, integer_vars, &int_var_ids) {
                if debug {
                    safe_eprintln!(
                        "[GOMORY] Skipping row for var {} — not all non-basics at bounds",
                        basic_var
                    );
                }
                continue;
            }

            candidates.push(GomoryCandidate {
                row_idx,
                basic_var,
                score: Self::gomory_score(&basic_value),
                usage: usage_counts.get(basic_var as usize).copied().unwrap_or(0),
            });
        }

        // Sort by score ascending (prefer fractional parts closest to 0.5),
        // then by usage descending (prefer variables in more constraints).
        // Reference: Z3 gomory.cpp:397-404.
        candidates.sort_by(|a, b| {
            a.score
                .partial_cmp(&b.score)
                .unwrap_or(Ordering::Equal)
                .then_with(|| b.usage.cmp(&a.usage))
        });

        // Select candidates using cubic-bias randomization (Z3 gomory.cpp:408-422).
        // Instead of deterministically taking the first N, we pick one candidate at
        // a time with cubic bias toward the front. If a candidate fails the
        // coefficient guard, we continue selecting from the remaining pool.
        let mut cuts = Vec::new();
        while cuts.len() < MAX_GOMORY_CUTS_PER_CHECK && !candidates.is_empty() {
            let candidate = Self::cubic_bias_pick(&mut candidates, &mut self.gomory_rng);
            let row = &self.rows[candidate.row_idx];
            let basic_var = candidate.basic_var;
            let basic_value = self.vars[basic_var as usize].value.rational();

            let Some(cut) = self.build_gomory_cut(
                row,
                basic_var,
                &basic_value,
                integer_vars,
                &int_var_ids,
                debug,
            ) else {
                continue;
            };

            if !self.current_solution_violates_cut(&cut) {
                if debug {
                    safe_eprintln!("[GOMORY] WARNING: cut does not violate current LP vertex");
                }
                continue;
            }

            cuts.push(cut);
        }

        cuts
    }

    pub(super) fn build_gomory_cut(
        &self,
        row: &TableauRow,
        basic_var: u32,
        basic_value: &BigRational,
        integer_vars: &HashSet<TermId>,
        int_var_ids: &HashSet<u32>,
        debug: bool,
    ) -> Option<GomoryCut> {
        let f_0 = crate::fractional_part(basic_value);
        if f_0.is_zero() {
            return None;
        }

        let one_minus_f_0 = BigRational::one() - &f_0;
        // Z3-style coefficient explosion guard:
        // skip rows whose transformed coefficients exceed abs_max^2.
        let abs_max = row
            .coeffs
            .iter()
            .map(|(_, coeff)| Self::abs_ceil_coeff(&coeff.to_big()))
            .max()
            .unwrap_or_default();
        let big_number = &abs_max * &abs_max;
        let mut found_big_coeff = false;

        let mut cut_coeffs: Vec<(u32, BigRational)> = Vec::new();
        let mut row_is_valid = true;
        let mut has_integer_term = false;
        // Constant adjustment for the RHS: when bounds are non-zero,
        // converting from slack space back to original variables shifts the
        // cut bound by Σ g_j*lb_j (lower) or -Σ g_j*ub_j (upper).
        let mut bound_adjust = BigRational::zero();

        for (var, coeff_rat) in &row.coeffs {
            if *var == basic_var {
                continue;
            }

            let info = &self.vars[*var as usize];
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                if debug {
                    safe_eprintln!(
                        "[GOMORY] Skipping row for basic var {}: coeff var {} is not non-basic",
                        basic_var,
                        var
                    );
                }
                row_is_valid = false;
                break;
            }

            // Convert Rational coefficient to BigRational for GMI computation.
            let coeff = coeff_rat.to_big();

            // Skip fixed variables (Z3 gomory.cpp:296-300).
            // Fixed variables contribute a constant to the row; their coefficient
            // vanishes in the cut. Record their bound reasons for completeness but
            // do not add a cut term.
            let at_lb = Self::is_at_lower_bound(info);
            let at_ub = Self::is_at_upper_bound(info);
            if at_lb && at_ub {
                // Both bounds hold ⇒ variable is fixed.
                continue;
            }

            let is_int_nonbasic = self.is_integer_var(*var, integer_vars, int_var_ids);

            // at_lb/at_ub already computed above (fixed-variable check).
            if !at_lb && !at_ub {
                if debug {
                    safe_eprintln!(
                        "[GOMORY] Skipping row for basic var {}: var {} is non-basic but not at a bound",
                        basic_var, var
                    );
                }
                row_is_valid = false;
                break;
            }

            // Standard GMI (Cornuejols 2007) cut coefficient g_j.
            let g_j = if is_int_nonbasic {
                let effective_coeff = if at_ub { -coeff.clone() } else { coeff.clone() };
                let f_j = crate::fractional_part(&effective_coeff);
                if f_j.is_zero() {
                    continue;
                }
                // Unified formula for both LB and UB: effective_coeff already
                // converts to slack-space, so the GMI formula is the same.
                // Bug fix (#4830): the old code used a different formula for UB
                // (swapped f_0 and 1-f_0 thresholds/denominators), double-counting
                // the sign conversion that effective_coeff already handles.
                if f_j <= one_minus_f_0 {
                    &f_j / &one_minus_f_0
                } else {
                    (BigRational::one() - &f_j) / &f_0
                }
            } else if at_lb {
                let a = coeff.clone();
                if !a.is_negative() {
                    a / &one_minus_f_0
                } else {
                    (-a) / &f_0
                }
            } else if at_ub {
                let a = -coeff.clone();
                if !a.is_negative() {
                    a / &one_minus_f_0
                } else {
                    (-a) / &f_0
                }
            } else {
                // Production soundness gate: non-basic var should be at bounds
                // per simplex invariant. If violated, skip this cut rather than
                // generating an unsound Gomory cut.
                safe_eprintln!(
                    "BUG: non-basic var {var} is not at bounds in Gomory row for basic var {basic_var}"
                );
                row_is_valid = false;
                break;
            };

            if g_j.is_zero() {
                continue;
            }

            // Z3-style coefficient explosion guard:
            // Z3 uses numerator(g_j) > abs_max^2 as the cutoff.
            // This intentionally ignores denominator size and sign.
            if g_j.numer() > &big_number {
                found_big_coeff = true;
                if debug {
                    safe_eprintln!(
                        "[GOMORY] Skipping row for var {} — coefficient explosion: numerator({})={} > {}",
                        basic_var,
                        g_j,
                        g_j.numer(),
                        big_number
                    );
                }
                break;
            }

            // Convert from slack space to original variable space:
            // At lower bound: s_j = x_j - lb_j  => coeff on x_j is +g_j,
            //                 bound adjusts by +g_j*lb_j
            // At upper bound: s_j = ub_j - x_j  => coeff on x_j is -g_j,
            //                 bound adjusts by -g_j*ub_j
            if is_int_nonbasic {
                has_integer_term = true;
            }
            if at_ub {
                cut_coeffs.push((*var, -g_j.clone()));
                if let Some(ref ub) = info.upper {
                    bound_adjust -= &g_j * &ub.value;
                }
            } else {
                cut_coeffs.push((*var, g_j.clone()));
                if let Some(ref lb) = info.lower {
                    bound_adjust += &g_j * &lb.value;
                }
            }
        }

        if found_big_coeff || !row_is_valid || cut_coeffs.is_empty() || !has_integer_term {
            if debug && row_is_valid && !cut_coeffs.is_empty() && !has_integer_term {
                safe_eprintln!(
                    "[GOMORY] Skipping row for basic var {}: cut has no integer non-basic terms",
                    basic_var
                );
            }
            return None;
        }

        let reasons = self.collect_row_active_bound_reasons(row, basic_var);
        let source_term = self.var_to_term.get(&basic_var).copied();
        Some(GomoryCut {
            coeffs: cut_coeffs,
            bound: BigRational::one() + &bound_adjust,
            is_lower: true,
            reasons,
            source_term,
        })
    }

    pub(super) fn current_solution_violates_cut(&self, cut: &GomoryCut) -> bool {
        let mut lhs = BigRational::zero();
        for (var, coeff) in &cut.coeffs {
            lhs += coeff * self.vars[*var as usize].value.rational();
        }
        if cut.is_lower {
            lhs < cut.bound
        } else {
            lhs > cut.bound
        }
    }
}
