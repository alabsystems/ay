// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tableau row bound tightening via Diophantine substitutions.
//!
//! Implements AY's equivalent of Z3's `tighten_terms_with_S()` from
//! `dioph_eq.cpp`. Extracted from `dioph_bridge.rs` to keep each file
//! under 500 lines.

use super::*;

impl LiaSolver<'_> {
    /// Tighten bounds on LP tableau rows using Diophantine substitutions.
    ///
    /// This is the AY equivalent of Z3's `tighten_terms_with_S()` from
    /// `dioph_eq.cpp`.  For each simplex row whose basic variable is an
    /// integer:
    ///
    /// 1. Express the row as `basic = Σ(c_j * v_j) + K`.
    /// 2. Substitute any variable `v_j` that has a Dioph cached substitution
    ///    (`v_j = const + Σ(a_i * d_i)`), replacing it in the expression.
    /// 3. Substitute fixed variables (equal LRA lower/upper bounds) into the
    ///    constant.
    /// 4. Compute `g = GCD` of the remaining coefficients.
    /// 5. If `g > 1`, the row expression ≡ `K'` (mod `g`), so we can tighten
    ///    the basic variable's bounds to the nearest value in the correct
    ///    residue class.
    ///
    /// Returns `true` if any bound was tightened.
    pub(crate) fn tighten_tableau_rows_via_dioph(&mut self) -> bool {
        if self.dioph_cached_substitutions.is_empty() {
            return false;
        }
        let debug = self.debug_dioph;
        let mut changed = false;

        // Build lookup: TermId → (&coeffs, &constant) from cached Dioph substitutions.
        type SubRef<'b> = (&'b [(TermId, BigInt)], &'b BigInt);
        let sub_map: HashMap<TermId, SubRef<'_>> = self
            .dioph_cached_substitutions
            .iter()
            .map(|(tid, coeffs, constant)| (*tid, (coeffs.as_slice(), constant)))
            .collect();

        // Reasons for any tightened bounds: the equalities that produced the
        // Dioph substitutions.
        let reasons = self.dioph_cached_reasons.clone();

        // Get all bounded integer rows from the simplex tableau.
        let rows = self.lra.get_bounded_integer_rows(&self.integer_vars);

        for row in &rows {
            // Row equation: basic_var = Σ(c_j * v_j) + constant
            // We want to substitute Dioph results into the RHS and compute GCD.

            // Collect the substituted expression: TermId → BigInt coefficient
            let mut expr: HashMap<TermId, BigInt> = HashMap::default();
            let mut expr_constant = BigInt::zero();

            // Scale everything to integers: find LCM of denominators in row.
            let mut lcm_den = BigInt::one();
            for (_, coeff) in &row.coeffs {
                lcm_den = lcm_den.lcm(&coeff.denom().clone());
            }
            lcm_den = lcm_den.lcm(&row.constant.denom().clone());
            debug_assert!(
                lcm_den > BigInt::zero(),
                "BUG: tighten_tableau_rows_via_dioph: LCM of denominators is non-positive ({lcm_den})"
            );

            // Scaled constant from the tableau row
            expr_constant += (&row.constant * &lcm_den).to_integer();

            for &(var_id, ref coeff) in &row.coeffs {
                let scaled = (coeff * &lcm_den).to_integer();

                // Map internal LRA var to TermId
                let Some(term_id) = self.lra.var_term_id(var_id) else {
                    // Unknown variable — can't substitute, breaks GCD
                    expr.clear();
                    break;
                };

                // Check if this variable is fixed (equal bounds)
                if let Some((Some(lb), Some(ub))) = self.lra.get_var_bounds(var_id) {
                    if lb == ub {
                        // Fixed variable: fold into constant.
                        // Contribution: scaled * lb = (coeff * lcm_den) * (lb_numer / lb_denom).
                        // This must be an exact integer; truncation would corrupt the GCD
                        // analysis. If the division isn't exact, skip the row.
                        let numer_product = &scaled * lb.numer();
                        let (contrib, remainder) = numer_product.div_rem(lb.denom());
                        if !remainder.is_zero() {
                            // Non-integer contribution — can't do exact GCD analysis
                            expr.clear();
                            break;
                        }
                        expr_constant += contrib;
                        continue;
                    }
                }

                // Check if this variable is a non-integer (real) variable
                if !self.integer_vars.contains(&term_id) {
                    // Real variable in the row — can't derive integer GCD
                    expr.clear();
                    break;
                }

                // Check for Dioph substitution
                if let Some(&(sub_coeffs, sub_const)) = sub_map.get(&term_id) {
                    // Replace: term_id → sub_const + Σ(sub_coeff * dep_term)
                    // Contribution: scaled * (sub_const + Σ(sub_coeff * dep_term))
                    expr_constant += &scaled * sub_const;
                    for (dep_term, sub_coeff) in sub_coeffs {
                        *expr.entry(*dep_term).or_insert_with(BigInt::zero) += &scaled * sub_coeff;
                    }
                } else {
                    // No substitution — keep as is
                    *expr.entry(term_id).or_insert_with(BigInt::zero) += scaled;
                }
            }

            if expr.is_empty() {
                continue; // Row had reals or unknown vars
            }

            // Clean up zero coefficients
            expr.retain(|_, v| !v.is_zero());

            if expr.is_empty() {
                continue; // All coefficients cancelled out
            }

            // Compute GCD of the substituted expression coefficients
            let mut gcd = BigInt::zero();
            for coeff in expr.values() {
                if gcd.is_zero() {
                    gcd = coeff.abs();
                } else {
                    gcd = gcd.gcd(&coeff.abs());
                }
                if gcd.is_one() {
                    break;
                }
            }

            if gcd <= BigInt::one() {
                continue;
            }

            debug_assert!(
                gcd > BigInt::one(),
                "BUG: tighten_tableau_rows_via_dioph: GCD {gcd} should be > 1 to tighten"
            );

            // The expression Σ(c'_k * v_k) ≡ 0 (mod gcd).
            // Therefore: basic_var (scaled by lcm_den) ≡ expr_constant (mod gcd).
            // Compute the residue class.
            let c_mod_g = positive_mod(&expr_constant, &gcd);

            let Some(basic_term) = row.basic_term else {
                continue;
            };

            // Tighten upper bound
            if let Some(ref ub_rat) = row.upper_bound {
                let ub_scaled = (ub_rat * &lcm_den).to_integer();
                let diff = &ub_scaled - &c_mod_g;
                let rs_g = positive_mod(&diff, &gcd);
                if !rs_g.is_zero() {
                    // Tighten: new_ub_scaled = ub_scaled - rs_g
                    // new_ub = new_ub_scaled / lcm_den
                    let new_ub_scaled = &ub_scaled - &rs_g;
                    let new_ub = BigRational::new(new_ub_scaled, lcm_den.clone());

                    if &new_ub < ub_rat {
                        if debug {
                            safe_eprintln!(
                                "[DIOPH-ROW] Tighten upper: {:?} {} -> {} (mod {} residue {}, lcm {})",
                                basic_term,
                                ub_rat,
                                new_ub,
                                gcd,
                                c_mod_g,
                                lcm_den
                            );
                        }
                        let lra_var = self.lra.ensure_var_registered(basic_term);
                        self.lra
                            .add_direct_bound_with_reasons(lra_var, new_ub, false, &reasons);
                        // Dioph row tightening → rescan this var (#C4).
                        // (Direct field access: `sub_map` holds a borrow of
                        // `dioph_cached_substitutions` across the loop.)
                        if !self.int_bounds_all_dirty {
                            self.int_bounds_dirty.insert(basic_term);
                        }
                        changed = true;
                    }
                }
            }

            // Tighten lower bound
            if let Some(ref lb_rat) = row.lower_bound {
                let lb_scaled = (lb_rat * &lcm_den).to_integer();
                let diff = &c_mod_g - &lb_scaled;
                let rs_g = positive_mod(&diff, &gcd);
                if !rs_g.is_zero() {
                    let new_lb_scaled = &lb_scaled + &rs_g;
                    let new_lb = BigRational::new(new_lb_scaled, lcm_den.clone());

                    if &new_lb > lb_rat {
                        if debug {
                            safe_eprintln!(
                                "[DIOPH-ROW] Tighten lower: {:?} {} -> {} (mod {} residue {}, lcm {})",
                                basic_term,
                                lb_rat,
                                new_lb,
                                gcd,
                                c_mod_g,
                                lcm_den
                            );
                        }
                        let lra_var = self.lra.ensure_var_registered(basic_term);
                        self.lra
                            .add_direct_bound_with_reasons(lra_var, new_lb, true, &reasons);
                        // Dioph row tightening → rescan this var (#C4).
                        // (Direct field access: `sub_map` holds a borrow of
                        // `dioph_cached_substitutions` across the loop.)
                        if !self.int_bounds_all_dirty {
                            self.int_bounds_dirty.insert(basic_term);
                        }
                        changed = true;
                    }
                }
            }
        }

        changed
    }
}
