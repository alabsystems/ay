// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tableau-level GCD infeasibility checks for LIA.
//!
//! Contains `gcd_test_tableau` (extended GCD on fractional integer rows),
//! `ext_gcd_test` (interval arithmetic feasibility), and
//! `collect_tableau_gcd_conflict_literals` (conflict reason collection).
//!
//! Extracted from gcd.rs as part of #5970 code-health splits.

use super::*;
use tracing::{debug, info};

impl LiaSolver<'_> {
    /// Extended GCD test on tableau rows with fractional integer basic variables.
    ///
    /// For each row where the basic variable is an integer with a non-integer
    /// value in the LP relaxation, we check:
    ///
    /// 1. Basic test: GCD of non-fixed coefficients must divide the constant
    /// 2. Extended test: If the variable with smallest coefficient is bounded,
    ///    use interval arithmetic to check if any integer solution exists
    ///
    /// This is ported from Z3's `theory_arith_int.h::gcd_test()` and `ext_gcd_test()`.
    ///
    /// Reference: Z3 src/smt/theory_arith_int.h:693-858
    pub(super) fn gcd_test_tableau(&self) -> Option<TheoryConflict> {
        let debug = self.debug_gcd_tab;

        let rows = self.lra.get_fractional_int_rows(&self.integer_vars);
        let row_count = rows.len();
        let mut basic_checks = 0usize;
        let mut extended_checks = 0usize;

        if debug && !rows.is_empty() {
            safe_eprintln!(
                "[GCD_TAB] Testing {} rows with fractional integer basic vars",
                rows.len()
            );
        }

        for row in rows {
            basic_checks += 1;
            // Compute LCM of denominators to work with integer coefficients
            let mut lcm_den = BigInt::one();
            for (_, coeff) in &row.coeffs {
                lcm_den = lcm_den.lcm(&coeff.denom().clone());
            }
            lcm_den = lcm_den.lcm(&row.constant.denom().clone());
            debug_assert!(
                lcm_den.is_positive(),
                "BUG: tableau denominator LCM is non-positive {lcm_den}"
            );

            // Accumulate constant from fixed variables and GCD of non-fixed coefficients
            let mut consts = BigInt::zero();
            let mut gcds = BigInt::zero();
            let mut least_coeff = BigInt::zero();
            let mut least_coeff_is_bounded = false;

            // The tableau row is: basic_var = Σ(coeff_i * nonbasic_i) + constant.
            // After scaling by lcm_den, the basic variable has implicit coefficient
            // lcm_den. If the basic variable is a non-fixed integer, its coefficient
            // must participate in the GCD computation. Without this, the GCD test
            // over-approximates infeasibility (e.g., 3x + 5y = 7 with GCD(5)=5
            // instead of GCD(3,5)=1). Fix for #5648.
            if !row.is_fixed {
                let basic_is_int = row
                    .basic_term
                    .is_some_and(|t| self.integer_vars.contains(&t));
                if basic_is_int {
                    Self::update_gcd_and_least_coeff(
                        &lcm_den,
                        row.is_bounded,
                        &mut gcds,
                        &mut least_coeff,
                        &mut least_coeff_is_bounded,
                    );
                }
            }

            for (var, coeff) in &row.coeffs {
                // Scale coefficient by LCM
                let scaled = (coeff * &lcm_den).to_integer();
                let abs_scaled = scaled.abs();

                // Check if this variable is fixed
                if let Some((lb, ub)) = self.lra.get_var_bounds(*var) {
                    let is_fixed = lb.is_some() && ub.is_some() && lb == ub;
                    let is_bounded = lb.is_some() && ub.is_some();
                    let is_int = self.lra.is_int_var(*var, &self.integer_vars);

                    if is_fixed {
                        // Fixed variable: accumulate its contribution to constant
                        if let Some(ref bound_val) = lb {
                            let contrib = &scaled * bound_val.numer() / bound_val.denom();
                            consts += contrib;
                        }
                    } else if !is_int {
                        // Real (non-integer) variable in the row - skip this row
                        // (GCD test only applies to pure integer rows)
                        gcds = BigInt::zero();
                        break;
                    } else {
                        // Non-fixed integer variable: contribute to GCD
                        Self::update_gcd_and_least_coeff(
                            &abs_scaled,
                            is_bounded,
                            &mut gcds,
                            &mut least_coeff,
                            &mut least_coeff_is_bounded,
                        );
                    }
                }
            }

            if gcds.is_zero() {
                // All variables are fixed or row has reals - skip
                continue;
            }

            // Scale the constant term and add fixed variable contributions
            // The row equation is: basic = Σ(coeff * var) + constant
            // Fixed vars contribute: Σ(scaled_coeff * value) = consts
            // So the "effective constant" is: scaled_constant + consts
            let scaled_const = (&row.constant * &lcm_den).to_integer() + &consts;

            // Basic GCD test: check if GCD divides constant
            let remainder = &scaled_const % &gcds;
            if !remainder.is_zero() {
                if debug {
                    safe_eprintln!(
                        "[GCD_TAB] UNSAT: Row basic_var={} GCD={} does not divide const={} (remainder={})",
                        row.basic_var, gcds, scaled_const, remainder
                    );
                }
                info!(
                    target: "ay::lia",
                    row_count,
                    basic_checks,
                    extended_checks,
                    basic_var = row.basic_var,
                    gcd = %gcds,
                    scaled_const = %scaled_const,
                    remainder = %remainder,
                    "LIA tableau GCD basic conflict"
                );
                let literals = self.collect_tableau_gcd_conflict_literals(&row);
                return Some(TheoryConflict::new(literals));
            }

            // Extended GCD test: if variable with smallest coefficient is bounded,
            // check if any integer solution exists using interval arithmetic
            if least_coeff_is_bounded && !least_coeff.is_one() {
                extended_checks += 1;
                if let Some(conflict) = self.ext_gcd_test(&row, &least_coeff, &lcm_den, &consts) {
                    if debug {
                        safe_eprintln!(
                            "[GCD_TAB] Extended GCD test detected UNSAT for row basic_var={}",
                            row.basic_var
                        );
                    }
                    info!(
                        target: "ay::lia",
                        row_count,
                        basic_checks,
                        extended_checks,
                        basic_var = row.basic_var,
                        least_coeff = %least_coeff,
                        "LIA tableau GCD extended conflict"
                    );
                    return Some(conflict);
                }
            }
        }

        debug!(
            target: "ay::lia",
            row_count,
            basic_checks,
            extended_checks,
            "LIA tableau GCD checks completed without conflict"
        );

        None
    }

    /// Extended GCD test auxiliary method.
    ///
    /// When the variable with the smallest coefficient in a row is bounded,
    /// we can use interval arithmetic to check if any integer solution exists.
    ///
    /// For variables with |coeff| == least_coeff, accumulate their bounds into [l, u].
    /// For other variables, compute their GCD.
    /// Check if ceil(l/gcds) <= floor(u/gcds).
    fn ext_gcd_test(
        &self,
        row: &GcdRowInfo,
        least_coeff: &BigInt,
        lcm_den: &BigInt,
        fixed_consts: &BigInt,
    ) -> Option<TheoryConflict> {
        let mut gcds = BigInt::zero();
        // Use rationals for precise interval computation (Z3 does the same)
        //
        // #ssl-residue D3 (lia_143 spurious extended-GCD conflict): the row is
        // `basic = Σ(coeff_i·x_i) + constant`, i.e. after scaling by lcm_den:
        // `Σ(scaled_i·x_i) − lcm_den·basic + lcm_den·constant + fixed = 0`.
        // The interval of the least-coefficient part must therefore START from
        // `fixed + lcm_den·row.constant` (the scaled ROW CONSTANT was dropped,
        // shifting the interval and manufacturing conflicts on rows with a
        // non-zero constant), and the basic variable participates with SIGNED
        // coefficient `−lcm_den` (its bounds pair crosswise). The
        // contains-a-multiple-of-g test itself is negation-symmetric, so no
        // other sign normalization is needed.
        let scaled_row_const = &row.constant * BigRational::from_integer(lcm_den.clone());
        let mut l_rat = BigRational::from_integer(fixed_consts.clone()) + &scaled_row_const;
        let mut u_rat = BigRational::from_integer(fixed_consts.clone()) + &scaled_row_const;

        // Include basic variable's implicit coefficient (lcm_den) if non-fixed.
        // Same reasoning as in gcd_test_tableau: the basic variable participates
        // in the equation and its coefficient must be in the GCD. Fix for #5648.
        if !row.is_fixed {
            let basic_is_int = row
                .basic_term
                .is_some_and(|t| self.integer_vars.contains(&t));
            if basic_is_int {
                if lcm_den == least_coeff {
                    // Basic variable has the least coefficient — use its bounds
                    // with its SIGNED coefficient −lcm_den (bounds cross over).
                    if let (Some(ref lb_val), Some(ref ub_val)) =
                        (&row.lower_bound, &row.upper_bound)
                    {
                        let neg_scaled_rat = -BigRational::from_integer(lcm_den.clone());
                        l_rat += &neg_scaled_rat * ub_val;
                        u_rat += &neg_scaled_rat * lb_val;
                    } else {
                        // SOUNDNESS (#gcd-tableau half-bounded drop): a half-/un-
                        // bounded least-coeff basic var must NOT be dropped from the
                        // interval — that narrows feasibility and can manufacture a
                        // spurious UNSAT. Fold its coefficient into the gcd instead
                        // (the same over-approximation the basic GCD test uses):
                        // weakening the test can only remove conflicts, never add a
                        // wrong one.
                        if gcds.is_zero() {
                            gcds = lcm_den.clone();
                        } else {
                            gcds = gcds.gcd(lcm_den);
                        }
                    }
                } else {
                    // Basic variable contributes to GCD
                    if gcds.is_zero() {
                        gcds = lcm_den.clone();
                    } else {
                        gcds = gcds.gcd(lcm_den);
                    }
                }
            }
        }

        for (var, coeff) in &row.coeffs {
            if let Some((lb, ub)) = self.lra.get_var_bounds(*var) {
                let is_fixed = lb.is_some() && ub.is_some() && lb == ub;
                if is_fixed {
                    continue; // Already handled in fixed_consts
                }

                let scaled_rat = coeff * BigRational::from_integer(lcm_den.clone());
                let scaled = scaled_rat.to_integer();
                let abs_scaled = scaled.abs();

                if &abs_scaled == least_coeff {
                    // Variable with smallest coefficient - use its EXACT bounds
                    // Don't truncate to integer - keep full precision until the end
                    let (Some(lb_val), Some(ub_val)) = (lb, ub) else {
                        // SOUNDNESS (#gcd-tableau half-bounded drop): a half-/un-
                        // bounded least-coeff variable cannot be dropped (that
                        // narrows the interval and yields a spurious UNSAT — e.g.
                        // `(mod (+ x (mod x 2)) 7) = 5 ∧ x >= 0`). Fold its
                        // coefficient into the gcd instead; this over-approximates
                        // feasibility (any integer shift), so it only ever weakens
                        // the test — never a wrong conflict.
                        if gcds.is_zero() {
                            gcds = abs_scaled;
                        } else {
                            gcds = gcds.gcd(&abs_scaled);
                        }
                        continue;
                    };

                    if scaled.is_positive() {
                        l_rat += &scaled_rat * &lb_val;
                        u_rat += &scaled_rat * &ub_val;
                    } else {
                        l_rat += &scaled_rat * &ub_val;
                        u_rat += &scaled_rat * &lb_val;
                    }
                } else {
                    // Other non-fixed variables contribute to GCD
                    if gcds.is_zero() {
                        gcds = abs_scaled;
                    } else {
                        gcds = gcds.gcd(&abs_scaled);
                    }
                }
            }
        }

        if gcds.is_zero() {
            return None;
        }
        debug_assert!(
            gcds.is_positive(),
            "BUG: ext_gcd_test produced non-positive gcd {gcds}"
        );

        // Check if ceil(l/gcds) > floor(u/gcds) => UNSAT
        // Now apply ceil/floor AFTER the full interval computation
        let gcds_rat = BigRational::from_integer(gcds);
        let l1 = Self::ceil_rational(&(&l_rat / &gcds_rat));
        let u1 = Self::floor_rational(&(&u_rat / &gcds_rat));

        if u1 < l1 {
            // No integer solution exists in the interval
            let literals = self.collect_tableau_gcd_conflict_literals(row);
            return Some(TheoryConflict::new(literals));
        }

        None
    }

    /// Collect conflict literals for tableau-based GCD conflicts.
    ///
    /// The GCD infeasibility argument uses (a) the tableau row equation, which
    /// is a sound pivot combination of slack DEFINITIONS and needs no reasons,
    /// and (b) the asserted bounds of every variable in the row — most
    /// critically the FIXED variables whose values were folded into the row
    /// constant, and the bounds used by the extended interval test. All of
    /// those bound reasons must appear in the conflict clause.
    ///
    /// Collection is VAR-keyed (seed-3167 false UNSAT): slack variables for
    /// compound expressions (e.g. the equality-fixed sum `2*x1 + x2`) have no
    /// `var_to_term` mapping, so the previous term-keyed walk silently dropped
    /// exactly the equality reasons that fixed them, producing an under-sized
    /// (even unit) conflict clause that excluded satisfiable space. If no
    /// reasons are found at all, fall back to all asserted literals to
    /// preserve soundness.
    pub(super) fn collect_tableau_gcd_conflict_literals(&self, row: &GcdRowInfo) -> Vec<TheoryLit> {
        let mut participant_vars = Vec::new();
        let mut seen_vars = HashSet::default();
        if seen_vars.insert(row.basic_var) {
            participant_vars.push(row.basic_var);
        }
        for (var, _) in &row.coeffs {
            if seen_vars.insert(*var) {
                participant_vars.push(*var);
            }
        }

        let mut seen = HashSet::default();
        let mut literals = Vec::new();
        let mut complete = true;

        for var in participant_vars {
            let Some((lower, upper)) = self.lra.var_bounds_with_reasons(var) else {
                continue;
            };
            if let Some(lower) = lower {
                complete &= Self::append_bound_reason_literals(lower, &mut seen, &mut literals);
            }
            if let Some(upper) = upper {
                complete &= Self::append_bound_reason_literals(upper, &mut seen, &mut literals);
            }
        }

        // #ssl-residue D3 (lia_143): a SENTINEL reason (Gomory/HNF cut or
        // unconditional theory axiom bound — both integer-valid consequences of
        // the asserted set) has no SAT-level atom to voice. Skipping it used to
        // leave the conflict UNDER-EXPLAINED: the emitted literal set was
        // satisfiable as stated, so the semantic conflict verifier (correctly)
        // rejected it and the solve fail-closed to Unknown. When any sentinel
        // reason was dropped, widen to the documented all-asserted-literals
        // fallback (below) — a sound superset conflict: the cut/axiom bounds
        // are Z-entailed by the full asserted set, so if the row is integer-
        // infeasible under them, the asserted set itself is integer-infeasible.
        if !literals.is_empty() && complete {
            return literals;
        }

        debug!(
            target: "ay::lia",
            reason_literals = literals.len(),
            complete,
            asserted = self.asserted.len(),
            "GCD tableau conflict widened to all-asserted fallback (sentinel or empty reasons)"
        );

        for &(term, value) in &self.asserted {
            let lit = TheoryLit::new(term, value);
            if seen.insert(lit) {
                literals.push(lit);
            }
        }

        literals
    }

    /// Returns `false` when a sentinel (unvoiceable) reason was skipped — the
    /// collected literal set then under-explains the bound and the caller must
    /// fall back to the all-asserted-literals conflict.
    fn append_bound_reason_literals(
        bound: &Bound,
        seen: &mut HashSet<TheoryLit>,
        literals: &mut Vec<TheoryLit>,
    ) -> bool {
        debug_assert_eq!(
            bound.reasons.len(),
            bound.reason_values.len(),
            "BUG: bound reason vectors out of sync (reasons={0}, values={1})",
            bound.reasons.len(),
            bound.reason_values.len(),
        );
        let mut complete = true;
        for (reason, value) in bound.reasons.iter().zip(bound.reason_values.iter()) {
            if reason.is_sentinel() {
                complete = false;
                continue;
            }
            let lit = TheoryLit::new(*reason, *value);
            if seen.insert(lit) {
                literals.push(lit);
            }
        }
        complete
    }
}
