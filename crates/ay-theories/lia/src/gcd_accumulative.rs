// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Accumulative GCD/CRT test for cross-row modular incompatibility.
//!
//! Z3 reference: `int_gcd_test.cpp:251-317`

use super::*;

impl LiaSolver<'_> {
    fn append_unique_reasons(base: &mut Vec<TheoryLit>, extra: &[TheoryLit]) {
        let mut seen: HashSet<TheoryLit> = base.iter().copied().collect();
        for lit in extra {
            if seen.insert(*lit) {
                base.push(*lit);
            }
        }
    }

    /// Accumulative GCD/CRT test: detect cross-row modular incompatibility.
    ///
    /// For each tableau row with a fractional integer basic variable, extract
    /// modular constraints on unit-coefficient variables. When two rows imply
    /// incompatible residues for the same variable (checked via CRT), report UNSAT.
    ///
    /// For example, if row 1 implies `x ≡ 2 (mod 6)` and row 2 implies
    /// `x ≡ 1 (mod 4)`, then `gcd(6,4) = 2` but `2 mod 2 ≠ 1 mod 2`,
    /// so no integer x satisfies both constraints simultaneously.
    ///
    /// Z3 reference: `int_gcd_test.cpp:251-317`
    pub(super) fn gcd_accumulative_test(&self) -> Option<TheoryConflict> {
        use ay_core::extended_gcd_bigint;

        // Map: variable TermId -> (residue mod modulus, modulus, reason literals)
        let mut constraints: HashMap<TermId, (BigInt, BigInt, Vec<TheoryLit>)> = HashMap::default();

        let rows = self.lra.get_fractional_int_rows(&self.integer_vars);

        for row in &rows {
            // Compute LCM of denominators to work with integer coefficients
            let mut lcm_den = BigInt::one();
            for (_, coeff) in &row.coeffs {
                lcm_den = lcm_den.lcm(&coeff.denom().clone());
            }
            lcm_den = lcm_den.lcm(&row.constant.denom().clone());

            // Find variables with unit coefficient (|scaled_coeff| == 1)
            // and compute GCD of all other non-fixed integer coefficients
            for (target_var, target_coeff) in &row.coeffs {
                let scaled_target = (target_coeff * &lcm_den).to_integer();
                if scaled_target.abs() != BigInt::one() {
                    continue;
                }

                let target_term = match self.lra.var_term_id(*target_var) {
                    Some(t) if self.integer_vars.contains(&t) => t,
                    _ => continue,
                };

                // Compute GCD of other non-fixed integer coefficients and accumulate
                // fixed-variable contributions into the constant.
                let mut other_gcd = BigInt::zero();
                let mut constant_accum = BigInt::zero();
                let mut has_real = false;

                for (var, coeff) in &row.coeffs {
                    if var == target_var {
                        continue;
                    }
                    let sc = (coeff * &lcm_den).to_integer();
                    let abs_sc = sc.abs();

                    if let Some((lb, ub)) = self.lra.get_var_bounds(*var) {
                        let is_fixed = lb.is_some() && ub.is_some() && lb == ub;
                        let is_int = self.lra.is_int_var(*var, &self.integer_vars);

                        if is_fixed {
                            if let Some(ref bound_val) = lb {
                                constant_accum += &sc * bound_val.numer() / bound_val.denom();
                            }
                        } else if !is_int {
                            has_real = true;
                            break;
                        } else if other_gcd.is_zero() {
                            other_gcd = abs_sc;
                        } else {
                            other_gcd = other_gcd.gcd(&abs_sc);
                        }
                    }
                }

                if has_real || other_gcd <= BigInt::one() {
                    continue;
                }

                // Extract residue: the row says
                //   scaled_target * target_var + Σ(sc_i * var_i) + scaled_const = 0
                // So target_var = -(Σ(sc_i * var_i) + scaled_const) / scaled_target
                // Since |scaled_target| == 1, target_var ≡ -(scaled_const + constant_accum) (mod other_gcd)
                // (the sign of scaled_target flips the residue sign)
                let scaled_const = (&row.constant * &lcm_den).to_integer() + &constant_accum;
                let raw_residue = if scaled_target.is_positive() {
                    -&scaled_const
                } else {
                    scaled_const.clone()
                };
                let residue = positive_mod(&raw_residue, &other_gcd);

                let row_reasons = self.collect_tableau_gcd_conflict_literals(row);

                if let Some((prev_residue, prev_modulus, ref prev_reasons)) =
                    constraints.get(&target_term)
                {
                    // CRT compatibility check
                    let g = prev_modulus.gcd(&other_gcd);
                    if positive_mod(&residue, &g) != positive_mod(prev_residue, &g) {
                        // Cross-row modular conflict
                        let mut combined_reasons = prev_reasons.clone();
                        Self::append_unique_reasons(&mut combined_reasons, &row_reasons);
                        return Some(TheoryConflict::new(combined_reasons));
                    }

                    // CRT merge: combine into tighter constraint for future rows.
                    // x ≡ c1 (mod m1) AND x ≡ c2 (mod m2)  →  x ≡ c (mod lcm(m1, m2))
                    let (g_ext, s, _t) = extended_gcd_bigint(prev_modulus, &other_gcd);
                    let lcm_mod = prev_modulus.lcm(&other_gcd);
                    let diff = &residue - prev_residue;
                    let new_residue = positive_mod(
                        &(prev_residue + prev_modulus * (&diff / &g_ext) * &s),
                        &lcm_mod,
                    );

                    debug_assert!(
                        positive_mod(&new_residue, prev_modulus) == *prev_residue
                            && positive_mod(&new_residue, &other_gcd) == residue,
                        "BUG: CRT merge produced inconsistent result: {} mod {} = {} (expected {}), {} mod {} = {} (expected {})",
                        new_residue, prev_modulus, positive_mod(&new_residue, prev_modulus), prev_residue,
                        new_residue, other_gcd, positive_mod(&new_residue, &other_gcd), residue,
                    );

                    let mut merged_reasons = prev_reasons.clone();
                    Self::append_unique_reasons(&mut merged_reasons, &row_reasons);
                    constraints.insert(target_term, (new_residue, lcm_mod, merged_reasons));
                } else {
                    constraints.insert(target_term, (residue, other_gcd, row_reasons));
                }
            }
        }

        None
    }
}
