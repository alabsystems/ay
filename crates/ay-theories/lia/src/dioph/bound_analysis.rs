// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound-aware analysis of Diophantine substitutions.
//!
//! After the core solver eliminates variables and produces substitutions,
//! these methods check whether the resulting system is feasible given
//! variable bounds. This is the AY equivalent of Z3's "rewrite conflict"
//! and "tighten conflict" in `dioph_eq.cpp`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use super::expansion::{ExpansionPolicy, SubstitutionExpander};
use super::solver::DiophSolver;
use crate::SubstitutionTriple;

impl DiophSolver {
    /// Get fully-expanded substitution expressions for bound propagation.
    ///
    /// Returns substitutions only for original variables (< num_original_vars)
    /// that depend only on other original variables.
    ///
    /// Each entry is: (substituted_var, coefficients, constant)
    /// Meaning: substituted_var = constant + Σ(coeff * var)
    ///
    /// When `expand_fresh` is true,
    /// fresh variables in substitutions are recursively expanded using their own
    /// substitution definitions.  This allows recovering the full expression of
    /// an original variable in terms of other original (free) variables, even
    /// when coefficient reduction introduced intermediate fresh variables.
    /// An expression that needs a free fresh parameter (#4830), or whose exact
    /// expansion exceeds the expander's budget (D3), is left out: every entry
    /// returned is an exact consequence of the equations.
    pub(crate) fn get_expanded_substitutions(
        &self,
        num_original_vars: usize,
        expand_fresh: bool,
    ) -> Vec<SubstitutionTriple<usize, BigInt>> {
        let mut result = Vec::new();
        let mut expander = SubstitutionExpander::new(
            &self.substitutions,
            ExpansionPolicy::StopAtOriginals { num_original_vars },
        );

        for (&var, (coeffs, constant)) in &self.substitutions {
            if var >= num_original_vars {
                continue;
            }

            if !expand_fresh {
                if coeffs.keys().any(|&v| v >= num_original_vars) {
                    continue;
                }
                let mut coeffs_vec: Vec<_> = coeffs.iter().map(|(&v, c)| (v, c.clone())).collect();
                coeffs_vec.sort_by_key(|(v, _)| *v);
                result.push((var, coeffs_vec, constant.clone()));
            } else if let Some(form) = expander.expand(var) {
                if form.coeffs.is_empty() || form.coeffs.keys().any(|&v| v >= num_original_vars) {
                    continue;
                }
                let mut coeffs_vec: Vec<_> =
                    form.coeffs.iter().map(|(&v, c)| (v, c.clone())).collect();
                coeffs_vec.sort_by_key(|(v, _)| *v);
                result.push((var, coeffs_vec, form.constant.clone()));
            }
        }

        result.sort_by_key(|(v, _, _)| *v);
        result
    }

    /// Get modular constraints for all original variables from Diophantine
    /// substitutions.
    ///
    /// For each original variable that has a substitution, fully expands it
    /// (including free fresh parameters) and computes the GCD of all
    /// coefficients. Free parameters contribute to the GCD just like original
    /// variables — they represent unconstrained integer multiples.
    ///
    /// Returns `(var_idx, gcd, residue)` for variables where GCD > 1,
    /// meaning `var ≡ residue (mod gcd)`. A variable whose exact expansion is
    /// not available (budget) yields nothing: the GCD of a partial sum is not
    /// a modulus of the variable (D3).
    ///
    /// This is critical for cross-mod reasoning: when `x = 2*q1` and
    /// `x = 3*q2`, the Dioph solver derives `r3 = -6*f - 6*q3` where `f`
    /// is a free parameter. The GCD of (-6, -6) = 6, giving `r3 ≡ 0 (mod 6)`.
    pub(crate) fn get_modular_constraints(
        &self,
        num_original_vars: usize,
    ) -> Vec<(usize, BigInt, BigInt)> {
        use super::super::positive_mod;

        let mut result = Vec::new();
        let mut expander =
            SubstitutionExpander::new(&self.substitutions, ExpansionPolicy::FreeParams);

        for &var in self.substitutions.keys() {
            if var >= num_original_vars {
                continue;
            }

            let Some(form) = expander.expand(var) else {
                continue;
            };

            if form.coeffs.is_empty() {
                continue;
            }

            // Compute GCD of all coefficient absolute values
            let mut gcd = BigInt::zero();
            for coeff in form.coeffs.values() {
                let abs_c = coeff.abs();
                if gcd.is_zero() {
                    gcd = abs_c;
                } else {
                    gcd = gcd.gcd(&abs_c);
                }
                if gcd.is_one() {
                    break; // GCD=1 is trivial
                }
            }

            if gcd > BigInt::one() {
                let residue = positive_mod(&form.constant, &gcd);
                result.push((var, gcd, residue));
            }
        }

        result.sort_by_key(|(v, _, _)| *v);
        result
    }

    /// Check remaining equations (after `solve()`) against variable bounds.
    ///
    /// For each remaining 2-variable equation a*x + b*y = c, uses extended GCD
    /// to compute the parametric solution and checks whether any integer solution
    /// exists within the given bounds.  Returns the source provenance of an
    /// infeasible equation, or `None` if no conflict is detected.
    pub(crate) fn check_remaining_with_bounds(
        &self,
        bounds: &HashMap<usize, (Option<BigInt>, Option<BigInt>)>,
    ) -> Option<Vec<usize>> {
        for eq in &self.equations {
            if eq.is_trivial() {
                continue;
            }
            if eq.coeffs.len() == 2 {
                if let Some(sol) = eq.solve_two_variable() {
                    let (x_lo, x_hi) = bounds
                        .get(&sol.var_x)
                        .map(|(lo, hi)| (lo.as_ref(), hi.as_ref()))
                        .unwrap_or((None, None));
                    let (y_lo, y_hi) = bounds
                        .get(&sol.var_y)
                        .map(|(lo, hi)| (lo.as_ref(), hi.as_ref()))
                        .unwrap_or((None, None));

                    let (k_min_x, k_max_x) = sol.k_bounds_from_x(x_lo, x_hi);
                    let (k_min_y, k_max_y) = sol.k_bounds_from_y(y_lo, y_hi);

                    let k_min = match (k_min_x, k_min_y) {
                        (Some(a), Some(b)) => Some(a.max(b)),
                        (Some(a), None) | (None, Some(a)) => Some(a),
                        (None, None) => None,
                    };
                    let k_max = match (k_max_x, k_max_y) {
                        (Some(a), Some(b)) => Some(a.min(b)),
                        (Some(a), None) | (None, Some(a)) => Some(a),
                        (None, None) => None,
                    };

                    if let (Some(lo), Some(hi)) = (&k_min, &k_max) {
                        if lo > hi {
                            if self.debug {
                                safe_eprintln!(
                                    "[DIOPH] Remaining 2-var equation infeasible: \
                                     k range [{}, {}] is empty",
                                    lo,
                                    hi
                                );
                            }
                            return Some(eq.sources.clone());
                        }
                    }
                }
            } else if eq.coeffs.len() == 1 {
                let (&var, coeff) = eq.coeffs.iter().next().unwrap();
                if !(&eq.constant % coeff).is_zero() {
                    return Some(eq.sources.clone());
                }
                let val = &eq.constant / coeff;
                if let Some((lo, hi)) = bounds.get(&var) {
                    if lo.as_ref().is_some_and(|l| &val < l) {
                        return Some(eq.sources.clone());
                    }
                    if hi.as_ref().is_some_and(|h| &val > h) {
                        return Some(eq.sources.clone());
                    }
                }
            }
        }
        None
    }
}
