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
    pub(crate) fn get_expanded_substitutions(
        &self,
        num_original_vars: usize,
        expand_fresh: bool,
    ) -> Vec<SubstitutionTriple<usize, BigInt>> {
        let mut result = Vec::new();

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
            } else {
                let expanded = self.expand_single_substitution(coeffs, constant, num_original_vars);
                if let Some((coeffs_vec, expanded_const)) = expanded {
                    result.push((var, coeffs_vec, expanded_const));
                }
            }
        }

        result.sort_by_key(|(v, _, _)| *v);
        result
    }

    /// Expand a single substitution by recursively substituting fresh variables.
    fn expand_single_substitution(
        &self,
        coeffs: &HashMap<usize, BigInt>,
        constant: &BigInt,
        num_original_vars: usize,
    ) -> Option<(Vec<(usize, BigInt)>, BigInt)> {
        let mut expanded_coeffs: HashMap<usize, BigInt> = HashMap::default();
        let mut expanded_const = constant.clone();
        let mut worklist: Vec<(usize, BigInt)> =
            coeffs.iter().map(|(&v, c)| (v, c.clone())).collect();

        let mut iteration = 0;
        let max_iterations = 100;
        while let Some((dep_var, dep_coeff)) = worklist.pop() {
            iteration += 1;
            if iteration > max_iterations {
                break;
            }

            if dep_var < num_original_vars {
                *expanded_coeffs.entry(dep_var).or_insert_with(BigInt::zero) += &dep_coeff;
            } else if let Some((sub_coeffs, sub_const)) = self.substitutions.get(&dep_var) {
                expanded_const += &dep_coeff * sub_const;
                for (&sub_dep, sub_c) in sub_coeffs {
                    worklist.push((sub_dep, &dep_coeff * sub_c));
                }
            } else {
                // Fresh variable with no substitution — it's a free parameter.
                // The expansion is incomplete; return None so this substitution
                // is not used for bound feasibility inference (#4830).
                return None;
            }
        }

        expanded_coeffs.retain(|_, v| !v.is_zero());

        if !expanded_coeffs.is_empty() && expanded_coeffs.keys().all(|&v| v < num_original_vars) {
            let mut coeffs_vec: Vec<_> = expanded_coeffs.into_iter().collect();
            coeffs_vec.sort_by_key(|(v, _)| *v);
            Some((coeffs_vec, expanded_const))
        } else {
            None
        }
    }

    /// Expand a single substitution including free fresh parameters.
    ///
    /// Unlike `expand_single_substitution` which returns None when free
    /// parameters are encountered, this method includes them in the
    /// expansion. This preserves GCD information needed for modular
    /// constraint detection.
    ///
    /// Returns (coefficients_map, expanded_constant) where coefficients
    /// may include both original and fresh variable indices.
    fn expand_substitution_with_free_params(
        &self,
        coeffs: &HashMap<usize, BigInt>,
        constant: &BigInt,
    ) -> (HashMap<usize, BigInt>, BigInt) {
        let mut expanded_coeffs: HashMap<usize, BigInt> = HashMap::default();
        let mut expanded_const = constant.clone();
        let mut worklist: Vec<(usize, BigInt)> =
            coeffs.iter().map(|(&v, c)| (v, c.clone())).collect();

        let mut iteration = 0;
        let max_iterations = 100;
        while let Some((dep_var, dep_coeff)) = worklist.pop() {
            iteration += 1;
            if iteration > max_iterations {
                break;
            }

            if let Some((sub_coeffs, sub_const)) = self.substitutions.get(&dep_var) {
                // Variable has a substitution — expand it
                expanded_const += &dep_coeff * sub_const;
                for (&sub_dep, sub_c) in sub_coeffs {
                    worklist.push((sub_dep, &dep_coeff * sub_c));
                }
            } else {
                // Original variable or free fresh parameter — keep as-is
                *expanded_coeffs.entry(dep_var).or_insert_with(BigInt::zero) += &dep_coeff;
            }
        }

        expanded_coeffs.retain(|_, v| !v.is_zero());
        (expanded_coeffs, expanded_const)
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
    /// meaning `var ≡ residue (mod gcd)`.
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

        for (&var, (coeffs, constant)) in &self.substitutions {
            if var >= num_original_vars {
                continue;
            }

            let (expanded_coeffs, expanded_const) =
                self.expand_substitution_with_free_params(coeffs, constant);

            if expanded_coeffs.is_empty() {
                continue;
            }

            // Compute GCD of all coefficient absolute values
            let mut gcd = BigInt::zero();
            for coeff in expanded_coeffs.values() {
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
                let residue = positive_mod(&expanded_const, &gcd);
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
