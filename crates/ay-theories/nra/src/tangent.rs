//! Linearization constraints for NRA solver: McCormick envelopes + tangent planes
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! ## McCormick Envelopes (binary monomials with known bounds)
//!
//! For m = x*y with x ∈ [xL, xU], y ∈ [yL, yU], the tightest convex
//! relaxation is the McCormick envelope (McCormick, 1976):
//!
//!   Lower: m ≥ xL*y + x*yL - xL*yL   (tangent at (xL, yL))
//!          m ≥ xU*y + x*yU - xU*yU   (tangent at (xU, yU))
//!   Upper: m ≤ xU*y + x*yL - xU*yL   (tangent at (xU, yL))
//!          m ≤ xL*y + x*yU - xL*yU   (tangent at (xL, yU))
//!
//! These are globally valid over the box [xL,xU] × [yL,yU].
//!
//! ## Tangent hyperplanes (higher-degree monomials)
//!
//! For m = x₁*x₂*...*xₙ at model point (v₁,...,vₙ):
//!   T(x₁,...,xₙ) = Σᵢ (∏_{j≠i} vⱼ) * xᵢ - (n-1) * ∏ᵢ vᵢ
//!
//! Based on Z3's `nla_tangent_lemmas.cpp`.

use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::monomial::Monomial;
use crate::NraSolver;

impl NraSolver<'_> {
    /// Add a single McCormick bound: m - a*y - b*x [cmp] -a*b
    ///
    /// `vars`: (m_var, x_var, y_var) — LRA variable indices for the monomial.
    fn add_mccormick_bound(
        &mut self,
        m: ay_core::term::TermId,
        vars: (u32, u32, u32),
        a_val: &BigRational,
        b_val: &BigRational,
        is_lower: bool,
    ) {
        let (m_var, x_var, y_var) = vars;
        let coeffs = vec![
            (m_var, BigRational::one()),
            (y_var, -a_val.clone()),
            (x_var, -b_val.clone()),
        ];
        let bound = -(a_val * b_val);
        self.lra.add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            m,
        );
    }

    /// Add McCormick envelope constraints for a binary monomial m = x*y.
    ///
    /// Uses bounds from the LRA solver to generate globally valid linear
    /// relaxations. Returns the number of constraints added.
    pub(crate) fn add_mccormick_constraints(&mut self, mon: &Monomial) -> usize {
        if !mon.is_binary() {
            return 0;
        }

        let Some(x) = mon.x() else { return 0 };
        let Some(y) = mon.y() else { return 0 };
        let m = mon.aux_var;

        let (x_lb, x_ub) = match self.lra.get_bounds(x) {
            Some((lb, ub)) => (lb, ub),
            None => return 0,
        };
        let (y_lb, y_ub) = match self.lra.get_bounds(y) {
            Some((lb, ub)) => (lb, ub),
            None => return 0,
        };

        let vars = (
            self.lra.ensure_var_registered(m),
            self.lra.ensure_var_registered(x),
            self.lra.ensure_var_registered(y),
        );

        let mut count = 0;

        // Lower bound 1: m ≥ xL*y + yL*x - xL*yL
        if let (Some(ref xl), Some(ref yl)) = (&x_lb, &y_lb) {
            self.add_mccormick_bound(m, vars, &xl.value_big(), &yl.value_big(), true);
            count += 1;
        }
        // Lower bound 2: m ≥ xU*y + yU*x - xU*yU
        if let (Some(ref xu), Some(ref yu)) = (&x_ub, &y_ub) {
            self.add_mccormick_bound(m, vars, &xu.value_big(), &yu.value_big(), true);
            count += 1;
        }
        // Upper bound 1: m ≤ xU*y + yL*x - xU*yL
        if let (Some(ref xu), Some(ref yl)) = (&x_ub, &y_lb) {
            self.add_mccormick_bound(m, vars, &xu.value_big(), &yl.value_big(), false);
            count += 1;
        }
        // Upper bound 2: m ≤ xL*y + yU*x - xL*yU
        if let (Some(ref xl), Some(ref yu)) = (&x_lb, &y_ub) {
            self.add_mccormick_bound(m, vars, &xl.value_big(), &yu.value_big(), false);
            count += 1;
        }

        if self.debug {
            tracing::debug!(
                "[NRA] McCormick envelope: {} constraints for m={:?}",
                count,
                m
            );
        }

        count
    }

    /// Add a tangent hyperplane constraint for a general degree-N monomial.
    ///
    /// For m = x₁*x₂*...*xₙ at model point v = (v₁,...,vₙ):
    ///   T(x) = Σᵢ (∏_{j≠i} vⱼ) * xᵢ - (n-1) * ∏ᵢ vᵢ
    ///
    /// Linear constraint: m - Σᵢ (∏_{j≠i} vⱼ) * xᵢ  [cmp]  -(n-1) * product
    pub(crate) fn add_tangent_constraint_general(
        &mut self,
        mon: &Monomial,
        factor_values: &[BigRational],
        is_below: bool,
    ) -> bool {
        let n = mon.vars.len();
        if n < 2 || n != factor_values.len() {
            return false;
        }

        let m = mon.aux_var;
        let m_var = self.lra.ensure_var_registered(m);

        // Compute the full product: v₁ * v₂ * ... * vₙ
        let mut full_product = BigRational::one();
        for v in factor_values {
            full_product *= v;
        }

        // Build coefficients: m has coefficient 1, each xᵢ has coefficient -(∏_{j≠i} vⱼ)
        let mut coeffs = Vec::with_capacity(n + 1);
        coeffs.push((m_var, BigRational::one()));

        for (i, &var) in mon.vars.iter().enumerate() {
            let var_id = self.lra.ensure_var_registered(var);

            // ∏_{j≠i} vⱼ = full_product / vᵢ
            // If vᵢ = 0, the partial derivative is 0 (skip this term)
            if factor_values[i].is_zero() {
                continue;
            }
            let partial = &full_product / &factor_values[i];
            coeffs.push((var_id, -partial));
        }

        // Bound: -(n-1) * full_product
        let n_minus_1 = BigRational::from_integer((n as i64 - 1).into());
        let bound = -(&n_minus_1 * &full_product);

        let cut = GomoryCut {
            coeffs,
            bound,
            is_lower: is_below,
            reasons: Vec::new(),
            source_term: None,
        };

        self.lra.add_gomory_cut(&cut, m);

        if self.debug {
            tracing::debug!(
                "[NRA] Added tangent hyperplane (degree {}): {} for m={:?}",
                n,
                if is_below { ">=" } else { "<=" },
                m
            );
        }

        true
    }

    /// Add basic non-negativity lemma for even-power monomials.
    ///
    /// For m = x^2 (or x^2k), m >= 0 is always true. When the LRA model
    /// assigns m < 0, this constraint forces the model to respect the
    /// algebraic identity.
    pub(crate) fn add_even_power_nonneg(&mut self, mon: &Monomial) -> bool {
        // Check if the monomial is an even power: all factors are the same variable.
        if mon.vars.is_empty() {
            return false;
        }
        let first = mon.vars[0];
        let is_even_power =
            mon.vars.len().is_multiple_of(2) && mon.vars.iter().all(|&v| v == first);
        if !is_even_power {
            return false;
        }

        // Check if aux value is already non-negative — no lemma needed.
        if let Some(v) = self.var_value(mon.aux_var) {
            if v >= BigRational::zero() {
                return false;
            }
        }

        let m_var = self.lra.ensure_var_registered(mon.aux_var);
        let coeffs = vec![(m_var, BigRational::one())];
        let bound = BigRational::zero();
        self.lra.add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower: true, // m >= 0
                reasons: Vec::new(),
                source_term: None,
            },
            mon.aux_var,
        );
        true
    }

    /// Add linearization constraints for all monomials with incorrect values.
    /// Uses McCormick envelopes for binary monomials (sound, globally valid).
    /// Falls back to tangent hyperplanes when McCormick is unavailable (no bounds).
    /// Returns the number of constraints added.
    /// Returns `(total_added, used_tangent_hyperplane)` where `used_tangent_hyperplane`
    /// is true if any tangent hyperplane (model-point approximation) was added.
    /// McCormick envelopes and even-power non-negativity are exact and do not set
    /// this flag (#5959).
    pub(crate) fn add_tangent_constraints_for_incorrect_monomials(&mut self) -> (usize, bool) {
        let mut binary_mons: Vec<(Monomial, Vec<BigRational>, bool)> = Vec::new();
        let mut general_constrain: Vec<(Monomial, Vec<BigRational>, bool)> = Vec::new();

        let mut sorted_mons: Vec<_> = self.monomials.values().collect();
        sorted_mons.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));

        for mon in sorted_mons {
            // Collect factor values for all monomials
            let mut factor_values = Vec::with_capacity(mon.vars.len());
            let mut all_known = true;
            for &var in &mon.vars {
                if let Some(val) = self.var_value(var) {
                    factor_values.push(val);
                } else {
                    all_known = false;
                    break;
                }
            }
            if !all_known {
                continue;
            }

            let Some(v) = self.var_value(mon.aux_var) else {
                continue;
            };

            let mut c = BigRational::one();
            for fv in &factor_values {
                c *= fv;
            }

            if v == c {
                continue;
            }

            if mon.is_binary() {
                binary_mons.push((mon.clone(), factor_values, v < c));
            } else {
                general_constrain.push((mon.clone(), factor_values, v < c));
            }
        }

        let mut count = 0;
        let mut used_tangent = false;

        // Binary monomials: try McCormick first, fall back to tangent hyperplane
        for (mon, factor_values, is_below) in binary_mons {
            let mc = self.add_mccormick_constraints(&mon);
            if mc > 0 {
                count += mc;
            } else {
                // McCormick unavailable (unbounded variables). Add basic lemmas
                // and tangent hyperplane at model point instead.
                if self.add_even_power_nonneg(&mon) {
                    count += 1;
                }
                if self.add_tangent_constraint_general(&mon, &factor_values, is_below) {
                    count += 1;
                    used_tangent = true;
                }
            }
        }

        // Higher-degree monomials: tangent hyperplane at model point
        for (mon, factor_values, is_below) in general_constrain {
            self.add_even_power_nonneg(&mon);
            if self.add_tangent_constraint_general(&mon, &factor_values, is_below) {
                count += 1;
                used_tangent = true;
            }
        }

        (count, used_tangent)
    }
}

#[cfg(test)]
#[path = "tangent_tests.rs"]
mod tests;
