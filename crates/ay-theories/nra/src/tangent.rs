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
//!
//! ## Fixed-factor linearization (exact, no bounds required)
//!
//! Both relaxations above need a finite box: McCormick returns NOTHING when
//! either factor is unbounded, and the tangent plane is only an approximation
//! at the model point, so any UNSAT reached through it must be rechecked and
//! any SAT near an irrational witness is unreachable.
//!
//! But a product needs no box at all when the ASSERTED constraints already pin
//! all of its factors but one. If `x = c` follows from the assertions, then
//!
//!   `m = x*y  ∧  x = c   ⊨   m = c*y`
//!
//! for EVERY real `y` — a linear identity, not a relaxation. Likewise `m = 0`
//! whenever any pinned factor is zero, whatever the remaining factors are, and
//! `m = c₁·…·cₙ` when every factor is pinned.
//!
//! This is the shape of the template-synthesis families (LassoRanker,
//! UltimateAutomizer): the products are `motzkin · templateVar` where the
//! Motzkin multiplier is confined to `{0, 1}` by a case-split clause and the
//! template coefficient is a completely unbounded real. Once DPLL(T) picks a
//! side of the split, every one of those products becomes linear — the whole
//! query collapses into LRA. Before this, the linearization saturated in
//! milliseconds with `McCormick envelope: 0 constraints` on every monomial and
//! the check loop returned `unknown`.
//!
//! Soundness: the pins come from [`NraSolver::fixed_factor_values`], which is
//! computed from the LRA bound state BEFORE any tentative scope is pushed, so
//! it never picks up a model-point patch, sign cut or feasible-set pin. The
//! emitted equalities are therefore implied by the asserted atoms, exactly like
//! McCormick over asserted bounds — they do NOT set the tangent-approximation
//! flag, and an UNSAT reached with them alone stays genuine.

use ay_core::term::TermId;
use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::monomial::Monomial;
use crate::NraSolver;

#[path = "tangent/fixed_factor.rs"]
mod fixed_factor;
impl NraSolver<'_> {
    /// Add a single McCormick bound: m - a*y - b*x [cmp] -a*b
    ///
    /// `vars`: (m_var, x_var, y_var) — LRA variable indices for the monomial.
    ///
    /// Returns `true` when the row was NEW (see
    /// [`NraSolver::add_linearization_cut`]); a row identical to one already
    /// live in this scope is suppressed and reported as no progress.
    fn add_mccormick_bound(
        &mut self,
        m: TermId,
        vars: (u32, u32, u32),
        aux_reciprocal: &BigRational,
        a_val: &BigRational,
        b_val: &BigRational,
        is_lower: bool,
    ) -> bool {
        let (m_var, x_var, y_var) = vars;
        let coeffs = vec![
            (m_var, aux_reciprocal.clone()),
            (y_var, -a_val.clone()),
            (x_var, -b_val.clone()),
        ];
        let bound = -(a_val * b_val);
        self.add_linearization_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            m,
        )
    }

    /// Add McCormick envelope constraints for a binary monomial m = x*y.
    ///
    /// Uses bounds from the LRA solver to generate globally valid linear
    /// relaxations. Returns `(new_rows, available_rows)`: `available_rows`
    /// counts the envelope rows the current bounds support at all (0 means the
    /// factors are too unbounded for McCormick, which is what selects the
    /// tangent-hyperplane fallback), while `new_rows` counts only the ones this
    /// call actually added. The two differ exactly when the envelope has
    /// SATURATED — the loop has already emitted these rows and re-deriving them
    /// is not progress.
    pub(crate) fn add_mccormick_constraints(&mut self, mon: &Monomial) -> (usize, usize) {
        if !mon.is_binary() {
            return (0, 0);
        }

        let Some(x) = mon.x() else { return (0, 0) };
        let Some(y) = mon.y() else { return (0, 0) };
        let m = mon.aux_var;

        let (x_lb, x_ub) = match self.lra.get_bounds(x) {
            Some((lb, ub)) => (lb, ub),
            None => return (0, 0),
        };
        let (y_lb, y_ub) = match self.lra.get_bounds(y) {
            Some((lb, ub)) => (lb, ub),
            None => return (0, 0),
        };

        let vars = (
            self.lra.ensure_var_registered(m),
            self.lra.ensure_var_registered(x),
            self.lra.ensure_var_registered(y),
        );
        let aux_reciprocal = BigRational::one() / &mon.coeff;

        let mut new_rows = 0;
        let mut available = 0;

        // Lower bound 1: m ≥ xL*y + yL*x - xL*yL
        if let (Some(ref xl), Some(ref yl)) = (&x_lb, &y_lb) {
            available += 1;
            new_rows += usize::from(self.add_mccormick_bound(
                m,
                vars,
                &aux_reciprocal,
                &xl.value_big(),
                &yl.value_big(),
                true,
            ));
        }
        // Lower bound 2: m ≥ xU*y + yU*x - xU*yU
        if let (Some(ref xu), Some(ref yu)) = (&x_ub, &y_ub) {
            available += 1;
            new_rows += usize::from(self.add_mccormick_bound(
                m,
                vars,
                &aux_reciprocal,
                &xu.value_big(),
                &yu.value_big(),
                true,
            ));
        }
        // Upper bound 1: m ≤ xU*y + yL*x - xU*yL
        if let (Some(ref xu), Some(ref yl)) = (&x_ub, &y_lb) {
            available += 1;
            new_rows += usize::from(self.add_mccormick_bound(
                m,
                vars,
                &aux_reciprocal,
                &xu.value_big(),
                &yl.value_big(),
                false,
            ));
        }
        // Upper bound 2: m ≤ xL*y + yU*x - xL*yU
        if let (Some(ref xl), Some(ref yu)) = (&x_lb, &y_ub) {
            available += 1;
            new_rows += usize::from(self.add_mccormick_bound(
                m,
                vars,
                &aux_reciprocal,
                &xl.value_big(),
                &yu.value_big(),
                false,
            ));
        }

        if self.debug {
            tracing::debug!(
                "[NRA] McCormick envelope: {} new of {} available constraints for m={:?}",
                new_rows,
                available,
                m
            );
        }

        (new_rows, available)
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

        // Build coefficients: m has coefficient 1/coeff, each xᵢ has
        // coefficient -(∏_{j≠i} vⱼ).
        let mut coeffs = Vec::with_capacity(n + 1);
        coeffs.push((m_var, BigRational::one() / &mon.coeff));

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

        // A tangent plane is taken AT the model point, so an identical row means
        // the point has not moved — no progress, and the caller must be told so
        // rather than counting the same plane again.
        if !self.add_linearization_cut(&cut, m) {
            return false;
        }

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
        self.add_even_power_nonneg_with_reasons(mon, &[])
    }

    /// Add even-power non-negativity with asserted reasons for global replay.
    pub(crate) fn add_even_power_nonneg_with_reasons(
        &mut self,
        mon: &Monomial,
        reasons: &[(TermId, bool)],
    ) -> bool {
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

        // The lemma concerns the bare even power, i.e. `aux / coeff >= 0`.
        if let Some(v) = self.var_value(mon.aux_var) {
            if mon.product_from_aux(&v) >= BigRational::zero() {
                return false;
            }
        }

        let m_var = self.lra.ensure_var_registered(mon.aux_var);
        let coeffs = vec![(m_var, BigRational::one() / &mon.coeff)];
        let bound = BigRational::zero();
        self.lra.add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower: true, // m >= 0
                reasons: reasons.to_vec(),
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

        let mut sorted_mons: Vec<_> = self.products().collect();
        sorted_mons.sort_unstable_by(|a, b| (&a.vars, a.aux_var.0).cmp(&(&b.vars, b.aux_var.0)));

        for mon in sorted_mons {
            // Collect factor values for all monomials
            let mut factor_values = Vec::with_capacity(mon.vars.len());
            let mut all_known = true;
            for &var in &mon.vars {
                // DELIBERATELY `var_value`, not `monomial_factor_value`: every
                // cut below feeds the factor to `lra.ensure_var_registered`,
                // and `intern_var` mints a FRESH, DISCONNECTED column for any
                // term it has not seen — a compound Horner factor `(+ ...)`
                // would become an LRA variable unrelated to its own summands.
                // Cuts over such a column constrain nothing real and two of
                // them can contradict, manufacturing a spurious UNSAT. So a
                // factor without a tableau column is skipped here: this path
                // may only refine monomials it can express, and the published
                // model's correctness is the executor strict oracle's job.
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

            let mut true_product = BigRational::one();
            for fv in &factor_values {
                true_product *= fv;
            }

            let model_product = mon.product_from_aux(&v);
            if model_product == true_product {
                continue;
            }
            let is_below = model_product < true_product;

            if mon.is_binary() {
                binary_mons.push((mon.clone(), factor_values, is_below));
            } else {
                general_constrain.push((mon.clone(), factor_values, is_below));
            }
        }

        let mut count = 0;
        let mut used_tangent = false;

        // Binary monomials: exact fixed-factor identity, then McCormick, then
        // the tangent hyperplane. The identity is tried first because it is
        // strictly stronger than both (an equality, and available with no
        // bound at all on the free factor).
        for (mon, factor_values, is_below) in binary_mons {
            if self.add_fixed_factor_linearization(&mon) > 0 {
                count += 2;
                continue;
            }
            // Branch on rows the bounds SUPPORT, not on rows newly added: a
            // saturated envelope still means "McCormick is the right relaxation
            // here", so a saturated monomial must not silently acquire a
            // model-point tangent plane (that variant is measured in
            // the development design notes; it converted nothing and pushed five
            // instances into timeouts). Only the COUNT changes.
            let (mc_new, mc_available) = self.add_mccormick_constraints(&mon);
            if mc_available > 0 {
                count += mc_new;
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

        // Higher-degree monomials: exact fixed-factor identity when the pins
        // reduce them to linear, else the tangent hyperplane at the model point.
        for (mon, factor_values, is_below) in general_constrain {
            if self.add_fixed_factor_linearization(&mon) > 0 {
                count += 2;
                continue;
            }
            self.add_even_power_nonneg(&mon);
            if self.add_tangent_constraint_general(&mon, &factor_values, is_below) {
                count += 1;
                used_tangent = true;
            }
        }

        // Scaled aliases are independent LRA atoms until this exact identity
        // ties each one to the representative over the same factor multiset.
        let representatives = std::mem::take(&mut self.monomials);
        let aliases = std::mem::take(&mut self.scaled_aliases);
        count += self.add_alias_tie_constraints(&representatives, &aliases);
        self.monomials = representatives;
        self.scaled_aliases = aliases;

        (count, used_tangent)
    }

    /// Emit `alias == (alias.coeff / representative.coeff) * representative`
    /// as an exact two-sided linear identity whenever the current model violates it.
    pub(crate) fn add_alias_tie_constraints(
        &mut self,
        representatives: &crate::HashMap<Vec<TermId>, Monomial>,
        aliases: &[Monomial],
    ) -> usize {
        let mut added = 0;
        for alias in aliases {
            let Some(representative) = representatives.get(&alias.vars) else {
                continue;
            };
            let ratio = &alias.coeff / &representative.coeff;
            let (Some(alias_value), Some(representative_value)) = (
                self.var_value(alias.aux_var),
                self.var_value(representative.aux_var),
            ) else {
                continue;
            };
            if alias_value == &ratio * representative_value {
                continue;
            }
            let alias_var = self.lra.ensure_var_registered(alias.aux_var);
            let representative_var = self.lra.ensure_var_registered(representative.aux_var);
            let coefficients = vec![
                (alias_var, BigRational::one()),
                (representative_var, -ratio),
            ];
            for is_lower in [true, false] {
                self.lra.add_gomory_cut(
                    &GomoryCut {
                        coeffs: coefficients.clone(),
                        bound: BigRational::zero(),
                        is_lower,
                        reasons: Vec::new(),
                        source_term: None,
                    },
                    alias.aux_var,
                );
            }
            added += 2;
        }
        added
    }
}

#[cfg(test)]
#[path = "tangent_tests.rs"]
mod tests;
