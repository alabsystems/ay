// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model patching for NIA solver
//!
//! Before generating lemmas, try to fix the LIA model so that monomials
//! agree with the product of their factors. Avoids unnecessary lemma
//! generation and can discover SAT results faster.
//!
//! Algorithm from Z3's `nla_core.cpp:patch_monomials()` (lines 1160-1224):
//!   1. For each inconsistent monomial m with factors x1,...,xn:
//!      - Compute correct product c = val(x1) * ... * val(xn)
//!      - Direct patch: if c is within m's bounds, set val(m) = c
//!      - Factor patch: try adjusting one factor to make the product correct
//!   2. If all monomials become consistent, the model is valid -- return SAT.

use ay_core::term::TermId;
use ay_core::TheorySolver;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::Monomial;
use super::NiaSolver;
use ay_lra::GomoryCut;

/// A planned patch: variable to change and the target value.
struct PatchPlan {
    var: TermId,
    value: BigRational,
}

impl NiaSolver<'_> {
    /// Collect monomials whose aux_var value disagrees with the factor product.
    fn collect_inconsistent_monomials(&self) -> Vec<(Monomial, BigRational)> {
        let mut patches = Vec::new();
        for mon in self.monomials.values() {
            if let Some(product) = self.compute_monomial_product(mon) {
                if let Some(m_val) = self.var_value(mon.aux_var) {
                    if m_val != product {
                        patches.push((mon.clone(), product));
                    }
                }
            }
        }
        patches
    }

    /// Compute the product of a monomial's factors from the current model.
    fn compute_monomial_product(&self, mon: &Monomial) -> Option<BigRational> {
        let mut product = BigRational::one();
        for &var in &mon.vars {
            product *= self.var_value(var)?;
        }
        Some(product)
    }

    /// Decide how to patch each inconsistent monomial. Returns `None` if any
    /// monomial cannot be patched.
    fn plan_patches(&self, patches: &[(Monomial, BigRational)]) -> Option<Vec<PatchPlan>> {
        let mut plans = Vec::new();
        let mut patched_vars: Vec<TermId> = Vec::new();

        for (mon, correct_product) in patches {
            // Strategy 1: Direct patch -- set monomial aux_var to correct product
            if self.can_patch_to(mon.aux_var, correct_product)
                && !self.would_break_other_monomials(mon.aux_var, correct_product, &patched_vars)
            {
                plans.push(PatchPlan {
                    var: mon.aux_var,
                    value: correct_product.clone(),
                });
                patched_vars.push(mon.aux_var);
                continue;
            }

            // Strategy 2: Factor patch
            {
                let plan = self.try_factor_patch(mon, &patched_vars)?;
                patched_vars.push(plan.var);
                plans.push(plan);
            }
        }

        Some(plans)
    }

    /// Try adjusting one factor of a monomial so its product matches val(m).
    fn try_factor_patch(&self, mon: &Monomial, patched_vars: &[TermId]) -> Option<PatchPlan> {
        let m_val = self.var_value(mon.aux_var)?;

        for (idx, &var) in mon.vars.iter().enumerate() {
            if patched_vars.contains(&var) {
                continue;
            }
            let other_product = self.product_excluding_factor(mon, idx)?;
            if other_product.is_zero() {
                continue;
            }

            let new_val = &m_val / &other_product;
            if self.can_patch_to(var, &new_val)
                && !self.would_break_other_monomials(var, &new_val, patched_vars)
            {
                return Some(PatchPlan {
                    var,
                    value: new_val,
                });
            }
        }
        None
    }

    /// Compute product of all factors of a monomial except the one at `skip_idx`.
    fn product_excluding_factor(&self, mon: &Monomial, skip_idx: usize) -> Option<BigRational> {
        let mut product = BigRational::one();
        for (j, &var) in mon.vars.iter().enumerate() {
            if j == skip_idx {
                continue;
            }
            product *= self.var_value(var)?;
        }
        Some(product)
    }

    /// Apply all planned patches by injecting tight bounds into LRA.
    fn apply_planned_patches(&mut self, plans: &[PatchPlan]) {
        for plan in plans {
            self.apply_patch(plan.var, &plan.value);
        }
    }

    /// Check whether a variable can be set to a given value without violating bounds.
    fn can_patch_to(&self, var: TermId, value: &BigRational) -> bool {
        let Some((lower, upper)) = self.lia.lra_solver().get_bounds(var) else {
            return false;
        };
        if let Some(ref lb) = lower {
            let lb_val = lb.value_big();
            if lb.strict && value <= &lb_val {
                return false;
            }
            if !lb.strict && value < &lb_val {
                return false;
            }
        }
        if let Some(ref ub) = upper {
            let ub_val = ub.value_big();
            if ub.strict && value >= &ub_val {
                return false;
            }
            if !ub.strict && value > &ub_val {
                return false;
            }
        }
        true
    }

    /// Check whether patching a variable would make another monomial inconsistent.
    fn would_break_other_monomials(
        &self,
        var: TermId,
        new_value: &BigRational,
        already_patched: &[TermId],
    ) -> bool {
        for mon in self.monomials.values() {
            if !mon.vars.contains(&var) || already_patched.contains(&mon.aux_var) {
                continue;
            }
            if self.would_break_monomial(mon, var, new_value) {
                return true;
            }
        }
        false
    }

    /// Check if patching `var` to `new_value` would break a specific monomial.
    fn would_break_monomial(&self, mon: &Monomial, var: TermId, new_value: &BigRational) -> bool {
        let mut old_product = BigRational::one();
        let mut new_product = BigRational::one();
        for &v in &mon.vars {
            let Some(val) = self.var_value(v) else {
                return false;
            };
            old_product *= &val;
            new_product *= if v == var { new_value.clone() } else { val };
        }

        let Some(m_val) = self.var_value(mon.aux_var) else {
            return false;
        };
        let was_consistent = m_val == old_product;
        let is_consistent = m_val == new_product;
        was_consistent && !is_consistent
    }

    /// Apply a model patch by injecting Gomory cuts that force the variable
    /// to equal the target value.
    fn apply_patch(&mut self, var: TermId, value: &BigRational) {
        let lra_var = self.lia.lra_solver_mut().ensure_var_registered(var);
        let coeffs = vec![(lra_var, BigRational::one())];

        // Lower bound: var >= value
        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs: coeffs.clone(),
                bound: value.clone(),
                is_lower: true,
                reasons: Vec::new(),
                source_term: None,
            },
            var,
        );

        // Upper bound: var <= value
        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound: value.clone(),
                is_lower: false,
                reasons: Vec::new(),
                source_term: None,
            },
            var,
        );
    }

    /// Collect division purifications whose model values are inconsistent:
    /// `model(denom) * model(div_term) != model(num)`.
    /// Returns list of `(div_term, correct_value)` patches.
    /// Ported from NRA (#8453, #6811).
    fn collect_inconsistent_division_patches(&self) -> Vec<PatchPlan> {
        let mut patches = Vec::new();
        for purif in &self.div_purifications {
            let Some(d) = self.var_value(purif.denominator) else {
                continue;
            };
            let Some(k) = self.var_value(purif.div_term) else {
                continue;
            };
            let Some(num_val) = self.term_value(purif.numerator) else {
                continue;
            };
            if &d * &k == num_val {
                continue; // already consistent
            }
            if d.is_zero() {
                continue; // division by zero -- no patch possible
            }
            let correct_div = &num_val / &d;
            if self.can_patch_to(purif.div_term, &correct_div) {
                patches.push(PatchPlan {
                    var: purif.div_term,
                    value: correct_div,
                });
            }
        }
        patches
    }

    /// Integer rounding: when simplex returns a non-integral rational value
    /// for a monomial factor variable, try floor and ceil to find a nearby
    /// integer that satisfies bounds and makes monomial products consistent.
    ///
    /// This is NIA-specific: NRA doesn't need it because real-valued solutions
    /// are acceptable. For NIA, the model must ultimately consist of integers,
    /// so rounding fractional values toward valid integer points accelerates
    /// convergence. (#8453)
    ///
    /// Returns true if at least one variable was successfully rounded.
    pub(crate) fn try_integer_rounding(&mut self) -> bool {
        // Collect unique monomial factor variables (not aux vars)
        let mut factor_vars: Vec<TermId> = Vec::new();
        for mon in self.monomials.values() {
            for &var in &mon.vars {
                if !factor_vars.contains(&var) && !self.aux_to_monomial.contains_key(&var) {
                    factor_vars.push(var);
                }
            }
        }
        factor_vars.sort_by_key(|t| t.0);

        let mut any_rounded = false;

        for &var in &factor_vars {
            let Some(val) = self.var_value(var) else {
                continue;
            };

            // Check if value is already an integer
            if val.denom() == &BigInt::one() {
                continue;
            }

            // Compute floor and ceil
            let (quot, rem) = val.numer().div_rem(val.denom());
            let floor_val = if rem.is_zero() || val.numer() > &BigInt::zero() {
                quot.clone()
            } else {
                &quot - &BigInt::one()
            };
            let ceil_val = if rem.is_zero() {
                quot
            } else if val.numer() > &BigInt::zero() {
                &quot + &BigInt::one()
            } else {
                quot
            };

            // Try both candidates, preferring the one closer to the current value
            let floor_rat = BigRational::from_integer(floor_val);
            let ceil_rat = BigRational::from_integer(ceil_val);

            let candidates = if (&val - &floor_rat).abs() <= (&val - &ceil_rat).abs() {
                [&floor_rat, &ceil_rat]
            } else {
                [&ceil_rat, &floor_rat]
            };

            for candidate in candidates {
                if !self.can_patch_to(var, candidate) {
                    continue;
                }
                // Check if rounding would break any monomials that are currently consistent
                if self.would_break_other_monomials(var, candidate, &[]) {
                    continue;
                }
                // Apply the rounding
                self.apply_patch(var, candidate);
                any_rounded = true;
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Integer rounding: {:?} = {} -> {}",
                        var,
                        val,
                        candidate
                    );
                }
                break;
            }
        }

        any_rounded
    }

    /// Tentative model patching: push LIA scope, apply patches, verify
    /// feasibility. If the patched model is LIA-feasible and monomials
    /// and divisions are consistent, return true (scope is kept). Otherwise
    /// pop the scope to undo the patches and return false. (#4125 soundness fix)
    pub(crate) fn try_tentative_patch(&mut self) -> bool {
        let mon_patches = self.collect_inconsistent_monomials();
        let div_patches = self.collect_inconsistent_division_patches();
        if mon_patches.is_empty() && div_patches.is_empty() {
            return !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions();
        }

        let mut all_plans = match self.plan_patches(&mon_patches) {
            Some(p) => p,
            None => return false,
        };
        all_plans.extend(div_patches);

        if all_plans.is_empty() {
            return false;
        }

        // Push a scope so patch cuts can be undone
        self.lia.push();

        self.apply_planned_patches(&all_plans);

        // Verify: LIA must be feasible with the patched values
        use ay_core::TheoryResult;
        match self.lia.check() {
            TheoryResult::Sat | TheoryResult::Unknown
                // LIA is feasible -- verify monomials and divisions are consistent
                if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions() => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Tentative patch succeeded: {} monomials, {} divisions",
                            mon_patches.len(),
                            all_plans.len() - mon_patches.len()
                        );
                    }
                    // Keep the scope (patched values active).
                    // Increment depth so undo_tentative_patch() pops
                    // both this scope and the sign-cut scope.
                    self.tentative_depth += 1;
                    return true;
                }
            _ => {}
        }

        // Patch failed -- undo the cuts
        self.lia.pop();
        false
    }

    /// Check if any tracked monomial has an inconsistent value
    pub(crate) fn has_inconsistent_monomials(&self) -> bool {
        self.monomials
            .values()
            .any(|m| !self.check_monomial_consistency(m))
    }
}
