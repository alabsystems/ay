//! Model patching for NRA solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Before generating lemmas, try to fix the LRA model so that monomials
//! agree with the product of their factors. This avoids unnecessary
//! lemma generation and can discover SAT results faster.
//!
//! Algorithm from Z3's `nla_core.cpp:patch_monomials()` (lines 1160-1224):
//!   1. For each inconsistent monomial m with factors x₁,...,xₙ:
//!      - Compute correct product c = val(x₁) * ... * val(xₙ)
//!      - Direct patch: if c is within m's bounds, set val(m) = c
//!      - Factor patch: try adjusting one factor to make the product correct
//!   2. If all monomials become consistent, the model is valid — return SAT.

use ay_core::term::TermId;
use ay_core::TheorySolver;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::monomial::Monomial;
use crate::NraSolver;

/// A planned patch: variable to change and the target value.
struct PatchPlan {
    var: TermId,
    value: BigRational,
}

impl NraSolver<'_> {
    /// Collect monomials whose auxiliary is absent or disagrees with the factor
    /// product. An absent auxiliary can occur when a nonlinear term appears
    /// only beneath an uninterpreted-function application: its factors still
    /// have arithmetic model values, but LRA never needed a row for the term
    /// itself. Treat that as an exact extension to materialize, not as a reason
    /// to weaken the final consistency check.
    fn collect_inconsistent_monomials(&self) -> Vec<(Monomial, BigRational)> {
        let mut patches = Vec::new();
        for mon in self.products() {
            if let Some(product) = self.compute_monomial_product(mon) {
                if self
                    .var_value(mon.aux_var)
                    .is_none_or(|value| value != product)
                {
                    patches.push((mon.clone(), product));
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
        Some(mon.aux_from_product(&product))
    }

    /// Decide how to patch each inconsistent monomial. Returns `None` if any
    /// monomial cannot be patched.
    fn plan_patches(&self, patches: &[(Monomial, BigRational)]) -> Option<Vec<PatchPlan>> {
        let mut plans = Vec::new();
        let mut patched_vars: Vec<TermId> = Vec::new();

        for (mon, correct_product) in patches {
            // Strategy 1: Direct patch — set monomial aux_var to correct product
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
            let other_product = &mon.coeff * self.product_excluding_factor(mon, idx)?;
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
        let Some((lower, upper)) = self.lra.get_bounds(var) else {
            // No LRA variable means no row or bound constrains this term. The
            // caller will register it and install exact equal lower/upper cuts
            // in the tentative scope. This is the model extension needed for
            // products occurring only below opaque applications.
            return true;
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
        for mon in self.products() {
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
        // Compute old and new products
        let mut old_product = BigRational::one();
        let mut new_product = BigRational::one();
        for &v in &mon.vars {
            let Some(val) = self.var_value(v) else {
                return false; // Unknown value — assume safe
            };
            old_product *= &val;
            new_product *= if v == var { new_value.clone() } else { val };
        }

        let Some(m_val) = self.var_value(mon.aux_var) else {
            return false;
        };
        let was_consistent = m_val == mon.aux_from_product(&old_product);
        let is_consistent = m_val == mon.aux_from_product(&new_product);
        was_consistent && !is_consistent
    }

    /// Apply a model patch by injecting Gomory cuts that force the variable
    /// to equal the target value. These cuts must be wrapped in push/pop
    /// to avoid permanently over-constraining the LRA system.
    fn apply_patch(&mut self, var: TermId, value: &BigRational) {
        use ay_lra::GomoryCut;

        let lra_var = self.lra.ensure_var_registered(var);
        let coeffs = vec![(lra_var, BigRational::one())];

        // Lower bound: var >= value
        self.lra.add_gomory_cut(
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
        self.lra.add_gomory_cut(
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
                continue; // division by zero — no patch possible
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

    /// Tentative model patching: push LRA scope, apply patches, verify
    /// feasibility. If the patched model is LRA-feasible and monomials
    /// and divisions are consistent, return true (scope is kept). Otherwise
    /// pop the scope to undo the patches and return false. (#4125 soundness fix)
    pub(crate) fn try_tentative_patch(&mut self) -> bool {
        let mon_patches = self.collect_inconsistent_monomials();
        let div_patches = self.collect_inconsistent_division_patches();
        if mon_patches.is_empty() && div_patches.is_empty() {
            return !self.has_inconsistent_monomials();
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
        self.lra.push();

        self.apply_planned_patches(&all_plans);

        // Verify: LRA must be feasible with the patched values
        use ay_core::TheoryResult;
        match self.lra.check() {
            TheoryResult::Sat | TheoryResult::Unknown
                // LRA is feasible — verify monomials and divisions are consistent
                if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions() => {
                    if self.debug {
                        tracing::debug!(
                            "[NRA] Tentative patch succeeded: {} monomials, {} divisions",
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

        // Patch failed — undo the cuts
        self.lra.pop();
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::{Symbol, TermStore};
    use ay_core::{Sort, TheoryResult};
    use num_bigint::BigInt;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn opaque_positive(terms: &mut TermStore, argument: TermId) -> TermId {
        let application = terms.mk_app(Symbol::named("f"), vec![argument], Sort::Real);
        let zero = terms.mk_rational(BigRational::zero());
        terms.mk_gt(application, zero)
    }

    #[test]
    fn missing_scaled_product_aux_is_materialized_exactly() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let two = terms.mk_rational(integer(2));
        let three = terms.mk_rational(integer(3));
        let product = terms.mk_mul(vec![three, x, x]);
        let x_is_two = terms.mk_eq(x, two);
        let uf_atom = opaque_positive(&mut terms, product);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(x_is_two, true);
        solver.assert_literal(uf_atom, true);

        assert!(matches!(solver.check(), TheoryResult::Sat));
        assert_eq!(solver.var_value(product), Some(integer(12)));
        assert!(!solver.has_inconsistent_monomials());
    }

    #[test]
    fn missing_product_factor_remains_fail_closed() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let two = terms.mk_rational(integer(2));
        let product = terms.mk_mul(vec![x, y]);
        let x_is_two = terms.mk_eq(x, two);
        let uf_atom = opaque_positive(&mut terms, product);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(x_is_two, true);
        solver.assert_literal(uf_atom, true);

        assert!(matches!(solver.check(), TheoryResult::Unknown));
        assert!(solver.var_value(y).is_none());
        assert!(solver.has_inconsistent_monomials());
    }

    #[test]
    fn missing_symbolic_division_beneath_uf_remains_extendable() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let one = terms.mk_rational(integer(1));
        let two = terms.mk_rational(integer(2));
        let division = terms.mk_div(one, x);
        let x_is_two = terms.mk_eq(x, two);
        let uf_atom = opaque_positive(&mut terms, division);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(x_is_two, true);
        solver.assert_literal(uf_atom, true);

        assert!(matches!(solver.check(), TheoryResult::Sat));
        assert!(!solver.has_inconsistent_divisions());
        assert!(!solver.zero_divisor_model_is_unsound());
    }
}
