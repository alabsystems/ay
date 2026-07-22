// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NIA sign consistency checking on `NiaSolver`.
//!
//! Supports general-degree monomials (not just binary). The product sign
//! is computed from all factor signs using `nonlinear::product_sign`.

use ay_core::nonlinear;

use super::*;

impl NiaSolver<'_> {
    /// Check if a monomial's value is consistent with its factors
    pub(crate) fn check_monomial_consistency(&self, mon: &Monomial) -> bool {
        let mut product = BigRational::one();
        for &var in &mon.vars {
            if let Some(val) = self.var_value(var) {
                product *= val;
            } else {
                return false;
            }
        }
        if let Some(aux_val) = self.var_value(mon.aux_var) {
            aux_val == product
        } else {
            false
        }
    }

    /// Check sign consistency for all monomials using constraint-based approach.
    /// Supports general-degree monomials by computing the product sign from
    /// all factor signs.
    pub(crate) fn check_sign_consistency(&self) -> Option<Vec<TheoryLit>> {
        if self.debug {
            safe_eprintln!("[NIA] check_sign_consistency: {} monomials, {} sign_constraints, {} var_sign_constraints",
                self.monomials.len(), self.sign_constraints.len(), self.var_sign_constraints.len());
            for (vars, constraints) in &self.sign_constraints {
                safe_eprintln!(
                    "[NIA]   monomial {:?} has {} constraints: {:?}",
                    vars,
                    constraints.len(),
                    constraints
                );
            }
            for (var, constraints) in &self.var_sign_constraints {
                safe_eprintln!(
                    "[NIA]   var {:?} has {} constraints: {:?}",
                    var,
                    constraints.len(),
                    constraints
                );
            }
        }

        let mut sorted_sign: Vec<_> = self.sign_constraints.iter().collect();
        sorted_sign.sort_by_key(|(a, _)| *a);
        for (vars, constraints) in sorted_sign {
            let Some(_mon) = self.monomials.get(vars) else {
                if self.debug {
                    safe_eprintln!("[NIA] No monomial found for vars {:?}", vars);
                }
                continue;
            };

            // Collect signs for all factors (general-degree support)
            let mut factor_signs = Vec::new();
            let mut all_known = true;
            for var in vars {
                let var_signs = self.var_sign_constraints.get(var);
                if let Some(sign) = nonlinear::sign_from_constraints(var_signs) {
                    factor_signs.push(sign);
                } else {
                    all_known = false;
                    break;
                }
            }

            if !all_known {
                continue;
            }

            let expected_sign = nonlinear::product_sign(&factor_signs);
            if self.debug {
                safe_eprintln!(
                    "[NIA] Monomial {:?}: factor_signs={:?}, expected_sign={}",
                    vars,
                    factor_signs,
                    expected_sign
                );
            }
            for (constraint, _assertion) in constraints {
                if nonlinear::sign_contradicts(*constraint, expected_sign) {
                    if self.debug {
                        safe_eprintln!("[NIA] Sign conflict: factor_signs={:?}, expected_prod={}, constraint={:?}", factor_signs, expected_sign, constraint);
                    }
                    return Some(
                        self.asserted
                            .iter()
                            .map(|(term, val)| TheoryLit::new(*term, *val))
                            .collect(),
                    );
                }
            }
        }
        None
    }

    /// Extract sign constraint from a comparison with zero
    pub(crate) fn extract_sign_constraint(
        &self,
        term: TermId,
        value: bool,
    ) -> Option<(TermId, SignConstraint)> {
        nonlinear::extract_sign_constraint(self.terms, term, value)
    }

    /// Record sign constraint for a subject term (variable or monomial).
    ///
    /// Also records trail entries for efficient push/pop (#8626).
    pub(crate) fn record_sign_constraint(
        &mut self,
        subject: TermId,
        constraint: SignConstraint,
        assertion: TermId,
    ) {
        // Record trail entries BEFORE the mutation so we know what was added.
        if let Some(vars) = self.aux_to_monomial.get(&subject).cloned() {
            self.sign_constraint_trail
                .push(SignConstraintTrailEntry::Monomial(vars));
        }
        if matches!(self.terms.get(subject), TermData::Var(_, _)) {
            self.sign_constraint_trail
                .push(SignConstraintTrailEntry::Variable(subject));
        }
        nonlinear::record_sign_constraint(
            self.terms,
            &self.aux_to_monomial,
            &mut self.sign_constraints,
            &mut self.var_sign_constraints,
            subject,
            constraint,
            assertion,
        );
    }
}
