//! Pseudo-Boolean objective function.

use std::{cmp::Ordering, collections::BTreeMap, rc::Rc};

use malachite_bigint::{BigInt, Sign};
use num_traits::{One, Zero};

use crate::{prelude::*, substitution::Substitutable};

/// A pseudo-Boolean objective consists of a set of terms and a constant term.
///
/// This data structure preserves that the constraint is always stored in normalized form, i.e., the terms are over distinct variables, all coefficients are non-negative, and the terms are sorted by the index of the variable in the variable manager.
#[derive(Debug, Default, PartialEq, Clone)]
pub struct PBObjective {
    pub terms: BTreeMap<VarIdx, GeneralPBTerm<BigInt>>,
    pub constant: BigInt,
}

impl PBObjective {
    /// Construct a pseudo-Boolean objective by its terms and the constant term.
    ///
    /// The terms do not need to be normalized. This function automatically normalizes the terms of the objective.
    ///
    /// The parameter `is_maximization` determines if the coefficients and constant should be negated, as the objective is always considered to be minimized.
    pub fn from_terms(
        terms: Vec<GeneralPBTerm<BigInt>>,
        mut constant: BigInt,
        is_maximization: bool,
    ) -> Self {
        let mut terms_map: BTreeMap<usize, GeneralPBTerm<BigInt>> = BTreeMap::new();

        // Add terms to map and merging them if we have multiple terms talking about the same variable.
        for term in terms {
            if let Some(existing_term) = terms_map.get_mut(&term.lit.get_var()) {
                constant += existing_term.add_with(term);
            } else {
                terms_map.insert(term.lit.get_var(), term);
            }
        }

        // Change maximization to minimization.
        if is_maximization {
            constant = -constant;
            for term in terms_map.values_mut() {
                term.coeff = -&term.coeff;
            }
        }

        // Normalize the terms to only have positive coefficients.
        terms_map.retain(|_, t| !t.coeff.is_zero());
        for term in terms_map.values_mut() {
            if term.coeff.sign() == Sign::Minus {
                term.change_negation();
                constant -= &term.coeff;
            }
        }

        PBObjective {
            terms: terms_map,
            constant,
        }
    }

    /// Get the objective value for this objective under the `assignment`.
    pub fn evaluate(&self, assignment: &Assignment<BooleanVar>) -> Option<BigInt> {
        let mut value = self.constant.to_owned();

        for term in self.terms.values() {
            match assignment.get_lit_value(term.lit) {
                BoolValue::Unassigned => return None,
                BoolValue::Assigned(true) => value += &term.coeff,
                BoolValue::Assigned(false) => {}
            }
        }

        Some(value)
    }

    /// Get the objective improving proofgoal with respect to the `substitution`, where the degree is initialized with `degree`.
    #[inline]
    fn get_proofgoal_init_degree(
        &self,
        substitution: &Substitution,
        mut degree: BigInt,
    ) -> Rc<DBConstraint> {
        let mut terms = Vec::new();
        if self.terms.len() > substitution.len() {
            // It is more efficient to linearly iterate through the substitution and access the terms.
            for var_idx in substitution.syntactic_support() {
                if let Some(term) = self.terms.get(var_idx) {
                    let var_maps_to = substitution.get(*var_idx).unwrap();
                    let lit_maps_to = if term.lit.is_negated() {
                        var_maps_to.into_negation()
                    } else {
                        var_maps_to
                    };
                    terms.push(term.clone());
                    match lit_maps_to {
                        SubstitutionValue::TRUE => degree += &term.coeff,
                        SubstitutionValue::FALSE => {}
                        lit => {
                            terms.push(GeneralPBTerm::new(-term.coeff.clone(), lit.get_lit()));
                        }
                    }
                }
            }
        } else {
            // It is more efficient to linearly iterate through the terms and access the substitution.
            for term in self.terms.values() {
                if let Some(lit_maps_to) = substitution.get_lit(term.lit) {
                    terms.push(term.clone());
                    match lit_maps_to {
                        SubstitutionValue::TRUE => degree += &term.coeff,
                        SubstitutionValue::FALSE => {}
                        lit => {
                            terms.push(GeneralPBTerm::new(-term.coeff.clone(), lit.get_lit()));
                        }
                    }
                }
            }
        }

        Rc::new(constraint_from_terms(terms, degree).into())
    }

    /// Get the objective improving proofgoal for redundance-based strengthening with respect to the `substitution`.
    #[inline]
    pub fn get_proofgoal(&self, substitution: &Substitution) -> Rc<DBConstraint> {
        let degree = BigInt::zero();
        self.get_proofgoal_init_degree(substitution, degree)
    }

    /// Get the strict objective improving proofgoal used for dominance-based strengthening with respect to the `substitution`.
    #[inline]
    pub fn get_proofgoal_strict(&self, substitution: &Substitution) -> Rc<DBConstraint> {
        let degree = BigInt::one();
        self.get_proofgoal_init_degree(substitution, degree)
    }

    /// Compute the difference between the objective and another objective.
    pub fn difference(
        &self,
        other: &PBObjective,
    ) -> (Vec<GeneralPBTerm<BigInt>>, Vec<GeneralPBTerm<BigInt>>) {
        // Making use of the fact that values are sorted by variable.
        let mut self_terms = self.terms.values().peekable();
        let mut other_terms = other.terms.values().peekable();
        let mut extra_self_terms = Vec::new();
        let mut extra_other_terms = Vec::new();
        while let Some(self_term) = self_terms.peek()
            && let Some(other_term) = other_terms.peek()
        {
            if self_term == other_term {
                self_terms.next();
                other_terms.next();
                continue;
            }
            match self_term.lit.cmp(&other_term.lit) {
                Ordering::Equal => {
                    extra_self_terms.push((*self_term).clone());
                    self_terms.next();
                    extra_other_terms.push((*other_term).clone());
                    other_terms.next();
                }
                Ordering::Less => {
                    extra_self_terms.push((*self_term).clone());
                    self_terms.next();
                }
                Ordering::Greater => {
                    extra_other_terms.push((*other_term).clone());
                    other_terms.next();
                }
            }
        }
        extra_self_terms.extend(self_terms.cloned());
        extra_other_terms.extend(other_terms.cloned());
        (extra_self_terms, extra_other_terms)
    }

    /// Return the number of terms in [`PBObjective`].
    #[inline]
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Check if [`PBObjective`] has no terms.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.terms.len() == 0
    }
}

impl ToPrettyString for PBObjective {
    #[inline]
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        let mut out = String::with_capacity(self.len() * 4);
        for term in self.terms.values() {
            out.push_str(&term.coeff.to_string());
            out.push(' ');
            out.push_str(&term.lit.to_pretty_string(var_names));
            out.push(' ');
        }
        out.push_str(&self.constant.to_string());
        out
    }
}
