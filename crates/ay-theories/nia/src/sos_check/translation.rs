// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded translation from asserted arithmetic literals to degree-2 polynomials.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::{SosFragment, MAX_SOS_VARS};
use crate::sos::budget::{
    checked_poly_add, checked_poly_mul, checked_poly_neg, checked_poly_sub, rational_fits,
    SosPolynomialBudget, MAX_SOS_ASSERTED_LITERALS, MAX_SOS_COEFFICIENT_BITS,
    MAX_SOS_TOTAL_POLY_TERMS,
};
use crate::sos::{MultiConstraint, MultiPoly, Rel};
use crate::NiaSolver;

/// Classification of a single asserted atom for the SOS fragment.
enum NiaMultiAtom {
    /// A genuine `poly REL 0` constraint.
    Constraint(MultiConstraint),
    /// The atom is a constant `true` (vacuous — dropped from the system).
    ConstTrue,
    /// The atom is a constant `false` — the asserted conjunction is UNSAT.
    ConstFalse,
}

impl NiaSolver<'_> {
    /// Translate every asserted literal into the SOS polynomial fragment.
    ///
    /// Out-of-fragment atoms (unrecognized comparisons, `/`, `mod`, …) are
    /// skipped. Resource exhaustion is distinct: it declines the whole attempt.
    pub(super) fn build_sos_fragment(&self) -> SosFragment {
        if self.asserted.len() > MAX_SOS_ASSERTED_LITERALS {
            return SosFragment::Exhausted;
        }
        let mut budget = SosTranslationBudget::default();
        let mut constraints = Vec::new();
        let mut retained_terms = 0usize;
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value, &mut budget) {
                Some(NiaMultiAtom::ConstFalse) => return SosFragment::ConstFalse,
                Some(NiaMultiAtom::ConstTrue) => {}
                Some(NiaMultiAtom::Constraint(constraint)) => {
                    let Some(total) = retained_terms.checked_add(constraint.poly.terms.len())
                    else {
                        return SosFragment::Exhausted;
                    };
                    if total > MAX_SOS_TOTAL_POLY_TERMS {
                        return SosFragment::Exhausted;
                    }
                    retained_terms = total;
                    constraints.push(constraint);
                }
                // Dropping an unsupported conjunct weakens the system and is
                // therefore sound for this UNSAT-only lane.
                None => {}
            }
            if budget.exhausted {
                return SosFragment::Exhausted;
            }
        }
        let mut vars = Vec::with_capacity(MAX_SOS_VARS);
        let mut seen = HashSet::default();
        for constraint in &constraints {
            for &variable in constraint
                .poly
                .terms
                .iter()
                .flat_map(|(monomial, _)| monomial)
            {
                if seen.insert(variable) {
                    if vars.len() >= MAX_SOS_VARS {
                        return SosFragment::Exhausted;
                    }
                    vars.push(variable);
                }
            }
        }
        vars.sort_unstable_by_key(|term| term.0);
        SosFragment::System { constraints, vars }
    }

    fn atom_to_multi(
        &self,
        atom: TermId,
        value: bool,
        budget: &mut SosTranslationBudget,
    ) -> Option<NiaMultiAtom> {
        let (base_relation, lhs, rhs) = self.comparison_parts(atom)?;
        let relation = if value {
            base_relation
        } else {
            negate_rel(base_relation)
        };
        let lhs_poly = self.term_to_multipoly(lhs, 0, budget)?;
        let rhs_poly = self.term_to_multipoly(rhs, 0, budget)?;
        let poly = budget.checked_sub(&lhs_poly, &rhs_poly)?;
        if poly.terms.iter().all(|(monomial, _)| monomial.is_empty()) {
            let sign = if poly.is_zero() {
                0
            } else {
                rational_sign(&poly.terms[0].1)
            };
            if relation.holds_for_sign(sign) {
                Some(NiaMultiAtom::ConstTrue)
            } else {
                Some(NiaMultiAtom::ConstFalse)
            }
        } else {
            Some(NiaMultiAtom::Constraint(MultiConstraint {
                poly,
                rel: relation,
            }))
        }
    }

    fn comparison_parts(&self, atom: TermId) -> Option<(Rel, TermId, TermId)> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(atom) else {
            return None;
        };
        if args.len() != 2 || self.terms.sort(atom) != &Sort::Bool {
            return None;
        }
        let lhs_sort = self.terms.sort(args[0]);
        if lhs_sort != self.terms.sort(args[1]) || !is_arithmetic_sort(lhs_sort) {
            return None;
        }
        let relation = match name.as_str() {
            "<" => Rel::Lt,
            "<=" => Rel::Le,
            "=" => Rel::Eq,
            ">=" => Rel::Ge,
            ">" => Rel::Gt,
            "distinct" | "!=" => Rel::Ne,
            _ => return None,
        };
        Some((relation, args[0], args[1]))
    }

    fn term_to_multipoly(
        &self,
        term: TermId,
        depth: usize,
        budget: &mut SosTranslationBudget,
    ) -> Option<MultiPoly> {
        if !budget.visit_term(depth) || !is_arithmetic_sort(self.terms.sort(term)) {
            return None;
        }
        let child_depth = depth.saturating_add(1);
        match self.terms.get(term) {
            TermData::Const(Constant::Int(value)) if self.terms.sort(term) == &Sort::Int => {
                if !budget.admit(value.bits() <= MAX_SOS_COEFFICIENT_BITS) {
                    return None;
                }
                Some(MultiPoly::constant(BigRational::from_integer(
                    value.clone(),
                )))
            }
            TermData::Const(Constant::Rational(value)) if self.terms.sort(term) == &Sort::Real => {
                if !budget.admit(rational_fits(&value.0)) {
                    return None;
                }
                Some(MultiPoly::constant(value.0.clone()))
            }
            TermData::Var(..) => Some(MultiPoly::var(term)),
            TermData::App(Symbol::Named(name), args)
                if args
                    .iter()
                    .all(|&argument| self.terms.sort(argument) == self.terms.sort(term)) =>
            {
                match name.as_str() {
                    "+" if !args.is_empty() => {
                        let mut accumulator = MultiPoly::zero();
                        for &argument in args {
                            let part = self.term_to_multipoly(argument, child_depth, budget)?;
                            accumulator = budget.checked_add(&accumulator, &part)?;
                        }
                        Some(accumulator)
                    }
                    "-" if args.len() == 1 => {
                        let inner = self.term_to_multipoly(args[0], child_depth, budget)?;
                        budget.checked_neg(&inner)
                    }
                    "-" if args.len() >= 2 => {
                        let mut accumulator =
                            self.term_to_multipoly(args[0], child_depth, budget)?;
                        for &argument in &args[1..] {
                            let part = self.term_to_multipoly(argument, child_depth, budget)?;
                            accumulator = budget.checked_sub(&accumulator, &part)?;
                        }
                        Some(accumulator)
                    }
                    "*" if !args.is_empty() => {
                        let mut accumulator = MultiPoly::constant(BigRational::one());
                        for &argument in args {
                            let part = self.term_to_multipoly(argument, child_depth, budget)?;
                            accumulator = budget.checked_mul(&accumulator, &part)?;
                        }
                        Some(accumulator)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

fn is_arithmetic_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

/// Translation-local work meter. `exhausted` distinguishes an unsupported
/// operator (safe weakening) from a resource give-up (whole attempt declines).
#[derive(Debug, Default)]
struct SosTranslationBudget {
    polynomial: SosPolynomialBudget,
    exhausted: bool,
}

impl SosTranslationBudget {
    fn visit_term(&mut self, depth: usize) -> bool {
        let accepted = self.polynomial.visit_term(depth);
        self.admit(accepted)
    }

    fn admit(&mut self, accepted: bool) -> bool {
        if !accepted {
            self.exhausted = true;
        }
        accepted
    }

    fn checked_add(&mut self, left: &MultiPoly, right: &MultiPoly) -> Option<MultiPoly> {
        let result = checked_poly_add(left, right, &mut self.polynomial);
        self.admit_polynomial(result)
    }

    fn checked_neg(&mut self, poly: &MultiPoly) -> Option<MultiPoly> {
        let result = checked_poly_neg(poly, &mut self.polynomial);
        self.admit_polynomial(result)
    }

    fn checked_sub(&mut self, left: &MultiPoly, right: &MultiPoly) -> Option<MultiPoly> {
        let result = checked_poly_sub(left, right, &mut self.polynomial);
        self.admit_polynomial(result)
    }

    fn checked_mul(&mut self, left: &MultiPoly, right: &MultiPoly) -> Option<MultiPoly> {
        let result = checked_poly_mul(left, right, &mut self.polynomial);
        self.admit_polynomial(result)
    }

    fn admit_polynomial(&mut self, result: Option<MultiPoly>) -> Option<MultiPoly> {
        if result.is_none() {
            self.exhausted = true;
        }
        result
    }
}

/// Whether a retained constraint contains a degree-two monomial.
pub(super) fn is_nonlinear(constraint: &MultiConstraint) -> bool {
    constraint
        .poly
        .terms
        .iter()
        .any(|(monomial, _)| monomial.len() >= 2)
}

fn negate_rel(relation: Rel) -> Rel {
    match relation {
        Rel::Lt => Rel::Ge,
        Rel::Le => Rel::Gt,
        Rel::Eq => Rel::Ne,
        Rel::Ge => Rel::Lt,
        Rel::Gt => Rel::Le,
        Rel::Ne => Rel::Eq,
    }
}

fn rational_sign(rational: &BigRational) -> i32 {
    if rational.is_zero() {
        0
    } else if rational.is_positive() {
        1
    } else {
        -1
    }
}
