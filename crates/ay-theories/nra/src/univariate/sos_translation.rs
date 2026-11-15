// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SOS-only source translation with a shared degree, size, and work envelope.
//! The general NRA deciders retain their existing polynomial translators.

use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use num_rational::BigRational;
use num_traits::One;
use std::mem::size_of;

use super::{negate_rel, rational_sign, MultiAtom, MultiConstraint, MultiPoly, Rel};
use crate::sos::budget::{
    checked_poly_add, checked_poly_mul, checked_poly_neg, checked_poly_sub, rational_fits,
    SosPolynomialBudget, MAX_SOS_ASSERTED_LITERALS, MAX_SOS_COEFFICIENT_BITS,
    MAX_SOS_TOTAL_POLY_TERMS,
};
use crate::NraSolver;

#[cfg(test)]
mod tests;

/// Bytes charged for one fresh rational coefficient: its header plus a fixed
/// allocator overhead. Evaluated at compile time, so it cannot overflow at
/// run time.
const RATIONAL_SLOT_BYTES: usize = size_of::<BigRational>() + 64;

impl NraSolver<'_> {
    /// Stateless source view for portable candidates. Every exact clause slot
    /// becomes one constraint for its negation, including constant comparisons.
    /// Unlike the legacy evidence lane below, no slot is filtered or reindexed.
    pub(crate) fn sos_clause_constraints(
        terms: &TermStore,
        clause: &[TermId],
        budget: &mut SosPolynomialBudget<'_>,
    ) -> Option<Vec<MultiConstraint>> {
        if clause.is_empty() || clause.len() > MAX_SOS_ASSERTED_LITERALS {
            return None;
        }
        if !budget.charge_array::<MultiConstraint>(clause.len()) {
            return None;
        }
        let mut constraints = Vec::new();
        constraints.try_reserve_exact(clause.len()).ok()?;
        let mut retained = 0usize;
        for &literal in clause {
            let (mut atom, mut value) = (literal, false);
            loop {
                if !budget.visit_term(0)
                    || atom.index() >= terms.len()
                    || terms.sort(atom) != &Sort::Bool
                {
                    return None;
                }
                match terms.get(atom) {
                    TermData::Not(inner) => {
                        atom = *inner;
                        value = !value;
                    }
                    _ => break,
                }
            }
            let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let rel = match name.as_str() {
                "<" => Rel::Lt,
                "<=" => Rel::Le,
                "=" => Rel::Eq,
                ">=" => Rel::Ge,
                ">" => Rel::Gt,
                _ => return None,
            };
            let rel = if value { rel } else { negate_rel(rel) };
            let constraint = source_constraint(terms, rel, args[0], args[1], budget)?;
            retained = retained.checked_add(constraint.poly.terms.len())?;
            if retained > MAX_SOS_TOTAL_POLY_TERMS {
                return None;
            }
            constraints.push(constraint);
        }
        budget.poll().then_some(constraints)
    }

    /// Translate the complete asserted source view for the private SOS witness.
    /// Unsupported syntax or an exhausted budget declines this evidence lane.
    pub(crate) fn sos_source_constraints(&self) -> Option<Vec<MultiConstraint>> {
        if self.asserted.len() > MAX_SOS_ASSERTED_LITERALS {
            return None;
        }
        let mut budget = SosPolynomialBudget::default();
        let mut constraints = Vec::new();
        let mut retained = 0usize;
        for &(atom, value) in &self.asserted {
            match self.sos_source_atom(atom, value, &mut budget)? {
                // Preserve the existing post-UNSAT evidence policy for a
                // degenerate constant contradiction; no certificate is minted.
                MultiAtom::ConstFalse => return None,
                MultiAtom::ConstTrue => {}
                MultiAtom::Constraint(constraint) => {
                    retained = retained.checked_add(constraint.poly.terms.len())?;
                    if retained > MAX_SOS_TOTAL_POLY_TERMS {
                        return None;
                    }
                    constraints.push(constraint);
                }
            }
        }
        Some(constraints)
    }

    fn sos_source_atom(
        &self,
        atom: TermId,
        value: bool,
        budget: &mut SosPolynomialBudget<'_>,
    ) -> Option<MultiAtom> {
        if !budget.visit_term(0)
            || atom.index() >= self.terms.len()
            || self.terms.sort(atom) != &Sort::Bool
        {
            return None;
        }
        let (original_rel, lhs, rhs) = self.comparison_parts(atom)?;
        let rel = if value {
            original_rel
        } else {
            negate_rel(original_rel)
        };
        let MultiConstraint { poly, rel } = source_constraint(self.terms, rel, lhs, rhs, budget)?;
        if poly.terms.iter().all(|(monomial, _)| monomial.is_empty()) {
            let sign = poly.terms.first().map_or(0, |(_, c)| rational_sign(c));
            return Some(if rel.holds_for_sign(sign) {
                MultiAtom::ConstTrue
            } else {
                MultiAtom::ConstFalse
            });
        }
        Some(MultiAtom::Constraint(MultiConstraint { poly, rel }))
    }

    #[cfg(test)]
    fn sos_source_polynomial(
        &self,
        term: TermId,
        depth: usize,
        budget: &mut SosPolynomialBudget<'_>,
    ) -> Option<MultiPoly> {
        source_polynomial(self.terms, term, depth, budget)
    }
}

fn source_constraint(
    terms: &TermStore,
    rel: Rel,
    lhs: TermId,
    rhs: TermId,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiConstraint> {
    if lhs.index() >= terms.len()
        || rhs.index() >= terms.len()
        || terms.sort(lhs) != terms.sort(rhs)
    {
        return None;
    }
    let left = source_polynomial(terms, lhs, 1, budget)?;
    let right = source_polynomial(terms, rhs, 1, budget)?;
    Some(MultiConstraint {
        poly: checked_poly_sub(&left, &right, budget)?,
        rel,
    })
}

fn source_polynomial(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.visit_term(depth) || term.index() >= terms.len() {
        return None;
    }
    let sort = terms.sort(term);
    if !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    match terms.get(term) {
        TermData::Const(Constant::Int(value))
            if sort == &Sort::Int && value.bits() <= MAX_SOS_COEFFICIENT_BITS =>
        {
            if !budget.charge_array::<(Vec<TermId>, BigRational)>(1) {
                return None;
            }
            let words = (value.bits().div_ceil(64) as usize).checked_add(1)?;
            let bytes = (value.bits().div_ceil(8) as usize).checked_add(RATIONAL_SLOT_BYTES)?;
            if !budget.charge(words, bytes) {
                return None;
            }
            Some(MultiPoly::constant(BigRational::from_integer(
                value.clone(),
            )))
        }
        TermData::Const(Constant::Rational(value))
            if sort == &Sort::Real && rational_fits(&value.0) =>
        {
            if !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
                || !budget.charge_rational_clone(&value.0)
            {
                return None;
            }
            Some(MultiPoly::constant(value.0.clone()))
        }
        TermData::Var(..) => {
            if !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
                || !budget.charge_array::<TermId>(1)
                || !budget.charge(1, RATIONAL_SLOT_BYTES)
            {
                return None;
            }
            Some(MultiPoly::var(term))
        }
        TermData::App(Symbol::Named(name), args)
            if !args.is_empty() && matches!(name.as_str(), "+" | "-" | "*") =>
        {
            source_application(terms, name, args, sort, depth, budget)
        }
        _ => None,
    }
}

fn source_application(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    sort: &Sort,
    depth: usize,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    let child_depth = depth.checked_add(1)?;
    let mut accumulator = if name == "*" {
        if !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
            || !budget.charge(1, RATIONAL_SLOT_BYTES)
        {
            return None;
        }
        MultiPoly::constant(BigRational::one())
    } else {
        MultiPoly::zero()
    };
    for (position, &argument) in args.iter().enumerate() {
        // Each child is metered before its value can be cloned or expanded.
        // Check its sort here, without a separate unmetered all-args scan.
        let part = source_polynomial(terms, argument, child_depth, budget)?;
        if terms.sort(argument) != sort {
            return None;
        }
        accumulator = match name {
            "+" => checked_poly_add(&accumulator, &part, budget)?,
            "*" => checked_poly_mul(&accumulator, &part, budget)?,
            "-" if args.len() == 1 => checked_poly_neg(&part, budget)?,
            "-" if position == 0 => part,
            "-" => checked_poly_sub(&accumulator, &part, budget)?,
            _ => return None,
        };
    }
    Some(accumulator)
}
