// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The arithmetic literal solver behind qe-lite: read `a ≠ b` (`∀`) or
//! `a = b` (`∃`) as a linear combination over arbitrary atoms and solve it for
//! one bound variable. Over `Int` only a unit coefficient is solved, so the
//! solution is an integer term; over `Real` any nonzero coefficient.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::quantifier_rules::LiteralSolver;
use super::terms::{as_binary_diseq, as_binary_eq, is_var_named, mentions_any_name, Binder};

/// Solves a linear arithmetic literal for a bound variable.
pub(super) struct ArithSolver;

impl LiteralSolver for ArithSolver {
    fn solve(
        &mut self,
        terms: &mut TermStore,
        lit: TermId,
        var: &str,
        sort: &Sort,
        binder: Binder,
    ) -> Option<TermId> {
        if !matches!(sort, Sort::Int | Sort::Real) {
            return None;
        }
        let (a, b) = match binder {
            Binder::Forall => as_binary_diseq(terms, lit)?,
            Binder::Exists => as_binary_eq(terms, lit)?,
        };
        if terms.sort(a) != sort || terms.sort(b) != sort {
            return None;
        }
        let mut lin = Linear::default();
        if !lin.add_term(terms, a, &BigRational::one())
            || !lin.add_term(terms, b, &-BigRational::one())
        {
            return None;
        }
        lin.normalize();
        // Exactly one atom is the variable; no other atom mentions it.
        let mut var_coeff: Option<BigRational> = None;
        let mut rest: Vec<(TermId, BigRational)> = Vec::new();
        let mut single = HashSet::default();
        single.insert(var.to_string());
        for (atom, coeff) in &lin.atoms {
            if is_var_named(terms, *atom, var) {
                if var_coeff.is_some() {
                    return None;
                }
                var_coeff = Some(coeff.clone());
            } else if mentions_any_name(terms, *atom, &single) {
                return None;
            } else {
                rest.push((*atom, coeff.clone()));
            }
        }
        let c = var_coeff?;
        if matches!(sort, Sort::Int) && !(c.is_one() || (-c.clone()).is_one()) {
            return None;
        }
        // v = −(Σ rest + k) / c
        let factor = -c.recip();
        let atoms: Vec<(TermId, BigRational)> = rest
            .into_iter()
            .map(|(atom, coeff)| (atom, coeff * &factor))
            .collect();
        let constant = lin.constant * &factor;
        build_linear(terms, sort, &atoms, &constant)
    }
}

/// A linear combination `Σ coeff·atom + constant` over arbitrary atoms.
#[derive(Default)]
struct Linear {
    atoms: Vec<(TermId, BigRational)>,
    constant: BigRational,
}

impl Linear {
    /// Add `scale · t`. Every non-arithmetic node (and every nonlinear
    /// product) is an opaque atom, so this always succeeds today; the `bool`
    /// lets a caller refuse a literal without restructuring the call sites.
    fn add_term(&mut self, terms: &TermStore, t: TermId, scale: &BigRational) -> bool {
        if let Some(c) = numeral(terms, t) {
            self.constant += scale * c;
            return true;
        }
        match terms.get(t) {
            TermData::App(sym, args) => match (sym.name(), args.len()) {
                ("+", _) => {
                    let args = args.clone();
                    args.iter().all(|&a| self.add_term(terms, a, scale))
                }
                ("-", 1) => {
                    let arg = args[0];
                    self.add_term(terms, arg, &-scale.clone())
                }
                ("-", n) if n >= 2 => {
                    let args = args.clone();
                    self.add_term(terms, args[0], scale)
                        && args[1..]
                            .iter()
                            .all(|&a| self.add_term(terms, a, &-scale.clone()))
                }
                ("*", _) => {
                    let args = args.clone();
                    let mut product = BigRational::one();
                    let mut nonconst: Option<TermId> = None;
                    for &a in &args {
                        if let Some(c) = numeral(terms, a) {
                            product *= c;
                        } else if nonconst.is_some() {
                            // Nonlinear product: an opaque atom.
                            self.atoms.push((t, scale.clone()));
                            return true;
                        } else {
                            nonconst = Some(a);
                        }
                    }
                    match nonconst {
                        Some(a) => self.add_term(terms, a, &(scale * product)),
                        None => {
                            self.constant += scale * product;
                            true
                        }
                    }
                }
                _ => {
                    self.atoms.push((t, scale.clone()));
                    true
                }
            },
            _ => {
                self.atoms.push((t, scale.clone()));
                true
            }
        }
    }

    /// Merge repeated atoms and drop zero coefficients.
    fn normalize(&mut self) {
        let mut merged: Vec<(TermId, BigRational)> = Vec::new();
        for (atom, coeff) in self.atoms.drain(..) {
            if let Some(entry) = merged.iter_mut().find(|(a, _)| *a == atom) {
                entry.1 += coeff;
            } else {
                merged.push((atom, coeff));
            }
        }
        merged.retain(|(_, c)| !c.is_zero());
        self.atoms = merged;
    }
}

/// The value of an Int/Real numeral (optionally under unary minus).
fn numeral(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(sym, args) if sym.name() == "-" && args.len() == 1 => {
            Some(-numeral(terms, args[0])?)
        }
        _ => None,
    }
}

/// Build `Σ coeff·atom + constant` as a term of `sort`. Over `Int` every
/// coefficient must be an integer. Every atom must already have `sort`.
fn build_linear(
    terms: &mut TermStore,
    sort: &Sort,
    atoms: &[(TermId, BigRational)],
    constant: &BigRational,
) -> Option<TermId> {
    let is_int = matches!(sort, Sort::Int);
    let mk_num = |terms: &mut TermStore, value: &BigRational| -> Option<TermId> {
        if is_int {
            if !value.is_integer() {
                return None;
            }
            Some(terms.mk_int(value.to_integer()))
        } else {
            Some(terms.mk_rational(value.clone()))
        }
    };
    let mut summands: Vec<TermId> = Vec::with_capacity(atoms.len() + 1);
    for (atom, coeff) in atoms {
        if terms.sort(*atom) != sort {
            return None;
        }
        let summand = if coeff.is_one() {
            *atom
        } else if (-coeff.clone()).is_one() {
            terms.mk_neg(*atom)
        } else {
            let c = mk_num(terms, coeff)?;
            terms.mk_mul(vec![c, *atom])
        };
        summands.push(summand);
    }
    if !constant.is_zero() || summands.is_empty() {
        summands.push(mk_num(terms, constant)?);
    }
    let term = match summands.as_slice() {
        [single] => *single,
        _ => terms.mk_add(summands),
    };
    (terms.sort(term) == sort).then_some(term)
}
