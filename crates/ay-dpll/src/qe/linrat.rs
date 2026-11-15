// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear rational terms and literal normalization over linear real
//! arithmetic, shared by the Loos-Weispfenning eliminator ([`super::lw`]) and
//! the nested CEGQI selection (`crate::cegqi::lra_nested`).
//!
//! Moved out of `lw.rs` unchanged except for visibility and one
//! `pop().expect(..)` on a length-1 vector rewritten as a slice pattern.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap};

use super::cooper::Rel;

// ===========================================================================
// Linear rational terms
// ===========================================================================

/// A linear real term: `Σ coeff·var + constant` with rational coefficients.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinRat {
    /// `var -> nonzero coefficient` (deterministic order).
    pub(crate) coeffs: BTreeMap<TermId, BigRational>,
    /// The additive constant.
    pub(crate) constant: BigRational,
}

impl LinRat {
    pub(crate) fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: BigRational::zero(),
        }
    }

    pub(crate) fn add_var(&mut self, var: TermId, c: BigRational) {
        if c.is_zero() {
            return;
        }
        let entry = self.coeffs.entry(var).or_insert_with(BigRational::zero);
        *entry += c;
        if entry.is_zero() {
            self.coeffs.remove(&var);
        }
    }

    pub(crate) fn add(&mut self, other: &Self) {
        for (v, c) in &other.coeffs {
            self.add_var(*v, c.clone());
        }
        self.constant += &other.constant;
    }

    pub(crate) fn sub(&mut self, other: &Self) {
        for (v, c) in &other.coeffs {
            self.add_var(*v, -c.clone());
        }
        self.constant -= &other.constant;
    }

    pub(crate) fn scale(&mut self, factor: &BigRational) {
        if factor.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= factor;
        }
        self.constant *= factor;
    }

    /// Coefficient of `var` (0 if absent).
    pub(crate) fn coeff_of(&self, var: TermId) -> BigRational {
        self.coeffs
            .get(&var)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }

    /// Return `self` with `var` removed (the "rest" of the term).
    pub(crate) fn without(&self, var: TermId) -> Self {
        let mut c = self.clone();
        c.coeffs.remove(&var);
        c
    }

    /// Substitute `x := value` (a linear term without `x`) into `self`.
    pub(crate) fn substitute(&self, var: TermId, value: &Self) -> Self {
        let c = self.coeff_of(var);
        let mut out = self.without(var);
        if !c.is_zero() {
            let mut scaled = value.clone();
            scaled.scale(&c);
            out.add(&scaled);
        }
        out
    }

    /// Evaluate under a ground rational assignment (all vars must be bound).
    pub(crate) fn eval(&self, assign: &HashMap<TermId, BigRational>) -> Option<BigRational> {
        let mut acc = self.constant.clone();
        for (v, c) in &self.coeffs {
            acc += c * assign.get(v)?;
        }
        Some(acc)
    }

    /// Build the corresponding hash-consed Real term.
    pub(crate) fn to_term(&self, terms: &mut TermStore) -> TermId {
        let mut summands: Vec<TermId> = Vec::new();
        for (var, coeff) in &self.coeffs {
            if coeff.is_one() {
                summands.push(*var);
            } else {
                let c = terms.mk_rational(coeff.clone());
                summands.push(terms.mk_mul(vec![c, *var]));
            }
        }
        if !self.constant.is_zero() || summands.is_empty() {
            summands.push(terms.mk_rational(self.constant.clone()));
        }
        match summands.as_slice() {
            [single] => *single,
            _ => terms.mk_add(summands),
        }
    }
}

// ===========================================================================
// Literal parsing & normalization
// ===========================================================================

/// Parse a single SMT literal into `(rel, t)` meaning `t ⋈ 0`. Returns `None`
/// outside the supported fragment.
pub(crate) fn parse_literal(terms: &TermStore, lit: TermId) -> Option<(Rel, LinRat)> {
    match terms.get(lit).clone() {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let (lhs, rhs) = (args[0], args[1]);
            match name.as_str() {
                "=" => parse_pair(terms, lhs, rhs, Rel::Eq),
                "<=" => parse_pair(terms, lhs, rhs, Rel::Le),
                "<" => parse_pair(terms, lhs, rhs, Rel::Lt),
                // `a >= b`  ≡  `b <= a` ; `a > b`  ≡  `b < a`
                ">=" => parse_pair(terms, rhs, lhs, Rel::Le),
                ">" => parse_pair(terms, rhs, lhs, Rel::Lt),
                _ => None,
            }
        }
        TermData::Not(inner) => match terms.get(inner).clone() {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                match name.as_str() {
                    "=" => parse_pair(terms, lhs, rhs, Rel::Ne),
                    // not(lhs ≤ rhs) ≡ rhs < lhs ; not(lhs < rhs) ≡ rhs ≤ lhs
                    "<=" => parse_pair(terms, rhs, lhs, Rel::Lt),
                    "<" => parse_pair(terms, rhs, lhs, Rel::Le),
                    // not(lhs ≥ rhs) ≡ lhs < rhs ; not(lhs > rhs) ≡ lhs ≤ rhs
                    ">=" => parse_pair(terms, lhs, rhs, Rel::Lt),
                    ">" => parse_pair(terms, lhs, rhs, Rel::Le),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse `lhs ⋈ rhs` into `(⋈, lhs - rhs)`.
pub(crate) fn parse_pair(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    rel: Rel,
) -> Option<(Rel, LinRat)> {
    let l = parse_lin(terms, lhs)?;
    let r = parse_lin(terms, rhs)?;
    let mut t = l;
    t.sub(&r);
    Some((rel, t))
}

/// Rational value of a constant term (integer or rational literal, possibly
/// under a unary minus). `None` if not a constant.
pub(crate) fn rat_const(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            Some(-rat_const(terms, args[0])?)
        }
        _ => None,
    }
}

/// Parse an arbitrary term into a [`LinRat`], failing (out of fragment) on
/// any non-linear-real structure: Int-sorted variables (a mixed-sort output
/// would not be well-sorted), products of two non-constants, division by a
/// non-constant or by zero, `ite`/quantifiers/UF, etc.
pub(crate) fn parse_lin(terms: &TermStore, t: TermId) -> Option<LinRat> {
    if let Some(c) = rat_const(terms, t) {
        return Some(LinRat {
            coeffs: BTreeMap::new(),
            constant: c,
        });
    }
    match terms.get(t).clone() {
        TermData::Var(_, _) => {
            if !matches!(terms.sort(t), Sort::Real) {
                return None;
            }
            let mut lt = LinRat::zero();
            lt.add_var(t, BigRational::one());
            Some(lt)
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut acc = LinRat::zero();
                for a in &args {
                    let sub = parse_lin(terms, *a)?;
                    acc.add(&sub);
                }
                Some(acc)
            }
            "-" if args.len() == 1 => {
                let mut sub = parse_lin(terms, args[0])?;
                sub.scale(&-BigRational::one());
                Some(sub)
            }
            "-" if args.len() >= 2 => {
                let mut acc = parse_lin(terms, args[0])?;
                for a in &args[1..] {
                    let sub = parse_lin(terms, *a)?;
                    acc.sub(&sub);
                }
                Some(acc)
            }
            "*" => {
                // Linear multiplication: at most one non-constant factor.
                let mut const_product = BigRational::one();
                let mut nonconst: Option<LinRat> = None;
                for a in &args {
                    if let Some(c) = rat_const(terms, *a) {
                        const_product *= c;
                    } else {
                        if nonconst.is_some() {
                            return None; // Two non-constant factors ⇒ non-linear.
                        }
                        nonconst = Some(parse_lin(terms, *a)?);
                    }
                }
                match nonconst {
                    Some(mut lt) => {
                        lt.scale(&const_product);
                        Some(lt)
                    }
                    None => Some(LinRat {
                        coeffs: BTreeMap::new(),
                        constant: const_product,
                    }),
                }
            }
            "/" if args.len() == 2 => {
                let d = rat_const(terms, args[1])?;
                if d.is_zero() {
                    return None;
                }
                let mut num = parse_lin(terms, args[0])?;
                num.scale(&d.recip());
                Some(num)
            }
            _ => None,
        },
        _ => None,
    }
}
