// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Values, exact evaluation and linear forms for the QSAT engine.
//!
//! The engine works on quantifier-free terms over `Int`/`Real`/`Bool`
//! variables. Evaluation is exact (rationals, SMT-LIB Euclidean `div`/`mod`
//! with a constant non-zero divisor); anything outside the fragment evaluates
//! to `None`, which every caller turns into a decline.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// A model value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Val {
    Num(BigRational),
    Bool(bool),
}

impl Val {
    pub(crate) fn num(&self) -> Option<&BigRational> {
        match self {
            Self::Num(n) => Some(n),
            Self::Bool(_) => None,
        }
    }

    pub(crate) fn boolean(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            Self::Num(_) => None,
        }
    }
}

/// An assignment to engine variables.
#[derive(Clone, Debug, Default)]
pub(crate) struct Model {
    pub(crate) vals: HashMap<TermId, Val>,
}

impl Model {
    pub(crate) fn num(&self, var: TermId) -> Option<&BigRational> {
        self.vals.get(&var).and_then(Val::num)
    }
}

/// Rational value of a numeral term (possibly under unary minus).
pub(crate) fn numeral(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            Some(-numeral(terms, args[0])?)
        }
        TermData::App(Symbol::Named(name), args) if name == "/" && args.len() == 2 => {
            let d = numeral(terms, args[1])?;
            if d.is_zero() {
                return None;
            }
            Some(numeral(terms, args[0])? / d)
        }
        TermData::App(Symbol::Named(name), args) if name == "to_real" && args.len() == 1 => {
            numeral(terms, args[0])
        }
        _ => None,
    }
}

/// An integral numeral.
pub(crate) fn int_numeral(terms: &TermStore, t: TermId) -> Option<BigInt> {
    let r = numeral(terms, t)?;
    r.is_integer().then(|| r.to_integer())
}

pub(crate) use super::eval::Eval;

/// SMT-LIB `div` (Euclidean: remainder in `[0, |d|)`).
pub(crate) fn euclid_div(n: &BigInt, d: &BigInt) -> BigInt {
    let r = euclid_rem(n, d);
    (n - r) / d
}

/// SMT-LIB `mod` (Euclidean remainder, in `[0, |d|)`).
pub(crate) fn euclid_rem(n: &BigInt, d: &BigInt) -> BigInt {
    let m = d.abs();
    n.mod_floor(&m)
}

/// A linear form `Σ c·v + k` over `Int`/`Real` variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Lin {
    pub(crate) coeffs: BTreeMap<TermId, BigRational>,
    pub(crate) constant: BigRational,
}

impl Lin {
    pub(crate) fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: BigRational::zero(),
        }
    }

    pub(crate) fn constant(c: BigRational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    pub(crate) fn var(v: TermId) -> Self {
        let mut l = Self::zero();
        l.add_var(v, BigRational::one());
        l
    }

    pub(crate) fn add_var(&mut self, v: TermId, c: BigRational) {
        if c.is_zero() {
            return;
        }
        let e = self.coeffs.entry(v).or_insert_with(BigRational::zero);
        *e += c;
        if e.is_zero() {
            self.coeffs.remove(&v);
        }
    }

    pub(crate) fn add(&mut self, o: &Self) {
        for (v, c) in &o.coeffs {
            self.add_var(*v, c.clone());
        }
        self.constant += &o.constant;
    }

    pub(crate) fn sub(&mut self, o: &Self) {
        for (v, c) in &o.coeffs {
            self.add_var(*v, -c.clone());
        }
        self.constant -= &o.constant;
    }

    pub(crate) fn scale(&mut self, f: &BigRational) {
        if f.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= f;
        }
        self.constant *= f;
    }

    pub(crate) fn scaled(&self, f: &BigRational) -> Self {
        let mut s = self.clone();
        s.scale(f);
        s
    }

    pub(crate) fn coeff(&self, v: TermId) -> BigRational {
        self.coeffs
            .get(&v)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }

    pub(crate) fn without(&self, v: TermId) -> Self {
        let mut s = self.clone();
        s.coeffs.remove(&v);
        s
    }

    pub(crate) fn mentions(&self, v: TermId) -> bool {
        self.coeffs.contains_key(&v)
    }

    /// `self[v := value]`.
    pub(crate) fn subst(&self, v: TermId, value: &Self) -> Self {
        let c = self.coeff(v);
        let mut out = self.without(v);
        if !c.is_zero() {
            out.add(&value.scaled(&c));
        }
        out
    }

    pub(crate) fn eval(&self, m: &Model) -> Option<BigRational> {
        let mut acc = self.constant.clone();
        for (v, c) in &self.coeffs {
            acc += c * m.num(*v)?;
        }
        Some(acc)
    }

    pub(crate) fn is_const(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Least common multiple of all coefficient and constant denominators.
    pub(crate) fn denom_lcm(&self) -> BigInt {
        let mut l = self.constant.denom().clone();
        for c in self.coeffs.values() {
            l = l.lcm(c.denom());
        }
        l
    }

    /// Whether every variable is `Int`-sorted.
    pub(crate) fn all_int(&self, terms: &TermStore) -> bool {
        self.coeffs
            .keys()
            .all(|&v| matches!(terms.sort(v), Sort::Int))
    }

    /// Build the term at `sort`. An `Int` build requires integral
    /// coefficients and constant and `Int` variables; a `Real` build wraps
    /// `Int` variables in `to_real`.
    pub(crate) fn to_term(&self, terms: &mut TermStore, sort: &Sort) -> Option<TermId> {
        let int = matches!(sort, Sort::Int);
        let mut summands = Vec::new();
        for (&v, c) in &self.coeffs {
            let var_int = matches!(terms.sort(v), Sort::Int);
            let base = if !int && var_int {
                terms.mk_to_real(v)
            } else {
                v
            };
            if int && (!var_int || !c.is_integer()) {
                return None;
            }
            if c.is_one() {
                summands.push(base);
            } else {
                let k = if int {
                    terms.mk_int(c.to_integer())
                } else {
                    terms.mk_rational(c.clone())
                };
                summands.push(terms.mk_mul(vec![k, base]));
            }
        }
        if int && !self.constant.is_integer() {
            return None;
        }
        if !self.constant.is_zero() || summands.is_empty() {
            summands.push(if int {
                terms.mk_int(self.constant.to_integer())
            } else {
                terms.mk_rational(self.constant.clone())
            });
        }
        Some(match summands.as_slice() {
            [one] => *one,
            _ => terms.mk_add(summands),
        })
    }
}

/// Parse a linear arithmetic term. `to_real` is transparent; `ite`, `div`,
/// `mod`, `abs`, nonlinear products and anything else answer `None`.
pub(crate) fn lin_of(terms: &TermStore, t: TermId) -> Option<Lin> {
    lin_of_depth(terms, t, 0)
}

fn lin_of_depth(terms: &TermStore, t: TermId, depth: usize) -> Option<Lin> {
    if depth > 10_000 {
        return None;
    }
    if let Some(c) = numeral(terms, t) {
        return Some(Lin::constant(c));
    }
    match terms.get(t) {
        TermData::Var(..) => matches!(terms.sort(t), Sort::Int | Sort::Real).then(|| Lin::var(t)),
        TermData::App(sym, args) => {
            let name = sym.name();
            if args.is_empty() {
                return matches!(terms.sort(t), Sort::Int | Sort::Real).then(|| Lin::var(t));
            }
            match name {
                "+" => {
                    let mut acc = Lin::zero();
                    for &a in args {
                        acc.add(&lin_of_depth(terms, a, depth + 1)?);
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => {
                    let mut s = lin_of_depth(terms, args[0], depth + 1)?;
                    s.scale(&-BigRational::one());
                    Some(s)
                }
                "-" => {
                    let mut acc = lin_of_depth(terms, args[0], depth + 1)?;
                    for &a in &args[1..] {
                        acc.sub(&lin_of_depth(terms, a, depth + 1)?);
                    }
                    Some(acc)
                }
                "*" => {
                    let mut k = BigRational::one();
                    let mut non: Option<Lin> = None;
                    for &a in args {
                        if let Some(c) = numeral(terms, a) {
                            k *= c;
                        } else {
                            if non.is_some() {
                                return None;
                            }
                            non = Some(lin_of_depth(terms, a, depth + 1)?);
                        }
                    }
                    Some(match non {
                        Some(mut l) => {
                            l.scale(&k);
                            l
                        }
                        None => Lin::constant(k),
                    })
                }
                "/" if args.len() == 2 => {
                    let d = numeral(terms, args[1])?;
                    if d.is_zero() {
                        return None;
                    }
                    let mut n = lin_of_depth(terms, args[0], depth + 1)?;
                    n.scale(&d.recip());
                    Some(n)
                }
                "to_real" if args.len() == 1 => lin_of_depth(terms, args[0], depth + 1),
                _ => None,
            }
        }
        _ => None,
    }
}
