// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear forms of arithmetic terms, and which arithmetic operators the
//! arithmetic plug-in owns (design H2: registration by content).
//!
//! An arithmetic term is a linear combination of *leaves* plus a constant.
//! A leaf is a variable (a declared constant), an uninterpreted application
//! (opaque to arithmetic; the hub decides it), or an application the
//! arithmetic plug-in interprets itself by in-search definitions: an
//! arithmetic `ite` (the link lemmas), `div`/`mod` by a non-zero numeral and
//! `abs` (their defining clauses, `arith_defs`). Every other operator has no
//! owner, and the check names it before the search starts.

use std::collections::BTreeMap;

use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::content::is_uf_app;
use crate::plugin::GiveUp;

/// `Σ coeff·leaf + constant`, with no zero coefficients.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct LinForm {
    pub(crate) coeffs: BTreeMap<TermId, BigRational>,
    pub(crate) constant: BigRational,
}

impl LinForm {
    fn constant(c: BigRational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn leaf(term: TermId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(term, BigRational::one());
        Self {
            coeffs,
            constant: BigRational::zero(),
        }
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn scale(&mut self, k: &BigRational) {
        if k.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= k;
        }
        self.constant *= k;
    }

    /// `self += k·other`.
    pub(crate) fn add_scaled(&mut self, other: &Self, k: &BigRational) {
        for (&leaf, c) in &other.coeffs {
            let slot = self.coeffs.entry(leaf).or_insert_with(BigRational::zero);
            *slot += c * k;
            if slot.is_zero() {
                self.coeffs.remove(&leaf);
            }
        }
        self.constant += &other.constant * k;
    }
}

/// A numeral's exact value.
pub(crate) fn numeral(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        _ => None,
    }
}

/// Whether `term` is an arithmetic variable: a declared constant of sort Int
/// or Real.
pub(crate) fn is_arith_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.sort(term), Sort::Int | Sort::Real)
        && match terms.get(term) {
            TermData::Var(..) => true,
            TermData::App(_, args) => args.is_empty(),
            _ => false,
        }
}

/// The kind of an interpreted leaf the plug-in defines in the search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Defined {
    /// `(div x k)` for a non-zero integer numeral `k`.
    Div,
    /// `(mod x k)` for a non-zero integer numeral `k`.
    Mod,
    /// `(abs x)`.
    Abs,
}

/// The defined-operator kind of `term`, with its operand and (for `div` and
/// `mod`) its divisor, when `term` is one.
pub(crate) fn defined_leaf(
    terms: &TermStore,
    term: TermId,
) -> Option<(Defined, TermId, Option<BigInt>)> {
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    match (sym.name(), args.as_slice()) {
        ("div" | "mod", &[x, k]) if *terms.sort(term) == Sort::Int => {
            let k = numeral(terms, k)?;
            if !k.is_integer() || k.is_zero() {
                return None;
            }
            let kind = if sym.name() == "div" {
                Defined::Div
            } else {
                Defined::Mod
            };
            Some((kind, x, Some(k.to_integer())))
        }
        ("abs", &[x]) => Some((Defined::Abs, x, None)),
        _ => None,
    }
}

/// Linear forms, memoized per term for one registration pass.
#[derive(Default)]
pub(crate) struct Linearizer {
    memo: BTreeMap<TermId, LinForm>,
}

impl Linearizer {
    /// The linear form of an arithmetic term, or the operator that no plug-in
    /// owns (named, design H2).
    pub(crate) fn linearize(&mut self, terms: &TermStore, term: TermId) -> Result<LinForm, GiveUp> {
        if let Some(hit) = self.memo.get(&term) {
            return Ok(hit.clone());
        }
        let form = self.compute(terms, term)?;
        self.memo.insert(term, form.clone());
        Ok(form)
    }

    fn compute(&mut self, terms: &TermStore, term: TermId) -> Result<LinForm, GiveUp> {
        if let Some(c) = numeral(terms, term) {
            return Ok(LinForm::constant(c));
        }
        // An uninterpreted application is an opaque leaf: the hub decides
        // its equalities with other terms (design H1).
        if is_arith_var(terms, term) || is_uf_app(terms, term) {
            return Ok(LinForm::leaf(term));
        }
        match terms.get(term) {
            TermData::Ite(_, t, e) => {
                // The branches are arithmetic the plug-in parses when the link
                // lemmas name them; the condition is Boolean structure.
                self.linearize(terms, *t)?;
                self.linearize(terms, *e)?;
                Ok(LinForm::leaf(term))
            }
            TermData::App(sym, args) => {
                let op = sym.name();
                match (op, args.as_slice()) {
                    ("+", _) => {
                        let mut sum = LinForm::default();
                        for &arg in args {
                            let form = self.linearize(terms, arg)?;
                            sum.add_scaled(&form, &BigRational::one());
                        }
                        Ok(sum)
                    }
                    ("-", &[x]) => {
                        let mut form = self.linearize(terms, x)?;
                        form.scale(&-BigRational::one());
                        Ok(form)
                    }
                    ("-", [first, rest @ ..]) => {
                        let mut form = self.linearize(terms, *first)?;
                        for &arg in rest {
                            let sub = self.linearize(terms, arg)?;
                            form.add_scaled(&sub, &-BigRational::one());
                        }
                        Ok(form)
                    }
                    ("*", _) => {
                        let mut factor = BigRational::one();
                        let mut var_part: Option<LinForm> = None;
                        for &arg in args {
                            let form = self.linearize(terms, arg)?;
                            if form.is_constant() {
                                factor *= &form.constant;
                            } else if var_part.is_none() {
                                var_part = Some(form);
                            } else {
                                return Err(GiveUp::new(
                                    "no plug-in owns nonlinear `*` (roadmap AN)",
                                ));
                            }
                        }
                        let mut form =
                            var_part.unwrap_or_else(|| LinForm::constant(BigRational::one()));
                        form.scale(&factor);
                        Ok(form)
                    }
                    ("/", &[x, d]) => {
                        let divisor = self.linearize(terms, d)?;
                        if !divisor.is_constant() || divisor.constant.is_zero() {
                            return Err(GiveUp::new(
                                "no plug-in owns `/` by a non-constant or zero divisor",
                            ));
                        }
                        let mut form = self.linearize(terms, x)?;
                        form.scale(&divisor.constant.recip());
                        Ok(form)
                    }
                    ("div" | "mod", &[x, _]) | ("abs", &[x]) => {
                        if defined_leaf(terms, term).is_none() {
                            return Err(GiveUp::new(format!(
                                "no plug-in owns `{op}` by a non-constant or zero divisor"
                            )));
                        }
                        self.linearize(terms, x)?;
                        Ok(LinForm::leaf(term))
                    }
                    _ => Err(GiveUp::new(format!("no plug-in owns operator `{op}`"))),
                }
            }
            other => Err(GiveUp::new(format!(
                "no plug-in owns arithmetic term {:.60}",
                format!("{other:?}")
            ))),
        }
    }
}
