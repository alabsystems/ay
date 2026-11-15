// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `poly_simp` over bit-vector terms (Clean's Carcara
//! `polynomial.rs`): both sides flattened to polynomials over `+`/`bvadd`,
//! `-`/`bvsub`/`bvneg` and `*`/`bvmul`, every other term an atom; for a
//! bit-vector sort each coefficient and the constant reduced modulo 2^width,
//! KEEPING a monomial whose reduced coefficient is 0; then the difference
//! must be empty. The consumer's `insert` skips a zero addend, so such a kept
//! monomial is not cancelled by the other side: that asymmetry is mirrored.
//! A real division, `to_real` or a side whose sort is not an inferred
//! bit-vector width is `Undetermined`.

use std::collections::hash_map::{Entry, HashMap};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::document::Document;
use super::{require, shape, undecided, Checked, StepInput, Verdict};

type Monomial = Vec<u32>;

#[derive(Default)]
struct Polynomial {
    terms: HashMap<Monomial, BigInt>,
    constant: BigInt,
}

impl Polynomial {
    /// The consumer's `insert`: a zero addend is skipped; an entry that sums
    /// to zero is removed.
    fn insert(&mut self, key: Monomial, value: BigInt) {
        if value.is_zero() {
            return;
        }
        match self.terms.entry(key) {
            Entry::Occupied(mut entry) => {
                *entry.get_mut() += value;
                if entry.get().is_zero() {
                    entry.remove();
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(value);
            }
        }
    }

    fn from_term(document: &Document, term: u32) -> Result<Self, Verdict> {
        let mut result = Self::default();
        result.add_term(document, term, &BigInt::one())?;
        Ok(result)
    }

    fn add_term(&mut self, document: &Document, term: u32, coeff: &BigInt) -> Result<(), Verdict> {
        let args = document.args(term);
        match document.head(term) {
            Some("+" | "bvadd") => {
                for arg in args {
                    self.add_term(document, arg, coeff)?;
                }
            }
            Some("-" | "bvneg") if args.len() == 1 => self.add_term(document, args[0], &-coeff)?,
            Some("-" | "bvsub") if !args.is_empty() => {
                self.add_term(document, args[0], coeff)?;
                for &arg in &args[1..] {
                    self.add_term(document, arg, &-coeff)?;
                }
            }
            Some("*" | "bvmul") if !args.is_empty() => {
                let mut product = Self::from_term(document, args[0])?;
                for &arg in &args[1..] {
                    product = product.mul(Self::from_term(document, arg)?);
                }
                for (monomial, inner) in product.terms {
                    self.insert(monomial, inner * coeff);
                }
                self.constant += coeff * product.constant;
            }
            Some("/" | "to_real" | "div") => {
                return undecided("a real or integer division is not mirrored")
            }
            _ => {
                if let Some(bits) = document.constant_bits(term) {
                    let mut value = BigInt::zero();
                    for &one in bits.iter().rev() {
                        value = value * 2 + u8::from(one);
                    }
                    self.constant += value * coeff;
                } else if document
                    .atom_text(term)
                    .is_some_and(|t| t.starts_with(|c: char| c.is_ascii_digit()))
                {
                    return undecided("an arithmetic constant is not mirrored");
                } else {
                    self.insert(vec![term], coeff.clone());
                }
            }
        }
        Ok(())
    }

    fn mul(self, other: Self) -> Self {
        let mut result = Self::default();
        for (x1, c1) in &self.terms {
            for (x2, c2) in &other.terms {
                let mut monomial = x1.clone();
                monomial.extend(x2);
                monomial.sort_unstable();
                result.insert(monomial, c1 * c2);
            }
            result.insert(x1.clone(), c1 * &other.constant);
        }
        for (x2, c2) in &other.terms {
            result.insert(x2.clone(), c2 * &self.constant);
        }
        result.constant = &self.constant * &other.constant;
        result
    }

    /// `modulo`: every coefficient and the constant reduced, entries kept.
    fn modulo(&mut self, n: &BigInt) {
        for coeff in self.terms.values_mut() {
            *coeff = ((&*coeff % n) + n) % n;
        }
        self.constant = ((&self.constant % n) + n) % n;
    }
}

/// `t_norm.sub(s_norm).is_zero()` with the consumer's `insert`.
fn difference_is_zero(t: &Polynomial, s: &Polynomial) -> bool {
    let t_keys_cancel = t
        .terms
        .iter()
        .all(|(key, c1)| s.terms.get(key).is_some_and(|c2| !c2.is_zero() && c1 == c2));
    let s_keys_vanish = s
        .terms
        .iter()
        .all(|(key, c2)| t.terms.contains_key(key) || c2.is_zero());
    t_keys_cancel && s_keys_vanish && t.constant == s.constant
}

pub(super) fn poly_simp(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let Some(width) = document.width(sides[0]) else {
        return undecided("the side's sort is not an inferred bit-vector width");
    };
    let mut t = Polynomial::from_term(document, sides[0])?;
    let mut s = Polynomial::from_term(document, sides[1])?;
    let n = BigInt::one() << width;
    t.modulo(&n);
    s.modulo(&n);
    require(difference_is_zero(&t, &s), || {
        format!(
            "{} and {} are different polynomials",
            document.show(sides[0]),
            document.show(sides[1])
        )
    })
}
