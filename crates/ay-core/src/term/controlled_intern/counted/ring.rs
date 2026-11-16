// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed ring construction and exact coefficients under the original owner.
use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One as _, Signed as _, ToPrimitive as _, Zero as _};

/// Closed arithmetic vocabulary; no caller-supplied head or result sort.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CountedRingBuiltin {
    /// Addition of integer or real terms.
    Add,
    /// Subtraction of integer or real terms.
    Subtract,
    /// Multiplication of integer or real terms.
    Multiply,
    /// Additive inverse of an integer or real term.
    Negate,
    /// Exact coercion of an integer term to the real sort.
    ToReal,
    /// Floor a real term to the integer sort.
    ToInt,
    /// Binary exponentiation with the native real result sort.
    Power,
}

#[derive(Clone, Copy)]
enum NumericOp {
    Add,
    Multiply,
    Negate,
    Reciprocal,
}
enum OwnedNumber {
    Integer(BigInt),
    Real(BigRational),
}

fn parts<'a>(
    term: &'a TermData,
    owner: &dyn TermConstructionAdmission,
) -> Result<(&'a BigInt, Option<&'a BigInt>)> {
    match term {
        TermData::Const(Constant::Int(n)) => {
            payload::bigint(n, owner, PayloadUse::Inspect)?;
            Ok((n, None))
        }
        TermData::Const(Constant::Rational(r)) => {
            payload::bigint(r.0.numer(), owner, PayloadUse::Inspect)?;
            payload::bigint(r.0.denom(), owner, PayloadUse::Inspect)?;
            if !r.0.denom().is_positive() {
                return Err(CountedTermError::InvalidInput);
            }
            Ok((r.0.numer(), Some(r.0.denom())))
        }
        _ => Err(CountedTermError::InvalidInput),
    }
}
fn denominator(value: Option<&BigInt>, owner: &dyn TermConstructionAdmission) -> Result<BigInt> {
    match value {
        Some(n) => numbers::copy(n, owner),
        None => numbers::one(owner),
    }
}
fn calculate(
    left: &TermData,
    right: Option<&TermData>,
    sort: &Sort,
    op: NumericOp,
    owner: &dyn TermConstructionAdmission,
) -> Result<OwnedNumber> {
    let (a, ad) = parts(left, owner)?;
    if sort == &Sort::Int {
        if ad.is_some() {
            return Err(CountedTermError::InvalidInput);
        }
        let n = match op {
            NumericOp::Negate => -numbers::copy(a, owner)?,
            NumericOp::Add | NumericOp::Multiply => {
                let (b, bd) = parts(right.ok_or(CountedTermError::InvalidInput)?, owner)?;
                if bd.is_some() {
                    return Err(CountedTermError::InvalidInput);
                }
                match op {
                    NumericOp::Add => numbers::add(a, b, owner)?,
                    _ => numbers::multiply(a, b, owner)?,
                }
            }
            NumericOp::Reciprocal => return Err(CountedTermError::InvalidInput),
        };
        return Ok(OwnedNumber::Integer(n));
    }
    if sort != &Sort::Real {
        return Err(CountedTermError::InvalidInput);
    }
    let (n, d) = match op {
        NumericOp::Negate => (-numbers::copy(a, owner)?, denominator(ad, owner)?),
        NumericOp::Reciprocal => {
            if a.is_zero() {
                return Err(CountedTermError::InvalidInput);
            }
            let n = denominator(ad, owner)?;
            let d = numbers::copy(a, owner)?;
            if d.is_negative() {
                (-n, -d)
            } else {
                (n, d)
            }
        }
        NumericOp::Add | NumericOp::Multiply => {
            let (b, bd) = parts(right.ok_or(CountedTermError::InvalidInput)?, owner)?;
            let ad = denominator(ad, owner)?;
            let bd = denominator(bd, owner)?;
            let n = match op {
                NumericOp::Multiply => numbers::multiply(a, b, owner)?,
                _ => {
                    let lhs = numbers::multiply(a, &bd, owner)?;
                    let rhs = numbers::multiply(b, &ad, owner)?;
                    numbers::add(&lhs, &rhs, owner)?
                }
            };
            (n, numbers::multiply(&ad, &bd, owner)?)
        }
    };
    owner.check()?;
    Ok(OwnedNumber::Real(BigRational::new_raw(n, d)))
}

impl<O: TermConstructionAdmission> CountedTermBuilder<'_, '_, O> {
    fn numeric_parts(&self, a: TermId) -> Result<(&BigInt, Option<&BigInt>)> {
        self.owner.admit(1, 0)?;
        if !matches!(self.store.sort(a), Sort::Int | Sort::Real)
            || (self.store.sort(a) == &Sort::Int
                && matches!(self.store.get(a), TermData::Const(Constant::Rational(_))))
        {
            return Err(CountedTermError::InvalidInput);
        }
        parts(self.store.get(a), self.owner)
    }
    /// Build a known arithmetic operator after validating its actual operands.
    pub fn ring_apply(&mut self, op: CountedRingBuiltin, args: &[TermId]) -> Result<TermId> {
        self.owner.admit(
            args.len()
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?,
            0,
        )?;
        let first = *args.first().ok_or(CountedTermError::InvalidInput)?;
        let initial = self.store.sort(first);
        let (result, name) = match op {
            CountedRingBuiltin::ToReal | CountedRingBuiltin::ToInt => {
                if args.len() != 1 {
                    return Err(CountedTermError::InvalidInput);
                }
                let (input, output, head) = if op == CountedRingBuiltin::ToReal {
                    (Sort::Int, Sort::Real, "to_real")
                } else {
                    (Sort::Real, Sort::Int, "to_int")
                };
                if initial != &input {
                    return Err(CountedTermError::InvalidInput);
                }
                (output, head)
            }
            _ => {
                if !matches!(initial, Sort::Int | Sort::Real)
                    || args.iter().any(|id| self.store.sort(*id) != initial)
                {
                    return Err(CountedTermError::InvalidInput);
                }
                if (op == CountedRingBuiltin::Negate && args.len() != 1)
                    || (op == CountedRingBuiltin::Power && args.len() != 2)
                {
                    return Err(CountedTermError::InvalidInput);
                }
                let result = if op == CountedRingBuiltin::Power {
                    Sort::Real
                } else if initial == &Sort::Int {
                    Sort::Int
                } else {
                    Sort::Real
                };
                let name = match op {
                    CountedRingBuiltin::Add => "+",
                    CountedRingBuiltin::Multiply => "*",
                    CountedRingBuiltin::Power => "^",
                    _ => "-",
                };
                (result, name)
            }
        };
        let term = payload::named(name, args, self.owner)?;
        self.check_generated_head(&term)?;
        let result = self.intern_typed_data(term, result, Some(false));
        self.owner.check()?;
        result
    }
    /// Small exact coefficient, with its domain taken from the original term.
    pub fn number_like(&mut self, value: i64, prototype: TermId) -> Result<TermId> {
        self.owner.admit(1, 8)?;
        let n = BigInt::from(value);
        match self.store.sort(prototype) {
            Sort::Int => self.integer(&n),
            Sort::Real => {
                let d = numbers::one(self.owner)?;
                self.rational(&BigRational::new_raw(n, d))
            }
            _ => Err(CountedTermError::InvalidInput),
        }
    }
    fn numeric(&mut self, left: TermId, right: Option<TermId>, op: NumericOp) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let sort = self.store.sort(left);
        if right.is_some_and(|id| self.store.sort(id) != sort) {
            return Err(CountedTermError::InvalidInput);
        }
        let result = calculate(
            self.store.get(left),
            right.map(|id| self.store.get(id)),
            sort,
            op,
            self.owner,
        )?;
        match result {
            OwnedNumber::Integer(n) => self.integer(&n),
            OwnedNumber::Real(r) => self.rational(&r),
        }
    }
    /// Exact addition of two numeric literals, with original admission.
    pub fn number_add(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.numeric(a, Some(b), NumericOp::Add)
    }
    /// Exact multiplication of two numeric literals, with original admission.
    pub fn number_product(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.numeric(a, Some(b), NumericOp::Multiply)
    }
    /// Exact negation of a numeric literal, with original admission.
    pub fn number_negate(&mut self, a: TermId) -> Result<TermId> {
        self.numeric(a, None, NumericOp::Negate)
    }
    /// Exact nonzero reciprocal; this refuses zero rather than choosing its unspecified value.
    pub fn number_reciprocal(&mut self, a: TermId) -> Result<TermId> {
        self.numeric(a, None, NumericOp::Reciprocal)
    }
    /// Inspect an exact coefficient without allocating an encoding or a default model.
    pub fn number_is_zero(&self, a: TermId) -> Result<bool> {
        let (n, _) = self.numeric_parts(a)?;
        Ok(n.is_zero())
    }
    /// Inspect an exact coefficient without allocating an encoding.
    pub fn number_is_one(&self, a: TermId) -> Result<bool> {
        let (n, d) = self.numeric_parts(a)?;
        Ok(match d {
            None => n.is_one(),
            Some(d) => n == d,
        })
    }
    /// Checked natural exponent; fractional/negative/large values remain non-polynomial.
    pub fn number_natural(&self, a: TermId) -> Result<Option<u32>> {
        let (n, d) = self.numeric_parts(a)?;
        if d.is_some_and(|d| !d.is_one()) {
            return Ok(None);
        }
        Ok(n.to_u32())
    }
    /// Canonical Int copy of an integral numeric literal, for compact powers.
    pub fn number_integer(&mut self, a: TermId) -> Result<TermId> {
        let (n, d) = self.numeric_parts(a)?;
        if d.is_some_and(|d| !d.is_one()) {
            return Err(CountedTermError::InvalidInput);
        }
        let n = numbers::copy(n, self.owner)?;
        self.integer(&n)
    }
    /// Inspect positivity/integrality without expanding a declared degree.
    pub fn number_positive_integral(&self, a: TermId) -> Result<bool> {
        let (n, d) = self.numeric_parts(a)?;
        Ok(n.is_positive() && d.is_none_or(|d| d.is_one()))
    }
    /// Actual output cardinality; absence must refuse admission before allocation.
    pub fn number_usize(&self, a: TermId) -> Result<Option<usize>> {
        let (n, d) = self.numeric_parts(a)?;
        if d.is_some_and(|d| !d.is_one()) {
            return Ok(None);
        }
        Ok(n.to_usize())
    }
    /// Copy an exact numeric literal into an explicitly checked ring domain.
    pub fn number_convert_like(&mut self, a: TermId, prototype: TermId) -> Result<TermId> {
        let (n, d) = self.numeric_parts(a)?;
        let real = match self.store.sort(prototype) {
            Sort::Int => false,
            Sort::Real => true,
            _ => return Err(CountedTermError::InvalidInput),
        };
        if !real && d.is_some_and(|d| !d.is_one()) {
            return Err(CountedTermError::InvalidInput);
        }
        let n = numbers::copy(n, self.owner)?;
        if real {
            let d = denominator(d, self.owner)?;
            self.rational(&BigRational::new_raw(n, d))
        } else {
            self.integer(&n)
        }
    }
}
