// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Logical SMT FP operations, not Rust raw NaN payload semantics. Equality
//! identifies every NaN representation; IEEE fp.eq excludes NaN and identifies
//! both zero signs. All non-NaN sign/exponent/fraction fields remain significant.

use super::super::graph::{Binary, Bits};
use super::super::{Arithmetic, Format};
use super::source::{Builder, Value};
use super::{Error, Result};
use ay_core::{Sort, TermId};

impl Builder<'_, '_> {
    pub(super) fn constructor(
        &mut self,
        s: TermId,
        e: TermId,
        f: TermId,
        sort: &Sort,
    ) -> Result<Value> {
        let Sort::FloatingPoint(eb, p) = sort else {
            return Err(Error::Source);
        };
        Format::checked_for(Arithmetic::Mul, *eb, *p)?;
        let sign = self.bv(s)?;
        let exponent = self.bv(e)?;
        let fraction = self.bv(f)?;
        if self.program.reference.width(sign)? != 1
            || self.program.reference.width(exponent)? != *eb
            || self.program.reference.width(fraction)? != p - 1
        {
            return Err(Error::Source);
        }
        Ok(Value::Fp {
            bits: Bits {
                sign,
                exponent,
                fraction,
            },
            eb: *eb,
            p: *p,
        })
    }

    pub(super) fn arithmetic(
        &mut self,
        name: &str,
        rm: TermId,
        x: TermId,
        y: TermId,
        sort: &Sort,
    ) -> Result<Value> {
        let operation = match name {
            "fp.mul" => Arithmetic::Mul,
            "fp.add" => Arithmetic::Add,
            "fp.sub" => Arithmetic::Sub,
            _ => return Err(Error::Source),
        };
        let Sort::FloatingPoint(eb, p) = sort else {
            return Err(Error::Source);
        };
        let (x, xe, xp) = self.fp(x)?;
        let (y, ye, yp) = self.fp(y)?;
        if (xe, xp) != (*eb, *p) || (ye, yp) != (*eb, *p) {
            return Err(Error::Source);
        }
        let Value::Rm(rm) = self.value(rm)? else {
            return Err(Error::Source);
        };
        self.program.reference.format = Format::checked_for(operation, *eb, *p)?;
        self.program.reference.operation = operation;
        let five = self.program.reference.small(5, 3)?;
        let domain = self.program.reference.binary(Binary::Ult, rm, five)?;
        let output = match operation {
            Arithmetic::Mul => {
                let finite = self.program.reference.product(x, y, rm)?;
                self.program.reference.specials(x, y, finite, domain)?
            }
            Arithmetic::Add | Arithmetic::Sub => {
                self.program.reference.addition(x, y, rm, domain)?
            }
        };
        Ok(Value::Fp {
            bits: Bits {
                sign: output.sign,
                exponent: output.exponent,
                fraction: output.fraction,
            },
            eb: *eb,
            p: *p,
        })
    }

    pub(super) fn structural_equality(&mut self, x: Bits, y: Bits) -> Result<Value> {
        // Derive format from checked field widths, not a previous operation.
        self.program.reference.format.eb = self.program.reference.width(x.exponent)?;
        let (xn, _, _) = self.program.reference.classifications(x)?;
        let (yn, _, _) = self.program.reference.classifications(y)?;
        let both_nan = self.program.reference.binary(Binary::And, xn, yn)?;
        let sign = self.program.reference.binary(Binary::Eq, x.sign, y.sign)?;
        let exponent = self
            .program
            .reference
            .binary(Binary::Eq, x.exponent, y.exponent)?;
        let fraction = self
            .program
            .reference
            .binary(Binary::Eq, x.fraction, y.fraction)?;
        let fields = self
            .program
            .reference
            .binary(Binary::And, exponent, fraction)?;
        let fields = self.program.reference.binary(Binary::And, sign, fields)?;
        Ok(Value::Bool(self.program.reference.binary(
            Binary::Or,
            both_nan,
            fields,
        )?))
    }

    pub(super) fn classifier(&mut self, name: &str, x: TermId) -> Result<Value> {
        let (x, eb, _) = self.fp(x)?;
        self.program.reference.format.eb = eb;
        let (nan, infinity, zero) = self.program.reference.classifications(x)?;
        let exp_zero = self.program.reference.is_zero(x.exponent)?;
        let exp_all = self.program.reference.ones(eb)?;
        let exp_all = self
            .program
            .reference
            .binary(Binary::Eq, x.exponent, exp_all)?;
        let fraction_nonzero = self.program.reference.nonzero(x.fraction)?;
        let result = match name {
            "fp.isNaN" => nan,
            "fp.isInfinite" => infinity,
            "fp.isZero" => zero,
            "fp.isSubnormal" => {
                self.program
                    .reference
                    .binary(Binary::And, exp_zero, fraction_nonzero)?
            }
            "fp.isNormal" => {
                let special = self
                    .program
                    .reference
                    .binary(Binary::Or, exp_zero, exp_all)?;
                self.program.reference.not(special)?
            }
            "fp.isNegative" | "fp.isPositive" => {
                let non_nan = self.program.reference.not(nan)?;
                let sign = if name == "fp.isNegative" {
                    x.sign
                } else {
                    self.program.reference.not(x.sign)?
                };
                self.program.reference.binary(Binary::And, non_nan, sign)?
            }
            _ => return Err(Error::Source),
        };
        Ok(Value::Bool(result))
    }

    pub(super) fn fp_compare(&mut self, name: &str, a: TermId, b: TermId) -> Result<Value> {
        let (a, ae, ap) = self.fp(a)?;
        let (b, be, bp) = self.fp(b)?;
        if (ae, ap) != (be, bp) {
            return Err(Error::Source);
        }
        self.program.reference.format.eb = ae;
        let (an, _, az) = self.program.reference.classifications(a)?;
        let (bn, _, bz) = self.program.reference.classifications(b)?;
        let nan = self.program.reference.binary(Binary::Or, an, bn)?;
        let ordered = self.program.reference.not(nan)?;
        let zeros = self.program.reference.binary(Binary::And, az, bz)?;
        let Value::Bool(structural) = self.structural_equality(a, b)? else {
            return Err(Error::Source);
        };
        let equal = self
            .program
            .reference
            .binary(Binary::Or, zeros, structural)?;
        let less = self.ordered_less(a, b, zeros)?;
        let greater = self.ordered_less(b, a, zeros)?;
        let result = match name {
            "fp.eq" => equal,
            "fp.lt" => less,
            "fp.gt" => greater,
            "fp.leq" => self.program.reference.binary(Binary::Or, less, equal)?,
            "fp.geq" => self.program.reference.binary(Binary::Or, greater, equal)?,
            _ => return Err(Error::Source),
        };
        Ok(Value::Bool(self.program.reference.binary(
            Binary::And,
            ordered,
            result,
        )?))
    }

    fn ordered_less(
        &mut self,
        a: Bits,
        b: Bits,
        both_zero: super::super::graph::RefId,
    ) -> Result<super::super::graph::RefId> {
        let sign_diff = self.program.reference.binary(Binary::Xor, a.sign, b.sign)?;
        let a_mag = self.concat(a.exponent, a.fraction)?;
        let b_mag = self.concat(b.exponent, b.fraction)?;
        let positive = self.program.reference.binary(Binary::Ult, a_mag, b_mag)?;
        let negative = self.program.reference.binary(Binary::Ult, b_mag, a_mag)?;
        let same_sign = self.program.reference.select(a.sign, negative, positive)?;
        let less = self
            .program
            .reference
            .select(sign_diff, a.sign, same_sign)?;
        let not_zeros = self.program.reference.not(both_zero)?;
        Ok(self
            .program
            .reference
            .binary(Binary::And, not_zeros, less)?)
    }
}
