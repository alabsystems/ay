// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete fixed-width word lowering using total Boolean gates. Every
//! product bit is retained until its actual modular output width. Shift
//! amount high bits are OR-reduced before selection, never modulo-masked.

use super::super::graph::Binary;
use super::circuit::Compiler;
use super::{Error, Result};
use ay_sat::Literal;

#[derive(Clone, Copy)]
pub(super) enum BitConstant {
    Zero,
    One,
}
#[derive(Clone, Copy)]
enum CarryInput {
    Zero,
    One,
}

impl Compiler<'_, '_, '_> {
    pub(super) fn binary(
        &mut self,
        op: Binary,
        a: &[Literal],
        b: &[Literal],
    ) -> Result<Vec<Literal>> {
        if a.len() != b.len() || a.is_empty() {
            return Err(Error::Source);
        }
        match op {
            Binary::Add => self.add(a, b, CarryInput::Zero),
            Binary::Sub => {
                let mut complement = self.reserve(b.len())?;
                for &bit in b {
                    self.reference.charge(1, 0)?;
                    complement.push(bit.negated());
                }
                self.add(a, &complement, CarryInput::One)
            }
            Binary::Mul => self.multiply(a, b),
            Binary::Eq => {
                let mut equal = self.constant(BitConstant::One)?;
                for (&a, &b) in a.iter().zip(b) {
                    let diff = self.xor(a, b)?;
                    equal = self.and(equal, diff.negated())?;
                }
                let mut result = self.reserve(1)?;
                result.push(equal);
                Ok(result)
            }
            Binary::Ult => {
                let mut less = self.constant(BitConstant::Zero)?;
                for (&a, &b) in a.iter().zip(b) {
                    let local = self.and(a.negated(), b)?;
                    let equal = self.xor(a, b)?.negated();
                    let lower = self.and(equal, less)?;
                    less = self.or(local, lower)?;
                }
                let mut result = self.reserve(1)?;
                result.push(less);
                Ok(result)
            }
            Binary::Shl | Binary::Lshr => self.shift(op, a, b),
            Binary::And | Binary::Or | Binary::Xor => {
                let mut result = self.reserve(a.len())?;
                for (&a, &b) in a.iter().zip(b) {
                    result.push(match op {
                        Binary::And => self.and(a, b)?,
                        Binary::Or => self.or(a, b)?,
                        Binary::Xor => self.xor(a, b)?,
                        _ => return Err(Error::Source),
                    });
                }
                Ok(result)
            }
        }
    }

    fn add(&mut self, a: &[Literal], b: &[Literal], carry: CarryInput) -> Result<Vec<Literal>> {
        if a.len() != b.len() {
            return Err(Error::Source);
        }
        let mut carry = self.constant(match carry {
            CarryInput::Zero => BitConstant::Zero,
            CarryInput::One => BitConstant::One,
        })?;
        let mut result = self.reserve(a.len())?;
        for (&a, &b) in a.iter().zip(b) {
            let parity = self.xor(a, b)?;
            result.push(self.xor(parity, carry)?);
            let together = self.and(a, b)?;
            let propagated = self.and(parity, carry)?;
            carry = self.or(together, propagated)?;
        }
        // Final carry is defined but not part of this MODULAR output word.
        Ok(result)
    }

    fn multiply(&mut self, a: &[Literal], b: &[Literal]) -> Result<Vec<Literal>> {
        let width = a.len();
        let zero = self.constant(BitConstant::Zero)?;
        let mut result = self.reserve(width)?;
        for _ in 0..width {
            self.reference.charge(1, 0)?;
            result.push(zero);
        }
        for (shift, &control) in b.iter().enumerate() {
            let mut row = self.reserve(width)?;
            for index in 0..width {
                self.reference.charge(1, 0)?;
                row.push(if index < shift {
                    zero
                } else {
                    self.and(control, a[index - shift])?
                });
            }
            result = self.add(&result, &row, CarryInput::Zero)?;
        }
        Ok(result)
    }

    fn shift(&mut self, op: Binary, a: &[Literal], amount: &[Literal]) -> Result<Vec<Literal>> {
        let width = a.len();
        let mut result = self.reserve(width)?;
        for &bit in a {
            self.reference.charge(1, 0)?;
            result.push(bit);
        }
        let zero = self.constant(BitConstant::Zero)?;
        let mut excessive = zero;
        for (index, &control) in amount.iter().enumerate() {
            self.reference.charge(1, 0)?;
            let shift = u32::try_from(index)
                .ok()
                .and_then(|n| 1usize.checked_shl(n));
            let Some(shift) = shift.filter(|n| *n < width) else {
                excessive = self.or(excessive, control)?;
                continue;
            };
            let mut next = self.reserve(width)?;
            for bit in 0..width {
                let from = match op {
                    Binary::Shl => bit.checked_sub(shift),
                    Binary::Lshr => bit.checked_add(shift).filter(|n| *n < width),
                    _ => return Err(Error::Source),
                };
                let shifted = from.map_or(zero, |index| result[index]);
                next.push(self.mux(control, shifted, result[bit])?);
            }
            result = next;
        }
        for bit in &mut result {
            *bit = self.and(excessive.negated(), *bit)?;
        }
        Ok(result)
    }
}
