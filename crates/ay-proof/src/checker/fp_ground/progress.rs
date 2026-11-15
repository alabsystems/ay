// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One sticky borrowed owner for a complete ground-FP validation request.

use super::*;
use std::mem::size_of;

#[derive(Clone, Copy)]
pub(super) enum Arithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
}

// Two rational operands each have a numerator and denominator. Scaling an FP
// significand may add its <=256 bits to the existing power-of-two bound. The
// sum also bounds cross-products before normalization/precision refusal.
const MAX_TRANSIENT_BITS: u64 = 4 * (MAX_RATIONAL_BITS + MAX_SB as u64) + 2;

pub(super) struct Meter<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    remaining: usize,
    refused: bool,
}

impl<'a> Meter<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            progress,
            remaining: FP_GROUND_WORK_LIMIT,
            refused: false,
        }
    }

    pub(super) fn refused(&self) -> bool {
        self.refused
    }

    #[cfg(test)]
    pub(super) fn with_local_limit(
        progress: &'a mut dyn FnMut(usize, usize) -> bool,
        limit: usize,
    ) -> Self {
        Self {
            progress,
            remaining: limit,
            refused: false,
        }
    }

    pub(super) fn refuse<T>(&mut self) -> Option<T> {
        self.refused = true;
        None
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Option<()> {
        if self.refused {
            return None;
        }
        if !(self.progress)(work, bytes) {
            return self.refuse();
        }
        Some(())
    }

    // Preserve the kernel's existing local bound in NODE visits. Numeric
    // bit-scaled work and scratch additionally debit the original caller,
    // rather than silently changing that local unit into limb operations.
    pub(super) fn node(&mut self) -> Option<()> {
        if self.refused {
            return None;
        }
        let Some(remaining) = self.remaining.checked_sub(1) else {
            return self.refuse();
        };
        self.remaining = remaining;
        self.charge(1, 0)
    }

    pub(super) fn inspect(&mut self, count: usize) -> Option<()> {
        if self.refused {
            return None;
        }
        if count > self.remaining {
            return self.refuse();
        }
        self.charge(count, 0)
    }

    pub(super) fn entries<T>(&mut self, count: usize) -> Option<()> {
        if self.refused {
            return None;
        }
        if count > self.remaining {
            return self.refuse();
        }
        let Some(bytes) = super::super::nra_poly::generic_container_slot_bytes::<T>()
            .ok()
            .and_then(|slot| slot.checked_mul(count))
        else {
            return self.refuse();
        };
        self.charge(count, bytes)
    }

    pub(super) fn numeric(&mut self, bits: u64) -> Option<()> {
        if self.refused {
            return None;
        }
        let Some(bytes) =
            super::super::nra_poly::bounded_rational_scratch_bytes(bits, MAX_TRANSIENT_BITS).ok()
        else {
            return self.refuse();
        };
        let Some(work) = usize::try_from(super::super::nra_poly::bit_scaled(1, bits)).ok() else {
            return self.refuse();
        };
        self.charge(work, bytes)
    }

    pub(super) fn rational_bits(value: &BigRational) -> Option<u64> {
        value.numer().bits().checked_add(value.denom().bits())
    }

    pub(super) fn rational_copy(&mut self, value: &BigRational) -> Option<BigRational> {
        self.numeric(Self::rational_bits(value)?)?;
        Some(value.clone())
    }

    pub(super) fn rational_abs(&mut self, value: &BigRational) -> Option<BigRational> {
        self.numeric(Self::rational_bits(value)?)?;
        Some(value.abs())
    }

    pub(super) fn to_integer(&mut self, value: &BigRational) -> Option<BigInt> {
        self.numeric(Self::rational_bits(value)?)?;
        Some(value.to_integer())
    }

    pub(super) fn rational_binary(
        &mut self,
        left: &BigRational,
        right: &BigRational,
        op: Arithmetic,
    ) -> Option<BigRational> {
        self.numeric(
            Self::rational_bits(left)?
                .checked_add(Self::rational_bits(right)?)?
                .checked_add(1)?,
        )?;
        Some(match op {
            Arithmetic::Add => left + right,
            Arithmetic::Subtract => left - right,
            Arithmetic::Multiply => left * right,
            Arithmetic::Divide => {
                if right.is_zero() {
                    return None;
                }
                left / right
            }
        })
    }

    pub(super) fn rational_compare(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> Option<std::cmp::Ordering> {
        self.numeric(Self::rational_bits(left)?.checked_add(Self::rational_bits(right)?)?)?;
        Some(left.cmp(right))
    }

    pub(super) fn integer_copy(&mut self, value: &BigInt) -> Option<BigInt> {
        self.numeric(value.bits())?;
        Some(value.clone())
    }

    pub(super) fn integer_compare(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Option<std::cmp::Ordering> {
        let bits = left.bits().max(right.bits());
        let work = usize::try_from(super::super::nra_poly::bit_scaled(1, bits)).ok()?;
        self.charge(work, 0)?;
        Some(left.cmp(right))
    }

    pub(super) fn integer_binary(
        &mut self,
        left: &BigInt,
        right: &BigInt,
        op: Arithmetic,
    ) -> Option<BigInt> {
        self.numeric(left.bits().checked_add(right.bits())?.checked_add(1)?)?;
        Some(match op {
            Arithmetic::Add => left + right,
            Arithmetic::Subtract => left - right,
            Arithmetic::Multiply => left * right,
            Arithmetic::Divide => {
                if right.is_zero() {
                    return None;
                }
                left / right
            }
        })
    }

    pub(super) fn bit_and(&mut self, left: &BigInt, right: &BigInt) -> Option<BigInt> {
        self.numeric(left.bits().checked_add(right.bits())?)?;
        Some(left & right)
    }

    pub(super) fn integer(&mut self, value: u128) -> Option<BigInt> {
        self.numeric(u64::from(u128::BITS - value.leading_zeros()))?;
        Some(BigInt::from(value))
    }

    pub(super) fn shift(&mut self, value: &BigInt, shift: i64) -> Option<BigInt> {
        if shift.unsigned_abs() > MAX_RATIONAL_BITS {
            return None;
        }
        self.numeric(
            value
                .bits()
                .checked_add(shift.unsigned_abs())?
                .checked_add(1)?,
        )?;
        let amount = usize::try_from(shift.unsigned_abs()).ok()?;
        Some(if shift >= 0 {
            value << amount
        } else {
            value >> amount
        })
    }

    pub(super) fn rational(
        &mut self,
        numerator: BigInt,
        denominator: BigInt,
    ) -> Option<BigRational> {
        if denominator.is_zero() {
            return None;
        }
        self.numeric(numerator.bits().checked_add(denominator.bits())?)?;
        Some(BigRational::new(numerator, denominator))
    }

    pub(super) fn from_integer(&mut self, value: BigInt) -> Option<BigRational> {
        self.numeric(value.bits().checked_add(1)?)?;
        Some(BigRational::from_integer(value))
    }

    pub(super) fn literal_integer(&mut self, value: &BigInt) -> Option<()> {
        if value.bits() > MAX_RATIONAL_BITS {
            return self.refuse();
        }
        self.numeric(value.bits())
    }

    pub(super) fn literal_rational(&mut self, value: &BigRational) -> Option<()> {
        if !rational_is_bounded(value) {
            return self.refuse();
        }
        self.numeric(value.numer().bits().checked_add(value.denom().bits())?)
    }

    pub(super) fn value_clone(&mut self, value: Option<&Val>) -> Option<()> {
        self.charge(1, size_of::<Option<Val>>())?;
        match value {
            Some(Val::Bv(value, _) | Val::Int(value)) => self.numeric(value.bits()),
            Some(Val::Real(value)) => {
                self.numeric(value.numer().bits().checked_add(value.denom().bits())?)
            }
            _ => Some(()),
        }
    }

    pub(super) fn children(&mut self, terms: &TermStore, term: TermId) -> Option<Vec<TermId>> {
        if self.refused {
            return None;
        }
        let count = match terms.get(term) {
            TermData::App(_, args) => args.len(),
            TermData::Not(_) => 1,
            TermData::Ite(..) => 3,
            TermData::Let(bindings, _) => bindings.len().checked_add(1)?,
            TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => {
                self.inspect(triggers.len())?;
                let mut count = 1usize;
                for trigger in triggers {
                    self.node()?;
                    count = count.checked_add(trigger.len())?;
                }
                count
            }
            TermData::Const(_) | TermData::Var(..) => 0,
            _ => return None,
        };
        self.entries::<TermId>(count)?;
        Some(terms.children(term))
    }
}
