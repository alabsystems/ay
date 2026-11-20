// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted assignment decoding and blockers for exact scalar projections.

use super::*;
use num_bigint::BigInt;
use num_traits::{One, Zero};

#[derive(Debug, Clone)]
pub(crate) enum Encoding {
    Bool(i32),
    Int(Vec<i32>),
}

pub(crate) fn copy_value(value: &Scalar, owner: &CountedAdmission) -> Result<Scalar> {
    match value {
        Scalar::Bool(value) => Ok(Scalar::Bool(*value)),
        Scalar::Int(value) => {
            let words = usize::try_from(value.bits().div_ceil(64))
                .map_err(|_| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            let bytes = words
                .checked_add(1)
                .and_then(|words| words.checked_mul(16))
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            owner.admit(words.saturating_add(1), bytes)?;
            Ok(Scalar::Int(value.clone()))
        }
    }
}

impl Encoding {
    pub(crate) fn literals(&self) -> &[i32] {
        match self {
            Self::Bool(literal) => std::slice::from_ref(literal),
            Self::Int(bits) => bits,
        }
    }

    pub(crate) fn decode(&self, model: &[bool], owner: &CountedAdmission) -> Result<Scalar> {
        let bit = |literal: i32| -> Result<bool> {
            owner.admit(1, 0)?;
            model
                .get(literal_index(literal)?)
                .map(|value| *value == (literal > 0))
                .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))
        };
        match self {
            Self::Bool(literal) => Ok(Scalar::Bool(bit(*literal)?)),
            Self::Int(bits) => {
                if bits.is_empty() {
                    return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
                }
                let bytes = bits
                    .len()
                    .div_ceil(64)
                    .checked_add(1)
                    .and_then(|words| words.checked_mul(64))
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                owner.admit(bits.len(), bytes)?;
                let mut value = BigInt::zero();
                for (index, &literal) in bits.iter().enumerate() {
                    if bit(literal)? {
                        value.set_bit(index as u64, true);
                    }
                }
                if bit(*bits
                    .last()
                    .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))?)?
                {
                    value -= BigInt::one() << bits.len();
                }
                Ok(Scalar::Int(value))
            }
        }
    }

    pub(crate) fn block(
        &self,
        value: &Scalar,
        clause: &mut Vec<Literal>,
        owner: &CountedAdmission,
    ) -> Result<()> {
        reserve(clause, self.literals().len(), owner)?;
        match (self, value) {
            (Self::Bool(literal), Scalar::Bool(value)) => {
                owner.admit(1, 0)?;
                literal_index(*literal)?;
                clause.push(Literal::from_dimacs(if *value {
                    -*literal
                } else {
                    *literal
                }));
            }
            (Self::Int(bits), Scalar::Int(value)) if !bits.is_empty() => {
                for (index, &literal) in bits.iter().enumerate() {
                    owner.admit(1, 0)?;
                    literal_index(literal)?;
                    clause.push(Literal::from_dimacs(if value.bit(index as u64) {
                        -literal
                    } else {
                        literal
                    }));
                }
            }
            _ => return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected)),
        }
        Ok(())
    }
}
