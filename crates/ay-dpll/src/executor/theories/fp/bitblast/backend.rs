// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One dispatch vocabulary for legacy and owning FP construction.

use std::convert::Infallible;

use ay_core::TermId;
use ay_fp::{FpBuildError, FpConstruction, FpSolver};

pub(in crate::executor::theories::fp) enum Predicate {
    Eq(TermId, TermId),
    Lt(TermId, TermId),
    Le(TermId, TermId),
    Gt(TermId, TermId),
    Ge(TermId, TermId),
    IsNan(TermId),
    IsInfinite(TermId),
    IsZero(TermId),
    IsNormal(TermId),
    IsSubnormal(TermId),
    IsPositive(TermId),
    IsNegative(TermId),
    StructuralEq(TermId, TermId),
    /// `=` over two rounding-mode terms.
    RmEq(TermId, TermId),
    Bv(TermId),
    BvEq(TermId, TermId),
}

pub(in crate::executor::theories::fp) trait Encoder {
    type Error;

    fn checkpoint(&mut self) -> Result<(), Self::Error>;
    fn predicate(&mut self, predicate: Predicate) -> Result<Option<i32>, Self::Error>;
}

impl Encoder for FpSolver<'_> {
    type Error = Infallible;

    fn checkpoint(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn predicate(&mut self, predicate: Predicate) -> Result<Option<i32>, Self::Error> {
        Ok(Some(match predicate {
            Predicate::Eq(x, y) => self.bitblast_fp_eq(x, y),
            Predicate::Lt(x, y) => self.bitblast_fp_lt(x, y),
            Predicate::Le(x, y) => self.bitblast_fp_le(x, y),
            Predicate::Gt(x, y) => self.bitblast_fp_gt(x, y),
            Predicate::Ge(x, y) => self.bitblast_fp_ge(x, y),
            Predicate::IsNan(x) => self.bitblast_is_nan(x),
            Predicate::IsInfinite(x) => self.bitblast_is_infinite(x),
            Predicate::IsZero(x) => self.bitblast_is_zero(x),
            Predicate::IsNormal(x) => self.bitblast_is_normal(x),
            Predicate::IsSubnormal(x) => self.bitblast_is_subnormal(x),
            Predicate::IsPositive(x) => self.bitblast_is_positive(x),
            Predicate::IsNegative(x) => self.bitblast_is_negative(x),
            Predicate::StructuralEq(x, y) => self.bitblast_fp_structural_eq(x, y),
            Predicate::RmEq(x, y) => self.bitblast_rm_eq(x, y),
            Predicate::Bv(term) => return Ok(self.bitblast_bv_predicate(term)),
            Predicate::BvEq(x, y) => return Ok(self.try_bitblast_bv_eq(x, y)),
        }))
    }
}

impl Encoder for FpConstruction<'_, '_> {
    type Error = FpBuildError;

    fn checkpoint(&mut self) -> Result<(), Self::Error> {
        self.try_has_encoding_gap().map(|_| ())
    }

    fn predicate(&mut self, predicate: Predicate) -> Result<Option<i32>, Self::Error> {
        Ok(Some(match predicate {
            Predicate::Eq(x, y) => self.try_bitblast_fp_eq(x, y)?,
            Predicate::Lt(x, y) => self.try_bitblast_fp_lt(x, y)?,
            Predicate::Le(x, y) => self.try_bitblast_fp_le(x, y)?,
            Predicate::Gt(x, y) => self.try_bitblast_fp_gt(x, y)?,
            Predicate::Ge(x, y) => self.try_bitblast_fp_ge(x, y)?,
            Predicate::IsNan(x) => self.try_bitblast_is_nan(x)?,
            Predicate::IsInfinite(x) => self.try_bitblast_is_infinite(x)?,
            Predicate::IsZero(x) => self.try_bitblast_is_zero(x)?,
            Predicate::IsNormal(x) => self.try_bitblast_is_normal(x)?,
            Predicate::IsSubnormal(x) => self.try_bitblast_is_subnormal(x)?,
            Predicate::IsPositive(x) => self.try_bitblast_is_positive(x)?,
            Predicate::IsNegative(x) => self.try_bitblast_is_negative(x)?,
            Predicate::StructuralEq(x, y) => self.try_bitblast_fp_structural_eq(x, y)?,
            Predicate::RmEq(x, y) => self.try_bitblast_rm_eq(x, y)?,
            Predicate::Bv(term) => return self.try_bitblast_bv_predicate(term),
            Predicate::BvEq(x, y) => return self.try_bitblast_bv_eq(x, y),
        }))
    }
}

#[cfg(test)]
pub(in crate::executor::theories::fp) fn infallible<T>(result: Result<T, Infallible>) -> T {
    match result {
        Ok(value) => value,
        Err(never) => match never {},
    }
}
