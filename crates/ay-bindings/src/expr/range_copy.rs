// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constant-size unsigned BV64 range-copy expression.
//!
//! The printed parallel let evaluates every operand outside both its private
//! bindings and the lambda. Thus even adversarial operand symbol names cannot
//! be captured; no source symbol is inserted into the private lambda matrix.
//! SMT-LIB 2.6 parallel-let semantics and ArraysEx extensionality supply the
//! equivalence to the pointwise range definition.

use super::{Expr, ExprValue};
use crate::{Sort, SortError};
use std::sync::Arc;

impl Expr {
    /// Replace `self[lo..hi]` by `src[i - lo + src_start]` for each BV64 index.
    /// All arithmetic and comparisons are unsigned BV64 operations. No lane
    /// unrolling, pointer assertion or non-wrapping arithmetic is implied.
    pub fn try_array_range_copy(
        self,
        src: Self,
        lo: Self,
        hi: Self,
        src_start: Self,
    ) -> Result<Self, SortError> {
        let array = self
            .sort()
            .array_sort()
            .ok_or_else(|| SortError::unary("array_range_copy", "Array", self.sort()))?;
        if self.sort() != src.sort() || array.index_sort.bitvec_width() != Some(64) {
            return Err(SortError::binary(
                "array_range_copy",
                "equal BV64-indexed arrays",
                self.sort(),
                src.sort(),
            ));
        }
        let index_sort = Sort::bitvec(64);
        for bound in [&lo, &hi, &src_start] {
            if bound.sort() != &index_sort {
                return Err(SortError::binary(
                    "array_range_copy",
                    "BV64 bounds",
                    bound.sort(),
                    &index_sort,
                ));
            }
        }
        Ok(Self {
            sort: self.sort().clone(),
            value: Arc::new(ExprValue::ArrayRangeCopy {
                dst: self,
                src,
                lo,
                hi,
                src_start,
            }),
        })
    }
}

pub(super) fn display(args: [&Expr; 5], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
        f,
        "(let ((ay_range_dst {}) (ay_range_src {}) (ay_range_lo {}) \
        (ay_range_hi {}) (ay_range_src_lo {})) \
        (lambda ((ay_range_i (_ BitVec 64))) \
        (ite (and (bvule ay_range_lo ay_range_i) (bvult ay_range_i ay_range_hi)) \
        (select ay_range_src (bvadd (bvsub ay_range_i ay_range_lo) ay_range_src_lo)) \
        (select ay_range_dst ay_range_i))))",
        args[0], args[1], args[2], args[3], args[4]
    )
}

#[cfg(test)]
mod tests;
