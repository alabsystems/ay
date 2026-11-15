// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact signed order, represented in the ordinary unsigned BV carrier.
//!
//! A signed comparison denotes one half-open interval in [-2^(w-1), 2^(w-1)).
//! Split that interval at zero BEFORE translating its negative portion by
//! 2^w. This is a bijection, not an unsigned comparison or a complement of an
//! approximate support. Boolean composition remains in `SupportAnalysis`.

use super::{
    charge, Bound, Intervals, QuantifierRejection, SupportAnalysis, MAX_GUARDED_BITVEC_WIDTH,
};
use ay_core::Sort;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Zero};

impl SupportAnalysis<'_, '_> {
    pub(super) fn signed_comparison(
        &self,
        operator: &str,
        endpoint: BigInt,
        desired: bool,
    ) -> Result<Intervals, QuantifierRejection> {
        let Sort::BitVec(bitvec) = self.sort else {
            return Err(QuantifierRejection::BindingSortMismatch);
        };
        let width = bitvec.width;
        if !(1..=MAX_GUARDED_BITVEC_WIDTH).contains(&width)
            || endpoint.sign() == Sign::Minus
            || endpoint.bits() > u64::from(width)
        {
            return Err(QuantifierRejection::BindingSortMismatch);
        }
        // Prepay shifts, signed conversion, bound copies/comparisons, splitting
        // and translation. The extra bit includes 2^w and the exclusive upper
        // endpoint. Union separately charges its own storage/sort/limb work.
        // This is a conservative work allowance, not total heap accounting.
        charge(self.evaluator, 32 * (width + 1).div_ceil(64) as usize)?;
        let modulus = BigInt::one() << width;
        let half = BigInt::one() << (width - 1);
        let endpoint = if endpoint >= half {
            endpoint - &modulus
        } else {
            endpoint
        };
        let next = &endpoint + BigInt::one();
        let (lower, upper) = match (operator, desired) {
            ("bvslt", true) | ("bvsge", false) => (-&half, endpoint),
            ("bvslt", false) | ("bvsge", true) => (endpoint, half),
            ("bvsle", true) | ("bvsgt", false) => (-&half, next),
            ("bvsle", false) | ("bvsgt", true) => (next, half),
            _ => return Ok(Intervals::whole()),
        };
        // Nonnegative values retain their value; negative values occupy the
        // high unsigned suffix. Union normalizes the two pieces and merges a
        // whole-carrier result without duplicate enumeration.
        let zero = BigInt::zero();
        let positive = Intervals::between(
            Bound::Finite(lower.clone().max(zero.clone())),
            Bound::Finite(upper.clone()),
        );
        let negative = Intervals::between(
            Bound::Finite(lower + &modulus),
            Bound::Finite(upper.min(zero) + modulus),
        );
        positive.union(negative, self.evaluator)
    }
}

#[cfg(test)]
mod tests;
