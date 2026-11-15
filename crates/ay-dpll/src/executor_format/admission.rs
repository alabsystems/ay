// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preflight allocations hidden inside num-bigint 0.4.6's native radix writer.
//! Output buffer growth/copies are charged separately by the shared UTF-8 sink.

use ay_core::render_admission::{self as output, Owner};
use num_bigint::BigInt;

pub(super) fn bitwise(bits: u64, radix_bits: u64, owner: Owner<'_>) -> bool {
    if owner.is_none() {
        return true;
    }
    let bytes = usize::try_from(bits.div_ceil(radix_bits).max(1));
    match bytes {
        Ok(bytes) => output::pay(owner, bytes, bytes),
        Err(_) => {
            output::invalid(owner);
            false
        }
    }
}

/// Standard radix conversion by repeated division. This is the same in-place
/// word-division building block as num-bigint0.4.6
/// biguint/convert.rs::to_radix_digits_le. A10^9 chunk fits u32; multiplying a
/// smaller remainder by2^32 and adding one word is strictly below2^64.
pub(super) fn decimal(value: &BigInt, owner: Owner<'_>) -> Option<String> {
    let Some(original) = owner else {
        return Some(value.magnitude().to_str_radix(10));
    };
    let input = value.magnitude().iter_u32_digits();
    let mut words = Vec::new();
    if !output::reserve(&mut words, input.len(), owner) || !output::pay(owner, input.len(), 0) {
        return None;
    }
    words.extend(input);
    let mut chunks = Vec::new();
    while !words.is_empty() {
        if !output::pay(owner, words.len(), 0) {
            return None;
        }
        let mut remainder = 0u64;
        for word in words.iter_mut().rev() {
            let current = (remainder << 32) | u64::from(*word);
            *word = (current / 1_000_000_000) as u32;
            remainder = current % 1_000_000_000;
        }
        while words.last() == Some(&0) {
            if !output::pay(owner, 1, 0) {
                return None;
            }
            words.pop();
        }
        if !output::reserve(&mut chunks, 1, owner) {
            return None;
        }
        chunks.push(remainder as u32);
    }
    let mut result = output::Buffer::new(owner);
    let mut chunks = chunks.iter().rev();
    if let Some(first) = chunks.next() {
        if !result.format(format_args!("{first}")) {
            return None;
        }
        for chunk in chunks {
            if !result.format(format_args!("{chunk:09}")) {
                return None;
            }
        }
    } else if !result.push("0") {
        return None;
    }
    original.check().ok()?;
    Some(result.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;

    #[test]
    fn counted_decimal_retains_large_and_signed_numeric_values() {
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        for value in [
            BigInt::from(0),
            BigInt::from(1_000_000_001u64),
            (BigInt::from(1) << 4096) + BigInt::from(3),
        ] {
            let digits = decimal(&value, Some(&owner)).unwrap();
            assert_eq!(BigInt::parse_bytes(digits.as_bytes(), 10).unwrap(), value);
            let negative = -&value;
            assert_eq!(
                crate::executor_format::format_bigint_owned(&negative, Some(&owner)),
                crate::executor_format::format_bigint(&negative)
            );
        }
        let stopped =
            CountedAdmission::new(FiniteAdmissionGrant::new(0, 0), None, Arc::new(|| false))
                .unwrap();
        assert!(decimal(&BigInt::from(1), Some(&stopped)).is_none());
        assert!(decimal(&BigInt::from(1), Some(&stopped)).is_none());
    }

    #[test]
    fn scalar_admission_exports_preserve_exact_values_and_original_refusal() {
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(2_000_000, 2_000_000),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let value = (BigInt::from(1) << 199usize) + 3;
        let text = crate::format_bigint_with_admission(&value, &owner).unwrap();
        assert_eq!(BigInt::parse_bytes(text.as_bytes(), 10), Some(value));
        let rational = num_rational::BigRational::new((-3).into(), 2.into());
        assert_eq!(
            crate::format_rational_with_admission(&rational, &owner).unwrap(),
            "(- (/ 3 2))"
        );
        assert_eq!(
            crate::format_bitvec_with_admission(&17.into(), 5, &owner).unwrap(),
            "#b10001"
        );
        let malformed = num_rational::BigRational::new_raw(1.into(), 0.into());
        assert!(crate::format_rational_with_admission(&malformed, &owner).is_err());
        assert!(
            crate::format_bigint_with_admission(&1.into(), &owner).is_err(),
            "same owner must stay refused"
        );
    }
}
