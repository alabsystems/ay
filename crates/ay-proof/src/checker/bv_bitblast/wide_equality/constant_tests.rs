// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compare the wide source literal with separately encoded 128-bit chunks.

use super::*;
use num_bigint::{BigInt, Sign};

fn byte_pattern(width: u32) -> Vec<u8> {
    let mut bytes: Vec<u8> = (0..width.div_ceil(8))
        .map(|index| (index as u8).wrapping_mul(37) ^ 0xa5)
        .collect();
    let top = bytes.last_mut().expect("positive test width");
    *top &= ((1u16 << ((width - 1) % 8 + 1)) - 1) as u8;
    *top |= 1 << ((width - 1) % 8);
    bytes
}

fn chunked(terms: &mut TermStore, bytes: &[u8], width: u32) -> TermId {
    let mut result = None;
    let mut covered = 0;
    for chunk in bytes.chunks(16) {
        let mut limb = [0u8; 16];
        limb[..chunk.len()].copy_from_slice(chunk);
        let bits = (width - covered).min(128);
        let high = terms.mk_bitvec(u128::from_le_bytes(limb).into(), bits);
        result = Some(match result {
            None => high,
            Some(low) => terms.mk_app(
                Symbol::named("concat"),
                [high, low],
                Sort::bitvec(covered + bits),
            ),
        });
        covered += bits;
    }
    assert_eq!(covered, width);
    result.expect("positive test width")
}

#[test]
fn nonzero_wide_constants_keep_every_limb_and_reject_changed_high_bits() {
    for width in [129, 191, 257, 511, 1024] {
        let bytes = byte_pattern(width);
        let value = BigInt::from_bytes_le(Sign::Plus, &bytes);
        for changed_bit in [None, Some(0), Some(127), Some(128), Some(width - 1)] {
            let mut terms = TermStore::new();
            let expected = chunked(&mut terms, &bytes, width);
            let actual = changed_bit
                .map_or_else(|| value.clone(), |bit| &value ^ (BigInt::from(1u8) << bit));
            let actual = terms.mk_bitvec(actual, width);
            let equal = terms.mk_app(Symbol::named("="), [actual, expected], Sort::Bool);
            let root = terms.mk_not_raw(equal);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            if changed_bit.is_none() {
                assert!(result.is_ok(), "width {width}: {result:?}");
            } else {
                assert!(
                    matches!(result, Err(BoolBvUnsatAuthenticationError::Satisfiable)),
                    "width {width}, changed {changed_bit:?}: {result:?}"
                );
            }
        }
    }
}
