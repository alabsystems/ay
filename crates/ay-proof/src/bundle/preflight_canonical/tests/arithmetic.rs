// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn equal(
    left: &BigRational,
    right: &BigRational,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    rational::equal(left, right, &mut CanonicalMeter::new(progress))
}

#[test]
fn canonical_rational_schoolbook_matches_independent_bigint_cross_products() {
    // Exercise both native limb sizes, carry-heavy rows, signed denominators,
    // different operand lengths, and non-reduced but equal representations.
    for limbs in [1, 2, 3, 7, 16, 33] {
        let numerator = BigInt::from_slice(Sign::Plus, &vec![u32::MAX; limbs]);
        let denominator = BigInt::from_slice(Sign::Plus, &vec![u32::MAX - 1; limbs + 1]);
        let scale = BigInt::from_slice(Sign::Plus, &[u32::MAX, 17, 1]);
        for sign in [BigInt::from(1), BigInt::from(-1)] {
            let left = BigRational::new_raw(numerator.clone(), &denominator * &sign);
            let right = BigRational::new_raw(&numerator * &scale, &denominator * &scale * &sign);
            let different = BigRational::new_raw(right.numer() + 1, right.denom().clone());
            for other in [&right, &different] {
                let expected = left.numer() * other.denom() == other.numer() * left.denom();
                assert_eq!(equal(&left, other, &mut |_, _| true).unwrap(), expected);
            }
        }
    }
}

#[test]
fn canonical_rational_equality_exhausts_small_raw_signed_encodings() {
    let mut values = Vec::new();
    for numerator in -3..=3 {
        for denominator in [-3, -2, -1, 1, 2, 3] {
            values.push(BigRational::new_raw(
                BigInt::from(numerator),
                BigInt::from(denominator),
            ));
        }
    }
    for left in &values {
        for right in &values {
            let expected = left.numer() * right.denom() == right.numer() * left.denom();
            assert_eq!(equal(left, right, &mut |_, _| true).unwrap(), expected);
        }
    }
}

#[test]
fn canonical_rational_raw_fast_path_needs_no_product_allocation() {
    let large = BigInt::from_slice(Sign::Plus, &vec![u32::MAX; 1_024]);
    let left = BigRational::new_raw(large.clone(), &large + 1);
    let same = left.clone();
    assert!(equal(&left, &same, &mut |_, bytes| bytes == 0).unwrap());
    let zero = BigRational::new_raw(BigInt::from(0), large);
    let other_zero = BigRational::new_raw(BigInt::from(0), BigInt::from(-7));
    assert!(equal(&zero, &other_zero, &mut |_, bytes| bytes == 0).unwrap());
}

#[test]
fn canonical_rational_cross_product_refuses_before_scratch_allocation() {
    let left = BigRational::new_raw(BigInt::from(1), BigInt::from(2));
    let right = BigRational::new_raw(BigInt::from(2), BigInt::from(4));
    let mut allocations = 0;
    assert_eq!(
        equal(&left, &right, &mut |_, bytes| {
            allocations += usize::from(bytes != 0);
            bytes == 0
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(allocations, 1);
}

#[test]
fn canonical_rational_cross_product_cells_are_incrementally_cancellable() {
    let numerator = BigInt::from_slice(Sign::Plus, &vec![u32::MAX; 128]);
    let denominator = BigInt::from_slice(Sign::Plus, &vec![u32::MAX - 1; 128]);
    let left = BigRational::new_raw(numerator.clone(), denominator.clone());
    let right = BigRational::new_raw(&numerator * 3, &denominator * 3);
    let mut cells = 0;
    let mut allocated = false;
    assert_eq!(
        equal(&left, &right, &mut |work, bytes| {
            allocated |= bytes != 0;
            if allocated && bytes == 0 {
                cells += work;
            }
            cells <= 100
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(allocated);
    assert_eq!(
        cells, 101,
        "no opaque multiply runs between cancellation polls"
    );
}
