// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exponent8320_and_precision257_use_checked_metadata_not_fixed_carriers() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let wide = SumFixture::new(8320, 4, operation);
        let mut progress = |_, _| true;
        let reference = Reference::build_operation(
            &wide.fixture.terms,
            wide.fixture.source,
            operation,
            &mut progress,
        )
        .expect("word metadata has no invented exponent ceiling");
        assert_eq!(reference.format.product_width, 8);
        assert!(reference.format.exponent_width >= 8324);
        drop(reference);

        let mut exact = SumFixture::new(2, 257, operation);
        let sign = exact.fixture.terms.mk_bitvec(BigInt::zero(), 1);
        let exponent = exact.fixture.terms.mk_bitvec(BigInt::one(), 2);
        let fraction = exact.fixture.terms.mk_bitvec(BigInt::zero(), 256);
        let one = app(
            &mut exact.fixture.terms,
            "fp",
            &[sign, exponent, fraction],
            Sort::FloatingPoint(2, 257),
        );
        exact.fixture.source = app(
            &mut exact.fixture.terms,
            operation.name(),
            &[exact.fixture.rm, one, one],
            Sort::FloatingPoint(2, 257),
        );
        for mode in 0..5 {
            let expected = if operation == Arithmetic::Add {
                raw(0, 2, 0)
            } else {
                raw(u64::from(mode == 3), 0, 0)
            };
            assert_eq!(exact.evaluate(raw(0, 0, 0), raw(0, 0, 0), mode), expected);
        }
        // Fraction0 fits the test Raw; this is NOT a general u128-wide oracle.
    }
}
