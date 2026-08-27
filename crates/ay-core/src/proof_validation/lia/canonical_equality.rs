// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `lia.rs` so the canonical equality helper remains in
// the validator's private namespace.

fn canonical_int_equality(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    num_bigint::BigInt,
)> {
    use num_traits::Signed;
    let (coeffs, c0) = int_linear_diff(terms, lhs, rhs)?;
    let flip = coeffs
        .values()
        .next()
        .is_some_and(num_bigint::BigInt::is_negative);
    if flip {
        Some((coeffs.into_iter().map(|(v, c)| (v, -c)).collect(), c0))
    } else {
        Some((coeffs, -c0))
    }
}
