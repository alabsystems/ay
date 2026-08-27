// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `select_non_root` must be symmetric under negation.
#[test]
fn select_non_root_is_symmetric_under_negation() {
    let mut neg: Vec<BigInt> = vec![BigInt::from(1)];
    for j in 0u32..=6 {
        let two_j = BigInt::from(1i64 << j);
        let f = [&two_j + 1, two_j.clone()];
        let mut out = vec![BigInt::zero(); neg.len() + 1];
        for (i, c) in neg.iter().enumerate() {
            out[i] += c * &f[0];
            out[i + 1] += c * &f[1];
        }
        neg = out;
    }
    let iv_neg = BqInterval::new(bq(-3, 0), bq(-1, 0)).expect("lo < hi");
    let got_neg = select_non_root(&neg, &iv_neg)
        .expect("interior dyadic non-roots exist (-5/2, -11/4, -9/4, ...)");
    assert_ne!(
        poly_sign_at(&neg, &got_neg),
        Some(0),
        "answer must not be a root"
    );
    assert!(
        iv_neg.lo().cmp_bq(&got_neg) == Ordering::Less
            && got_neg.cmp_bq(iv_neg.hi()) == Ordering::Less,
        "answer must be strictly interior"
    );

    let pos: Vec<BigInt> = neg
        .iter()
        .enumerate()
        .map(|(i, c)| if i % 2 == 1 { -c.clone() } else { c.clone() })
        .collect();
    let iv_pos = BqInterval::new(bq(1, 0), bq(3, 0)).expect("lo < hi");
    let got_pos = select_non_root(&pos, &iv_pos).expect("mirror image must also answer");
    assert_ne!(
        poly_sign_at(&pos, &got_pos),
        Some(0),
        "answer must not be a root"
    );
}
