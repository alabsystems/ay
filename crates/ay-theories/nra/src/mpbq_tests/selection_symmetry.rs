// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `select_non_root` must be symmetric under negation.
#[test]
fn select_non_root_is_symmetric_under_negation() -> Result<(), Box<dyn std::error::Error>> {
    let mut neg: Vec<BigInt> = vec![BigInt::from(1)];
    for j in 0u32..=6 {
        let two_j = BigInt::from(1i64.checked_shl(j).ok_or("2^j fits i64")?);
        let (f0, f1) = (&two_j + 1, two_j.clone());
        // The product has one more coefficient than `neg`; seven factors keep
        // it at eight, far inside the fallible reservation.
        let len = neg
            .len()
            .checked_add(1)
            .ok_or("coefficient count fits usize")?;
        let mut out: Vec<BigInt> = Vec::new();
        out.try_reserve_exact(len)?;
        out.push(BigInt::zero());
        for c in &neg {
            if let Some(last) = out.last_mut() {
                *last += c * &f0;
            }
            out.push(c * &f1);
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
    Ok(())
}
