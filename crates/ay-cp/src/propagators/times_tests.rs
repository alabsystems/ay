// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn floor_and_ceil_division_round_the_right_way() {
    for n in -30..=30_i128 {
        for d in (-7..=7_i128).filter(|&d| d != 0) {
            let exact = n as f64 / d as f64;
            assert_eq!(floor_div(n, d), exact.floor() as i128, "{n} / {d}");
            assert_eq!(ceil_div(n, d), exact.ceil() as i128, "{n} / {d}");
        }
    }
}

/// Every `q` with `q * d = n` for `n`, `d` in the given intervals lies in
/// the hull; `None` only when both intervals contain 0.
#[test]
fn quotient_hull_contains_every_quotient() {
    for n_lo in -6..=6_i128 {
        for n_hi in n_lo..=6 {
            for d_lo in -4..=4_i128 {
                for d_hi in d_lo..=4 {
                    let hull = quotient_hull((n_lo, n_hi), (d_lo, d_hi));
                    let both_zero = n_lo <= 0 && 0 <= n_hi && d_lo <= 0 && 0 <= d_hi;
                    assert_eq!(hull.is_none(), both_zero);
                    let Some((lo, hi)) = hull else { continue };
                    for q in -40..=40_i128 {
                        let witness = (d_lo..=d_hi).any(|d| (n_lo..=n_hi).contains(&(q * d)));
                        if witness {
                            assert!(
                                lo <= q && q <= hi,
                                "q = {q} for n in [{n_lo}, {n_hi}], d in [{d_lo}, {d_hi}] \
                                 outside [{lo}, {hi}]"
                            );
                        }
                    }
                }
            }
        }
    }
}
