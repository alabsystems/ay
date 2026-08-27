// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `icp::tests` to preserve existing test FQNs.

#[test]
fn integer_kth_roots() {
    assert_eq!(
        integer_kth_root_floor(&BigInt::from(100), 2),
        BigInt::from(10)
    );
    assert_eq!(
        integer_kth_root_floor(&BigInt::from(99), 2),
        BigInt::from(9)
    );
    assert_eq!(
        integer_kth_root_ceil(&BigInt::from(99), 2),
        BigInt::from(10)
    );
    assert_eq!(
        integer_kth_root_floor(&BigInt::from(27), 3),
        BigInt::from(3)
    );
    assert_eq!(
        integer_kth_root_floor(&BigInt::from(26), 3),
        BigInt::from(2)
    );
    assert_eq!(integer_kth_root_ceil(&BigInt::from(28), 3), BigInt::from(4));
    assert_eq!(integer_kth_root_floor(&BigInt::zero(), 5), BigInt::zero());
}

#[test]
fn outward_rounded_roots_bracket() {
    // sqrt(9100): irrational; lower^2 <= 9100 <= upper^2 with strict
    // bracketing (9100 is not a perfect square).
    let u = rat(9100);
    let lo = kth_root_lower(&u, 2);
    let hi = kth_root_upper(&u, 2);
    assert!(&lo * &lo < u);
    assert!(&hi * &hi > u);
    assert!(lo < hi);
    // Exact perfect square stays exact.
    assert_eq!(kth_root_lower(&rat(100), 2), rat(10));
    assert_eq!(kth_root_upper(&rat(100), 2), rat(10));
    // Exact rational square: (3/2)^2 = 9/4.
    assert_eq!(kth_root_upper(&ratfrac(9, 4), 2), ratfrac(3, 2));
}

#[test]
fn simplest_rational_selection() {
    // Simplest in [1/10, 1] is 1 (an integer in range).
    assert_eq!(simplest_rational_between(&ratfrac(1, 10), &rat(1)), rat(1));
    // Simplest in [0.3, 0.4] is 1/3.
    assert_eq!(
        simplest_rational_between(&ratfrac(3, 10), &ratfrac(4, 10)),
        ratfrac(1, 3)
    );
    // Simplest in [5.08, 6.53] is 6.
    assert_eq!(
        simplest_rational_between(&ratfrac(508, 100), &ratfrac(653, 100)),
        rat(6)
    );
    // Zero-containing intervals prefer 0; negative intervals mirror.
    assert_eq!(simplest_rational_between(&rat(-10), &rat(10)), rat(0));
    assert_eq!(
        simplest_rational_between(&ratfrac(-653, 100), &ratfrac(-508, 100)),
        rat(-6)
    );
}

/// A WIDE interval must cost the same as a narrow one.
///
/// Regression for the `k == 0` blow-up: the original implementation
/// materialised every multiple of `2^-k` strictly inside the interval, which
/// is linear in WIDTH, and `k == 0` is taken for every finite interval wider
/// than `want + 1`. Measured on that version: width 1e9 took **347 seconds in
/// a single call** — one DFS node alone over a 300s competition cap.
///
/// It survived review because the only wide case tested was `[-3, 7]` (nine
/// iterations). This asserts the real thing: a 1e9-wide interval returns
/// promptly and still yields `want` in-interval values.
#[test]
fn interval_scale_points_is_flat_in_interval_width() {
    let iv = Interval {
        lo: Endpoint::Finite(rat(10), false),
        hi: Endpoint::Finite(rat(1_000_000_000), false),
    };
    let t0 = std::time::Instant::now();
    let pts = interval_scale_points(&iv, 5);
    let elapsed = t0.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(1),
        "interval_scale_points took {elapsed:?} on a 1e9-wide interval — the \
         O(width) materialisation is back"
    );
    assert!(!pts.is_empty(), "should still produce candidates");
    assert!(pts.len() <= 5, "must not exceed `want`");
    for q in &pts {
        assert!(
            interval_contains(&iv, q),
            "candidate {q} outside the interval"
        );
    }
}

/// [`interval_scale_points`] must produce points that are IN the interval,
/// dyadic, distinct, spread, and bounded in denominator — and must decline
/// rather than guess where there is no scale to work at.
#[test]
fn interval_scale_points_reach_where_the_fixed_alphabet_cannot() {
    let iv = |l: BigRational, h: BigRational| Interval {
        lo: Endpoint::Finite(l, false),
        hi: Endpoint::Finite(h, false),
    };
    // The shape the probe found: a contracted interval near pi/2 that
    // contains NO value of `dyadic_grid(3)` — every one of its 65 values is
    // a multiple of 1/8 with magnitude <= 4, and none lands in this window.
    let narrow = iv(ratfrac(15703, 10000), ratfrac(15709, 10000));
    assert!(
        dyadic_grid(GRID_MAX_LEVEL)
            .iter()
            .all(|g| !interval_contains(&narrow, g)),
        "the fixed alphabet is supposed to miss this interval entirely"
    );
    let pts = interval_scale_points(&narrow, GRID_MIN_BRANCH);
    assert_eq!(pts.len(), GRID_MIN_BRANCH);
    for p in &pts {
        assert!(interval_contains(&narrow, p), "{p} escaped the interval");
        let d = p.denom();
        assert!(
            d == &(BigInt::one() << (d.bits() as usize - 1)),
            "{p} is not dyadic — the denominator bound is the point"
        );
        assert!(p.denom().bits() as usize <= GRID_SCALE_MAX_BITS + 1);
    }
    for i in 1..pts.len() {
        assert!(pts[i - 1] != pts[i], "duplicate candidate {}", pts[i]);
    }
    // Spread, not clustered against the lower endpoint.
    assert!(pts.iter().max() > pts.iter().min());
    // A wide interval: still bounded, still inside, and small denominators.
    let wide = iv(rat(-3), rat(7));
    let w = interval_scale_points(&wide, GRID_MIN_BRANCH);
    assert_eq!(w.len(), GRID_MIN_BRANCH);
    assert!(w.iter().all(|p| interval_contains(&wide, p)));
    // Unbounded on either side: no scale exists, so no points, never a panic.
    assert!(interval_scale_points(
        &Interval {
            lo: Endpoint::Finite(rat(0), false),
            hi: Endpoint::PosInf
        },
        GRID_MIN_BRANCH
    )
    .is_empty());
    assert!(interval_scale_points(&Interval::whole(), GRID_MIN_BRANCH).is_empty());
    // Degenerate and empty requests decline.
    assert!(interval_scale_points(&iv(rat(1), rat(1)), GRID_MIN_BRANCH).is_empty());
    assert!(interval_scale_points(&wide, 0).is_empty());
    // Narrower than the scale cap: declines instead of building a
    // 2^GRID_SCALE_MAX_BITS-denominator candidate nobody can evaluate cheaply.
    let hair = iv(
        BigRational::new(BigInt::one(), BigInt::one() << 80u32),
        BigRational::new(BigInt::from(3), BigInt::one() << 80u32),
    );
    assert!(interval_scale_points(&hair, GRID_MIN_BRANCH).is_empty());
}

#[test]
fn nice_point_in_open_handles_unbounded_sides() {
    // `(0, +inf)` — the meti-tarski Skolem shape. `nice_point_in` gives up.
    let half_open = Interval {
        lo: Endpoint::Finite(rat(0), false),
        hi: Endpoint::PosInf,
    };
    assert_eq!(nice_point_in(&half_open), None);
    assert_eq!(nice_point_in_open(&half_open), Some(rat(1)));
    // `[0, +inf)` — the SOUND relaxation of the same strict bound. The
    // simplest rational IS 0 here, which is why the ladder must offer more.
    let half_closed = Interval {
        lo: Endpoint::Finite(rat(0), true),
        hi: Endpoint::PosInf,
    };
    assert_eq!(nice_point_in_open(&half_closed), Some(rat(0)));
    assert_eq!(pin_candidate(&half_closed, 1), Some(rat(1)));
    assert_eq!(pin_candidate(&half_closed, 2), None); // -1 is outside

    // `(-inf, hi]` mirrors, and the doubly-unbounded interval yields 0.
    let below = Interval {
        lo: Endpoint::NegInf,
        hi: Endpoint::Finite(rat(-5), false),
    };
    assert_eq!(nice_point_in_open(&below), Some(rat(-6)));
    let whole = Interval::whole();
    assert_eq!(nice_point_in_open(&whole), Some(rat(0)));
    // Every proposal lands inside the interval it was asked about.
    for iv in [&half_open, &half_closed, &below, &whole] {
        for k in 0..PIN_VALUE_LADDER {
            if let Some(p) = pin_candidate(iv, k) {
                assert!(interval_contains(iv, &p), "rung {k} escaped its interval");
            }
        }
    }
}

#[test]
fn pin_ladder_is_not_degenerate_on_a_bounded_interval() {
    // The three-rung ladder collapsed to one value on intervals like this;
    // the replacement must offer several DISTINCT candidates.
    let iv = Interval {
        lo: Endpoint::Finite(rat(0), false),
        hi: Endpoint::Finite(ratfrac(151, 50), false),
    };
    let vals: std::collections::BTreeSet<_> = (0..PIN_VALUE_LADDER)
        .filter_map(|k| pin_candidate(&iv, k))
        .collect();
    assert!(vals.len() >= 4, "ladder collapsed to {vals:?}");
    assert!(vals.contains(&rat(1)) && vals.contains(&rat(2)));
    for p in &vals {
        assert!(interval_contains(&iv, p));
    }
}

#[test]
fn invert_interval_positive_and_negative() {
    // 1/[2, 4] = [1/4, 1/2]
    let iv = Interval {
        lo: Endpoint::Finite(rat(2), true),
        hi: Endpoint::Finite(rat(4), true),
    };
    let inv = invert_interval(&iv).expect("invertible");
    assert_eq!(inv.lo, Endpoint::Finite(ratfrac(1, 4), true));
    assert_eq!(inv.hi, Endpoint::Finite(ratfrac(1, 2), true));
    // 1/[-4, -2] = [-1/2, -1/4]
    let iv = Interval {
        lo: Endpoint::Finite(rat(-4), true),
        hi: Endpoint::Finite(rat(-2), true),
    };
    let inv = invert_interval(&iv).expect("invertible");
    assert_eq!(inv.lo, Endpoint::Finite(ratfrac(-1, 2), true));
    assert_eq!(inv.hi, Endpoint::Finite(ratfrac(-1, 4), true));
    // Straddling zero: no sound inverse.
    let iv = Interval {
        lo: Endpoint::Finite(rat(-1), true),
        hi: Endpoint::Finite(rat(1), true),
    };
    assert!(invert_interval(&iv).is_none());
    // 1/[2, +inf) = (0, 1/2]: zero endpoint PROVEN open.
    let iv = Interval {
        lo: Endpoint::Finite(rat(2), true),
        hi: Endpoint::PosInf,
    };
    let inv = invert_interval(&iv).expect("invertible");
    assert_eq!(inv.lo, Endpoint::Finite(rat(0), false));
    assert_eq!(inv.hi, Endpoint::Finite(ratfrac(1, 2), true));
}

#[test]
fn contract_power_even_sign_aware() {
    // x^2 ∈ [100, 100], x ∈ [0, 10]: x contracts to exactly [10, 10].
    let cur = Interval {
        lo: Endpoint::Finite(rat(0), true),
        hi: Endpoint::Finite(rat(10), true),
    };
    let q = Interval::point(rat(100));
    let out = contract_power(&cur, &q, 2).expect("non-empty");
    assert_eq!(interval_point(&out), Some(&rat(10)));
    // x^2 ∈ [100, 100], x ∈ [-4, 4]: PROVEN empty.
    let cur = Interval {
        lo: Endpoint::Finite(rat(-4), true),
        hi: Endpoint::Finite(rat(4), true),
    };
    assert!(contract_power(&cur, &q, 2).is_none());
    // x^2 ∈ [-8, -1]: impossible (even power is non-negative).
    let cur = Interval::whole();
    let q = Interval {
        lo: Endpoint::Finite(rat(-8), true),
        hi: Endpoint::Finite(rat(-1), true),
    };
    assert!(contract_power(&cur, &q, 2).is_none());
    // x^3 ∈ [8, 27]: x ∈ [2, 3] exactly (odd root, perfect cubes).
    let cur = Interval::whole();
    let q = Interval {
        lo: Endpoint::Finite(rat(8), true),
        hi: Endpoint::Finite(rat(27), true),
    };
    let out = contract_power(&cur, &q, 3).expect("non-empty");
    assert_eq!(out.lo, Endpoint::Finite(rat(2), true));
    assert_eq!(out.hi, Endpoint::Finite(rat(3), true));
}

#[test]
fn rational_matrix_inverse() {
    // [[2, 0], [1, -1]]^-1 = [[1/2, 0], [1/2, -1]]
    let a = vec![vec![rat(2), rat(0)], vec![rat(1), rat(-1)]];
    let inv = invert_rational_matrix(&a).expect("nonsingular");
    assert_eq!(inv[0], vec![ratfrac(1, 2), rat(0)]);
    assert_eq!(inv[1], vec![ratfrac(1, 2), rat(-1)]);
    // Singular matrix.
    let s = vec![vec![rat(1), rat(2)], vec![rat(2), rat(4)]];
    assert!(invert_rational_matrix(&s).is_none());
}
