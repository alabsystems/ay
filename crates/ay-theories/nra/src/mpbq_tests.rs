// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::mpbq`] — the dyadic layer.
//!
//! The campaign's standing lesson is that a test named for a behaviour is not
//! evidence the behaviour is checked (`square_free` survived 4,000 fuzz cases
//! and its own unit test). So these tests are written as *identities against an
//! independent representation* — `BigRational`, which reduces by gcd and knows
//! nothing about powers of two — rather than as expected-value assertions on
//! hand-computed answers, and the degenerate inputs the campaign rules name are
//! each given their own negative control.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::mpbq::{
    candidate_at, enclose_rational, poly_eval_at, poly_sign_at, refine_step_bound, refine_to_width,
    refine_until_separated, select_int, select_non_root, select_small, Bq, BqInterval, Refined,
    Separation,
};

fn bq(a: i64, k: u32) -> Bq {
    Bq::new(BigInt::from(a), k)
}

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn zs(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}

// ---------------------------------------------------------------------------
// Canonical form
// ---------------------------------------------------------------------------

#[test]
fn canonical_form_strips_the_common_power_of_two() {
    // 6/4 == 3/2, and the two must be the SAME bits, not merely equal values.
    let a = bq(6, 2);
    let b = bq(3, 1);
    assert_eq!(a, b);
    assert_eq!(a.numerator(), &BigInt::from(3));
    assert_eq!(a.k(), 1);
    // 8/2^3 is the integer 1.
    let c = bq(8, 3);
    assert_eq!(c.k(), 0);
    assert_eq!(c.numerator(), &BigInt::one());
    assert!(c.is_int());
}

#[test]
fn zero_is_canonical_at_every_input_exponent() {
    for k in [0u32, 1, 7, 64, 1000] {
        let z = bq(0, k);
        assert!(z.is_zero());
        assert_eq!(z.k(), 0);
        assert_eq!(z, Bq::zero());
        assert_eq!(z.sign(), 0);
    }
}

#[test]
fn negatives_are_canonical_and_ordered() {
    let a = bq(-6, 2);
    assert_eq!(a.numerator(), &BigInt::from(-3));
    assert_eq!(a.k(), 1);
    assert_eq!(a.sign(), -1);
    assert_eq!(a.abs(), bq(3, 1));
    assert_eq!(a.neg(), bq(3, 1));
    assert_eq!(a.cmp_bq(&Bq::zero()), Ordering::Less);
    assert_eq!(Bq::zero().cmp_bq(&a), Ordering::Greater);
}

#[test]
fn structural_equality_is_numeric_equality() {
    // The soundness claim behind `derive(PartialEq)`. Sweep a grid and check
    // that Bq equality agrees with BigRational equality, case for case.
    let mut checked = 0u32;
    for a1 in -20i64..=20 {
        for k1 in 0u32..5 {
            for a2 in -20i64..=20 {
                for k2 in 0u32..5 {
                    let x = bq(a1, k1);
                    let y = bq(a2, k2);
                    assert_eq!(
                        x == y,
                        x.to_rational() == y.to_rational(),
                        "{a1}/2^{k1} vs {a2}/2^{k2}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 41 * 5 * 41 * 5);
}

// ---------------------------------------------------------------------------
// Arithmetic against the independent BigRational representation
// ---------------------------------------------------------------------------

#[test]
fn add_sub_mul_match_bigrational_exactly() {
    for a1 in -9i64..=9 {
        for k1 in 0u32..4 {
            for a2 in -9i64..=9 {
                for k2 in 0u32..4 {
                    let x = bq(a1, k1);
                    let y = bq(a2, k2);
                    let (rx, ry) = (x.to_rational(), y.to_rational());
                    assert_eq!(x.add(&y).to_rational(), &rx + &ry);
                    assert_eq!(x.sub(&y).to_rational(), &rx - &ry);
                    assert_eq!(x.mul(&y).unwrap().to_rational(), &rx * &ry);
                    assert_eq!(
                        x.cmp_bq(&y),
                        rx.cmp(&ry),
                        "ordering {a1}/2^{k1} vs {a2}/2^{k2}"
                    );
                }
            }
        }
    }
}

#[test]
fn k_zero_is_ordinary_integer_arithmetic() {
    let a = bq(7, 0);
    let b = bq(-3, 0);
    assert!(a.is_int() && b.is_int());
    assert_eq!(a.add(&b), bq(4, 0));
    assert_eq!(a.sub(&b), bq(10, 0));
    assert_eq!(a.mul(&b).unwrap(), bq(-21, 0));
    assert_eq!(a.floor(), BigInt::from(7));
    assert_eq!(a.ceil(), BigInt::from(7));
}

#[test]
fn shifts_by_powers_of_two_are_exact_and_move_only_k() {
    let x = bq(3, 1); // 3/2
    assert_eq!(x.mul_two_pow(1), bq(3, 0));
    assert_eq!(x.mul_two_pow(4), bq(24, 0));
    assert_eq!(x.div_two_pow(3).unwrap(), bq(3, 4));
    // The invariant that makes bisection cheap: dividing by 2^e raises k by at
    // most e, and multiplying by 2^e lowers it by at most e.
    for a in [-13i64, -1, 0, 1, 5, 1024] {
        for k in 0u32..6 {
            let v = bq(a, k);
            for e in 0u32..6 {
                let up = v.mul_two_pow(e);
                let down = v.div_two_pow(e).unwrap();
                assert!(up.k() <= v.k());
                assert!(down.k() <= v.k() + e);
                let two_e = BigRational::from(BigInt::one() << e);
                assert_eq!(up.to_rational(), v.to_rational() * &two_e);
                assert_eq!(down.to_rational(), v.to_rational() / &two_e);
            }
        }
    }
}

#[test]
fn floor_and_ceil_are_exact_on_negatives() {
    // The place a truncating shift would be wrong.
    assert_eq!(bq(-7, 1).floor(), BigInt::from(-4)); // -3.5
    assert_eq!(bq(-7, 1).ceil(), BigInt::from(-3));
    assert_eq!(bq(7, 1).floor(), BigInt::from(3));
    assert_eq!(bq(7, 1).ceil(), BigInt::from(4));
    assert_eq!(bq(-4, 0).floor(), BigInt::from(-4));
    assert_eq!(bq(-4, 0).ceil(), BigInt::from(-4));
}

#[test]
fn floor_at_and_ceil_at_agree_with_scaling_then_rounding() {
    for a in -33i64..=33 {
        for k in 0u32..5 {
            let v = bq(a, k);
            for t in 0u32..7 {
                let scaled = v.to_rational() * BigRational::from(BigInt::one() << t);
                let f = scaled.floor().to_integer();
                let c = scaled.ceil().to_integer();
                assert_eq!(v.floor_at(t), f, "floor_at {a}/2^{k} at {t}");
                assert_eq!(v.ceil_at(t), c, "ceil_at {a}/2^{k} at {t}");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Representability — with a negative control
// ---------------------------------------------------------------------------

#[test]
fn representability_accepts_dyadics_and_rejects_everything_else() {
    // Positive side.
    for (n, d) in [(3i64, 8i64), (-5, 16), (7, 1), (0, 5), (1, 2), (-1, 1024)] {
        let r = rat(n, d);
        assert!(Bq::is_representable(&r), "{n}/{d} should be dyadic");
        assert_eq!(Bq::from_rational(&r).unwrap().to_rational(), r);
    }
    // NEGATIVE CONTROL: without these the predicate could answer `true`
    // unconditionally and every positive assertion above would still pass.
    for (n, d) in [(1i64, 3i64), (2, 6), (5, 12), (-7, 9), (1, 100), (22, 7)] {
        let r = rat(n, d);
        assert!(!Bq::is_representable(&r), "{n}/{d} must NOT be dyadic");
        assert!(Bq::from_rational(&r).is_none());
    }
}

#[test]
fn round_trip_through_bigrational_is_the_identity() {
    for a in -40i64..=40 {
        for k in 0u32..6 {
            let v = bq(a, k);
            assert_eq!(Bq::from_rational(&v.to_rational()).unwrap(), v);
        }
    }
}

// ---------------------------------------------------------------------------
// Intervals — including both degenerate refusals
// ---------------------------------------------------------------------------

#[test]
fn interval_refuses_equal_and_inverted_endpoints() {
    // lo == hi: the open interval is empty.
    assert!(BqInterval::new(bq(3, 1), bq(3, 1)).is_none());
    assert!(BqInterval::new(bq(6, 2), bq(3, 1)).is_none()); // same value, different spelling
    assert!(BqInterval::new(Bq::zero(), Bq::zero()).is_none());
    // lo > hi: not an interval.
    assert!(BqInterval::new(bq(5, 0), bq(1, 0)).is_none());
    assert!(BqInterval::new(bq(-1, 3), bq(-1, 1)).is_none());
    // And a well-formed one survives.
    assert!(BqInterval::new(bq(-1, 1), bq(1, 1)).is_some());
}

#[test]
fn bisection_halves_the_width_exactly_and_costs_one_bit() {
    let mut iv = BqInterval::new(bq(0, 0), bq(1, 0)).unwrap();
    let mut expect_k = 0u32;
    for step in 1..=64u32 {
        let (left, mid, right) = iv.bisect().unwrap();
        assert!(iv.contains_open(&mid));
        assert_eq!(left.hi(), &mid);
        assert_eq!(right.lo(), &mid);
        // Exactly one bit of precision per step, never two.
        expect_k += 1;
        assert_eq!(mid.k(), expect_k, "step {step}");
        assert_eq!(left.width(), right.width());
        assert_eq!(left.width().mul_two_pow(1), iv.width());
        iv = left;
    }
    assert_eq!(iv.width(), Bq::inv_two_pow(64));
}

// ---------------------------------------------------------------------------
// Polynomial evaluation at a dyadic
// ---------------------------------------------------------------------------

#[test]
fn poly_sign_and_value_match_bigrational_evaluation() {
    let ps = [
        zs(&[-2, 0, 1]),
        zs(&[1, -3, 0, 2]),
        zs(&[0]),
        zs(&[5]),
        zs(&[-1, 1]),
    ];
    for p in &ps {
        for a in -12i64..=12 {
            for k in 0u32..5 {
                let x = bq(a, k);
                let xr = x.to_rational();
                let mut acc = BigRational::zero();
                let mut pow = BigRational::one();
                for c in p {
                    acc += BigRational::from(c.clone()) * &pow;
                    pow *= &xr;
                }
                let want = match acc.numer().sign() {
                    num_bigint::Sign::Minus => -1,
                    num_bigint::Sign::NoSign => 0,
                    num_bigint::Sign::Plus => 1,
                };
                assert_eq!(poly_sign_at(p, &x).unwrap(), want);
                assert_eq!(poly_eval_at(p, &x).unwrap().to_rational(), acc);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Refinement
// ---------------------------------------------------------------------------

#[test]
fn refine_narrows_sqrt2_and_the_step_count_is_pinned_by_the_width() {
    let p = zs(&[-2, 0, 1]); // x^2 - 2, root sqrt(2) in (1, 2)
    let iv = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    for tk in 1u32..=40 {
        let target = Bq::inv_two_pow(tk);
        let (out, trace) = refine_to_width(&p, &iv, &target).unwrap();
        let Refined::Narrowed(got) = out else {
            panic!("sqrt(2) is irrational; no midpoint can hit it");
        };
        assert!(got.width().cmp_bq(&target) != Ordering::Greater);
        assert!(trace.steps <= trace.bound);
        // The identity the oracle uses: width_end * 2^steps == width_start.
        assert_eq!(got.width().mul_two_pow(trace.steps), iv.width());
        // `end_max_k` is derived from the answer.
        assert_eq!(trace.end_max_k, got.max_k());
        // The root really is inside.
        assert_eq!(poly_sign_at(&p, got.lo()).unwrap(), -1);
        assert_eq!(poly_sign_at(&p, got.hi()).unwrap(), 1);
    }
}

#[test]
fn refine_reports_an_exact_dyadic_root() {
    // 2x - 3 has the dyadic root 3/2, which the first midpoint of (1, 2) hits.
    let p = zs(&[-3, 2]);
    let iv = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    let (out, trace) = refine_to_width(&p, &iv, &Bq::inv_two_pow(30)).unwrap();
    assert_eq!(out, Refined::Exact(bq(3, 1)));
    assert_eq!(trace.steps, 1);
    assert_eq!(trace.end_max_k, 1);
}

#[test]
fn refine_fails_closed_on_a_broken_bracket() {
    let p = zs(&[-2, 0, 1]);
    // Same sign at both ends: no bracketed root.
    assert!(refine_to_width(
        &p,
        &BqInterval::new(bq(2, 0), bq(3, 0)).unwrap(),
        &Bq::inv_two_pow(4)
    )
    .is_none());
    // Endpoint IS a root: x^2 - 4 on (2, 3).
    let q = zs(&[-4, 0, 1]);
    assert!(refine_to_width(
        &q,
        &BqInterval::new(bq(2, 0), bq(3, 0)).unwrap(),
        &Bq::inv_two_pow(4)
    )
    .is_none());
    // Non-positive target: nothing to converge to.
    let iv = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    assert!(refine_to_width(&p, &iv, &Bq::zero()).is_none());
    assert!(refine_to_width(&p, &iv, &bq(-1, 3)).is_none());
}

#[test]
fn the_step_bound_is_reached_and_never_exceeded() {
    // Directly exercise the derived bound: halving `width` `bound` times must
    // land at or below `target`, and `bound - 1` times must not always do so.
    for wk in 0u32..6 {
        for tk in 0u32..12 {
            let width = Bq::inv_two_pow(wk);
            let target = Bq::inv_two_pow(tk);
            let bound = refine_step_bound(&width, &target).unwrap();
            let after = width.div_two_pow(bound).unwrap();
            assert!(
                after.cmp_bq(&target) != Ordering::Greater,
                "bound {bound} insufficient for 2^-{wk} -> 2^-{tk}"
            );
        }
    }
    // A target wider than the interval needs zero steps.
    assert_eq!(
        refine_step_bound(&Bq::inv_two_pow(4), &bq(1, 0)).unwrap(),
        0
    );
    // Degenerate targets decline.
    assert!(refine_step_bound(&Bq::inv_two_pow(4), &Bq::zero()).is_none());
    assert!(refine_step_bound(&Bq::zero(), &bq(1, 0)).is_none());
}

#[test]
fn separation_orders_two_distinct_roots_and_declines_on_equal_ones() {
    // sqrt(2) in (1,2) and sqrt(3) in (1,2): distinct, so they separate.
    let p = zs(&[-2, 0, 1]);
    let q = zs(&[-3, 0, 1]);
    let a = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    let b = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    let (sep, ia, ib, rounds) = refine_until_separated(&p, &a, &q, &b, 64).unwrap();
    assert_eq!(sep, Separation::Ordered(Ordering::Less));
    assert!(ia.disjoint(&ib));
    assert!(rounds > 0);
    // NEGATIVE CONTROL: the same root against itself can never separate, and
    // the loop must DECLINE rather than spin.
    let (sep2, _, _, r2) = refine_until_separated(&p, &a, &p, &a, 200).unwrap();
    assert_eq!(sep2, Separation::Inconclusive);
    assert_eq!(r2, 200);
}

// ---------------------------------------------------------------------------
// select_small / select_int
// ---------------------------------------------------------------------------

#[test]
fn select_small_is_minimal_with_the_negative_half_of_the_certificate() {
    // Sweep every interval on a fine grid and check BOTH halves: the answer is
    // inside at exponent k, and NO dyadic of exponent k-1 is inside.
    let mut cases = 0u32;
    for lo_a in -24i64..24 {
        for hi_a in (lo_a + 1)..=24 {
            for k in 0u32..5 {
                let Some(iv) = BqInterval::new(bq(lo_a, k), bq(hi_a, k)) else {
                    continue;
                };
                let sel = select_small(&iv).unwrap();
                assert!(iv.contains_open(&sel.value));
                assert!(sel.value.k() <= sel.k_ceiling);
                assert_eq!(sel.k_ceiling, iv.width().k() + 1);
                if sel.value.k() > 0 {
                    assert!(
                        candidate_at(&iv, sel.value.k() - 1).is_none(),
                        "not minimal: ({lo_a}, {hi_a})/2^{k} answered k={}",
                        sel.value.k()
                    );
                }
                cases += 1;
            }
        }
    }
    assert!(cases > 4000, "grid too small to be evidence: {cases}");
}

#[test]
fn select_small_prefers_an_integer_and_prefers_zero() {
    // (-1, 1): 0 is inside, and 0 is the simplest thing there is.
    let iv = BqInterval::new(bq(-1, 0), bq(1, 0)).unwrap();
    assert_eq!(select_small(&iv).unwrap().value, Bq::zero());
    // (7/8, 9/8): the only integer inside is 1.
    let iv = BqInterval::new(bq(7, 3), bq(9, 3)).unwrap();
    assert_eq!(select_small(&iv).unwrap().value, bq(1, 0));
    // (1/4, 1/2): no integer inside; the simplest dyadic is 3/8.
    let iv = BqInterval::new(bq(1, 2), bq(1, 1)).unwrap();
    let s = select_small(&iv).unwrap();
    assert_eq!(s.value, bq(3, 3));
    assert!(candidate_at(&iv, 2).is_none());
}

#[test]
fn select_int_agrees_with_the_scaled_candidate_at_exponent_zero() {
    // Two independent code paths inside the module — `floor()`/`ceil()` versus
    // `floor_at(0)`/`ceil_at(0)` — must give the same answer everywhere.
    for lo_a in -30i64..30 {
        for hi_a in (lo_a + 1)..=30 {
            for k in 0u32..4 {
                let Some(iv) = BqInterval::new(bq(lo_a, k), bq(hi_a, k)) else {
                    continue;
                };
                assert_eq!(select_int(iv.lo(), iv.hi()), candidate_at(&iv, 0));
            }
        }
    }
    // No integer strictly inside (1/4, 1/2).
    assert_eq!(select_int(&bq(1, 2), &bq(1, 1)), None);
    // Degenerate: empty and inverted.
    assert_eq!(select_int(&bq(1, 0), &bq(1, 0)), None);
    assert_eq!(select_int(&bq(5, 0), &bq(1, 0)), None);
}

/// MEASURED, and it corrects a claim that is easy to make and is wrong.
///
/// `select_small` is **not** a way to make a tight interval cheap. Pure
/// bisection produces intervals whose endpoints are *consecutive* on the
/// `2^-n` grid; between two consecutive grid points there is no dyadic at all
/// below exponent `n+1`, and exactly one at `n+1` — the midpoint. So during a
/// straight bisection refinement `select_small` returns **precisely the
/// midpoint**, measured here at `k = 121` after 120 bisections of `(1, 2)`
/// around `sqrt(2)`. It costs nothing and saves nothing.
///
/// Where the rule actually pays is the case a CAD run hits constantly — a cell
/// whose endpoints were driven to high precision by *some other* coordinate but
/// which still straddles something simple. There the midpoint inherits the
/// endpoints' precision (`k = 201` below) and `select_small` returns `1`.
#[test]
fn select_small_never_loses_to_the_midpoint_and_wins_where_it_can() {
    let p = zs(&[-2, 0, 1]);
    let mut iv = BqInterval::new(bq(1, 0), bq(2, 0)).unwrap();
    for _ in 0..120 {
        let (out, _) = refine_to_width(&p, &iv, &iv.width().div_two_pow(1).unwrap()).unwrap();
        let Refined::Narrowed(next) = out else {
            panic!("sqrt(2) is irrational")
        };
        iv = next;
    }
    let mid = iv.midpoint().unwrap();
    let sel = select_small(&iv).unwrap();
    assert_eq!(iv.max_k(), 120);
    assert_eq!(mid.k(), 121);
    // On a bisection-produced interval the simplest interior dyadic IS the
    // midpoint. Never worse; here, exactly equal.
    assert!(sel.value.k() <= mid.k());
    assert_eq!(sel.value, mid);
    assert_eq!(sel.value.k(), 121);
    assert_eq!(sel.value.k(), iv.width().k() + 1);

    // The case the rule is FOR: high-precision endpoints, a simple point inside.
    // (1 - 2^-200, 1 + 2^-100) straddles the integer 1.
    let lo = Bq::one().sub(&Bq::inv_two_pow(200));
    let hi = Bq::one().add(&Bq::inv_two_pow(100));
    let wide = BqInterval::new(lo, hi).unwrap();
    assert_eq!(wide.max_k(), 200);
    assert_eq!(wide.midpoint().unwrap().k(), 201);
    let sel = select_small(&wide).unwrap();
    assert_eq!(sel.value, Bq::one());
    assert_eq!(sel.value.k(), 0);
}

#[test]
fn select_non_root_avoids_roots_and_declines_on_the_zero_polynomial() {
    // x(x - 1/2)(x - 1)... use integer roots the candidates will actually hit:
    // p = x(2x - 1)(x - 1) has roots 0, 1/2, 1.
    let p = zs(&[0, 1, -3, 2]);
    let iv = BqInterval::new(bq(-1, 0), bq(2, 0)).unwrap();
    let v = select_non_root(&p, &iv).unwrap();
    assert!(iv.contains_open(&v));
    assert_ne!(poly_sign_at(&p, &v).unwrap(), 0);
    // The zero polynomial has no non-roots: decline, do not spin.
    assert!(select_non_root(&zs(&[0, 0, 0]), &iv).is_none());
    assert!(select_non_root(&[], &iv).is_none());
}

// ---------------------------------------------------------------------------
// The BigRational bridge
// ---------------------------------------------------------------------------

#[test]
fn enclose_rational_never_narrows_and_lands_on_the_grid() {
    for (ln, ld, hn, hd) in [(1i64, 3i64, 1i64, 2i64), (-7, 9, 22, 7), (0, 1, 1, 1000)] {
        let lo = rat(ln, ld);
        let hi = rat(hn, hd);
        for k in 0u32..12 {
            let iv = enclose_rational(&lo, &hi, k).unwrap();
            assert!(iv.lo().to_rational() <= lo, "k={k} lower bound narrowed");
            assert!(iv.hi().to_rational() >= hi, "k={k} upper bound narrowed");
            assert!(iv.lo().k() <= k && iv.hi().k() <= k);
        }
    }
    // Degenerate inputs decline.
    assert!(enclose_rational(&rat(1, 2), &rat(1, 2), 4).is_none());
    assert!(enclose_rational(&rat(3, 2), &rat(1, 2), 4).is_none());
}

/// `refine_step_bound` must be SUFFICIENT: after that many bisections the
/// width really is within target.
///
/// This pins the `lb <= rb` clamp. When the two scaled bit-lengths are equal
/// the correct bound is 1 — `L` can exceed `R` by up to a factor of two — and
/// the clamp returned 0. A verifier measured 210 of 3,779 natural
/// `(width, target)` pairs receiving an insufficient bound, and the case below
/// DECLINED outright: the loop ran `0..=0`, failed its single width test and
/// fell through to the fail-closed `None` on a genuine isolating interval with
/// a legitimate target.
///
/// The oracle could not see any of it. Its generator draws
/// `target = width / 2^target_k` with `target_k >= 1`, so `target` is always an
/// exact power-of-two fraction of the width and the equal-bit-length branch is
/// structurally unreachable from the corpus.
#[test]
fn the_refine_step_bound_is_sufficient_including_at_equal_bit_lengths() {
    // The exact case a verifier found declining: x^2 - 2 on (1/2, 2), target 1.
    let p = [BigInt::from(-2), BigInt::zero(), BigInt::from(1)];
    let iv = BqInterval::new(bq(1, 1), bq(2, 0)).expect("lo < hi");
    let target = bq(1, 0);
    let (out, _) =
        refine_to_width(&p, &iv, &target).expect("must not decline: width 3/2 > target 1");
    if let Refined::Narrowed(got) = &out {
        assert!(
            got.width().cmp_bq(&target) != Ordering::Greater,
            "refined width must be within target"
        );
    }

    // And the bound itself must be sufficient across a sweep that INCLUDES
    // equal bit-lengths, which the oracle's corpus cannot reach.
    for wa in 1i64..=40 {
        for wk in 0u32..=5 {
            for ta in 1i64..=40 {
                for tk in 0u32..=5 {
                    let (w, t) = (bq(wa, wk), bq(ta, tk));
                    if w.cmp_bq(&t) != Ordering::Greater {
                        continue;
                    }
                    let n = refine_step_bound(&w, &t).expect("positive inputs");
                    // width / 2^n <= target must actually hold.
                    let shrunk = w.div_two_pow(n).expect("finite");
                    assert!(
                        shrunk.cmp_bq(&t) != Ordering::Greater,
                        "bound {n} insufficient for width {wa}/2^{wk} target {ta}/2^{tk}"
                    );
                }
            }
        }
    }
}

/// `select_non_root` must be SYMMETRIC under negation.
///
/// It used to start at `closest_to_zero` and step only upward. On a positive
/// interval that start is the smallest interior integer, so the walk had room;
/// on a WHOLLY NEGATIVE one it is the largest, so the first step left the
/// interval and the scan made a SINGLE probe per level instead of the `deg + 1`
/// its own completeness argument requires.
///
/// The polynomial below has its roots exactly at the points probed on
/// `(-3, -1)`, so the truncated walk returned `None` while `-5/2`, `-11/4`,
/// `-10/4`, `-9/4` and `-7/4` were all available. The oracle could not see it:
/// its generator's polynomial is always a degree-3 `(x^2 - d)(x - r)`, which
/// has far fewer roots than the scan has probe levels, so the single-probe path
/// never ran out.
#[test]
fn select_non_root_is_symmetric_under_negation() {
    // prod_j (x + 1 + 2^-j) for j = 0..=6 — roots at -1 - 2^-j, i.e. exactly
    // the dyadic points the scan probes on (-3, -1).
    let mut neg: Vec<BigInt> = vec![BigInt::from(1)];
    for j in 0u32..=6 {
        // factor (x + 1 + 2^-j), scaled by 2^j to stay integral: (2^j x + 2^j + 1)
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

    // The mirrored polynomial on the mirrored interval must also answer. Before
    // the fix this side succeeded while the negative side declined, and that
    // asymmetry is the whole finding.
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
