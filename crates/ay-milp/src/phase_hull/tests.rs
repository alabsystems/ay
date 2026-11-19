// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_rational::BigRational;

fn q(x: f64) -> BigRational {
    BigRational::from_float(x).unwrap()
}

fn exact(offset: f64, terms: &[(usize, f64)], x: &[f64]) -> BigRational {
    terms
        .iter()
        .fold(q(offset), |v, &(i, a)| v + q(a) * q(x[i]))
}

#[test]
fn excludes_a_triangle_point_and_accepts_the_exact_boundary() {
    // ReLU(x+y) is zero at (1,-1), while its interval triangle permits one.
    let inactive = AffineArm {
        offset: 0.0,
        terms: &[],
    };
    let active = AffineArm {
        offset: 0.0,
        terms: &[(0, 1.0), (1, 1.0)],
    };
    let point = [1.0, -1.0];
    let cut = separate_unit_box_hull(inactive, active, &point, 1.0).unwrap();
    assert!(exact(cut.offset, &cut.terms, &point) < q(1.0));
    assert!(separate_unit_box_hull(inactive, active, &point, 0.0).is_none());
}

#[test]
fn every_emitted_plane_dominates_both_arms_at_all_box_vertices() {
    let points = [[-0.9, 0.2, -1.0, 1.0], [0.3, -0.7, 0.8, -0.1], [1.0; 4]];
    for (l, r) in [(0.1, -0.7), (7.0, -20.0), (-13.0, 9.0), (0.0, 0.0)] {
        let a = AffineArm {
            offset: l,
            terms: &[(0, 0.1), (2, -1.75), (3, 0.5000000000000001)],
        };
        let b = AffineArm {
            offset: r,
            terms: &[(1, -0.45), (2, 3.25), (3, 0.5)],
        };
        for point in points {
            let plane = separate_unit_box_hull(a, b, &point, 100.0).unwrap();
            for bits in 0..16 {
                let corner: Vec<_> = (0..4)
                    .map(|i| if bits & (1 << i) == 0 { -1.0 } else { 1.0 })
                    .collect();
                let upper = exact(plane.offset, &plane.terms, &corner);
                assert!(upper >= exact(a.offset, a.terms, &corner));
                assert!(upper >= exact(b.offset, b.terms, &corner));
            }
        }
    }
}

#[test]
fn rejects_invalid_sparse_inputs_and_nonfinite_proposals() {
    let a = AffineArm {
        offset: 0.0,
        terms: &[],
    };
    for entries in [&[(0, 1.0), (0, 2.0)][..], &[(1, 0.0)], &[(0, f64::NAN)]] {
        let b = AffineArm {
            offset: 0.0,
            terms: entries,
        };
        assert!(separate_unit_box_hull(a, b, &[0.0], 2.0).is_none());
    }
    let b = AffineArm {
        offset: 0.0,
        terms: &[(0, 1.0)],
    };
    assert!(separate_unit_box_hull(a, b, &[1.1], 2.0).is_none());
    assert!(separate_unit_box_hull(a, b, &[0.0], f64::INFINITY).is_none());
}

#[test]
fn tiny_opposite_coefficients_and_huge_offsets_are_safe() {
    let tiny = f64::from_bits(3);
    let a = AffineArm {
        offset: tiny,
        terms: &[(0, -tiny)],
    };
    let b = AffineArm {
        offset: -tiny,
        terms: &[(0, tiny)],
    };
    let plane = separate_unit_box_hull(a, b, &[0.0], 1.0).unwrap();
    for x in [[-1.0], [1.0]] {
        let upper = exact(plane.offset, &plane.terms, &x);
        assert!(upper >= exact(a.offset, a.terms, &x));
        assert!(upper >= exact(b.offset, b.terms, &x));
    }
    let left = AffineArm {
        offset: 0.0,
        terms: &[(0, f64::MAX)],
    };
    let right = AffineArm {
        offset: 0.0,
        terms: &[(0, -f64::MAX)],
    };
    assert!(separate_unit_box_hull(left, right, &[1.0], f64::MAX).is_none());
}

#[test]
fn joint_hull_certifies_two_correlated_phases() {
    let terms: [&[(usize, f64)]; 4] = [
        &[],
        &[(0, 1.0), (1, 1.0)],
        &[(0, 1.0), (1, -1.0)],
        &[(0, 2.0)],
    ];
    let arms = terms.map(|terms| AffineArm { offset: 0.0, terms });
    let cut = separate_four_arm_unit_box_hull(arms, &[0.0, 0.0], 1.25).unwrap();
    assert!(cut.offset < 1.25);
    assert!(separate_four_arm_unit_box_hull(arms, &[0.0, 0.0], 1.0).is_none());
    for x in [-1.0, 1.0] {
        for y in [-1.0, 1.0] {
            let vertex = [x, y];
            for a in arms {
                assert!(
                    exact(cut.offset, &cut.terms, &vertex) >= exact(a.offset, a.terms, &vertex)
                );
            }
        }
    }
}

#[test]
fn all_four_sparse_supports_hold_at_every_corner() {
    let tiny = f64::from_bits(37);
    let arms = [
        AffineArm {
            offset: tiny,
            terms: &[(1, -tiny), (2, 0.9)],
        },
        AffineArm {
            offset: 0.1,
            terms: &[(0, 0.014), (3, 0.7500000000000001)],
        },
        AffineArm {
            offset: -0.7,
            terms: &[(2, -3.0), (4, tiny)],
        },
        AffineArm {
            offset: 0.31,
            terms: &[(0, -1.3), (1, 0.13), (4, 0.97)],
        },
    ];
    for point in [[-0.91, 0.1, -0.8, 0.2, 1.0], [1.0; 5], [-1.0; 5], [0.0; 5]] {
        let cut = separate_four_arm_unit_box_hull(arms, &point, 20.0).unwrap();
        for mask in 0..32 {
            let x: [f64; 5] =
                std::array::from_fn(|j| if mask & (1 << j) == 0 { -1.0 } else { 1.0 });
            for a in arms {
                assert!(exact(cut.offset, &cut.terms, &x) >= exact(a.offset, a.terms, &x));
            }
        }
    }
    let mut bad = arms;
    bad[3].terms = &[(3, 1.0), (3, 2.0)];
    assert!(separate_four_arm_unit_box_hull(bad, &[0.0; 5], 9.0).is_none());
    assert!(separate_four_arm_unit_box_hull(arms, &[-1.1; 5], 9.0).is_none());
}

#[test]
fn unrepresentable_four_arm_support_never_yields_a_cut() {
    let base = AffineArm {
        offset: f64::MAX,
        terms: &[(0, f64::MAX)],
    };
    let other = AffineArm {
        offset: f64::MAX,
        terms: &[(0, -f64::MAX)],
    };
    assert!(
        separate_four_arm_unit_box_hull([base, other, base, other], &[0.0], f64::MAX).is_none()
    );
}

#[test]
fn weighted_knapsack_finds_the_fractional_pivot_on_faces_and_interiors() {
    let n = 257;
    let terms: Vec<_> = (0..n).map(|i| (i, 1.0)).collect();
    let left = AffineArm {
        offset: 0.0,
        terms: &[],
    };
    let right = AffineArm {
        offset: 0.0,
        terms: &terms,
    };
    for on_face in [true, false] {
        let point: Vec<_> = (0..n)
            .map(|i| {
                let j = (i * 29) % n;
                if on_face {
                    [-1.0, -0.0, 0.0, 1.0][j % 4]
                } else {
                    (j as f64 - 128.0) / 128.0
                }
            })
            .collect();
        let mut ranks: Vec<_> = (0..n).collect();
        ranks.sort_by(|&a, &b| point[a].total_cmp(&point[b]).then(a.cmp(&b)));
        let cut = separate_unit_box_hull(left, right, &point, 1024.0).unwrap();
        let mut slopes = vec![0.0; n];
        for (j, slope) in cut.terms {
            slopes[j] = slope;
        }
        for (k, &j) in ranks.iter().enumerate() {
            assert_eq!(
                slopes[j],
                if k < 128 {
                    1.0
                } else if k == 128 {
                    0.5
                } else {
                    0.0
                }
            );
        }
        // Each arm reaches its maximal residual at a different box vertex.
        for arm in [left, right] {
            let support = (0..n).fold(q(arm.offset), |s, j| {
                let a = if arm.terms.is_empty() { 0.0 } else { 1.0 };
                s + q((a - slopes[j]).abs())
            });
            assert!(q(cut.offset) >= support);
        }
    }
}

#[test]
fn screening_handles_cancellation_underflow_and_signed_boundaries() {
    let tiny = f64::from_bits(1);
    // A rounded running sum can exceed the exact sum. Neither a lost unit
    // nor an underflow to signed zero may establish a lower bound.
    let cases: &[(f64, &[f64], &[f64], f64)] = &[
        (1e20, &[-1.0, -1e20], &[1.0, 1.0], 0.0),
        (0.0, &[tiny], &[-0.5], -0.0),
        (0.0, &[-tiny], &[0.5], 0.0),
        (f64::MIN_POSITIVE, &[-tiny], &[0.5], f64::MIN_POSITIVE),
        (-1.0, &[tiny], &[-1.0], -1.0),
        (1.0, &[0.0], &[-0.0], 1.0_f64.next_up()),
        (-1.0, &[-0.0], &[0.0], (-1.0_f64).next_up()),
        (0.0, &[f64::MAX, -f64::MAX], &[1.0, 1.0], tiny),
    ];
    for &(offset, coefficients, point, target) in cases {
        let terms: Vec<_> = coefficients.iter().copied().enumerate().collect();
        assert!(exact(offset, &terms, point) < q(target));
        assert_eq!(
            arm_precludes_cut(
                AffineArm {
                    offset,
                    terms: &terms
                },
                point,
                target
            ),
            Some(false)
        );
    }
    for x in [-1.0, -0.0, 0.0, 1.0] {
        let arm = AffineArm {
            offset: 0.0,
            terms: &[(0, 2.0)],
        };
        assert_eq!(arm_precludes_cut(arm, &[x], 2.0 * x - 0.25), Some(true));
        assert_eq!(
            arm_precludes_cut(arm, &[x], (2.0 * x).next_up()),
            Some(false)
        );
    }
}

#[test]
fn screening_rejects_malformed_arms_even_when_the_offset_looks_sufficient() {
    for terms in [
        &[(0, 1.0), (0, 2.0)][..],
        &[(1, 0.0), (0, 0.0)],
        &[(2, 0.0)],
        &[(0, f64::NEG_INFINITY)],
        &[(0, f64::NAN)],
    ] {
        assert_eq!(
            arm_precludes_cut(AffineArm { offset: 8.0, terms }, &[0.0; 2], 1.0),
            None
        );
    }
    let valid = AffineArm {
        offset: 8.0,
        terms: &[(0, 0.0)],
    };
    for x in [
        f64::NAN,
        f64::INFINITY,
        1.0_f64.next_up(),
        (-1.0_f64).next_down(),
    ] {
        assert_eq!(arm_precludes_cut(valid, &[x], 1.0), None);
    }
    for x in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(
            arm_precludes_cut(
                AffineArm {
                    offset: x,
                    terms: &[]
                },
                &[],
                1.0
            ),
            None
        );
        assert!(separate_unit_box_hull(valid, valid, &[0.0], x).is_none());
    }
}

#[test]
fn every_screened_random_price_is_covered_in_exact_arithmetic() {
    use num_traits::ToPrimitive;
    let mut state = 0xd477_ac16_7b63_b6e9_u64;
    let mut draw = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut screened = 0;
    for trial in 0..128 {
        let n = (draw() % 16) as usize;
        let mut point = Vec::with_capacity(n);
        let mut terms = Vec::with_capacity(n);
        let offset = f64::from_bits(draw() & 0xbfff_ffff_ffff_ffff);
        for j in 0..n {
            let r = draw();
            let mut price = match r % 8 {
                0 => -0.0,
                1 => 1.0,
                2 => f64::from_bits(draw() & 0x000f_ffff_ffff_ffff),
                3 => 1.0_f64.next_down(),
                _ => ((draw() >> 11) as f64) * (1.0 / (1_u64 << 53) as f64),
            };
            if r & 8 != 0 {
                price = -price;
            }
            point.push(price);
            let bits = draw();
            // Use both a moderate common scale (including cancellation) and
            // mixed binary64 exponents, from subnormals up to near overflow.
            let a = if trial % 2 == 0 {
                ((bits >> 11) as f64) * (1.0 / (1_u64 << 53) as f64) - 0.5
            } else {
                f64::from_bits(if bits & 0x7ff0_0000_0000_0000 == 0x7ff0_0000_0000_0000 {
                    bits ^ (1_u64 << 52)
                } else {
                    bits
                })
            };
            terms.push((j, a));
        }
        let rational = exact(offset, &terms, &point);
        let rounded = rational.to_f64().unwrap();
        for target in [
            rounded.next_down(),
            rounded,
            rounded.next_up(),
            0.0,
            -f64::MAX,
            f64::MAX,
        ] {
            if target.is_finite()
                && arm_precludes_cut(
                    AffineArm {
                        offset,
                        terms: &terms,
                    },
                    &point,
                    target,
                ) == Some(true)
            {
                screened += 1;
                assert!(rational >= q(target), "trial {trial}, target {target}");
            }
        }
    }
    assert!(screened >= 100);
}

#[test]
fn long_rows_cover_both_exact_supports_and_strictly_separate_the_point() {
    let mut state = 0x1716_cf69_15ee_ba3c_u64;
    let mut draw = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for trial in 0..32 {
        let n = 64 + trial;
        let mut point = Vec::new();
        let mut left = Vec::new();
        let mut right = Vec::new();
        for index in 0..n {
            let magnitude = match trial % 4 {
                0 => f64::from_bits(1 + draw() % 63),
                1 => f64::MIN_POSITIVE,
                2 => 2.0_f64.powi((draw() % 1801) as i32 - 900),
                _ => 1.0,
            };
            let a = magnitude * (draw() as i64 as f64 / i64::MAX as f64);
            let b = magnitude * (draw() as i64 as f64 / i64::MAX as f64);
            let x = match index % 8 {
                0 => -1.0,
                1 => 1.0,
                2 => -0.0,
                3 => 0.0,
                4 => (-1.0_f64).next_up(),
                5 => 1.0_f64.next_down(),
                6 => f64::from_bits(1),
                _ => draw() as i64 as f64 / i64::MAX as f64,
            };
            point.push(x);
            left.push((index, a));
            right.push((index, b));
        }
        let arm = |offset, terms| AffineArm { offset, terms };
        let tiny = f64::from_bits(1);
        let arms = [arm(tiny, &left[..]), arm(-tiny, &right[..])];
        let plane = separate_unit_box_hull(arms[0], arms[1], &point, f64::MAX).unwrap();
        let mut slopes = vec![0.0; n];
        for &(i, s) in &plane.terms {
            slopes[i] = s;
        }
        for a in arms {
            let support = a.terms.iter().fold(q(a.offset), |sum, &(i, w)| {
                let delta = q(w) - q(slopes[i]);
                sum + if delta < q(0.0) { -delta } else { delta }
            });
            assert!(q(plane.offset) >= support, "trial {trial}");
        }
        assert!(exact(plane.offset, &plane.terms, &point) < q(f64::MAX));
        let threshold = exact(arms[0].offset, arms[0].terms, &point);
        for x in [-0.0, tiny, -tiny] {
            if q(x) <= threshold {
                assert!(separate_unit_box_hull(arms[0], arms[1], &point, x).is_none());
            }
        }
    }
}

#[test]
fn long_rows_decline_unsupported_overflow_and_exact_signed_boundaries() {
    let n = 71;
    let mut terms: Vec<_> = (0..n)
        .map(|i| (i, if i % 2 == 0 { f64::MAX } else { -f64::MAX }))
        .collect();
    let zeros = vec![0.0; n];
    let huge = AffineArm {
        offset: 0.0,
        terms: &terms,
    };
    assert!(separate_unit_box_hull(
        huge,
        AffineArm {
            offset: 0.0,
            terms: &[]
        },
        &zeros,
        f64::MAX
    )
    .is_none());
    for (i, w) in &mut terms {
        *w = if *i % 2 == 0 { 1.0 } else { -1.0 };
    }
    let same = AffineArm {
        offset: -0.0,
        terms: &terms,
    };
    let point: Vec<_> = (0..n)
        .map(|i| if i % 2 == 0 { -0.0 } else { 0.0 })
        .collect();
    for threshold in [-0.0, 0.0, -f64::from_bits(1)] {
        assert!(separate_unit_box_hull(same, same, &point, threshold).is_none());
    }
}

#[test]
fn eliminates_opposite_box_faces_before_separating_an_interior_coordinate() {
    let rows = [
        [(0, -1.), (1, 2.), (2, -2.)],
        [(0, -1.), (1, -1.), (2, -2.)],
        [(0, -2.), (1, -1.), (2, -2.)],
        [(0, 2.), (1, 1.), (2, 0.)],
    ];
    let offsets = [-2., -1., 0., -2.];
    let arms = std::array::from_fn(|i| AffineArm {
        terms: &rows[i],
        offset: offsets[i],
    });
    let point = [1., -1., 0.25];
    // The hull over this edge interpolates the maxima 1 and -1 at its ends.
    // At x2=1/4 it is exactly -1/4. The unreduced search missed even 0.
    let cut = separate_four_arm_unit_box_hull(arms, &point, 0.).unwrap();
    let bound = exact(cut.offset, &cut.terms, &point);
    assert!(bound < q(0.) && bound >= q(-0.25));
    assert!(separate_four_arm_unit_box_hull(arms, &point, -0.25).is_none());
    for mask in 0..8 {
        let x: [f64; 3] = std::array::from_fn(|j| if mask & (1 << j) == 0 { -1. } else { 1. });
        let upper = exact(cut.offset, &cut.terms, &x);
        assert!(arms.iter().all(|a| upper >= exact(a.offset, a.terms, &x)));
    }
}

#[test]
fn a_face_proposal_cannot_hide_a_separation_on_two_remaining_coordinates() {
    let coeffs = [
        [5., -3., -6., -6., 6.],
        [-3., -5., 0., -1., 1.],
        [1., -1., 0., -2., 2.],
        [-5., 4., 6., 5., -4.],
    ];
    let terms = coeffs.map(|row| row.into_iter().enumerate().collect::<Vec<_>>());
    let offsets = [5., -5., 0., -5.];
    let arms = std::array::from_fn(|i| AffineArm {
        terms: &terms[i],
        offset: offsets[i],
    });
    let point = [-1., -1., 1., -0.5, 0.75];
    // The reduced search proposes 8.75, while the full search finds 8.5.
    let cut = separate_four_arm_unit_box_hull(arms, &point, 8.625).unwrap();
    assert!(exact(cut.offset, &cut.terms, &point) < q(8.625));
    for mask in 0..32 {
        let x: [f64; 5] = std::array::from_fn(|j| if mask & (1 << j) == 0 { -1. } else { 1. });
        let upper = exact(cut.offset, &cut.terms, &x);
        assert!(arms.iter().all(|a| upper >= exact(a.offset, a.terms, &x)));
    }
}
