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
