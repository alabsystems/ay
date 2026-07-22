// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::FromPrimitive;

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn test_tangent_plane() {
    // At point (2, 3), tangent plane is T(x,y) = 2*y + 3*x - 6
    let a = rat(2);
    let b = rat(3);

    // At the point itself: T(2,3) = 2*3 + 3*2 - 6 = 6 + 6 - 6 = 6 = 2*3
    assert_eq!(tangent_plane(&a, &b, &a, &b), rat(6));

    // At (3, 3): T = 2*3 + 3*3 - 6 = 6 + 9 - 6 = 9
    // Actual: 3*3 = 9, so tangent is exact on this line
    assert_eq!(tangent_plane(&a, &b, &rat(3), &rat(3)), rat(9));

    // At (1, 1): T = 2*1 + 3*1 - 6 = 2 + 3 - 6 = -1
    // Actual: 1*1 = 1 > -1, so tangent underestimates here
    assert_eq!(tangent_plane(&a, &b, &rat(1), &rat(1)), rat(-1));
}

#[test]
fn test_is_underestimate() {
    let a = rat(2);
    let b = rat(3);

    // First quadrant from (2,3): both dx, dy positive -> underestimate
    assert!(is_underestimate(&a, &b, &rat(3), &rat(4)));

    // Third quadrant from (2,3): both dx, dy negative -> underestimate
    assert!(is_underestimate(&a, &b, &rat(1), &rat(2)));

    // Second quadrant: dx < 0, dy > 0 -> overestimate
    assert!(!is_underestimate(&a, &b, &rat(1), &rat(4)));

    // Fourth quadrant: dx > 0, dy < 0 -> overestimate
    assert!(!is_underestimate(&a, &b, &rat(3), &rat(2)));
}

/// Regression test: tangent plane at the origin is degenerate (zero plane).
/// Z3-style offset tangent points avoid this by using (a+/-delta, b+/-delta).
/// Reference: Z3 nla_tangent_lemmas.cpp `get_initial_points()`.
#[test]
fn test_tangent_at_origin_is_degenerate() {
    let zero = rat(0);
    // Tangent plane at (0,0) evaluated at ANY point (x,y) gives T=0.
    // This is the degenerate zero-plane: T(x,y) = 0*y + 0*x - 0*0 = 0.
    assert_eq!(tangent_plane(&zero, &zero, &rat(5), &rat(5)), rat(0));
    assert_eq!(tangent_plane(&zero, &zero, &rat(-3), &rat(7)), rat(0));
}

/// Verify that offset tangent points produce non-degenerate planes.
/// At (1,1): T(x,y) = 1*y + 1*x - 1 = x + y - 1.
/// At (-1,-1): T(x,y) = -1*y + -1*x - 1 = -x - y - 1.
/// Both are non-trivial linear constraints.
#[test]
fn test_offset_tangent_from_origin_non_degenerate() {
    let one = rat(1);
    let neg_one = rat(-1);

    // Offset point (1, 1): T(x,y) = 1*y + 1*x - 1
    // At (3,3): T = 3 + 3 - 1 = 5 (actual: 9, so underestimate)
    let t_at_33 = tangent_plane(&one, &one, &rat(3), &rat(3));
    assert_eq!(t_at_33, rat(5));
    // Non-degenerate: T != 0 for non-origin points
    assert_ne!(t_at_33, rat(0));

    // Offset point (-1, -1): T(x,y) = -1*y + -1*x - 1
    // At (3,3): T = -3 + -3 - 1 = -7
    let t_at_33_neg = tangent_plane(&neg_one, &neg_one, &rat(3), &rat(3));
    assert_eq!(t_at_33_neg, rat(-7));
    assert_ne!(t_at_33_neg, rat(0));
}

/// Tangent plane at (1,1): T(x,y) = x + y - 1. Always underestimates
/// x*y since x*y - (x+y-1) = (x-1)(y-1) >= 0 in the first quadrant.
#[test]
fn test_tangent_plane_underestimate_property() {
    let one = rat(1);
    // Evaluate at several points and verify T(x,y) <= x*y
    for xi in 0..=5 {
        for yi in 0..=5 {
            let x = rat(xi);
            let y = rat(yi);
            let tangent_val = tangent_plane(&one, &one, &x, &y);
            let actual_val = &x * &y;
            // In first quadrant from (1,1), tangent underestimates
            if xi >= 1 && yi >= 1 {
                assert!(
                    tangent_val <= actual_val,
                    "tangent should underestimate in first quadrant: T({xi},{yi})={tangent_val} vs {actual_val}"
                );
            }
        }
    }
}

/// is_underestimate at the tangent point itself: displacement is zero.
/// The function should handle zero displacement gracefully.
#[test]
fn test_is_underestimate_at_tangent_point() {
    let a = rat(3);
    let b = rat(4);
    // At the tangent point (3,4): dx=0, dy=0, signum product is 0
    // (not positive), so is_underestimate returns false.
    let result = is_underestimate(&a, &b, &a, &b);
    assert!(!result, "at the tangent point, displacement is zero");
}

/// Tangent plane with negative model point: T(-2,-3) at (-2,-3) = (-2)(-3) = 6.
#[test]
fn test_tangent_plane_negative_model_point() {
    let a = rat(-2);
    let b = rat(-3);
    // T(x,y) at (a,b) should equal a*b = 6
    assert_eq!(tangent_plane(&a, &b, &a, &b), rat(6));
    // T at (0,0) = -2*0 + -3*0 - (-2)(-3) = -6
    assert_eq!(tangent_plane(&a, &b, &rat(0), &rat(0)), rat(-6));
}

/// Mixed sign model point: tangent at (2, -3).
/// T(x,y) = 2*y + (-3)*x - 2*(-3) = 2y - 3x + 6
#[test]
fn test_tangent_plane_mixed_signs() {
    let a = rat(2);
    let b = rat(-3);
    // At (2,-3): T = 2*(-3) + (-3)*2 - 2*(-3) = -6 - 6 + 6 = -6
    assert_eq!(tangent_plane(&a, &b, &a, &b), rat(-6));
    // At (0,0): T = 2*0 + (-3)*0 - 2*(-3) = 6
    assert_eq!(tangent_plane(&a, &b, &rat(0), &rat(0)), rat(6));
}

/// is_underestimate with large values should work correctly.
#[test]
fn test_is_underestimate_large_values() {
    let a = rat(1000);
    let b = rat(1000);
    // Same quadrant displacement
    assert!(is_underestimate(&a, &b, &rat(1001), &rat(1001)));
    // Opposite quadrant displacement
    assert!(!is_underestimate(&a, &b, &rat(999), &rat(1001)));
}
