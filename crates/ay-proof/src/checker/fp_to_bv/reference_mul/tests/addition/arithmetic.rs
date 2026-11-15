// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_rational_regression_checks_every_smallest_format_sum_and_difference() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(2, 2, operation);
        for sx in 0..2 {
            for ex in 0..4 {
                for fx in 0..2 {
                    for sy in 0..2 {
                        for ey in 0..4 {
                            for fy in 0..2 {
                                f.compare(raw(sx, ex, fx), raw(sy, ey, fy));
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn exact_cancellation_and_both_operand_orders_use_rtn_negative_zero_only() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(8, 24, operation);
        for value in [raw(0, 127, 17), raw(0, 1, 0), raw(0, 0, 1), raw(1, 127, 17)] {
            let mut opposite = value;
            if operation == Arithmetic::Add {
                opposite.sign ^= 1;
            }
            for mode in 0..5 {
                let zero = raw(u64::from(mode == 3), 0, 0);
                assert_eq!(f.evaluate(value, opposite, mode), zero);
                assert_eq!(f.evaluate(opposite, value, mode), zero);
            }
        }
    }
}

#[test]
fn all_zero_sign_pairs_follow_effective_subtraction_sign_and_rounding_mode() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation);
        for sx in 0..2 {
            for sy in 0..2 {
                for mode in 0..5 {
                    let effective = sy ^ u64::from(operation == Arithmetic::Sub);
                    let expected = if sx == effective {
                        sx
                    } else {
                        u64::from(mode == 3)
                    };
                    assert_eq!(
                        f.evaluate(raw(sx, 0, 0), raw(sy, 0, 0), mode),
                        raw(expected, 0, 0)
                    );
                }
            }
        }
    }
}

#[test]
fn exact_subnormal_cancellation_and_largest_subnormal_promotion_round_once() {
    for (eb, p) in [(3, 4), (5, 11), (8, 24), (11, 53), (15, 113)] {
        let fraction = (1u128 << (p - 1)) - 1;
        let add = SumFixture::new(eb, p, Arithmetic::Add);
        let sub = SumFixture::new(eb, p, Arithmetic::Sub);
        for sign in 0..2 {
            for mode in 0..5 {
                let normal = raw(sign, 1, 0);
                let largest = raw(sign, 0, fraction);
                let alpha = raw(sign, 0, 1);
                assert_eq!(sub.evaluate(normal, largest, mode), alpha);
                assert_eq!(add.evaluate(largest, alpha, mode), normal);
            }
        }
    }
}

#[test]
fn adjacent_normal_values_preserve_all_deep_cancellation_bits() {
    for (eb, p) in [(5, 11), (8, 24), (11, 53), (15, 113)] {
        let f = SumFixture::new(eb, p, Arithmetic::Sub);
        let bias = (1u64 << (eb - 1)) - 1;
        f.compare(raw(0, bias, 1), raw(0, bias, 0));
        f.compare(raw(0, bias, 0), raw(0, bias, 1));
        f.compare(raw(1, bias, 1), raw(1, bias, 0));
        f.compare(raw(0, 1, 1), raw(0, 1, 0));
    }
}

#[test]
fn one_minus_tiny_uses_fractional_borrow_and_one_plus_tiny_keeps_sticky() {
    for (eb, p) in [(5, 11), (8, 24), (11, 53), (15, 113)] {
        let add = SumFixture::new(eb, p, Arithmetic::Add);
        let sub = SumFixture::new(eb, p, Arithmetic::Sub);
        let bias = (1u64 << (eb - 1)) - 1;
        let one = raw(0, bias, 0);
        let tiny = raw(0, bias - u64::from(p + 2), 0);
        let predecessor = raw(0, bias - 1, (1u128 << (p - 1)) - 1);
        let successor = raw(0, bias, 1);
        for mode in 0..5 {
            assert_eq!(
                sub.evaluate(one, tiny, mode),
                if mode >= 3 { predecessor } else { one }
            );
            assert_eq!(
                add.evaluate(one, tiny, mode),
                if mode == 2 { successor } else { one }
            );
        }
        add.compare(one, tiny);
        sub.compare(one, tiny);
    }
}

#[test]
fn exact_guard_window_and_first_tail_and_huge_gap_are_not_masked() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(8, 24, operation);
        for gap in [3, 4, 27, 126] {
            f.compare(raw(0, 127, 0), raw(0, 127 - gap, 1));
            f.compare(raw(1, 127, 0), raw(1, 127 - gap, 1));
        }
    }
}

#[test]
fn nearest_midpoints_use_even_odd_guard_and_exact_below_above_tail() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation);
        for sign in 0..2 {
            for fraction in 0..2 {
                for tiny in 1..4 {
                    f.compare(raw(sign, 3, fraction), raw(sign, 0, tiny));
                }
            }
        }
    }
}

#[test]
fn maximum_finite_overflow_tie_below_above_and_directed_signs_are_exact() {
    let f = SumFixture::new(3, 4, Arithmetic::Add);
    for sign in 0..2 {
        for value in [raw(sign, 1, 6), raw(sign, 2, 0), raw(sign, 2, 1)] {
            f.compare(raw(sign, 6, 7), value);
        }
    }
}

#[test]
fn logical_nan_infinity_and_effective_subtraction_sign_precede_finite_sum() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation);
        for x in [raw(0, 7, 1), raw(1, 7, 7), raw(0, 7, 0), raw(1, 7, 0)] {
            for y in [
                raw(0, 7, 0),
                raw(1, 7, 0),
                raw(0, 7, 1),
                raw(0, 3, 1),
                raw(1, 0, 0),
            ] {
                f.compare(x, y);
                f.compare(y, x);
            }
        }
    }
}
