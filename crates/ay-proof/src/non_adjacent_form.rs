// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The non-adjacent form of a multiplier, shared by the printer's
//! `complete_blast/constant_product.rs` (a product re-spelled through
//! `poly_simp`) and the strict checker's `bv_bitblast/constant_product.rs` (a
//! product lowered as the same signed sum of shifts).

/// The non-adjacent form of `value` modulo `2^width`, most significant digit
/// first: `(power, negative)`, no two powers adjacent (Reitwiesner:
/// `d_i = b_i + c_i - 2·c_{i+1}`, `c_{i+1} = ⌊(b_i + b_{i+1} + c_i) / 2⌋`).
/// The carry out of the top bit is `2^width ≡ 0` and is dropped.
pub(crate) fn non_adjacent_form(value: u128, width: u32) -> Vec<(u32, bool)> {
    let bit = |index: u32| -> u8 {
        if index >= width || index >= u128::BITS {
            0
        } else {
            u8::from((value >> index) & 1 == 1)
        }
    };
    let mut digits = Vec::new();
    let mut carry = 0_u8;
    for index in 0..width {
        let (low, high) = (bit(index), bit(index + 1));
        let next = (low + high + carry) / 2;
        let digit = i16::from(low) + i16::from(carry) - 2 * i16::from(next);
        if digit != 0 {
            digits.push((index, digit < 0));
        }
        carry = next;
    }
    digits.reverse();
    digits
}

#[cfg(test)]
mod tests {
    use super::non_adjacent_form;

    fn evaluate(digits: &[(u32, bool)], width: u32) -> u128 {
        let modulus_mask = if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        };
        digits.iter().fold(0_u128, |acc, &(power, negative)| {
            let term = 1_u128 << power;
            if negative {
                acc.wrapping_sub(term)
            } else {
                acc.wrapping_add(term)
            }
        }) & modulus_mask
    }

    /// Every digit string represents its value modulo `2^w`, no two digits
    /// are adjacent, and none reaches the width.
    #[test]
    fn the_digits_are_the_value_modulo_the_width_and_non_adjacent() {
        for width in [4_u32, 8, 16, 64, 128] {
            let samples: Vec<u128> = (0..300_u128)
                .chain([
                    127,
                    (1 << 63) - 1,
                    (1 << 32) + 1,
                    u64::MAX as u128,
                    u128::MAX,
                ])
                .collect();
            for value in samples {
                let masked = if width == 128 {
                    value
                } else {
                    value & ((1_u128 << width) - 1)
                };
                let digits = non_adjacent_form(masked, width);
                assert_eq!(evaluate(&digits, width), masked, "{masked} at {width}");
                for pair in digits.windows(2) {
                    assert!(pair[0].0 > pair[1].0 + 1, "adjacent digits for {masked}");
                }
                assert!(digits.iter().all(|&(power, _)| power < width));
            }
        }
        // `2^64 - 1` at 64 bits is `-1`, and 127 is `128 - 1`.
        assert_eq!(non_adjacent_form(u64::MAX as u128, 64), vec![(0, true)]);
        assert_eq!(non_adjacent_form(127, 64), vec![(7, false), (0, true)]);
    }
}
