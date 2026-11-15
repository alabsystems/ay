// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! IEEE nearest-even remainder DATA, not Rust truncating remainder.

use super::*;
use std::time::{Duration, Instant};

mod refusal;
pub(super) mod support;
use support::{rem, roots, with_owner, word};

#[test]
fn binary32_ties_signs_and_fraction_have_unique_manual_words() {
    with_owner(8, |budget| {
        for (x, y, expected) in [
            (0x40a00000, 0x40000000, 0x3f800000), // 5/2: tie q=2 -> +1
            (0x40e00000, 0x40000000, 0xbf800000), // 7/2: tie q=4 -> -1
            (0xc0a00000, 0x40000000, 0xbf800000),
            (0xc0e00000, 0x40000000, 0x3f800000),
            (0x40a00000, 0xc0000000, 0x3f800000),
            (0x3f800000, 0x40400000, 0x3f800000), // 1 rem3 =1, NOT1/3
            (0x3fc00000, 0x3f800000, 0xbf000000), // 1.5 rem1 =-.5
            (0x40200000, 0x3f800000, 0x3f000000), // 2.5 rem1 =+.5
        ] {
            word(32, x, y, expected, budget);
        }
    });
}

#[test]
fn binary64_ties_signs_and_fraction_have_unique_manual_words() {
    with_owner(8, |budget| {
        for (x, y, expected) in [
            (0x4014000000000000, 0x4000000000000000, 0x3ff0000000000000),
            (0x401c000000000000, 0x4000000000000000, 0xbff0000000000000),
            (0xc014000000000000, 0x4000000000000000, 0xbff0000000000000),
            (0xc01c000000000000, 0x4000000000000000, 0x3ff0000000000000),
            (0x4014000000000000, 0xc000000000000000, 0x3ff0000000000000),
            (0x3ff0000000000000, 0x4008000000000000, 0x3ff0000000000000),
            (0x3ff8000000000000, 0x3ff0000000000000, 0xbfe0000000000000),
            (0x4004000000000000, 0x3ff0000000000000, 0x3fe0000000000000),
        ] {
            word(64, x, y, expected, budget);
        }
    });
}

#[test]
fn exact_zero_sign_and_infinite_divisor_preserve_the_dividend() {
    with_owner(12, |budget| {
        for (width, sign, one, two, infinity) in [
            (32, 1u64 << 31, 0x3f800000, 0x40000000, 0x7f800000),
            (
                64,
                1u64 << 63,
                0x3ff0000000000000,
                0x4000000000000000,
                0x7ff0000000000000,
            ),
        ] {
            for (x, y, expected) in [
                (0, one, 0),
                (sign, one, sign),
                (two, one, 0),
                (sign | two, one, sign),
                (one, infinity, one),
                (sign | one, sign | infinity, sign | one),
            ] {
                word(width, x, y, expected, budget);
            }
        }
    });
}

#[test]
fn invalid_arithmetic_is_one_nan_class_not_a_payload_or_ieee_equality() {
    with_owner(12, |budget| {
        for (width, one, infinity, nan) in [
            (32, 0x3f800000u64, 0x7f800000u64, 0x7fc00001u64),
            (
                64,
                0x3ff0000000000000,
                0x7ff0000000000000,
                0x7ff8000000000001,
            ),
        ] {
            for (x, y) in [
                (infinity, one),
                (one, 0),
                (nan, one),
                (one, nan),
                (0, 0),
                (infinity, infinity),
            ] {
                budget.admit(8192, 65_536).unwrap();
                let mut terms = TermStore::new();
                let x = fp_constant(&mut terms, x, width);
                let y = fp_constant(&mut terms, y, width);
                let actual = rem(&mut terms, x, y, width);
                let root = predicate(&mut terms, "fp.isNaN", &[actual]);
                let same = predicate(&mut terms, "fp.eq", &[actual, actual]);
                roots(&terms, &[root, same], &[true, false], budget);
                drop(terms);
                budget.charge(0).unwrap();
            }
        }
    });
}

#[test]
fn subnormal_and_max_exponent_remainders_keep_exact_binary_words() {
    with_owner(10, |budget| {
        for (width, sign, one, maximum, min_normal) in [
            (32, 1u64 << 31, 0x3f800000u64, 0x7f7fffffu64, 0x00800000u64),
            (
                64,
                1u64 << 63,
                0x3ff0000000000000,
                0x7fefffffffffffff,
                0x0010000000000000,
            ),
        ] {
            for (x, y, expected) in [
                (3, 2, sign | 1),
                (5, 2, 1),
                (sign | 3, 2, 1),
                (maximum, one, 0),
                (min_normal, 1, 0),
            ] {
                word(width, x, y, expected, budget);
            }
        }
    });
}

#[test]
fn whole_remainder_keeps_all_original_roots_and_lsb_first_free_input_links() {
    with_owner(1, |budget| {
        let mut terms = TermStore::new();
        let x = terms.mk_var("rem_x", Sort::FloatingPoint(11, 53));
        let y = terms.mk_var("rem_y", Sort::FloatingPoint(11, 53));
        let result = rem(&mut terms, x, y, 64);
        let root = predicate(&mut terms, "fp.isNormal", &[result]);
        let input_root = predicate(&mut terms, "fp.isNormal", &[x]);
        let roots = [root, input_root];
        let targets = [
            ChcVar::new("rem_x", crate::ChcSort::BitVec(64)),
            ChcVar::new("rem_y", crate::ChcSort::BitVec(64)),
        ];
        let inputs = [
            FpInputBinding {
                source: x,
                target: &targets[0],
            },
            FpInputBinding {
                source: y,
                target: &targets[1],
            },
        ];
        let namespace = ChcProblem::new();
        let output = lower_fp_clause(&terms, &roots, &inputs, &namespace, budget).unwrap();
        assert_eq!(output.source_roots(), &roots);
        assert!(std::ptr::eq(output.source_terms(), &terms));
        assert!(std::ptr::eq(output.source_namespace(), &namespace));
        assert_eq!(output.input_bindings().len(), 2);
        let ChcExpr::Op(crate::ChcOp::And, entries) = output.constraint() else {
            panic!()
        };
        for (index, entry) in entries.iter().skip(entries.len() - 128).enumerate() {
            budget.charge(1).unwrap();
            let ChcExpr::Op(crate::ChcOp::Eq, link) = entry.as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::Eq, value) = link[1].as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::BvExtract(hi, lo), word) = value[0].as_ref() else {
                panic!()
            };
            assert_eq!((*hi, *lo), ((index % 64) as u32, (index % 64) as u32));
            assert_eq!(word[0].as_ref(), &ChcExpr::Var(targets[index / 64].clone()));
        }
        drop(output);
        budget.charge(0).unwrap();
    });
}
