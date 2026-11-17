// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn signed_i8_manual_endpoints_select_only_the_complete_expected_fp_word() {
    raw_words::native::original_owner(|budget, end| {
        for (raw, fp32, fp64) in [
            (0, 0, 0),
            (1, 0x3f800000, 0x3ff0000000000000),
            (0x7f, 0x42fe0000, 0x405fc00000000000),
            (0x80, 0xc3000000, 0xc060000000000000),
            (0xff, 0xbf800000, 0xbff0000000000000),
        ] {
            for (width, expected) in [(32, fp32), (64, fp64)] {
                word_case(8, raw, width, Kind::Signed, expected, budget, end);
            }
        }
    });
}

#[test]
fn unsigned_manual_endpoints_and_u64_max_have_exact_whole_words() {
    raw_words::native::original_owner(|budget, end| {
        for (n, raw, fp32, fp64) in [
            (8, 0, 0, 0),
            (8, 1, 0x3f800000, 0x3ff0000000000000),
            (8, 0xff, 0x437f0000, 0x406fe00000000000),
            (64, u64::MAX, 0x5f800000, 0x43f0000000000000),
        ] {
            for (width, expected) in [(32, fp32), (64, fp64)] {
                word_case(n, raw, width, Kind::Unsigned, expected, budget, end);
            }
        }
    });
}

#[test]
fn signed_i64_extremes_and_both_even_ties_round_to_manual_words() {
    raw_words::native::original_owner(|budget, end| {
        for (raw, fp32, fp64) in [
            (i64::MAX as u64, 0x5f000000, 0x43e0000000000000),
            (i64::MIN as u64, 0xdf000000, 0xc3e0000000000000),
        ] {
            for (width, expected) in [(32, fp32), (64, fp64)] {
                word_case(64, raw, width, Kind::Signed, expected, budget, end);
            }
        }
        for (width, base, low, high) in [
            (32, 1u64 << 24, 0x4b800000, 0x4b800002),
            (64, 1u64 << 53, 0x4340000000000000, 0x4340000000000002),
        ] {
            for (value, expected) in [(base + 1, low), (base + 3, high)] {
                word_case(64, value, width, Kind::Signed, expected, budget, end);
                let negative = 0u64.wrapping_sub(value);
                word_case(
                    64,
                    negative,
                    width,
                    Kind::Signed,
                    expected | (1u64 << (width - 1)),
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn unsigned_even_ties_round_to_complete_manual_fp32_and_fp64_words() {
    raw_words::native::original_owner(|budget, end| {
        for (width, base, low, high) in [
            (32, 1u64 << 24, 0x4b800000, 0x4b800002),
            (64, 1u64 << 53, 0x4340000000000000, 0x4340000000000002),
        ] {
            for (raw, expected) in [(base + 1, low), (base + 3, high)] {
                word_case(64, raw, width, Kind::Unsigned, expected, budget, end);
            }
        }
    });
}

#[test]
fn raw_extract_multiple_casts_and_repeated_roots_share_original_input_links() {
    raw_words::native::original_owner(|budget, end| {
        for n in [32, 64] {
            budget.admit(1_048_576, 1_048_576).unwrap();
            let base = Expr::var("numeric_base", crate::Sort::bitvec(n));
            let input = [(
                base.clone(),
                ChcVar::new("numeric_base", ChcSort::BitVec(n)),
                0x1234ff,
                n,
            )];
            let word = base.extract(7, 0);
            let signed = cast(word.clone(), Kind::Signed, 32).eq(fields(0xbf800000, 32));
            let unsigned = cast(word, Kind::Unsigned, 64).eq(fields(0x406fe00000000000, 64));
            let roots = [signed.clone(), unsigned.clone(), signed.clone()];
            solve(&roots, &input, true, budget, end);
            solve(&[signed.not(), unsigned], &input, false, budget, end);
        }
    });
}

#[test]
fn mixed_guard_and_both_unchosen_numeric_branches_are_one_complete_relation() {
    raw_words::native::original_owner(|budget, end| {
        for raw in [0x7fu64, 0xff] {
            budget.admit(1_048_576, 1_048_576).unwrap();
            let word = Expr::var("numeric_guard_word", crate::Sort::bitvec(8));
            let input = [(
                word.clone(),
                ChcVar::new("numeric_guard_word", ChcSort::BitVec(8)),
                raw,
                8,
            )];
            let guard = word.clone().bvult(Expr::bitvec_const(128u8, 8));
            let signed = cast(word.clone(), Kind::Signed, 32);
            let unsigned = cast(word, Kind::Unsigned, 32);
            let selected = Expr::ite(guard.clone(), signed, unsigned);
            let bits = if raw == 0x7f { 0x42fe0000 } else { 0x437f0000 };
            let equal = selected.eq(fields(bits, 32));
            // OR is not strengthened by separately asserting its BV guard.
            let disjunction = guard.or(equal.clone());
            solve(&[equal.clone(), disjunction], &input, true, budget, end);
            solve(&[equal.not()], &input, false, budget, end);
        }
    });
}
