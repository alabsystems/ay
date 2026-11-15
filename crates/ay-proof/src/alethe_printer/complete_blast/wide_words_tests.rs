// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete documents for wide arithmetic, including wrong-flag controls.

use super::*;

fn carry_identity(width: u32, subtract: bool, inverted: bool) -> Option<String> {
    let mut f = Fixture::new();
    let a = f.bv("a", 128);
    let b = f.bv("b", 128);
    let op = if subtract { "bvsub" } else { "bvadd" };
    let value = f.op(op, &[a, b], 128);
    let ae = f.indexed("zero_extend", vec![width - 128], a, width);
    let be = f.indexed("zero_extend", vec![width - 128], b, width);
    let exact = f.op(op, &[ae, be], width);
    let flag = if subtract {
        f.predicate("bvult", a, b)
    } else {
        f.predicate("bvult", value, a)
    };
    let flag = if inverted { f.not(flag) } else { flag };
    let one = f.constant(1, 1);
    let zero = f.constant(0, 1);
    let bit = f.terms.mk_ite(flag, one, zero);
    let ext = if subtract {
        "sign_extend"
    } else {
        "zero_extend"
    };
    let prefix = f.indexed(ext, vec![width - 129], bit, width - 128);
    let expected = f.op("concat", &[prefix, value], width);
    let equal = f.equals(exact, expected);
    let assertion = f.not(equal);
    f.refute(assertion)
}

#[test]
fn wide_add_sub_carry_documents_are_complete_and_wrong_flags_decline() {
    for width in [257, 511, 1024] {
        for subtract in [false, true] {
            let document = carry_identity(width, subtract, false)
                .unwrap_or_else(|| panic!("width {width}, subtract {subtract}"));
            assert_complete(&document);
            assert!(document.contains(":rule bitblast_add"));
            assert!(carry_identity(width, subtract, true).is_none());
        }
    }
}

#[test]
fn nonzero_literals_above_u128_have_complete_word_documents() {
    for width in [257, 511, 1024] {
        let mut f = Fixture::new();
        let a = f.bv("a", 128);
        let extended = f.indexed("zero_extend", vec![width - 128], a, width);
        let value = (BigInt::from(0xa5u8) << (width - 8)) | (BigInt::from(1u8) << (width / 2));
        let literal = f.terms.mk_bitvec(value.clone(), width);
        let actual = f.op("bvadd", &[extended, literal], width);
        let high = f.terms.mk_bitvec(value >> 128u32, width - 128);
        let expected = f.op("concat", &[high, a], width);
        let equality = f.equals(actual, expected);
        let assertion = f.not(equality);
        let document = f.refute(assertion).expect("nonzero wide literal document");
        assert_complete(&document);
    }
}

#[test]
fn wide_derived_order_weights_do_not_truncate_at_u128() {
    for width in [129, 257, 1024] {
        for (derived, primitive, swapped, negated) in [
            ("bvugt", "bvult", true, false),
            ("bvuge", "bvult", false, true),
            ("bvule", "bvult", true, true),
            ("bvsgt", "bvslt", true, false),
            ("bvsge", "bvslt", false, true),
            ("bvsle", "bvslt", true, true),
        ] {
            let mut f = Fixture::new();
            let a = f.bv("a", width);
            let b = f.bv("b", width);
            let left = f.predicate(derived, a, b);
            let right = if swapped {
                f.predicate(primitive, b, a)
            } else {
                f.predicate(primitive, a, b)
            };
            let right = if negated { f.not(right) } else { right };
            let equality = f.equals(left, right);
            let assertion = f.not(equality);
            let document = f
                .refute(assertion)
                .unwrap_or_else(|| panic!("{derived}, width {width}"));
            assert_complete(&document);
            let coefficient = (BigInt::from(1u8) << (width - 1)).to_string();
            assert!(document.contains(&coefficient));
            // The opposite Boolean equivalence has real counterexamples.
            let opposite = f.not(right);
            let wrong_equality = f.equals(left, opposite);
            let wrong = f.not(wrong_equality);
            assert!(f.refute(wrong).is_none());
        }
    }
}
