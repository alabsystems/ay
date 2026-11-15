// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::addition_tests::certificate;
use super::*;
use ay_core::TermStore;

fn app(terms: &mut TermStore, op: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], Sort::bitvec(width))
}

#[test]
fn packed_masks_reassemble_all_widths_and_symbolic_sums() {
    for width in [1, 9, 32, 64, 128] {
        let mask = u128::MAX >> (128 - width);
        for selector in [
            0,
            mask,
            0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaau128 & mask,
        ] {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::bitvec(width));
            let y = terms.mk_var("y", Sort::bitvec(width));
            let source = app(&mut terms, "bvadd", x, y, width);
            let selected = terms.mk_bitvec(selector.into(), width);
            let complementary = terms.mk_bitvec((selector ^ mask).into(), width);
            let left = app(&mut terms, "bvand", selected, source, width);
            let right = app(&mut terms, "bvand", source, complementary, width);
            let sum = app(&mut terms, "bvadd", left, right, width);
            let equality = terms.mk_app(Symbol::named("="), [sum, source], Sort::Bool);
            certificate(
                &format!("mask-{width}-{selector}"),
                &terms,
                equality,
                &format!(
                    "(declare-const x (_ BitVec {width}))\n(declare-const y (_ BitVec {width}))"
                ),
            );
        }
    }
}

#[test]
fn packed_literal_shift_stages_match_masked_words() {
    for width in [1, 9, 32, 64, 128] {
        for amount in [0, 1, width / 2, width - 1, width] {
            // A one-bit shift count cannot represent 2; every value here is
            // representable at the exact input width.
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::bitvec(width));
            let count = terms.mk_bitvec(amount.into(), width);
            let high = app(&mut terms, "bvlshr", x, count, width);
            let actual = app(&mut terms, "bvshl", high, count, width);
            let mask = (u128::MAX >> (128 - width))
                .checked_shr(amount)
                .unwrap_or(0)
                .checked_shl(amount)
                .unwrap_or(0);
            let mask = terms.mk_bitvec(mask.into(), width);
            let expected = app(&mut terms, "bvand", x, mask, width);
            let equality = terms.mk_app(Symbol::named("="), [actual, expected], Sort::Bool);
            certificate(
                &format!("shift-mask-{width}-{amount}"),
                &terms,
                equality,
                &format!("(declare-const x (_ BitVec {width}))"),
            );
        }
    }
}

#[test]
fn packed_masks_reject_overlap_missing_bits_bad_children_and_overrides() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let page = terms.mk_bitvec((u64::MAX as u128 ^ 4095).into(), 64);
    let high = app(&mut terms, "bvand", x, page, 64);
    for offset in [4094, 8191] {
        let mask = terms.mk_bitvec(offset.into(), 64);
        let low = app(&mut terms, "bvand", x, mask, 64);
        let actual = app(&mut terms, "bvadd", high, low, 64);
        let equality = terms.mk_app(Symbol::named("="), [actual, x], Sort::Bool);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(7), &[equality])
            .is_none());
    }
    let short = terms.mk_bitvec(0.into(), 32);
    let bad = app(&mut terms, "bvand", x, short, 64);
    let reflexive = terms.mk_app(Symbol::named("="), [bad, bad], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[reflexive])
        .is_none());
    let mask = terms.mk_bitvec(4095.into(), 64);
    let low = app(&mut terms, "bvand", x, mask, 64);
    let actual = app(&mut terms, "bvadd", high, low, 64);
    let equality = terms.mk_app(Symbol::named("="), [actual, x], Sort::Bool);
    let mut overrides = DetHashMap::default();
    overrides.insert(mask, "(_ bv4094 64)".into());
    assert!(AlethePrinter::new_with_overrides(&terms, Some(&overrides))
        .format_bv_packed_identity(ProofId(7), &[equality])
        .is_none());
}
