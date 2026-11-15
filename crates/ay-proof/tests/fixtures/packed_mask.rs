// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Sort, Symbol, TermId, TermStore};

fn extract(terms: &mut TermStore, value: TermId, high: u32, low: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("extract", vec![high, low]),
        [value],
        Sort::bitvec(high - low + 1),
    )
}

fn equality(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn concat(terms: &mut TermStore, high: TermId, low: TermId) -> TermId {
    let Sort::BitVec(high_sort) = terms.sort(high) else {
        panic!("high sort")
    };
    let Sort::BitVec(low_sort) = terms.sort(low) else {
        panic!("low sort")
    };
    let width = high_sort.width + low_sort.width;
    terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(width))
}

fn pack(terms: &mut TermStore, bytes: &[TermId]) -> TermId {
    let mut result = bytes[0];
    for &byte in &bytes[1..] {
        result = concat(terms, byte, result);
    }
    result
}

#[derive(Clone, Copy)]
pub(crate) enum Mutation {
    None,
    WrongMaskBit,
    ReversedChoice,
    WrongSourceByte,
}

pub(crate) fn query(mutation: Mutation) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let mask = terms.mk_var("mask_bits", Sort::bitvec(16));
    let true_lo = terms.mk_var("true_lo", Sort::bitvec(64));
    let true_hi = terms.mk_var("true_hi", Sort::bitvec(64));
    let false_lo = terms.mk_var("false_lo", Sort::bitvec(64));
    let false_hi = terms.mk_var("false_hi", Sort::bitvec(64));
    let true_value = concat(&mut terms, true_hi, true_lo);
    let false_value = concat(&mut terms, false_hi, false_lo);
    let one = terms.mk_bitvec(1.into(), 1);
    let zero = terms.mk_bitvec(0.into(), 1);
    let byte_zero = terms.mk_bitvec(0.into(), 8);
    let byte_ones = terms.mk_bitvec(255.into(), 8);
    let mut mask_bytes = Vec::new();
    for bit in 0..16 {
        let selected = extract(&mut terms, mask, bit, bit);
        let condition = equality(&mut terms, selected, one);
        mask_bytes.push(terms.mk_ite_raw(condition, byte_ones, byte_zero));
    }
    let canonical_mask = pack(&mut terms, &mask_bytes);
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    for byte in 0..16 {
        let low = byte * 8;
        let mask_byte = extract(&mut terms, canonical_mask, low + 7, low);
        let true_byte = extract(&mut terms, true_value, low + 7, low);
        let false_byte = extract(&mut terms, false_value, low + 7, low);
        let whole_byte_set = equality(&mut terms, mask_byte, byte_ones);
        expected.push(terms.mk_ite_raw(whole_byte_set, true_byte, false_byte));
        let bit = if byte == 0 && matches!(mutation, Mutation::WrongMaskBit) {
            6
        } else {
            7
        };
        let sign_bit = extract(&mut terms, mask_byte, bit, bit);
        let value = if byte == 0 && matches!(mutation, Mutation::ReversedChoice) {
            zero
        } else {
            one
        };
        let sign_set = equality(&mut terms, sign_bit, value);
        let selected = if byte == 0 && matches!(mutation, Mutation::WrongSourceByte) {
            extract(&mut terms, true_value, 15, 8)
        } else {
            true_byte
        };
        actual.push(terms.mk_ite_raw(sign_set, selected, false_byte));
    }
    let expected = pack(&mut terms, &expected);
    let actual = pack(&mut terms, &actual);
    let same = equality(&mut terms, expected, actual);
    let root = terms.mk_not_raw(same);
    (terms, root)
}
