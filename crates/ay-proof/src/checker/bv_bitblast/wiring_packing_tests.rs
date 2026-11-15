// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};
use num_bigint::BigInt;

fn app(terms: &mut TermStore, name: &str, args: &[TermId], width: u32) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::bitvec(width))
}

fn equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

fn packing(terms: &mut TermStore, word: TermId, width: u32, chunk: u32, bad_shift: bool) -> TermId {
    let mut packed = None;
    for low in (0..width).step_by(chunk as usize) {
        let slice = terms.mk_app(
            Symbol::indexed("extract", vec![low + chunk - 1, low]),
            [word],
            Sort::bitvec(chunk),
        );
        let extended = terms.mk_app(
            Symbol::indexed("zero_extend", vec![width - chunk]),
            [slice],
            Sort::bitvec(width),
        );
        let piece = if low == 0 {
            extended
        } else {
            let shift = terms.mk_bitvec(BigInt::from(if bad_shift { low - 1 } else { low }), width);
            app(terms, "bvshl", &[extended, shift], width)
        };
        packed = Some(match packed {
            None => piece,
            Some(previous) => app(terms, "bvor", &[previous, piece], width),
        });
    }
    packed.unwrap()
}

#[test]
fn disjoint_shifted_packing_uses_existing_wiring_and_strict_proof() {
    for (width, chunk) in [(8, 1), (16, 4), (64, 8), (128, 16)] {
        let mut terms = TermStore::new();
        let mut proof = Proof::new();
        for index in 0..12 {
            let word = terms.mk_var(format!("word_{index}"), Sort::bitvec(width));
            let packed = packing(&mut terms, word, width, chunk, false);
            let identity = equality(&mut terms, packed, word);
            assert!(holds_by_wiring(&terms, &[identity]));
            assert!(!crate::bv_bitblast_requires_proof_producer(
                &terms,
                &[identity]
            ));
            let theorem =
                proof.add_theory_lemma_with_kind("bv", vec![identity], TheoryLemmaKind::BvBitBlast);
            if index == 11 {
                let negative = terms.mk_not_raw(identity);
                let assumption = proof.add_assume(negative, None);
                proof.add_resolution(Vec::new(), identity, theorem, assumption);
            }
        }
        assert!(crate::check_proof_strict(&proof, &terms)
            .unwrap()
            .is_complete());
    }
}

#[test]
fn wrong_shift_and_overlapping_distinct_wires_are_not_identities() {
    for width in [8, 64, 128] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let wrong = packing(&mut terms, x, width, 1, true);
        let wrong = equality(&mut terms, wrong, x);
        assert!(!holds_by_wiring(&terms, &[wrong]));
        let overlap = app(&mut terms, "bvor", &[x, y], width);
        let forged = equality(&mut terms, overlap, x);
        assert!(!holds_by_wiring(&terms, &[forged]));
        let same = app(&mut terms, "bvor", &[x, x], width);
        let identity = equality(&mut terms, same, x);
        assert!(holds_by_wiring(&terms, &[identity]));
    }
}

#[test]
fn oversized_literal_shifts_are_zero_but_variable_and_malformed_shifts_are_opaque() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    for amount in [BigInt::from(64), BigInt::from(65), BigInt::from(u64::MAX)] {
        let amount = terms.mk_bitvec(amount, 64);
        let shifted = app(&mut terms, "bvshl", &[x, amount], 64);
        let identity = equality(&mut terms, shifted, zero);
        assert!(holds_by_wiring(&terms, &[identity]));
    }
    let amount = terms.mk_var("amount", Sort::bitvec(64));
    let shifted = app(&mut terms, "bvshl", &[x, amount], 64);
    let forged = equality(&mut terms, shifted, zero);
    assert!(!holds_by_wiring(&terms, &[forged]));
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![64]),
        [shifted],
        Sort::bitvec(128),
    );
    let back = terms.mk_app(
        Symbol::indexed("extract", vec![63, 0]),
        [extended],
        Sort::bitvec(64),
    );
    let identity = equality(&mut terms, back, shifted);
    assert!(
        holds_by_wiring(&terms, &[identity]),
        "unsupported shifts retain opaque routing"
    );
    let wide_amount = terms.mk_bitvec(BigInt::from(0), 128);
    let malformed = app(&mut terms, "bvshl", &[x, wide_amount], 64);
    let forged = equality(&mut terms, malformed, x);
    assert!(!holds_by_wiring(&terms, &[forged]));
}
