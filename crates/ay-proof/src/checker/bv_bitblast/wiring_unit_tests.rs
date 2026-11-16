// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};
use num_bigint::BigInt;

fn equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

#[test]
fn literal_unit_ssa_products_are_checked_without_an_expensive_producer_charge() {
    for width in [1, 8, 64, MAX_WIDTH] {
        for swapped in [false, true] {
            let mut terms = TermStore::new();
            let value = terms.mk_var("value", Sort::bitvec(width));
            let unit = terms.mk_bitvec(BigInt::from(1), width);
            let args = if swapped {
                [unit, value]
            } else {
                [value, unit]
            };
            let product = terms.mk_app(Symbol::named("bvmul"), args, Sort::bitvec(width));
            let identity = equality(&mut terms, product, value);
            assert!(holds_by_wiring(&terms, &[identity]));
            assert!(!crate::bv_bitblast_requires_proof_producer(
                &terms,
                &[identity]
            ));
            let negative = terms.mk_not_raw(identity);
            let mut proof = Proof::new();
            let assumed = proof.add_assume(negative, None);
            let theorem =
                proof.add_theory_lemma_with_kind("bv", vec![identity], TheoryLemmaKind::BvBitBlast);
            proof.add_resolution(Vec::new(), identity, theorem, assumed);
            assert!(crate::check_proof_strict(&proof, &terms)
                .unwrap()
                .is_complete());
        }
    }
}

#[test]
fn nonunit_wrong_value_and_private_heads_are_not_unit_wiring() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let unit = terms.mk_bitvec(BigInt::from(1), 64);
    let two = terms.mk_bitvec(BigInt::from(2), 64);
    for (head, args, result) in [
        ("bvmul", vec![x, two], x),
        ("bvmul", vec![x, unit], y),
        ("bvmul!private", vec![x, unit], x),
        ("bvmul", vec![x], x),
    ] {
        let product = terms.mk_app(Symbol::named(head), args, Sort::bitvec(64));
        let forged = equality(&mut terms, product, result);
        assert!(!holds_by_wiring(&terms, &[forged]));
        assert!(crate::bv_bitblast_requires_proof_producer(
            &terms,
            &[forged]
        ));
    }
    let product = terms.mk_app(Symbol::named("bvmul"), [x, two], Sort::bitvec(64));
    let forged = equality(&mut terms, product, x);
    assert!(!crate::recognize_bv_bitblast(&terms, &[forged]));
}

#[test]
fn malformed_widths_literals_and_compound_values_keep_their_old_refusals() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let unit = terms.mk_bitvec(BigInt::from(1), 8);
    let wide_unit = terms.mk_bitvec(BigInt::from(1), 16);
    {
        let factor = wide_unit;
        let product = terms.mk_app(Symbol::named("bvmul"), [x, factor], Sort::bitvec(8));
        let forged = equality(&mut terms, product, x);
        assert!(!holds_by_wiring(&terms, &[forged]));
    }
    let product = terms.mk_app(Symbol::named("bvmul"), [x, unit], Sort::bitvec(8));
    let identity = equality(&mut terms, product, x);
    let mut entries = terms.entries_snapshot();
    entries[unit.index()].0 = TermData::Const(Constant::BitVec {
        value: BigInt::from(257),
        width: 8,
    });
    let malformed = TermStore::from_entries(entries, None, None, 0);
    assert!(!holds_by_wiring(&malformed, &[identity]));
    let compound = terms.mk_app(Symbol::named("bvadd"), [x, x], Sort::bitvec(8));
    let product = terms.mk_app(Symbol::named("bvmul"), [compound, unit], Sort::bitvec(8));
    let identity = equality(&mut terms, product, compound);
    assert!(
        !holds_by_wiring(&terms, &[identity]),
        "only opaque SSA leaves use this extension"
    );
    let too_wide = terms.mk_var("too_wide", Sort::bitvec(MAX_WIDTH + 1));
    let unit = terms.mk_bitvec(BigInt::from(1), MAX_WIDTH + 1);
    let product = terms.mk_app(
        Symbol::named("bvmul"),
        [too_wide, unit],
        Sort::bitvec(MAX_WIDTH + 1),
    );
    let identity = equality(&mut terms, product, too_wide);
    assert!(!holds_by_wiring(&terms, &[identity]));
    let mut exhausted = Wiring {
        budget: MAX_BITS,
        ..Wiring::default()
    };
    assert!(exhausted.bits(&terms, x).is_none());
}
