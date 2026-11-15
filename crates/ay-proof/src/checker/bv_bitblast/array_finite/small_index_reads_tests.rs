// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reads through store chains over SMALL index sorts (`<= 8` bits), where the
//! complete-domain scalarization is the first lane but can exceed the
//! proof-producing envelope.
//!
//! Measured on ay 3211f7fc7 (the Trust 450403669e bundle): the read-over-write
//! identity `(= v (select (store ((as const (Array (_ BitVec i) (_ BitVec e)))
//! #b0..0) off v) off))` was refused by `recognize_bv_bitblast` at exactly
//! these index/element widths, so the strict checker could not certify the
//! solver's UNSAT and `ay --strict-proofs` answered `unknown (incomplete
//! self-check-rejected)`. Index widths `>= 9` were accepted, through the
//! sparse store-chain lane that never enumerates the address domain; smaller
//! products were accepted through full-domain scalarization. The same bound
//! refused the two-store ROW2 frame-slot shape external-codegen asks about.
//!
//! The complete-domain attempt still refuses these reads for resources, as
//! `proof_producing_control/tests/store_chain_retry.rs` pins: idx8/elem8
//! overruns the lowering's 4096-node expression bound, and idx7/elem32 lowers
//! but overruns a counted bound of the bit-blast producer. The
//! store-chain retry lives in the strict checker's proof-producing validator
//! (`proof_producing_control::refute_ordinary_clause`), which is what
//! `recognize_bv_bitblast` and strict `BvBitBlast` validation run.

use super::super::*;
use num_bigint::BigInt;

/// `(index width, element width)` pairs the full-domain lane refused.
const REFUSED_WIDTHS: [(u32, u32); 9] = [
    (8, 1),
    (8, 4),
    (8, 8),
    (8, 16),
    (8, 32),
    (8, 64),
    (7, 32),
    (7, 64),
    (6, 64),
];

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

fn equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    app(terms, "=", &[left, right], Sort::Bool)
}

struct Memory {
    terms: TermStore,
    sort: Sort,
    zero_array: TermId,
    index_width: u32,
    value_width: u32,
}

impl Memory {
    fn new(index_width: u32, value_width: u32) -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(index_width), Sort::bitvec(value_width));
        let zero = terms.mk_bitvec(BigInt::from(0_u8), value_width);
        let zero_array = app(&mut terms, "const-array", &[zero], sort.clone());
        Self {
            terms,
            sort,
            zero_array,
            index_width,
            value_width,
        }
    }

    fn index(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::bitvec(self.index_width))
    }

    fn value(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::bitvec(self.value_width))
    }

    fn store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        let sort = self.sort.clone();
        app(&mut self.terms, "store", &[array, index, value], sort)
    }

    fn select(&mut self, array: TermId, index: TermId) -> TermId {
        let sort = Sort::bitvec(self.value_width);
        app(&mut self.terms, "select", &[array, index], sort)
    }
}

#[test]
fn row1_through_a_constant_array_is_recognized_at_every_refused_width() {
    for (index_width, value_width) in REFUSED_WIDTHS {
        let mut memory = Memory::new(index_width, value_width);
        let offset = memory.index("off");
        let value = memory.value("v");
        let stored = memory.store(memory.zero_array, offset, value);
        let read = memory.select(stored, offset);
        let identity = equality(&mut memory.terms, value, read);
        assert!(
            recognize_bv_bitblast(&memory.terms, &[identity]),
            "idx{index_width}/elem{value_width}: read-over-write identity must be recognized"
        );

        // The lane must still decide the clause, not accept any read: a
        // different value is not what the write left at `off`.
        let other = memory.value("w");
        let near_miss = equality(&mut memory.terms, other, read);
        assert!(
            !recognize_bv_bitblast(&memory.terms, &[near_miss]),
            "idx{index_width}/elem{value_width}: an unrelated value must not be recognized"
        );
    }
}

#[test]
fn row2_distinct_frame_slots_are_recognized_on_an_eight_bit_index() {
    // external-codegen FrameLayout "callee-save pair slots don't overlap (8-bit)":
    // (and (not (= a b)) (not (= va (select (store (store C a va) b vb) a))))
    for value_width in [8, 32] {
        let mut memory = Memory::new(8, value_width);
        let (slot_a, slot_b) = (memory.index("slot_a"), memory.index("slot_b"));
        let (value_a, value_b) = (memory.value("val_a"), memory.value("val_b"));
        let first = memory.store(memory.zero_array, slot_a, value_a);
        let second = memory.store(first, slot_b, value_b);
        let read = memory.select(second, slot_a);
        let same_slot = equality(&mut memory.terms, slot_a, slot_b);
        let preserved = equality(&mut memory.terms, value_a, read);
        assert!(
            recognize_bv_bitblast(&memory.terms, &[same_slot, preserved]),
            "elem{value_width}: a distinct later write preserves the first value"
        );
        // Without the distinct-slot guard the later write may land on `a`.
        assert!(
            !recognize_bv_bitblast(&memory.terms, &[preserved]),
            "elem{value_width}: the unguarded read is not an identity"
        );
    }
}

#[test]
fn row2_three_writes_preserve_the_first_value_on_an_eight_bit_index() {
    // external-codegen FrameLayout "triple callee-save slots preserve first value (8-bit)".
    let mut memory = Memory::new(8, 8);
    let (off_a, off_b, off_c) = (
        memory.index("off_a"),
        memory.index("off_b"),
        memory.index("off_c"),
    );
    let (val_a, val_b, val_c) = (
        memory.value("val_a"),
        memory.value("val_b"),
        memory.value("val_c"),
    );
    let first = memory.store(memory.zero_array, off_a, val_a);
    let second = memory.store(first, off_b, val_b);
    let third = memory.store(second, off_c, val_c);
    let read = memory.select(third, off_a);
    let a_is_c = equality(&mut memory.terms, off_a, off_c);
    let a_is_b = equality(&mut memory.terms, off_a, off_b);
    let preserved = equality(&mut memory.terms, val_a, read);
    assert!(recognize_bv_bitblast(
        &memory.terms,
        &[a_is_c, a_is_b, preserved]
    ));
    assert!(!recognize_bv_bitblast(&memory.terms, &[a_is_c, preserved]));
}

#[test]
fn row1_over_an_arbitrary_eight_bit_array_is_recognized() {
    let mut memory = Memory::new(8, 8);
    let base = memory.terms.mk_var("initial_memory", memory.sort.clone());
    let offset = memory.index("off");
    let value = memory.value("v");
    let stored = memory.store(base, offset, value);
    let read = memory.select(stored, offset);
    let identity = equality(&mut memory.terms, value, read);
    assert!(recognize_bv_bitblast(&memory.terms, &[identity]));
    let untouched = memory.select(base, offset);
    let wrong = equality(&mut memory.terms, untouched, read);
    assert!(!recognize_bv_bitblast(&memory.terms, &[wrong]));
}

#[test]
fn small_index_aliasing_needs_the_exact_lane_and_keeps_it() {
    // `select a i` and `select a j` under `i = j`: only full-domain
    // scalarization knows the two reads agree, so a query the exact lane can
    // afford must not be handed to the congruence-free read lane. (That a
    // const-array store/select the exact lane can afford still reports
    // `used_exact_finite_arrays` is pinned by
    // `array_finite_tests::authenticates_bv_index_bv_leaf_const_store_select`.)
    let mut memory = Memory::new(2, 4);
    let base = memory.terms.mk_var("aliased_memory", memory.sort.clone());
    let (i, j) = (memory.index("i"), memory.index("j"));
    let left = memory.select(base, i);
    let right = memory.select(base, j);
    let same = equality(&mut memory.terms, i, j);
    let different = memory.terms.mk_not_raw(same);
    let agree = equality(&mut memory.terms, left, right);
    assert!(recognize_bv_bitblast(&memory.terms, &[different, agree]));
}
