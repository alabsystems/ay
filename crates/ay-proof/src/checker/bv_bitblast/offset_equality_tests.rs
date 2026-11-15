// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::{Duration, Instant};

use super::*;
use num_bigint::BigInt;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(120)
}

fn bv(terms: &mut TermStore, op: &str, args: &[TermId], width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn predicate(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::Bool)
}

fn literal(terms: &mut TermStore, value: u64) -> TermId {
    terms.mk_bitvec(BigInt::from(value), 64)
}

/// `base + offset`, spelled as authored (no constant folding).
fn offset(terms: &mut TermStore, base: TermId, offset: u64) -> TermId {
    let constant = literal(terms, offset);
    bv(terms, "bvadd", &[constant, base], 64)
}

/// The coroutine-slot lemma over `bytes` bytes: under `guard`, no byte of
/// the store at `frame + 24` aliases a byte of the load at `vbase`. The
/// guard is the row's own when `separated`, and one byte short otherwise.
fn slot_lemma(terms: &mut TermStore, bytes: u64, separated: bool) -> TermId {
    let vbase = terms.mk_var("vbase", Sort::bitvec(64));
    let frame = terms.mk_var("frame", Sort::bitvec(64));
    let store = offset(terms, frame, 24);
    let store_end = offset(terms, frame, 24 + bytes);
    let load_end = offset(terms, vbase, if separated { bytes } else { bytes - 1 });
    let below = predicate(terms, "bvuge", &[store, load_end]);
    let above = predicate(terms, "bvuge", &[vbase, store_end]);
    let apart = predicate(terms, "or", &[below, above]);
    let store_fits = predicate(terms, "bvugt", &[store_end, store]);
    let load_top = offset(terms, vbase, bytes);
    let load_fits = predicate(terms, "bvugt", &[load_top, vbase]);
    let mut aliases = Vec::new();
    for j in 0..bytes {
        for i in 0..bytes {
            let written = offset(terms, frame, 24 + j);
            let read = offset(terms, vbase, i);
            aliases.push(predicate(terms, "=", &[written, read]));
        }
    }
    let alias = predicate(terms, "or", &aliases);
    let root = predicate(terms, "and", &[apart, store_fits, load_fits, alias]);
    terms.mk_not(root)
}

#[test]
fn an_offset_equality_lowers_through_one_difference() {
    let mut terms = TermStore::new();
    let vbase = terms.mk_var("vbase", Sort::bitvec(64));
    let frame = terms.mk_var("frame", Sort::bitvec(64));
    let (c24, c7) = (literal(&mut terms, 24), literal(&mut terms, 7));
    let slot = bv(&mut terms, "bvadd", &[c24, c7], 64);
    let written = bv(&mut terms, "bvadd", &[slot, frame], 64);
    let read = offset(&mut terms, vbase, 1);
    let authored = predicate(&mut terms, "=", &[written, read]);
    // A second equality over the same pair: the difference is shared.
    let other = offset(&mut terms, frame, 24);
    let sharing = predicate(&mut terms, "=", &[other, vbase]);
    let both = predicate(&mut terms, "and", &[authored, sharing]);
    let difference = bv(&mut terms, "bvsub", &[vbase, frame], 64);
    let thirty = literal(&mut terms, 30);
    let expected = predicate(&mut terms, "=", &[difference, thirty]);
    let twenty_four = literal(&mut terms, 24);
    let expected_sharing = predicate(&mut terms, "=", &[difference, twenty_four]);
    let expected_both = predicate(&mut terms, "and", &[expected, expected_sharing]);

    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    let lowered = lowerer.lower_bool(both).expect("authored equalities lower");
    lowerer.audit_census();
    let mut reference = ProofProducingLowerer::new(&terms, deadline());
    let spelled = reference
        .lower_bool(expected_both)
        .expect("differences lower");
    assert_eq!(lowered, spelled);
}

/// An equality whose pair no other equality of the lowering reads keeps its
/// authored lowering (DR-33): its subtractor would be shared by nothing.
#[test]
fn an_offset_equality_nothing_shares_lowers_as_authored() {
    let mut terms = TermStore::new();
    let vbase = terms.mk_var("vbase", Sort::bitvec(64));
    let frame = terms.mk_var("frame", Sort::bitvec(64));
    let written = offset(&mut terms, frame, 31);
    let read = offset(&mut terms, vbase, 1);
    let authored = predicate(&mut terms, "=", &[written, read]);
    assert!(terms.bv_offset_equality(written, read).is_some());

    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    let lowered = lowerer
        .lower_bool(authored)
        .expect("authored equality lowers");
    lowerer.audit_census();
    let mut reference = ProofProducingLowerer::new(&terms, deadline());
    let spelled = reference
        .lower_equality("=", written, read)
        .expect("the authored sides lower");
    assert_eq!(lowered, spelled);
}

#[test]
fn the_census_counts_the_words_an_offset_equality_requests() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(16));
    let y = terms.mk_var("y", Sort::bitvec(16));
    let one = terms.mk_bitvec(BigInt::from(1), 16);
    let two = terms.mk_bitvec(BigInt::from(2), 16);
    let x1 = bv(&mut terms, "bvadd", &[one, x], 16);
    let x2 = bv(&mut terms, "bvadd", &[two, x], 16);
    let first = predicate(&mut terms, "=", &[x1, y]);
    let second = predicate(&mut terms, "distinct", &[y, x2]);
    // `x1` is ALSO an operand of an ordinary comparison.
    let compared = predicate(&mut terms, "bvult", &[x1, y]);
    let root = predicate(&mut terms, "and", &[first, second, compared]);
    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    lowerer.lower_bool(root).expect("root lowers");
    lowerer.audit_census();
}

#[test]
fn the_coroutine_slot_lemma_is_validated_and_its_overlap_is_not() {
    let mut terms = TermStore::new();
    let lemma = slot_lemma(&mut terms, 4, true);
    assert!(
        validate_bv_bitblast(&terms, ProofId(0), &[lemma], None).is_ok(),
        "separated slots: every aliasing equality is refuted"
    );
    let mut terms = TermStore::new();
    let overlapping = slot_lemma(&mut terms, 4, false);
    assert!(
        validate_bv_bitblast(&terms, ProofId(0), &[overlapping], None).is_err(),
        "a guard one byte short lets a load byte alias a stored byte"
    );
}
