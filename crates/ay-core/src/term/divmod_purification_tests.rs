// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The purification provenance table: what it records, what it refuses, and
//! that it never outlives the terms it names.

use num_bigint::BigInt;

use super::DivModPurification;
use crate::{Sort, TermId, TermStore};

/// A pair minted as `mod_div_elim` mints one: two fresh `Int` symbols for
/// `(div x k)` / `(mod x k)`.
fn minted(store: &mut TermStore, dividend: TermId, k: i64) -> DivModPurification {
    let quotient = store.mk_fresh_var("_divmod_q", Sort::Int);
    let remainder = store.mk_fresh_var("_divmod_r", Sort::Int);
    let divisor = store.mk_int(BigInt::from(k));
    DivModPurification {
        quotient,
        remainder,
        dividend,
        divisor,
    }
}

#[test]
fn a_registered_pair_is_found_from_either_symbol() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    assert!(!store.has_divmod_purifications());
    let pair = minted(&mut store, x, -3);
    store.register_divmod_purification(pair);
    assert!(store.has_divmod_purifications());
    assert_eq!(store.divmod_purification(pair.quotient), Some(pair));
    assert_eq!(store.divmod_purification(pair.remainder), Some(pair));
    assert_eq!(store.divmod_purification(x), None);
}

#[test]
fn a_shape_that_is_no_purification_is_not_recorded() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let real = store.mk_var("y", Sort::Real);
    let valid = minted(&mut store, x, 2);
    let zero = store.mk_int(BigInt::from(0));
    let symbolic = store.mk_var("k", Sort::Int);
    let real_symbol = store.mk_fresh_var("_divmod_q", Sort::Real);
    for refused in [
        // `(mod x 0)` is unconstrained: it has no Euclidean pair.
        DivModPurification {
            divisor: zero,
            ..valid
        },
        DivModPurification {
            divisor: symbolic,
            ..valid
        },
        DivModPurification {
            remainder: valid.quotient,
            ..valid
        },
        DivModPurification {
            quotient: real_symbol,
            ..valid
        },
        DivModPurification {
            dividend: real,
            ..valid
        },
        // A compound term is not a fresh symbol.
        DivModPurification {
            quotient: valid.divisor,
            ..valid
        },
    ] {
        store.register_divmod_purification(refused);
        assert!(!store.has_divmod_purifications(), "{refused:?}");
    }
}

#[test]
fn a_rollback_drops_every_pair_naming_a_truncated_term() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let kept = minted(&mut store, x, 2);
    store.register_divmod_purification(kept);
    // Symbols minted before the checkpoint, registered with a dividend after.
    let early = minted(&mut store, x, 7);
    let checkpoint = store.rollback_checkpoint();
    let scratch = minted(&mut store, x, 5);
    store.register_divmod_purification(scratch);
    let late_dividend = store.mk_var("late", Sort::Int);
    let mixed = DivModPurification {
        dividend: late_dividend,
        ..early
    };
    store.register_divmod_purification(mixed);
    store.rollback_to(checkpoint);
    assert_eq!(store.divmod_purification(kept.quotient), Some(kept));
    assert_eq!(store.divmod_purification(kept.remainder), Some(kept));
    assert_eq!(store.divmod_purification(scratch.quotient), None);
    assert_eq!(store.divmod_purification(scratch.remainder), None);
    assert_eq!(store.divmod_purification(mixed.quotient), None);
    assert_eq!(store.divmod_purification.len(), 2);
}

#[test]
fn a_compaction_moves_a_live_pair_and_drops_a_reclaimed_one() {
    let mut store = TermStore::new();
    let _dead = store.mk_int(BigInt::from(41));
    let x = store.mk_var("x", Sort::Int);
    let live = minted(&mut store, x, 3);
    store.register_divmod_purification(live);
    let reclaimed = minted(&mut store, x, 9);
    store.register_divmod_purification(reclaimed);
    // Only the live pair's terms are reachable.
    let scaled = store.mk_mul(vec![live.divisor, live.quotient]);
    let sum = store.mk_add(vec![scaled, live.remainder]);
    let root = store.mk_eq(x, sum);
    let remap = store.mark_and_compact(&[root]);
    let moved = DivModPurification {
        quotient: remap.remap(live.quotient),
        remainder: remap.remap(live.remainder),
        dividend: remap.remap(live.dividend),
        divisor: remap.remap(live.divisor),
    };
    assert_ne!(moved, live, "the arena moved under the pair");
    assert_eq!(store.divmod_purification(moved.quotient), Some(moved));
    assert_eq!(store.divmod_purification(moved.remainder), Some(moved));
    assert!(remap.get(reclaimed.quotient).is_none());
    assert_eq!(
        store.divmod_purification.len(),
        2,
        "exactly the live pair's two keys remain"
    );
}

#[test]
fn a_clone_keeps_the_table() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let pair = minted(&mut store, x, 4);
    store.register_divmod_purification(pair);
    let cloned = store.clone();
    assert_eq!(cloned.divmod_purification(pair.remainder), Some(pair));
}
