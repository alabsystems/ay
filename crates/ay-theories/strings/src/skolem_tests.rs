// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;

fn make_terms() -> TermStore {
    TermStore::new()
}

#[test]
fn empty_split_returns_true_once() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);

    assert!(cache.mark_empty_split(x), "first call should return true");
    assert!(
        !cache.mark_empty_split(x),
        "second call should return false (already emitted)"
    );
}

#[test]
fn const_split_caches_skolem() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    let sk1 = cache.get_const_split(&mut terms, x, c, 0);
    let sk2 = cache.get_const_split(&mut terms, x, c, 0);
    assert_eq!(sk1, sk2, "same inputs should return same skolem");

    let d = terms.mk_var("d", Sort::String);
    let sk3 = cache.get_const_split(&mut terms, x, d, 0);
    assert_ne!(
        sk1, sk3,
        "different constant should produce different skolem"
    );
}

#[test]
fn const_split_key_includes_char_offset() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    let sk0 = cache.get_const_split(&mut terms, x, c, 0);
    let sk1 = cache.get_const_split(&mut terms, x, c, 1);
    assert_ne!(sk0, sk1, "different char offsets need different skolems");
}

#[test]
fn mark_const_split_dedups_by_offset() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    assert!(cache.mark_const_split(x, c, 0));
    assert!(!cache.mark_const_split(x, c, 0));
    assert!(
        cache.mark_const_split(x, c, 1),
        "different char offset should not be deduped"
    );
}

#[test]
fn mark_then_get_const_split_creates_real_skolem() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    assert!(cache.mark_const_split(x, c, 0));
    let sk = cache.get_const_split(&mut terms, x, c, 0);
    assert_ne!(sk, x, "get_const_split must return a fresh skolem");
}

#[test]
fn var_split_normalizes_key_order() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let sk1 = cache.get_var_split(&mut terms, x, y);
    let sk2 = cache.get_var_split(&mut terms, y, x);
    assert_eq!(
        sk1, sk2,
        "var split should normalize (x,y) and (y,x) to same skolem"
    );
}

#[test]
fn mark_var_split_normalizes_key_order() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    assert!(cache.mark_var_split(x, y));
    assert!(!cache.mark_var_split(y, x));
}

#[test]
fn push_pop_restores_cache() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    let sk1 = cache.get_const_split(&mut terms, x, c, 0);
    cache.push();

    let y = terms.mk_var("y", Sort::String);
    let sk2 = cache.get_const_split(&mut terms, y, c, 0);
    assert_ne!(sk1, sk2);
    assert!(cache.mark_empty_split(y));

    cache.pop();

    let sk3 = cache.get_const_split(&mut terms, y, c, 0);
    assert_ne!(
        sk2, sk3,
        "after pop, y's const split should create new skolem"
    );
    assert!(
        cache.mark_empty_split(y),
        "after pop, y's empty split should be new again"
    );

    let sk4 = cache.get_const_split(&mut terms, x, c, 0);
    assert_eq!(sk1, sk4, "x's skolem should survive the pop");
}

#[test]
fn purify_caches_skolem() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let t = terms.mk_var("t", Sort::String);

    let sk1 = cache.get_purify(&mut terms, t);
    let sk2 = cache.get_purify(&mut terms, t);
    assert_eq!(sk1, sk2, "purify should cache");
}

#[test]
fn reset_clears_everything() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_var("c", Sort::String);

    let sk1 = cache.get_const_split(&mut terms, x, c, 0);
    cache.push();
    cache.mark_empty_split(x);

    cache.reset();

    let sk2 = cache.get_const_split(&mut terms, x, c, 0);
    assert_ne!(sk1, sk2, "after reset, should get new skolem");
    assert!(cache.mark_empty_split(x), "after reset, empty split is new");
}

#[test]
fn mark_const_split_deduplicates() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_string("abc".to_string());

    assert!(
        cache.mark_const_split(x, c, 0),
        "first const split should be new"
    );
    assert!(
        !cache.mark_const_split(x, c, 0),
        "duplicate const split should be suppressed"
    );
}

#[test]
fn mark_var_split_deduplicates_with_normalized_order() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    assert!(cache.mark_var_split(x, y), "first var split should be new");
    assert!(
        !cache.mark_var_split(y, x),
        "reversed var split should be deduplicated"
    );
}

#[test]
fn mark_const_split_push_pop_restores_scope() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_string("abc".to_string());

    cache.push();
    assert!(cache.mark_const_split(x, c, 0));
    assert!(!cache.mark_const_split(x, c, 0));
    cache.pop();
    assert!(
        cache.mark_const_split(x, c, 0),
        "const split should be available again after pop"
    );
}

#[test]
fn mark_var_split_push_pop_restores_scope() {
    let mut cache = SkolemCache::new();
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    cache.push();
    assert!(cache.mark_var_split(x, y));
    assert!(!cache.mark_var_split(x, y));
    cache.pop();
    assert!(
        cache.mark_var_split(y, x),
        "var split should be available again after pop"
    );
}
