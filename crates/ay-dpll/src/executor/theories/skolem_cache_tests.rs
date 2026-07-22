// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

#[test]
fn contains_cache_reuses_identical_key() {
    let mut terms = TermStore::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = terms.mk_var("x", Sort::String);
    let needle = terms.mk_string("ab".to_owned());

    let first = cache.contains_pre(&mut terms, x, needle);
    let second = cache.contains_pre(&mut terms, x, needle);

    assert_eq!(first, second);
}

#[test]
fn different_kinds_do_not_alias() {
    let mut terms = TermStore::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let pre = cache.contains_pre(&mut terms, x, y);
    let post = cache.contains_post(&mut terms, x, y);

    assert_ne!(pre, post);
}

#[test]
fn var_split_normalizes_term_order() {
    let mut terms = TermStore::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let xy = cache.var_split(&mut terms, x, y);
    let yx = cache.var_split(&mut terms, y, x);

    assert_eq!(xy, yx);
}
