// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal verification-consumer-side FMap len/lookup SAT repros.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn test_distinct_fmap_len_lookup_ufs_can_differ() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-sort FMap 0)
        (declare-fun fmap_len (FMap) Int)
        (declare-fun fmap_lookup (FMap Int) Int)
        (declare-const m FMap)
        (assert (not (= (fmap_len m) (fmap_lookup m 0))))
        (check-sat)
    "#;

    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(10_000)]
fn test_fmap_len_proxy_and_lookup_uf_can_differ() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-sort FMap 0)
        (declare-fun fmap_lookup (FMap Int) Int)
        (declare-const m FMap)
        (declare-const fmap_len_proxy Int)
        (assert (not (= fmap_len_proxy (fmap_lookup m 0))))
        (check-sat)
    "#;

    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(10_000)]
fn test_auflia_fmap_len_nonnegative_and_lookup_uf_can_differ() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-sort FMap 0)
        (declare-fun fmap_len (FMap) Int)
        (declare-fun fmap_lookup (FMap Int) Int)
        (declare-const m FMap)
        (assert (>= (fmap_len m) 0))
        (assert (not (= (fmap_len m) (fmap_lookup m 0))))
        (check-sat)
    "#;

    assert_eq!(crate::common::solve(smt).trim(), "sat");
}
