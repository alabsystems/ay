// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn seq_last_indexof_semantics() {
    assert_eq!(li(&[5, 5, 5], &[5]), int(2)); // rightmost tie
    assert_eq!(li(&[5, 5], &[5]), int(1)); // z3-4.15.4 gets THIS wrong
    assert_eq!(li(&[9, 1, 2], &[9]), int(0)); // single leftmost occurrence
    assert_eq!(li(&[5, 6], &[9]), int(-1)); // not found
    assert_eq!(li(&[5, 6, 7], &[]), int(3)); // empty needle -> |s|
    assert_eq!(li(&[], &[]), int(0)); // empty haystack + empty needle
    assert_eq!(li(&[1], &[1, 1]), int(-1)); // needle longer than haystack
    assert_eq!(li(&[1, 1, 1], &[1, 1]), int(1)); // rightmost multi-element match
}
