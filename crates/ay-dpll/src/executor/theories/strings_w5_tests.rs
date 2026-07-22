// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the W5 position-aware witness-search helpers.

use super::*;

fn s(v: &[char]) -> String {
    v.iter().collect()
}

#[test]
fn w5_defaults_on_with_kill_switch() {
    // DEFAULT-ON: 31/58 remaining sat-side conversions, all z3-PIN-verified,
    // 478/478 solved-file regression exact. The contract is on-unless-killed.
    if std::env::var("AY_STR_W5").is_err() {
        assert!(str_w5_enabled(), "AY_STR_W5 must default ON");
    }
}

#[test]
fn positions_are_end_first_then_backwards_then_past_the_end() {
    // The end (append) is the cheapest structure-preserving landing spot, so
    // it must be tried first; padding positions come last.
    assert_eq!(w5_positions(0), vec![0, 1, 2, 3]);
    assert_eq!(w5_positions(3), vec![3, 2, 1, 0, 4, 5, 6]);
}

#[test]
fn positions_are_capped() {
    assert!(w5_positions(1000).len() <= MAX_W5_POSITIONS);
}

#[test]
fn find_respects_the_from_offset() {
    let hay: Vec<char> = "abcabc".chars().collect();
    let needle: Vec<char> = "abc".chars().collect();
    assert_eq!(w5_find(&hay, &needle, 0), Some(0));
    assert_eq!(w5_find(&hay, &needle, 1), Some(3));
    assert_eq!(w5_find(&hay, &needle, 4), None);
    // The empty needle is never "placed".
    assert_eq!(w5_find(&hay, &[], 0), None);
}

#[test]
fn place_insert_splices_and_preserves_the_tail() {
    let cur: Vec<char> = "abcd".chars().collect();
    let n: Vec<char> = "XY".chars().collect();
    let out = w5_place(&cur, 2, &n, W5Write::Insert, false, '#').unwrap();
    assert_eq!(s(&out), "abXYcd");
}

#[test]
fn place_at_the_end_appends() {
    // The measured PyEx shape: `value1 = "b\t=K"` needs `"L"` to OCCUR, and
    // the first landing position tried (the end) is the witness.
    let cur: Vec<char> = "b\t=K".chars().collect();
    let n: Vec<char> = "L".chars().collect();
    let out = w5_place(&cur, cur.len(), &n, W5Write::Insert, false, '#').unwrap();
    assert_eq!(s(&out), "b\t=KL");
}

#[test]
fn place_overwrite_writes_in_place() {
    let cur: Vec<char> = "abcd".chars().collect();
    let n: Vec<char> = "XY".chars().collect();
    let out = w5_place(&cur, 1, &n, W5Write::Overwrite, false, '#').unwrap();
    assert_eq!(s(&out), "aXYd");
}

#[test]
fn place_past_the_end_pads_with_fresh() {
    let cur: Vec<char> = "ab".chars().collect();
    let n: Vec<char> = "Z".chars().collect();
    let out = w5_place(&cur, 4, &n, W5Write::Insert, false, '#').unwrap();
    assert_eq!(s(&out), "ab##Z");
}

#[test]
fn place_scrubs_earlier_occurrences_so_indexof_lands_where_asked() {
    // "=" already occurs at 0; asking for it at 3 must BREAK the one at 0,
    // otherwise a first-occurrence read still returns 0.
    let cur: Vec<char> = "=abc".chars().collect();
    let n: Vec<char> = "=".chars().collect();
    let out = w5_place(&cur, 3, &n, W5Write::Overwrite, true, '#').unwrap();
    assert_eq!(s(&out), "#ab=");
    assert_eq!(w5_find(&out, &n, 0), Some(3));
}

#[test]
fn place_scrub_never_uses_the_needle_char_as_filler() {
    // Degenerate case: the fresh character IS the needle. Scrubbing must not
    // re-create the occurrence it is breaking.
    let cur: Vec<char> = "##ab".chars().collect();
    let n: Vec<char> = "#".chars().collect();
    let out = w5_place(&cur, 3, &n, W5Write::Overwrite, true, '#').unwrap();
    assert_eq!(w5_find(&out, &n, 0), Some(3));
}

#[test]
fn place_refuses_to_exceed_the_length_budget() {
    let cur: Vec<char> = "ab".chars().collect();
    let n: Vec<char> = "Z".chars().collect();
    assert!(w5_place(&cur, MAX_W4_LEN, &n, W5Write::Insert, false, '#').is_none());
    assert!(w5_place(&cur, 0, &[], W5Write::Insert, false, '#').is_none());
}

#[test]
fn scrub_before_breaks_only_the_occurrences_in_range() {
    let cur: Vec<char> = "=a=b=".chars().collect();
    let n: Vec<char> = "=".chars().collect();
    let alpha: Vec<char> = vec!['a', 'b'];
    // Only occurrences in [0, 4) are broken; the one at 4 survives and is now
    // the first at-or-after 0.
    let out = w5_scrub_before(&cur, 0, 4, &n, &alpha, '#').unwrap();
    assert_eq!(w5_find(&out, &n, 0), Some(4));
}

#[test]
fn scrub_before_is_a_no_op_when_nothing_precedes() {
    let cur: Vec<char> = "ab=".chars().collect();
    let n: Vec<char> = "=".chars().collect();
    let alpha: Vec<char> = vec!['a', 'b'];
    let out = w5_scrub_before(&cur, 0, 2, &n, &alpha, '#').unwrap();
    assert_eq!(s(&out), "ab=");
}
