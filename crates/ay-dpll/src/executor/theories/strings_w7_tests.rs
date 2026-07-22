// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the W7 chain-definition / multi-atom / witness-enumerator
//! helpers.

use super::*;
use ay_strings::we_regex::{find_witness_bounded, find_witnesses_bounded, WeRegex};

#[test]
fn w7_defaults_on_with_kill_switch() {
    // DEFAULT-ON after measurement: 6 conversions, all confirmed by AY's own
    // fail-closed --self-check; 0 losses on the 600-file sweep. Contract is
    // now on-unless-killed with `=0`.
    match std::env::var("AY_STR_W7").ok().as_deref() {
        Some("0") => assert!(!str_w7_enabled()),
        None => assert!(str_w7_enabled(), "AY_STR_W7 must default ON"),
        _ => assert!(str_w7_enabled()),
    }
}

#[test]
fn segmented_builds_k_fields_joined_by_the_separator() {
    // The `ip_int_from_string` parse chain needs 8 non-empty fields before any
    // of `_EXTEND_VAR_0..7` exists at all.
    assert_eq!(w7_segmented(":", "1", 3), "1:1:1");
    assert_eq!(w7_segmented(":", "1", 1), "1");
    assert_eq!(w7_segmented(".", "0", 4), "0.0.0.0");
    assert_eq!(w7_segmented(":", "1", 8).matches(':').count(), 7);
}

#[test]
fn witness_enumerator_agrees_with_the_single_witness_search() {
    // `find_witness_bounded` is now `find_witnesses_bounded(.., want = 1)`.
    // The BFS is unchanged, so the first word must be the same word.
    let r = WeRegex::Concat(vec![
        WeRegex::Lit("ab".to_string()),
        WeRegex::Star(Box::new(WeRegex::Lit("c".to_string()))),
    ]);
    let one = find_witness_bounded(std::slice::from_ref(&r), None, 8);
    let many = find_witnesses_bounded(std::slice::from_ref(&r), None, 8, 4);
    assert_eq!(one.as_deref(), many.first().map(String::as_str));
    assert!(one.is_some());
}

#[test]
fn witness_enumerator_yields_two_distinct_words_at_one_length() {
    // stringfuzz `regex-026`: x, y in `(BB (##)*)*` with `x != y` and equal
    // lengths. At length 4 the language has BOTH "BBBB" and "BB##" — the whole
    // reason a witness FINDER cannot decide the file and an ENUMERATOR can.
    let r = WeRegex::Star(Box::new(WeRegex::Concat(vec![
        WeRegex::Lit("BB".to_string()),
        WeRegex::Star(Box::new(WeRegex::Lit("##".to_string()))),
    ])));
    let words = find_witnesses_bounded(std::slice::from_ref(&r), Some(4), 8, 4);
    assert!(
        words.len() >= 2,
        "expected >= 2 distinct words of length 4, got {words:?}"
    );
    assert_eq!(words[0].chars().count(), 4);
    assert_eq!(words[1].chars().count(), 4);
    assert_ne!(words[0], words[1]);
    for w in &words {
        assert_eq!(r.matches(w), Some(true), "{w:?} must be in the language");
    }
}

#[test]
fn witness_enumerator_returns_nothing_for_the_empty_language() {
    // A failed enumeration is "not found", never "no witness exists" — and it
    // must never fabricate a word.
    let words = find_witnesses_bounded(&[WeRegex::None], None, 8, 4);
    assert!(words.is_empty());
    // `want = 0` is a request for nothing, not a request for everything.
    let r = WeRegex::Lit("a".to_string());
    assert!(find_witnesses_bounded(std::slice::from_ref(&r), None, 4, 0).is_empty());
}

#[test]
fn witness_enumerator_never_repeats_a_word() {
    let r = WeRegex::Star(Box::new(WeRegex::Range('a', 'b')));
    let words = find_witnesses_bounded(std::slice::from_ref(&r), Some(2), 4, 8);
    let mut sorted = words.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), words.len(), "duplicate witness in {words:?}");
}

#[test]
fn resize_window_edits_only_the_window() {
    // Growing `_EXTEND_VAR_1`'s field must not disturb the fields around it —
    // the other separators keep the positions the climb already found.
    let cur: Vec<char> = "1:22:3".chars().collect();
    // window [2,4) = "22" grown to 3
    assert_eq!(
        w7_resize_window(&cur, 2, 2, 3, '0')
            .unwrap()
            .iter()
            .collect::<String>(),
        "1:220:3"
    );
    assert_eq!(
        w7_resize_window(&cur, 2, 2, 1, '0')
            .unwrap()
            .iter()
            .collect::<String>(),
        "1:2:3"
    );
    // A no-op resize is not a candidate, and the length cap is respected.
    assert!(w7_resize_window(&cur, 2, 2, 2, '0').is_none());
    assert!(w7_resize_window(&cur, 2, 2, MAX_W4_LEN + 1, '0').is_none());
}

#[test]
fn coupling_closure_colours_classes_and_respects_disequalities() {
    // The `partition` shape: positions 4 and 5 coupled, everything else free.
    // Union-find + one colour per class satisfies every positive coupling by
    // construction and every negative coupling ACROSS classes for free.
    let mut parent: Vec<usize> = (0..8).collect();
    w7_union(&mut parent, 4, 5);
    assert_eq!(w7_find(&mut parent, 4), w7_find(&mut parent, 5));
    assert_ne!(w7_find(&mut parent, 0), w7_find(&mut parent, 4));
    // Transitivity: a chain of couplings is one class.
    w7_union(&mut parent, 0, 1);
    w7_union(&mut parent, 1, 2);
    assert_eq!(w7_find(&mut parent, 0), w7_find(&mut parent, 2));
    // The colouring alphabet must be able to give every position of a
    // MAX_W4_LEN value its own class without repeating.
    assert!(W7_COUPLING_ALPHABET.chars().count() >= MAX_W4_LEN);
}

#[test]
fn place_depth_is_bounded() {
    // The multi-atom search is a BOUNDED generalisation of W5's single
    // placement: without a cap the beam is an unbounded product search.
    let depth = std::hint::black_box(MAX_W7_PLACE_DEPTH);
    assert!(
        (2..=4).contains(&depth),
        "depth must be a bounded multi-placement search"
    );
}
