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
    // now on-unless-killed (`--dpll-no-str-w7`).
    assert!(
        str_w7_enabled(),
        "W7 must default ON (`--dpll-no-str-w7` kills it)"
    );
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
    assert_eq!(words, [] as [String; 0]);
    // `want = 0` is a request for nothing, not a request for everything.
    let r = WeRegex::Lit("a".to_string());
    assert_eq!(
        find_witnesses_bounded(std::slice::from_ref(&r), None, 4, 0),
        [] as [String; 0]
    );
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

#[test]
fn distinct_word_lengths_follow_the_asserted_window() {
    // No window: the historical 0..=12.
    assert_eq!(
        w7_word_lengths(None),
        (0..=MAX_W7_WORD_LEN).collect::<Vec<_>>()
    );
    // `len x = 14`: exactly 14 (the fixed 0..=12 never reached it).
    assert_eq!(w7_word_lengths(Some((14, 14))), vec![14]);
    // A window from 20 up: 13 lengths from its bottom.
    assert_eq!(
        w7_word_lengths(Some((20, usize::MAX))),
        (20..=20 + MAX_W7_WORD_LEN).collect::<Vec<_>>()
    );
    // Empty or out-of-reach windows probe nothing.
    assert_eq!(w7_word_lengths(Some((5, 4))), Vec::<usize>::new());
    assert_eq!(
        w7_word_lengths(Some((MAX_W7_WINDOW_WORD_LEN + 1, usize::MAX))),
        Vec::<usize>::new()
    );
}

/// QF_SLIA 9df5efea, minimised: two distinct words of one regular language
/// at an asserted length past 12. Length 4 was `sat`, length 14 `unknown`
/// after the candidates (all of the wrong length) ran out.
#[test]
fn distinct_words_at_an_asserted_length_past_twelve_are_found() {
    for n in [4, 14] {
        let input = format!(
            r#"
            (set-logic QF_SLIA)
            (declare-fun x1 () String)
            (declare-fun x2 () String)
            (assert (str.in_re x1 (re.* (re.++ (str.to_re "b") (re.* (str.to_re "aa"))))))
            (assert (str.in_re x2 (re.* (re.++ (str.to_re "b") (re.* (str.to_re "aa"))))))
            (assert (= (str.len x2) {n}))
            (assert (= (str.len x1) (str.len x2)))
            (assert (not (= x1 x2)))
            (check-sat)
            "#
        );
        let commands = ay_frontend::parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["sat"], "length {n}");
    }
}
