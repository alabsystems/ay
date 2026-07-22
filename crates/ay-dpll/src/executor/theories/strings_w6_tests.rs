// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the W6 digit/arithmetic-aware and regex-word helpers.

use super::*;

fn s(v: &[char]) -> String {
    v.iter().collect()
}

#[test]
fn w6_defaults_on_with_kill_switch() {
    // DEFAULT-ON: 16 of the last 27 sat-side misses convert, all confirmed by
    // AY's own fail-closed --self-check. Contract is on-unless-killed (=0).
    if std::env::var("AY_STR_W6").is_err() {
        assert!(str_w6_enabled(), "AY_STR_W6 must default ON");
    }
}

#[test]
fn digit_texts_lead_with_a_nonzero_of_the_current_length() {
    // The `full_str_int` family pins `(not (= (str.at W 0) "0"))` on every
    // window it reads with `str.to_int`, so the leading-nonzero shape at the
    // window's CURRENT length is the useful first proposal.
    let out = w6_digit_texts(3, &[]);
    assert_eq!(out.first().map(String::as_str), Some("100"));
    assert!(out.contains(&"000".to_string()));
    assert!(out.contains(&"999".to_string()));
}

#[test]
fn digit_texts_carry_the_atoms_own_boundary_constants() {
    // `(<= (str.to_int W) 255)` — 255 and its neighbours are the values that
    // decide the atom.
    let out = w6_digit_texts(3, &[255, 2]);
    assert!(out.contains(&"255".to_string()));
    assert!(out.contains(&"254".to_string()));
    assert!(out.contains(&"1".to_string()));
    assert!(out.iter().all(|t| t.chars().count() <= MAX_W6_NUM_LEN));
}

#[test]
fn digit_texts_never_emit_a_negative_decimal() {
    // `(= (- 1) (str.to_int W))` puts -1 in the constant set; "-1" is not a
    // digit string and `str.to_int` of it is -1 again.
    let out = w6_digit_texts(2, &[-1]);
    assert!(out.iter().all(|t| !t.starts_with('-')), "{out:?}");
}

#[test]
fn resize_body_grows_and_shrinks_the_window_only() {
    let cur: Vec<char> = "abcdef".chars().collect();
    // window [2,4) = "cd"
    assert_eq!(s(&w6_resize_body(&cur, 2, 2, 4, '0').unwrap()), "cd00");
    assert_eq!(s(&w6_resize_body(&cur, 2, 2, 1, '0').unwrap()), "c");
    // No-op resizes are not candidates.
    assert!(w6_resize_body(&cur, 2, 2, 2, '0').is_none());
}

#[test]
fn push_window_replaces_exactly_the_window() {
    let cur: Vec<char> = "abcdef".chars().collect();
    let mut out: Vec<Vec<char>> = Vec::new();
    w6_push_window(&cur, 2, 2, &['X', 'Y', 'Z'], &mut out);
    assert_eq!(out.len(), 1);
    assert_eq!(s(&out[0]), "abXYZef");
    // Identical candidates are not duplicated, and a no-change write is dropped.
    w6_push_window(&cur, 2, 2, &['X', 'Y', 'Z'], &mut out);
    w6_push_window(&cur, 2, 2, &['c', 'd'], &mut out);
    assert_eq!(out.len(), 1);
}

#[test]
fn push_window_respects_the_length_cap() {
    let cur: Vec<char> = "ab".chars().collect();
    let long: Vec<char> = std::iter::repeat_n('x', MAX_W4_LEN + 1).collect();
    let mut out: Vec<Vec<char>> = Vec::new();
    w6_push_window(&cur, 0, 2, &long, &mut out);
    assert!(out.is_empty());
}

#[test]
fn shortest_word_is_structural_over_concat_union_and_star() {
    // `(re.++ (re.* X) (str.to_re "/evil") (re.* Y))` — the derivative BFS
    // needs depth 5 to reach this; the structural walk is linear.
    let r = WeRegex::concat(vec![
        WeRegex::star(WeRegex::AnyChar),
        WeRegex::lit("/evil"),
        WeRegex::star(WeRegex::AnyChar),
    ]);
    let w = w6_shortest_word(&r, 0).unwrap();
    assert_eq!(w, "/evil");
    assert_eq!(r.matches(&w), Some(true));
}

#[test]
fn shortest_word_picks_the_shorter_union_branch() {
    let r = WeRegex::union(vec![WeRegex::lit("aaa"), WeRegex::lit("b")]);
    assert_eq!(w6_shortest_word(&r, 0).as_deref(), Some("b"));
}

#[test]
fn shortest_word_of_star_is_empty_and_of_plus_is_the_body() {
    assert_eq!(
        w6_shortest_word(&WeRegex::star(WeRegex::lit("ab")), 0).as_deref(),
        Some("")
    );
    assert_eq!(
        w6_shortest_word(&WeRegex::plus(WeRegex::lit("ab")), 0).as_deref(),
        Some("ab")
    );
    // `(re.+ (re.range "0" "1"))` — the `add_binary` membership.
    let digits = WeRegex::plus(WeRegex::range("0", "1"));
    let w = w6_shortest_word(&digits, 0).unwrap();
    assert_eq!(w, "0");
    assert_eq!(digits.matches(&w), Some(true));
}

#[test]
fn shortest_word_declines_inter_and_comp() {
    // "Shortest" is not structural under intersection/complement: those keep
    // using the exact derivative search.
    assert!(w6_shortest_word(&WeRegex::comp(WeRegex::lit("a")), 0).is_none());
    assert!(w6_shortest_word(
        &WeRegex::inter(vec![WeRegex::lit("a"), WeRegex::lit("b")]),
        0
    )
    .is_none());
}

#[test]
fn shortest_word_never_exceeds_the_witness_cap() {
    // A long concat chain must decline rather than build a giant witness.
    let parts: Vec<WeRegex> = (0..MAX_W4_LEN + 5).map(|_| WeRegex::lit("zz")).collect();
    assert!(w6_shortest_word(&WeRegex::concat(parts), 0).is_none());
}

#[test]
fn shortest_word_of_a_bounded_loop_takes_the_lower_bound() {
    let r = WeRegex::loop_bounded(WeRegex::lit("ab"), 2, 5);
    let w = w6_shortest_word(&r, 0).unwrap();
    assert_eq!(w, "abab");
    assert_eq!(r.matches(&w), Some(true));
}
