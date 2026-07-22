// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the W4 per-position witness synthesizer helpers.

use super::*;

#[test]
fn w4_defaults_on_with_kill_switch() {
    // W4 became DEFAULT-ON in 360a85b477 (31/92 sat-side conversions, 29 of
    // 31 models z3-pinned, 0 regressions on a 404-file sweep). The contract
    // the gate must keep is now: on unless explicitly killed with `=0`.
    if std::env::var("AY_STR_W4").is_err() {
        assert!(str_w4_enabled(), "AY_STR_W4 must default ON");
    }
}

#[test]
fn fresh_char_avoids_the_formula_alphabet() {
    let alpha: Vec<char> = "abcdefghijklmnopqrstuvwxyz".chars().collect();
    let fresh = w4_fresh_char(&alpha);
    assert!(!alpha.contains(&fresh));
}

#[test]
fn set_char_pins_appends_and_clears() {
    let cur: Vec<char> = "abc".chars().collect();
    let alpha: Vec<char> = vec!['a', 'b', 'c'];
    // Pin inside the string.
    let out = w4_set_char(&cur, 1, 'z', true, &alpha, 'q').unwrap();
    assert_eq!(out.iter().collect::<String>(), "azc");
    // Pin one past the end appends.
    let out = w4_set_char(&cur, 3, 'z', true, &alpha, 'q').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcz");
    // Clearing a character that is not there is a no-op (None).
    assert!(w4_set_char(&cur, 0, 'z', false, &alpha, 'q').is_none());
    // Clearing a character that IS there replaces it with a non-excluded one.
    let out = w4_set_char(&cur, 0, 'a', false, &alpha, 'q').unwrap();
    assert_ne!(out[0], 'a');
}

#[test]
fn overwrite_extends_when_needed() {
    let cur: Vec<char> = "ab".chars().collect();
    let lit: Vec<char> = "xyz".chars().collect();
    let out = w4_overwrite(&cur, 1, &lit).unwrap();
    assert_eq!(out.iter().collect::<String>(), "axyz");
}

#[test]
fn resize_window_grows_and_shrinks_in_place() {
    let cur: Vec<char> = "abcdef".chars().collect();
    // Window [2,5) of length 3 -> length 5: two pads inserted at the window end.
    let out = w4_resize_window(&cur, 2, 3, 5, '#').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcde##f");
    // Window [2,5) -> length 1: two characters dropped from the window tail.
    let out = w4_resize_window(&cur, 2, 3, 1, '#').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcf");
    // No-op resize is rejected (nothing to try).
    assert!(w4_resize_window(&cur, 2, 3, 3, '#').is_none());
}

#[test]
fn pick_char_prefers_fresh_then_alphabet() {
    let alpha: Vec<char> = vec!['x', 'y'];
    let mut excluded: HashSet<char> = HashSet::default();
    assert_eq!(w4_pick_char(&excluded, &alpha, 'q'), 'q');
    excluded.insert('q');
    assert_eq!(w4_pick_char(&excluded, &alpha, 'q'), 'x');
}
