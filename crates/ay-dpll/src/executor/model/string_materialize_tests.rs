// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the pure witness-construction helpers (#str-witness).

use super::{StringVarConstraints, FILL_CHAR};
use crate::executor::Executor;

fn cons() -> StringVarConstraints {
    StringVarConstraints::default()
}

#[test]
fn build_witness_length_only_fills_default() {
    let w = Executor::build_witness(5, &cons()).expect("length-only witness");
    assert_eq!(w, FILL_CHAR.to_string().repeat(5));
    assert_eq!(w.chars().count(), 5);
}

#[test]
fn build_witness_length_zero_is_empty() {
    let w = Executor::build_witness(0, &cons()).expect("zero-length witness");
    assert_eq!(w, "");
}

#[test]
fn build_witness_prefix_pins_front() {
    let mut c = cons();
    c.prefixes.push("ab".to_string());
    let w = Executor::build_witness(5, &c).expect("prefix witness");
    assert!(w.starts_with("ab"), "got {w}");
    assert_eq!(w.chars().count(), 5);
}

#[test]
fn build_witness_suffix_pins_back() {
    let mut c = cons();
    c.suffixes.push("yz".to_string());
    let w = Executor::build_witness(5, &c).expect("suffix witness");
    assert!(w.ends_with("yz"), "got {w}");
    assert_eq!(w.chars().count(), 5);
}

#[test]
fn build_witness_prefix_and_suffix_overlap_ok() {
    let mut c = cons();
    c.prefixes.push("ab".to_string());
    c.suffixes.push("yz".to_string());
    let w = Executor::build_witness(4, &c).expect("prefix+suffix witness");
    assert_eq!(w, "abyz");
}

#[test]
fn build_witness_prefix_suffix_conflict_returns_none() {
    let mut c = cons();
    // prefix "ab" pins pos0='a',pos1='b'; suffix "xb" at len 2 pins
    // pos0='x',pos1='b' — pos0 conflicts.
    c.prefixes.push("ab".to_string());
    c.suffixes.push("xb".to_string());
    assert!(Executor::build_witness(2, &c).is_none());
}

#[test]
fn build_witness_prefix_too_long_returns_none() {
    let mut c = cons();
    c.prefixes.push("abc".to_string());
    assert!(Executor::build_witness(2, &c).is_none());
}

#[test]
fn build_witness_forced_char_pins_position() {
    let mut c = cons();
    c.forced.insert(2, 'z');
    let w = Executor::build_witness(5, &c).expect("forced-char witness");
    assert_eq!(w.chars().nth(2), Some('z'));
    assert_eq!(w.chars().count(), 5);
}

#[test]
fn build_witness_forced_char_out_of_range_returns_none() {
    let mut c = cons();
    c.forced.insert(7, 'z');
    assert!(Executor::build_witness(5, &c).is_none());
}

#[test]
fn build_witness_contains_places_substring() {
    let mut c = cons();
    c.contains.push("xy".to_string());
    let w = Executor::build_witness(5, &c).expect("contains witness");
    assert!(w.contains("xy"), "got {w}");
    assert_eq!(w.chars().count(), 5);
}

#[test]
fn value_satisfies_constraints_checks_length() {
    let c = cons();
    assert!(Executor::value_satisfies_constraints("aaaaa", Some(5), &c));
    assert!(!Executor::value_satisfies_constraints("aaa", Some(5), &c));
}

#[test]
fn value_satisfies_constraints_checks_prefix_suffix() {
    let mut c = cons();
    c.prefixes.push("ab".to_string());
    c.suffixes.push("yz".to_string());
    assert!(Executor::value_satisfies_constraints("abxyz", Some(5), &c));
    assert!(!Executor::value_satisfies_constraints("xbxyz", Some(5), &c));
    assert!(!Executor::value_satisfies_constraints("abxxx", Some(5), &c));
}

#[test]
fn window_present_only_counts_pinned() {
    let buf = vec![Some('a'), Some('b'), None, None];
    assert!(Executor::window_present(&buf, &['a', 'b']));
    // 'cd' is not pinned anywhere — wildcards do not count as a match.
    assert!(!Executor::window_present(&buf, &['c', 'd']));
}

#[test]
fn window_compatible_respects_pins() {
    let buf = vec![Some('a'), None, None];
    assert!(Executor::window_compatible(&buf, 1, &['x', 'y']));
    assert!(!Executor::window_compatible(&buf, 0, &['x', 'y']));
}

// ── W2: regex-aware materializer (`AY_STR_WITNESS=1`) ─────────────────
//
// The COLLECTOR is env-gated (so flags-off stays byte-identical), but the
// constraint checking and witness construction below are pure functions of
// `StringVarConstraints`, so they are exercised directly here — no env
// mutation, no test-order coupling.

use ay_strings::we_regex::WeRegex;

/// `[a-c]{3}` — a language whose members the uniform `FILL_CHAR` pad can
/// satisfy only by accident, and never for `[x-z]`.
fn range_regex(lo: &str, hi: &str, n: usize) -> WeRegex {
    WeRegex::concat(vec![WeRegex::range(lo, hi); n])
}

#[test]
fn value_satisfies_constraints_rejects_non_member() {
    let mut c = cons();
    c.regexes.push(range_regex("x", "z", 3));
    // The historical pad is 'aaa', which is NOT in [x-z]{3}.
    assert!(!Executor::value_satisfies_constraints("aaa", Some(3), &c));
    assert!(Executor::value_satisfies_constraints("xyz", Some(3), &c));
}

#[test]
fn value_satisfies_constraints_negative_membership_via_comp() {
    let mut c = cons();
    // `x ∉ [x-z]{3}` carried EXACTLY as its complement.
    c.regexes.push(WeRegex::comp(range_regex("x", "z", 3)));
    assert!(Executor::value_satisfies_constraints("aaa", Some(3), &c));
    assert!(!Executor::value_satisfies_constraints("xyz", Some(3), &c));
}

#[test]
fn build_witness_constructs_regex_member_the_pad_cannot() {
    let mut c = cons();
    c.regexes.push(range_regex("x", "z", 3));
    let w = Executor::build_witness(3, &c).expect("regex witness");
    assert_eq!(w.chars().count(), 3);
    assert_eq!(
        range_regex("x", "z", 3).matches(&w),
        Some(true),
        "constructed witness {w:?} must be in the language"
    );
    assert_ne!(w, FILL_CHAR.to_string().repeat(3));
}

#[test]
fn build_witness_regex_respects_other_pins() {
    let mut c = cons();
    // `[a-c]{3}` with a forced 'c' at position 1: the constructed candidate is
    // only accepted when it also satisfies the pin, else the pad path runs.
    c.regexes.push(range_regex("a", "c", 3));
    c.forced.insert(1, 'c');
    let w = Executor::build_witness(3, &c).expect("regex+forced witness");
    assert_eq!(w.chars().count(), 3);
    assert_eq!(w.chars().nth(1), Some('c'));
}

#[test]
fn build_witness_regex_empty_language_falls_back_to_pad() {
    let mut c = cons();
    c.regexes.push(WeRegex::None);
    // No witness exists; the pre-existing fill path still returns a value and
    // the strict re-validation remains the gate.
    let w = Executor::build_witness(3, &c).expect("fallback witness");
    assert_eq!(w, FILL_CHAR.to_string().repeat(3));
}

#[test]
fn regexes_default_empty_so_flags_off_checks_are_noops() {
    let c = cons();
    assert!(c.regexes.is_empty());
    assert!(Executor::value_satisfies_constraints("aaa", Some(3), &c));
}

// ---------------------------------------------------------------------------
// NF-engine closure 6 (`AY_STR_NF=1`): hard `(not (str.contains v c))`.
// ---------------------------------------------------------------------------

#[test]
fn forbidden_defaults_empty_so_flags_off_checks_are_noops() {
    let c = cons();
    assert!(c.forbidden.is_empty());
    // The default fill is 'a'; with no forbidden needle it must stay accepted,
    // so the flags-off materializer is byte-identical.
    assert!(Executor::value_satisfies_constraints("aaa", Some(3), &c));
    assert_eq!(
        Executor::build_witness(3, &c).expect("pad witness"),
        FILL_CHAR.to_string().repeat(3)
    );
}

/// The check is the LITERAL negation of `str.contains`, so it must reject
/// exactly the values carrying the needle — including as an interior window,
/// not only as a prefix.
#[test]
fn forbidden_rejects_exactly_the_values_containing_the_needle() {
    let mut c = cons();
    c.forbidden.push(",".to_string());
    assert!(!Executor::value_satisfies_constraints("a,b", Some(3), &c));
    assert!(!Executor::value_satisfies_constraints(",aa", Some(3), &c));
    assert!(Executor::value_satisfies_constraints("abc", Some(3), &c));

    let mut c2 = cons();
    c2.forbidden.push("ab".to_string());
    assert!(!Executor::value_satisfies_constraints("xaby", Some(4), &c2));
    assert!(Executor::value_satisfies_constraints("xayb", Some(4), &c2));
}

/// The default pad character IS the needle here, so the pre-existing uniform
/// fill would build a value the gates must retract. Closure 6 widens the
/// candidate fill search, and every candidate is still accepted only through
/// `value_satisfies_constraints`.
#[test]
fn build_witness_avoids_a_forbidden_pad_character() {
    let mut c = cons();
    c.forbidden.push(FILL_CHAR.to_string());
    let w = Executor::build_witness(4, &c).expect("witness avoiding the pad char");
    assert_eq!(w.chars().count(), 4);
    assert!(
        !w.contains(FILL_CHAR),
        "constructed witness must avoid the forbidden needle, got {w:?}"
    );
    assert!(Executor::value_satisfies_constraints(&w, Some(4), &c));
}

/// A forbidden needle that no uniform fill can dodge (it is not a repetition
/// of one character) must NOT fabricate an answer: the pre-existing pad path
/// runs and the strict substitution re-validation stays the gate.
#[test]
fn build_witness_falls_through_when_no_uniform_fill_works() {
    let mut c = cons();
    c.forbidden.push("ab".to_string());
    c.forced.insert(0, 'a');
    c.forced.insert(1, 'b');
    let w = Executor::build_witness(3, &c).expect("fallback witness");
    assert_eq!(w.chars().count(), 3);
    // The forced pins make every candidate violate the constraint; the
    // materializer returns the pad value and lets the gate reject it.
    assert!(!Executor::value_satisfies_constraints(&w, Some(3), &c));
}
