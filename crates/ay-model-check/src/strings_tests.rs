// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the exact SMT-LIB string operations.
//!
//! Every expectation here was confirmed against z3 5.0.0 before being written
//! down: each was posed as `(assert (not (= <expr> <expected>)))` and z3
//! answered `unsat`, so these are the standard's answers rather than a reading
//! of it.

use num_bigint::BigInt;

use super::{eval, handles};
use crate::ModelValue;

fn s(v: &str) -> ModelValue {
    ModelValue::Str(v.to_string())
}

fn i(v: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(v))
}

#[track_caller]
fn str_of(name: &str, args: &[ModelValue]) -> String {
    match eval(name, args).unwrap() {
        ModelValue::Str(out) => out,
        other => panic!("{name} returned {other:?}, expected a string"),
    }
}

#[track_caller]
fn int_of(name: &str, args: &[ModelValue]) -> i64 {
    match eval(name, args).unwrap() {
        ModelValue::Int(out) => i64::try_from(out).unwrap(),
        other => panic!("{name} returned {other:?}, expected an integer"),
    }
}

#[track_caller]
fn bool_of(name: &str, args: &[ModelValue]) -> bool {
    match eval(name, args).unwrap() {
        ModelValue::Bool(out) => out,
        other => panic!("{name} returned {other:?}, expected a boolean"),
    }
}

/// `str.contains` takes the haystack FIRST and `str.prefixof` takes it SECOND.
/// Getting one of them backwards passes any test where both arguments happen to
/// be interchangeable, so both directions are pinned.
#[test]
fn the_subject_argument_differs_between_contains_and_prefixof() {
    assert!(bool_of("str.contains", &[s("abcde"), s("cd")]));
    assert!(!bool_of("str.contains", &[s("cd"), s("abcde")]));

    assert!(bool_of("str.prefixof", &[s("ab"), s("abcde")]));
    assert!(!bool_of("str.prefixof", &[s("abcde"), s("ab")]));

    assert!(bool_of("str.suffixof", &[s("de"), s("abcde")]));
    assert!(!bool_of("str.suffixof", &[s("abcde"), s("de")]));
}

#[test]
fn contains_prefixof_suffixof_edge_cases() {
    assert!(
        bool_of("str.contains", &[s("abc"), s("")]),
        "every string contains the empty one"
    );
    assert!(bool_of("str.contains", &[s(""), s("")]));
    assert!(!bool_of("str.contains", &[s(""), s("a")]));
    assert!(bool_of("str.contains", &[s("abc"), s("abc")]));
    assert!(bool_of("str.prefixof", &[s(""), s("abc")]));
    assert!(bool_of("str.suffixof", &[s(""), s("abc")]));
    assert!(bool_of("str.prefixof", &[s("abc"), s("abc")]));
}

#[test]
fn indexof_reports_the_first_occurrence_at_or_after_the_start() {
    assert_eq!(int_of("str.indexof", &[s("abcabc"), s("bc"), i(0)]), 1);
    assert_eq!(int_of("str.indexof", &[s("abcabc"), s("bc"), i(2)]), 4);
    assert_eq!(int_of("str.indexof", &[s("abc"), s("z"), i(0)]), -1);
    // An empty needle is found AT the start position, including at |s|.
    assert_eq!(int_of("str.indexof", &[s("abc"), s(""), i(2)]), 2);
    assert_eq!(int_of("str.indexof", &[s("abc"), s(""), i(3)]), 3);
    // A start outside `[0, |s|]` reports -1, on either side.
    assert_eq!(int_of("str.indexof", &[s("abc"), s(""), i(4)]), -1);
    assert_eq!(int_of("str.indexof", &[s("abc"), s("a"), i(-1)]), -1);
}

#[test]
fn substr_clamps_the_length_and_empties_out_of_range() {
    assert_eq!(str_of("str.substr", &[s("abcde"), i(1), i(3)]), "bcd");
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(3), i(99)]),
        "de",
        "length clamps"
    );
    assert_eq!(str_of("str.substr", &[s("abcde"), i(0), i(5)]), "abcde");
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(5), i(1)]),
        "",
        "start at |s|"
    );
    // PAST the end, not merely at it. The gate is documented total and
    // panic-free, and this is the input that slices out of range without the
    // guard — `start == |s|` alone does not reach it.
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(7), i(1)]),
        "",
        "start past |s|"
    );
    assert_eq!(
        str_of("str.substr", &[s(""), i(0), i(1)]),
        "",
        "empty subject"
    );
    assert_eq!(str_of("str.substr", &[s(""), i(1), i(1)]), "");
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(-1), i(2)]),
        "",
        "negative start"
    );
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(1), i(0)]),
        "",
        "zero length"
    );
    assert_eq!(
        str_of("str.substr", &[s("abcde"), i(1), i(-1)]),
        "",
        "negative length"
    );
    // A position too large for `usize` is still just out of range.
    let huge = ModelValue::Int(BigInt::from(1u64) << 100);
    assert_eq!(str_of("str.substr", &[s("abcde"), huge, i(2)]), "");
}

/// The empty needle behaves OPPOSITELY in the two replace operators, which is
/// the detail a shared implementation would get wrong for one of them.
#[test]
fn replace_and_replace_all_differ_on_an_empty_needle() {
    assert_eq!(
        str_of("str.replace", &[s("abcabc"), s("bc"), s("X")]),
        "aXabc"
    );
    assert_eq!(str_of("str.replace", &[s("abc"), s("z"), s("X")]), "abc");
    assert_eq!(
        str_of("str.replace", &[s("abc"), s(""), s("X")]),
        "Xabc",
        "the empty string occurs at position 0, so the replacement is prepended"
    );

    assert_eq!(
        str_of("str.replace_all", &[s("abcabc"), s("bc"), s("X")]),
        "aXaX"
    );
    assert_eq!(
        str_of("str.replace_all", &[s("abc"), s(""), s("X")]),
        "abc",
        "an empty needle leaves the string alone — and must not loop forever"
    );
    // Non-overlapping, left to right: "aaaa" with "aa" is two matches, not three.
    assert_eq!(
        str_of("str.replace_all", &[s("aaaa"), s("aa"), s("b")]),
        "bb"
    );
    assert_eq!(
        str_of("str.replace_all", &[s("aaa"), s("aa"), s("b")]),
        "ba"
    );
    assert_eq!(
        str_of("str.replace_all", &[s("abc"), s("z"), s("X")]),
        "abc"
    );
}

/// `str.to_int` is defined on NUMERALS: a non-empty run of digits. A leading
/// sign makes the string a non-numeral, so `"-1"` maps to `-1` for being
/// malformed — not because the value is negative.
#[test]
fn to_int_accepts_only_numerals() {
    assert_eq!(int_of("str.to_int", &[s("12")]), 12);
    assert_eq!(
        int_of("str.to_int", &[s("0012")]),
        12,
        "leading zeros are allowed"
    );
    assert_eq!(int_of("str.to_int", &[s("0")]), 0);
    assert_eq!(
        int_of("str.to_int", &[s("")]),
        -1,
        "the empty string is not a numeral"
    );
    assert_eq!(
        int_of("str.to_int", &[s("-1")]),
        -1,
        "a sign is not part of a numeral"
    );
    assert_eq!(int_of("str.to_int", &[s("1a")]), -1);
    assert_eq!(int_of("str.to_int", &[s(" 1")]), -1);
    // Arbitrary precision, not a machine integer.
    let big = "9".repeat(40);
    assert_eq!(
        eval("str.to_int", &[s(&big)]).unwrap().as_bool(),
        None,
        "sanity: it is an Int"
    );
    match eval("str.to_int", &[s(&big)]).unwrap() {
        ModelValue::Int(v) => assert_eq!(v, big.parse::<BigInt>().unwrap()),
        other => panic!("expected an integer, got {other:?}"),
    }
}

#[test]
fn from_int_is_empty_for_negatives() {
    assert_eq!(str_of("str.from_int", &[i(12)]), "12");
    assert_eq!(str_of("str.from_int", &[i(0)]), "0");
    assert_eq!(
        str_of("str.from_int", &[i(-5)]),
        "",
        "no representation for negatives"
    );
    // A round trip on a numeral.
    assert_eq!(
        int_of("str.to_int", &[s(&str_of("str.from_int", &[i(987)]))]),
        987
    );
}

#[test]
fn code_conversions() {
    assert_eq!(int_of("str.to_code", &[s("a")]), 97);
    assert_eq!(
        int_of("str.to_code", &[s("ab")]),
        -1,
        "only a single character"
    );
    assert_eq!(int_of("str.to_code", &[s("")]), -1);
    assert_eq!(str_of("str.from_code", &[i(97)]), "a");
    assert_eq!(str_of("str.from_code", &[i(-1)]), "", "out of the alphabet");
    assert_eq!(
        str_of("str.from_code", &[i(0x30000)]),
        "",
        "past the alphabet"
    );
    // A surrogate is IN the SMT-LIB alphabet but has no Rust `char`; refusing
    // beats substituting a different character.
    assert!(eval("str.from_code", &[i(0xd800)]).is_err());
    assert!(bool_of("str.is_digit", &[s("7")]));
    assert!(!bool_of("str.is_digit", &[s("77")]));
    assert!(!bool_of("str.is_digit", &[s("a")]));
    assert!(!bool_of("str.is_digit", &[s("")]));
}

#[test]
fn lexicographic_comparison_chains() {
    assert!(bool_of("str.<", &[s("abc"), s("abd")]));
    assert!(
        bool_of("str.<", &[s("ab"), s("abc")]),
        "a prefix is smaller"
    );
    assert!(!bool_of("str.<", &[s("abc"), s("abc")]));
    assert!(bool_of("str.<=", &[s("abc"), s("abc")]));
    assert!(
        bool_of("str.<", &[s("a"), s("b"), s("c")]),
        "chained over adjacent pairs"
    );
    assert!(!bool_of("str.<", &[s("a"), s("c"), s("b")]));
    assert!(bool_of("str.<", &[s(""), s("a")]));
}

/// Positions are CODE POINTS. Every operation that takes or returns one is
/// checked on a string whose characters are multi-byte, where a byte offset
/// would give a different — and wrong — answer.
#[test]
fn positions_are_code_points_not_bytes() {
    // "é" and "水" are 2 and 3 bytes in UTF-8, so byte and code-point offsets
    // diverge immediately.
    let text = "aé水bc";
    assert_eq!(str_of("str.substr", &[s(text), i(1), i(2)]), "é水");
    assert_eq!(str_of("str.substr", &[s(text), i(3), i(2)]), "bc");
    assert_eq!(int_of("str.indexof", &[s(text), s("b"), i(0)]), 3);
    assert_eq!(int_of("str.indexof", &[s(text), s("水"), i(0)]), 2);
    assert_eq!(int_of("str.indexof", &[s(text), s("水"), i(3)]), -1);
    assert!(bool_of("str.contains", &[s(text), s("é水")]));
    assert!(bool_of("str.prefixof", &[s("aé"), s(text)]));
    assert!(bool_of("str.suffixof", &[s("水bc"), s(text)]));
    assert_eq!(str_of("str.replace", &[s(text), s("水"), s("X")]), "aéXbc");
    assert_eq!(int_of("str.to_code", &[s("水")]), 0x6c34);
    assert_eq!(str_of("str.from_code", &[i(0x6c34)]), "水");
}

#[test]
fn wrong_shapes_are_refused_not_coerced() {
    assert!(eval("str.contains", &[s("a")]).is_err(), "wrong arity");
    assert!(eval("str.contains", &[s("a"), i(1)]).is_err(), "wrong sort");
    assert!(eval("str.substr", &[s("a"), s("b"), i(1)]).is_err());
    assert!(eval("str.no_such_op", &[s("a")]).is_err());
    assert!(!handles("str.no_such_op", 1));
    assert!(handles("str.contains", 2));
    assert!(!handles("str.contains", 3), "arity is part of the dispatch");
    assert!(handles("str.<", 5));
}

/// The two `find_at` contract points every caller leans on, checked directly
/// rather than only through the operators built on them.
#[test]
fn find_at_handles_an_empty_needle_and_a_start_past_the_end() {
    let haystack: Vec<char> = "abc".chars().collect();
    let empty: Vec<char> = Vec::new();
    for from in 0..=haystack.len() {
        assert_eq!(
            super::find_at(&haystack, &empty, from),
            Some(from),
            "an empty needle occurs at position {from}"
        );
    }
    assert_eq!(super::find_at(&haystack, &empty, 4), None, "past the end");
    assert_eq!(super::find_at(&haystack, &['b'], 4), None);
    assert_eq!(
        super::find_at(&haystack, &['b'], 2),
        None,
        "no occurrence at or after 2"
    );
    assert_eq!(super::find_at(&haystack, &['b'], 1), Some(1));
    // A needle longer than the haystack cannot occur, and must not underflow
    // the scan range.
    assert_eq!(super::find_at(&haystack, &['a', 'b', 'c', 'd'], 0), None);
    assert_eq!(super::find_at(&[], &empty, 0), Some(0));
    assert_eq!(super::find_at(&[], &['a'], 0), None);
}
