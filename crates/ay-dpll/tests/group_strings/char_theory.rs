// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Char theory: `(_ Char n)` / `(_ char #xNN)` literals and `char.to_int`,
//! `char.<=`, `char.is_digit`. SMT-LIB models a Char as a Unicode code point,
//! which AY represents as that bounded Int, so each operator desugars to Int
//! arithmetic. Every expected verdict below matches z3 4.15.4.

fn solve(smt: &str) -> String {
    crate::common::solve(smt)
}

#[test]
fn char_to_int_of_literal_is_the_code_point() {
    // (_ Char 97) = 'a', code point 97.
    assert_eq!(
        solve("(set-logic ALL)\n(assert (= (char.to_int (_ Char 97)) 97))\n(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (= (char.to_int (_ Char 97)) 42))\n(check-sat)"),
        "unsat"
    );
}

#[test]
fn char_le_is_code_point_order() {
    assert_eq!(
        solve("(set-logic ALL)\n(assert (char.<= (_ Char 97) (_ Char 98)))\n(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (char.<= (_ Char 98) (_ Char 97)))\n(check-sat)"),
        "unsat"
    );
}

#[test]
fn char_is_digit_checks_the_ascii_digit_range() {
    // '0' (48) .. '9' (57).
    assert_eq!(
        solve("(set-logic ALL)\n(assert (char.is_digit (_ Char 48)))\n(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (char.is_digit (_ Char 57)))\n(check-sat)"),
        "sat"
    );
    // 'a' (97) is not a digit.
    assert_eq!(
        solve("(set-logic ALL)\n(assert (char.is_digit (_ Char 97)))\n(check-sat)"),
        "unsat"
    );
}

#[test]
fn hex_char_literal_form_parses() {
    // z3's `(_ char #x61)` == code point 0x61 = 97; the parser must keep the
    // `#x61` index (it once mangled the name to `(_ char )`).
    assert_eq!(
        solve("(set-logic ALL)\n(assert (= (char.to_int (_ char #x61)) 97))\n(check-sat)"),
        "sat"
    );
}
