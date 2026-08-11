// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Z3 5.0.0 Char ground fragment: `(_ Char n)`, `char.to_int`, `char.<=`,
//! `char.is_digit`, `char.to_bv`, and `char.from_bv`.
//! SMT-LIB models a Char as a Unicode code point,
//! which AY represents as that bounded Int, so each operator desugars to Int
//! arithmetic or an exact 18-bit conversion. Every expected verdict below
//! matches Z3 5.0.0.

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
fn char_bitvector_conversions_use_the_exact_18_bit_code_point() {
    assert_eq!(
        solve("(set-logic ALL)\n(assert (= (char.to_bv (_ Char 65)) (_ bv65 18)))\n(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (distinct (char.to_bv (_ Char 65)) (_ bv65 18)))\n(check-sat)"),
        "unsat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (= (char.from_bv (_ bv65 18)) (_ Char 65)))\n(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve("(set-logic ALL)\n(assert (distinct (char.from_bv (_ bv65 18)) (_ Char 65)))\n(check-sat)"),
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
