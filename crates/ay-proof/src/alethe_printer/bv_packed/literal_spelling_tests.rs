// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::prints_alike;

#[test]
fn a_literal_is_forgiven_its_spelling_and_nothing_else() {
    let binary = "(= x (ite c #b00000111 #b00000000))";
    assert!(prints_alike("(= x (ite c (_ bv7 8) (_ bv0 8)))", binary));
    assert!(prints_alike("(= x (ite c #x07 (_ bv0 8)))", binary));
    assert!(prints_alike(binary, binary));
    // A different value, a different width, or any other text is not.
    assert!(!prints_alike("(= x (ite c (_ bv6 8) (_ bv0 8)))", binary));
    assert!(!prints_alike("(= x (ite c (_ bv7 16) (_ bv0 8)))", binary));
    assert!(!prints_alike("(= x (ite c #x0007 (_ bv0 8)))", binary));
    assert!(!prints_alike("(= y (ite c (_ bv7 8) (_ bv0 8)))", binary));
    assert!(!prints_alike("(= x (ite d (_ bv7 8) (_ bv0 8)))", binary));
}

#[test]
fn a_value_that_overflows_its_width_keeps_its_spelling() {
    // 256 needs nine bits: not a constant of width 8, so never `#b00000000`.
    assert!(!prints_alike("(= x (_ bv256 8))", "(= x #b00000000)"));
    assert!(!prints_alike("(= x (_ bv256 8))", "(= x #b100000000)"));
    assert!(!prints_alike("(= x (_ bv1 0))", "(= x #b1)"));
}

#[test]
fn only_a_whole_indexed_constant_is_read_as_a_literal() {
    // A quoted symbol or a string that spells a literal's characters is not a
    // literal, and neither is an indexed identifier with another name.
    assert!(!prints_alike("(= x |(_ bv1 8)|)", "(= x #b00000001)"));
    assert!(!prints_alike("((_ extract 0 0) x)", "(#b0 x)"));
    assert!(!prints_alike("(= x (_ bvx 8))", "(= x #b00000000)"));
    assert!(!prints_alike("(= s \"(_ bv1 8)\")", "(= s #b00000001)"));
    assert!(prints_alike("(= s \"a\"\"b\")", "(= s \"a\"\"b\")"));
    // An unterminated quote is not tokenized, so only exact text compares.
    assert!(!prints_alike("(= x |(_ bv1 8)", "(= x #b00000001"));
}

#[test]
fn a_wide_literal_is_spelled_at_its_own_width() {
    let one = format!("#b{}1", "0".repeat(127));
    assert!(prints_alike(
        "(concat (_ bv0 64) (_ bv1 64))",
        &format!("(concat #b{} #b{}1)", "0".repeat(64), "0".repeat(63))
    ));
    assert!(prints_alike(
        "(bvadd x (_ bv1 128))",
        &format!("(bvadd x {one})")
    ));
}
