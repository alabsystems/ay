// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_quote_symbol_simple() {
    assert_eq!(quote_symbol("x"), "x");
    assert_eq!(quote_symbol("myVar"), "myVar");
    assert_eq!(quote_symbol("foo_bar"), "foo_bar");
    assert_eq!(quote_symbol("a1"), "a1");
    assert_eq!(quote_symbol("+"), "+");
    assert_eq!(quote_symbol("-"), "-");
    assert_eq!(quote_symbol("<="), "<=");
}

#[test]
fn test_quote_symbol_needs_quoting() {
    // Empty
    assert_eq!(quote_symbol(""), "||");
    // Starts with digit
    assert_eq!(quote_symbol("123abc"), "|123abc|");
    // Contains space
    assert_eq!(quote_symbol("x y"), "|x y|");
    // Contains colon (common in Rust names)
    assert_eq!(quote_symbol("foo::bar"), "|foo::bar|");
    // Contains pipe - sanitized to underscore (#1841)
    assert_eq!(quote_symbol("a|b"), "|a_b|");
    // Contains backslash - sanitized to underscore (#1841)
    assert_eq!(quote_symbol(r"a\b"), "|a_b|");
    // Multiple invalid chars
    assert_eq!(quote_symbol(r"a|b\c|d"), "|a_b_c_d|");
}

#[test]
fn test_quote_symbol_reserved() {
    assert_eq!(quote_symbol("true"), "|true|");
    assert_eq!(quote_symbol("false"), "|false|");
    assert_eq!(quote_symbol("let"), "|let|");
    assert_eq!(quote_symbol("forall"), "|forall|");
    assert_eq!(quote_symbol("exists"), "|exists|");
    assert_eq!(quote_symbol("assert"), "|assert|");
    assert_eq!(quote_symbol("check-sat"), "|check-sat|");
}

#[test]
fn test_is_symbol_char() {
    // Valid chars
    assert!(is_symbol_char('a'));
    assert!(is_symbol_char('Z'));
    assert!(is_symbol_char('0'));
    assert!(is_symbol_char('_'));
    assert!(is_symbol_char('+'));
    assert!(is_symbol_char('-'));
    assert!(is_symbol_char('?'));
    assert!(is_symbol_char('@'));

    // Invalid chars
    assert!(!is_symbol_char(' '));
    assert!(!is_symbol_char('('));
    assert!(!is_symbol_char(')'));
    assert!(!is_symbol_char(':'));
    assert!(!is_symbol_char('|'));
    assert!(!is_symbol_char('"'));
}

#[test]
fn test_escape_string_contents() {
    assert_eq!(escape_string_contents("hello"), "hello");
    assert_eq!(escape_string_contents(""), "");
    // SMT-LIB 2.6: quotes escaped as ""
    assert_eq!(escape_string_contents(r#"say "hi""#), r#"say ""hi"""#);
    // Backslashes are literal in SMT-LIB 2.6 (no escaping needed)
    assert_eq!(escape_string_contents(r"path\to\file"), r"path\to\file");
    assert_eq!(escape_string_contents(r#"both \"#), r#"both \"#);
    // Non-ASCII / non-printable code points escape as \u{X} (lowercase,
    // minimal digits), matching z3's (get-value) convention.
    assert_eq!(escape_string_contents("\u{03b1}"), r"\u{3b1}");
    assert_eq!(escape_string_contents("\u{03c0}"), r"\u{3c0}");
    assert_eq!(escape_string_contents("\u{4e2d}"), r"\u{4e2d}");
    assert_eq!(escape_string_contents("\t"), r"\u{9}");
    assert_eq!(escape_string_contents("\u{0}"), r"\u{0}");
    assert_eq!(escape_string_contents("\u{1f600}"), r"\u{1f600}");
    assert_eq!(escape_string_contents("\u{2ffff}"), r"\u{2ffff}");
    assert_eq!(escape_string_contents("a\u{03b1}b"), r"a\u{3b1}b");
    // Round-trips through the parser's unescape.
    assert_eq!(
        unescape_string_contents(&escape_string_contents("α\tπ中")),
        "α\tπ中"
    );
}

#[test]
fn test_string_literal() {
    assert_eq!(string_literal("hello"), "\"hello\"");
    assert_eq!(string_literal(""), "\"\"");
    assert_eq!(string_literal(r#"say "hi""#), r#""say ""hi""""#);
}

#[test]
fn test_unescape_string_contents() {
    assert_eq!(unescape_string_contents("hello"), "hello");
    assert_eq!(unescape_string_contents(""), "");
    // SMT-LIB 2.6 standard: "" -> "
    assert_eq!(unescape_string_contents(r#"say ""hi"""#), r#"say "hi""#);
    // SMT-LIB 2.6: backslash is LITERAL (no C-style escapes). `\\` stays two
    // backslashes and `\"` stays backslash+quote — matching z3. Decoding `\\`
    // to a single `\` was a soundness bug on str.len/membership.
    assert_eq!(unescape_string_contents(r#"say \"hi\""#), r#"say \"hi\""#);
    assert_eq!(
        unescape_string_contents(r"path\\to\\file"),
        r"path\\to\\file"
    );
    // A backslash followed by a non-`u` character is literal backslash + char.
    assert_eq!(unescape_string_contents(r"\n"), "\\n");
}

#[test]
fn test_unescape_unicode_braced() {
    // \u{41} = 'A'
    assert_eq!(unescape_string_contents(r"\u{41}"), "A");
    // \u{1F600} = 😀 (emoji, outside BMP)
    assert_eq!(unescape_string_contents(r"\u{1F600}"), "😀");
    // \u{E9} = é (Latin small e with acute)
    assert_eq!(unescape_string_contents(r"\u{E9}"), "é");
    // Single digit
    assert_eq!(unescape_string_contents(r"\u{A}"), "\n"); // U+000A = newline
                                                          // Embedded in larger string
    assert_eq!(
        unescape_string_contents(r"hello \u{1F600} world"),
        "hello 😀 world"
    );
}

#[test]
fn test_unescape_unicode_four_digit() {
    // \u0041 = 'A'
    assert_eq!(unescape_string_contents(r"\u0041"), "A");
    // \u00E9 = é
    assert_eq!(unescape_string_contents(r"\u00E9"), "é");
    // Embedded
    assert_eq!(unescape_string_contents(r"a\u0042c"), "aBc");
}

#[test]
fn test_unescape_unicode_malformed() {
    // Empty braces — \u emitted, braces consumed
    assert_eq!(unescape_string_contents(r"\u{}"), "\\u");
    // Non-hex in braces — \u emitted, { consumed, remaining chars pass through
    assert_eq!(unescape_string_contents(r"\u{ZZZZ}"), "\\uZZZZ}");
    // Too few digits for \uXXXX form — \u emitted, consumed digits lost
    assert_eq!(unescape_string_contents(r"\u00"), "\\u");
}

#[test]
fn test_round_trip() {
    let test_cases = vec!["hello", "", r#"say "hi""#, r"path\to\file", "line1\nline2"];
    for s in test_cases {
        let escaped = escape_string_contents(s);
        let unescaped = unescape_string_contents(&escaped);
        assert_eq!(unescaped, s, "Round-trip failed for: {s:?}");
    }
}
