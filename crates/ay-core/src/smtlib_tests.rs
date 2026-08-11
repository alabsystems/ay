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
    // Z3 5.0.0 quoted-symbol escapes preserve both characters losslessly.
    assert_eq!(quote_symbol("a|b"), r"|a\|b|");
    assert_eq!(quote_symbol(r"a\b"), r"|a\\b|");
    assert_eq!(quote_symbol(r"a|b\c|d"), r"|a\|b\\c\|d|");
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
        unescape_string_contents(&escape_string_contents("α\tπ中")).unwrap(),
        "α\tπ中"
    );
}

/// `escape_string_contents` must be an exact left inverse of
/// `unescape_string_contents`: `get-value` prints a TERM, and per SMT-LIB 2.6
/// §3.9.2 that term must denote the model value. Printing a literal that
/// re-reads as a different String element is a wrong-value defect even when no
/// sat/unsat verdict moves, because every consumer of the model is misled.
///
/// This pins the SEMANTICS (decode(encode(v)) == v) rather than any particular
/// spelling, over a corpus that covers each branch of the printer.
#[test]
fn escape_string_contents_round_trips_exactly() {
    let corpus = [
        "",
        "hello",
        r"path\to\file",
        r#"both \"#,
        r#"say "hi""#,
        // The A8 witness: six code points `\ u { 6 1 }`. Printing them verbatim
        // yields `\u{61}`, which re-reads as the SINGLE character `a`.
        r"\u{61}",
        r"\u{5c}",
        r"\u{5c}u{61}",
        "a\\u0041b",
        r"\u{2ffff}",
        // Not escapes, so the backslash stays literal on the way out too.
        r"\u{}",
        r"\u{ZZZZ}",
        r"\u{41",
        r"\uZZZZ",
        r"\u",
        r"\n",
        r"\\u{41}",
        "\u{0}\t\u{3b1}\u{4e2d}\u{1f600}\u{2ffff}",
        // Above the theory alphabet: `\u{30000}` is not an escape at all, so the
        // code point must be written raw or the round-trip loses it.
        "\u{30000}",
        "x\u{10ffff}y",
        "\u{30000}\\u{41}",
    ];
    for original in corpus {
        let printed = escape_string_contents(original);
        let decoded = unescape_string_contents(&printed).unwrap_or_else(|e| {
            panic!("{original:?} printed as {printed:?} failed to decode: {e}")
        });
        assert_eq!(
            decoded, original,
            "round-trip lost {original:?} (printed as {printed:?})"
        );
        // The character count is what str.len reports; pin it independently so a
        // future regression cannot pass by coincidence of byte equality.
        assert_eq!(decoded.chars().count(), original.chars().count());
    }
}

/// The specific spellings the round-trip relies on, so the intent is readable.
#[test]
fn escape_string_contents_escapes_a_reabsorbable_backslash() {
    // A backslash that WOULD start a well-formed, in-alphabet escape is written
    // as `\u{5c}` (z3 does the same); one that would not stays literal.
    assert_eq!(escape_string_contents(r"\u{61}"), r"\u{5c}u{61}");
    assert_eq!(escape_string_contents("\\u0041"), "\\u{5c}u0041");
    assert_eq!(escape_string_contents(r"path\to\file"), r"path\to\file");
    assert_eq!(escape_string_contents(r"\u{}"), r"\u{}");
    assert_eq!(escape_string_contents(r"\u{FFFFF}"), r"\u{FFFFF}");
}

/// Code points above `SMTLIB_MAX_CODE_POINT` have no `\u` spelling at all — a
/// `\u{30000}` form is nine literal characters to a conformant reader — so they
/// are emitted raw, which does round-trip.
#[test]
fn escape_string_contents_does_not_fake_an_out_of_alphabet_escape() {
    assert_eq!(escape_string_contents("\u{30000}"), "\u{30000}");
    assert!(!escape_string_contents("\u{30000}").contains(r"\u"));
    // The last in-alphabet code point still escapes.
    assert_eq!(escape_string_contents("\u{2ffff}"), r"\u{2ffff}");
}

#[test]
fn test_string_literal() {
    assert_eq!(string_literal("hello"), "\"hello\"");
    assert_eq!(string_literal(""), "\"\"");
    assert_eq!(string_literal(r#"say "hi""#), r#""say ""hi""""#);
}

#[test]
fn test_unescape_string_contents() {
    assert_eq!(unescape_string_contents("hello").unwrap(), "hello");
    assert_eq!(unescape_string_contents("").unwrap(), "");
    // SMT-LIB 2.6 standard: "" -> "
    assert_eq!(
        unescape_string_contents(r#"say ""hi"""#).unwrap(),
        r#"say "hi""#
    );
    // SMT-LIB 2.6: backslash is LITERAL (no C-style escapes). `\\` stays two
    // backslashes and `\"` stays backslash+quote — matching z3. Decoding `\\`
    // to a single `\` was a soundness bug on str.len/membership.
    assert_eq!(
        unescape_string_contents(r#"say \"hi\""#).unwrap(),
        r#"say \"hi\""#
    );
    assert_eq!(
        unescape_string_contents(r"path\\to\\file").unwrap(),
        r"path\\to\\file"
    );
    // A backslash followed by a non-`u` character is literal backslash + char.
    assert_eq!(unescape_string_contents(r"\n").unwrap(), "\\n");
}

#[test]
fn test_unescape_unicode_braced() {
    // \u{41} = 'A'
    assert_eq!(unescape_string_contents(r"\u{41}").unwrap(), "A");
    // \u{1F600} = 😀 (emoji, outside BMP)
    assert_eq!(unescape_string_contents(r"\u{1F600}").unwrap(), "😀");
    // \u{E9} = é (Latin small e with acute)
    assert_eq!(unescape_string_contents(r"\u{E9}").unwrap(), "é");
    // Single digit
    assert_eq!(unescape_string_contents(r"\u{A}").unwrap(), "\n"); // U+000A = newline
                                                                   // Embedded in larger string
    assert_eq!(
        unescape_string_contents(r"hello \u{1F600} world").unwrap(),
        "hello 😀 world"
    );
}

#[test]
fn test_unescape_unicode_four_digit() {
    // \u0041 = 'A'
    assert_eq!(unescape_string_contents(r"\u0041").unwrap(), "A");
    // \u00E9 = é
    assert_eq!(unescape_string_contents(r"\u00E9").unwrap(), "é");
    // Embedded
    assert_eq!(unescape_string_contents(r"a\u0042c").unwrap(), "aBc");
}

#[test]
fn test_unescape_unicode_malformed() {
    // A `\u` form that is not a well-formed, in-alphabet escape is NOT an
    // escape sequence: per SMT-LIB 2.6 every one of its characters is literal
    // and nothing is consumed. The previous behaviour consumed the characters
    // it had already scanned before discovering the form was malformed, which
    // SHORTENED the decoded string and flipped str.len/membership verdicts.
    // Each expectation below is pinned to z3 5.0.0 via `(simplify (str.len …))`.
    assert_eq!(unescape_string_contents(r"\u{}").unwrap(), r"\u{}");
    assert_eq!(unescape_string_contents(r"\u{ZZZZ}").unwrap(), r"\u{ZZZZ}");
    assert_eq!(unescape_string_contents(r"\u00").unwrap(), r"\u00");
    assert_eq!(unescape_string_contents(r"\u{41").unwrap(), r"\u{41");
    assert_eq!(unescape_string_contents(r"\u{{41}").unwrap(), r"\u{{41}");
    assert_eq!(unescape_string_contents(r"\uZZZZ").unwrap(), r"\uZZZZ");
    assert_eq!(unescape_string_contents(r"\u").unwrap(), r"\u");
}

/// The SMT-LIB 2.6 alphabet is `0x00000..=0x2FFFF`. A `\u` form denoting a
/// value outside it is not an escape, so its characters are literal.
///
/// Accepting an out-of-alphabet value collapsed many characters into one and
/// was a live wrong-verdict defect: `(str.len "\u{FFFFF}")` evaluated to 1
/// where z3 gives 9, so `(assert (= (str.len x) 9))` returned a WRONG `unsat`.
#[test]
fn test_unescape_unicode_out_of_alphabet_is_literal() {
    // Boundary: 0x2FFFF is the last legal code point, 0x30000 the first illegal.
    assert_eq!(
        unescape_string_contents(r"\u{2FFFF}")
            .unwrap()
            .chars()
            .count(),
        1
    );
    assert_eq!(
        unescape_string_contents(r"\u{30000}").unwrap(),
        r"\u{30000}"
    );
    assert_eq!(
        unescape_string_contents(r"\u{FFFFF}").unwrap(),
        r"\u{FFFFF}"
    );
    // Six hex digits is never an escape, even when the value is in-alphabet.
    assert_eq!(
        unescape_string_contents(r"\u{02FFFF}").unwrap(),
        r"\u{02FFFF}"
    );
    assert_eq!(
        unescape_string_contents(r"\u{100000}").unwrap(),
        r"\u{100000}"
    );
    // Five digits with leading zeros is fine when the value is in range.
    assert_eq!(unescape_string_contents(r"\u{00041}").unwrap(), "A");
}

/// Surrogate code points are legal SMT-LIB characters but are not Unicode
/// scalar values, so they cannot be held in a Rust `String`. Decoding fails
/// closed instead of substituting or dropping — both would change `str.len`.
#[test]
fn test_unescape_surrogate_fails_closed() {
    for src in [r"\u{D800}", r"\u{DFFF}", r"\u{0D800}", r"\uD800"] {
        let err =
            unescape_string_contents(src).expect_err("surrogate literal must not decode silently");
        assert!(
            matches!(err, StringDecodeError::SurrogateCodePoint(_)),
            "unexpected error for {src:?}: {err:?}"
        );
    }
    // Just outside the surrogate range still decodes normally.
    assert_eq!(
        unescape_string_contents(r"\u{E000}")
            .unwrap()
            .chars()
            .count(),
        1
    );
}

/// Table-driven pin of the whole `\u` grammar against z3 5.0.0.
///
/// Every expected length here was measured with
/// `(set-logic QF_S) (simplify (str.len "<literal>"))` on z3 5.0.0; ay
/// disagreed with z3 on 10 of these 16 before the decoder was corrected.
#[test]
fn test_unescape_matches_z3_lengths() {
    // (literal contents, z3's str.len, or None if ay must fail closed)
    let cases: &[(&str, Option<usize>)] = &[
        (r"\u{41}", Some(1)),
        (r"\u{2FFFF}", Some(1)),
        (r"\u{30000}", Some(9)),
        (r"\u{FFFFF}", Some(9)),
        (r"\u{100000}", Some(10)),
        (r"\u{}", Some(4)),
        (r"\u{41", Some(5)),
        (r"\u{{41}", Some(7)),
        (r"A", Some(1)),
        (r"\u00", Some(4)),
        (r"\uZZZZ", Some(6)),
        (r"\u{ZZZZ}", Some(8)),
        (r"\u", Some(2)),
        (r"\\", Some(2)),
        (r"\t", Some(2)),
        (r"\u{1F600}", Some(1)),
        // Legal SMT-LIB, unrepresentable as a Rust char: must fail closed.
        (r"\u{D800}", None),
        (r"\uD800", None),
    ];
    for (src, expected) in cases {
        match (unescape_string_contents(src), expected) {
            (Ok(decoded), Some(want)) => assert_eq!(
                decoded.chars().count(),
                *want,
                "str.len mismatch vs z3 for {src:?}: decoded {decoded:?}"
            ),
            (Err(err), None) => {
                assert!(matches!(err, StringDecodeError::SurrogateCodePoint(_)));
            }
            (Ok(decoded), None) => {
                panic!("{src:?} must fail closed, decoded {decoded:?} instead")
            }
            (Err(err), Some(want)) => {
                panic!("{src:?} must decode to {want} chars, failed with {err}")
            }
        }
    }
}

#[test]
fn test_round_trip() {
    let test_cases = vec!["hello", "", r#"say "hi""#, r"path\to\file", "line1\nline2"];
    for s in test_cases {
        let escaped = escape_string_contents(s);
        let unescaped = unescape_string_contents(&escaped).unwrap();
        assert_eq!(unescaped, s, "Round-trip failed for: {s:?}");
    }
}
