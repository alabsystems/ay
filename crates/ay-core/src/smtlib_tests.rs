// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smtlib_char::{smtlib_char_cmp, smtlib_next_char, smtlib_str_cmp};

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
fn test_quote_symbol_signed_numbers() {
    // Carcara and Clean lex these as numerals, so they are quoted.
    for name in ["-1", "+1", "-0", "-1.5", "-1a", "-1e3", "-.5", "+.5"] {
        assert_eq!(quote_symbol(name), format!("|{name}|"), "{name}");
    }
    // A sign that does not begin a number stays a plain symbol.
    for name in ["-", "+", "-a", "+x", "-.", "-.a", "->", "--1"] {
        assert_eq!(quote_symbol(name), name, "{name}");
    }
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
    for reserved in [
        "choice",
        "lambda",
        "cl",
        "assume",
        "step",
        "anchor",
        "declare-rare-rule",
    ] {
        assert_eq!(quote_symbol(reserved), format!("|{reserved}|"));
    }
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
        let decoded = unescape_string_contents(&printed);
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
    // A `\u` form that is not a well-formed, in-alphabet escape is NOT an
    // escape sequence: per SMT-LIB 2.6 every one of its characters is literal
    // and nothing is consumed. The previous behaviour consumed the characters
    // it had already scanned before discovering the form was malformed, which
    // SHORTENED the decoded string and flipped str.len/membership verdicts.
    // Each expectation below is pinned to z3 5.0.0 via `(simplify (str.len …))`.
    assert_eq!(unescape_string_contents(r"\u{}"), r"\u{}");
    assert_eq!(unescape_string_contents(r"\u{ZZZZ}"), r"\u{ZZZZ}");
    assert_eq!(unescape_string_contents(r"\u00"), r"\u00");
    assert_eq!(unescape_string_contents(r"\u{41"), r"\u{41");
    assert_eq!(unescape_string_contents(r"\u{{41}"), r"\u{{41}");
    assert_eq!(unescape_string_contents(r"\uZZZZ"), r"\uZZZZ");
    assert_eq!(unescape_string_contents(r"\u"), r"\u");
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
    assert_eq!(unescape_string_contents(r"\u{2FFFF}").chars().count(), 1);
    assert_eq!(unescape_string_contents(r"\u{30000}"), r"\u{30000}");
    assert_eq!(unescape_string_contents(r"\u{FFFFF}"), r"\u{FFFFF}");
    // Six hex digits is never an escape, even when the value is in-alphabet.
    assert_eq!(unescape_string_contents(r"\u{02FFFF}"), r"\u{02FFFF}");
    assert_eq!(unescape_string_contents(r"\u{100000}"), r"\u{100000}");
    // Five digits with leading zeros is fine when the value is in range.
    assert_eq!(unescape_string_contents(r"\u{00041}"), "A");
}

/// Surrogate code points are SMT-LIB characters (the alphabet is every code
/// point `0..=0x2FFFF`), so each escape decodes to exactly ONE character — held
/// by its carrier — whose code point reads back unchanged. The earlier reader
/// refused these literals with a parse error, which z3 does not.
#[test]
fn test_unescape_surrogate_is_one_character() {
    for (src, code) in [
        (r"\u{D800}", 0xD800),
        (r"\u{DFFF}", 0xDFFF),
        (r"\u{0D800}", 0xD800),
        (r"\uD800", 0xD800),
        (r"\u{dabc}", 0xDABC),
    ] {
        let decoded = unescape_string_contents(src);
        let chars: Vec<char> = decoded.chars().collect();
        assert_eq!(chars.len(), 1, "{src:?} must be one character");
        assert_eq!(smtlib_code_point(chars[0]), code, "{src:?}");
        // And it prints back as the same escape, so get-value round-trips.
        assert_eq!(escape_string_contents(&decoded), format!("\\u{{{code:x}}}"));
    }
    // Just outside the surrogate range still decodes to the scalar itself.
    assert_eq!(unescape_string_contents(r"\u{E000}"), "\u{E000}");
    assert_eq!(unescape_string_contents(r"\u{D7FF}"), "\u{D7FF}");
}

/// The carrier is an exact, order-aware encoding of the whole alphabet.
#[test]
fn smtlib_char_is_a_bijection_on_the_alphabet() {
    let mut previous: Option<char> = None;
    for code in 0..=SMTLIB_MAX_CODE_POINT {
        let c = smtlib_char(code).expect("every in-alphabet code point has a char");
        assert_eq!(smtlib_code_point(c), code);
        if let Some(p) = previous {
            assert_eq!(smtlib_next_char(p), Some(c), "successor of {:x}", code - 1);
            assert_eq!(smtlib_char_cmp(p, c), core::cmp::Ordering::Less);
        }
        previous = Some(c);
    }
    assert_eq!(
        smtlib_next_char(previous.expect("alphabet is non-empty")),
        None
    );
    assert_eq!(smtlib_char(SMTLIB_MAX_CODE_POINT + 1), None);
    // Non-surrogates are stored as themselves.
    assert_eq!(smtlib_char(0xD7FF), Some('\u{D7FF}'));
    assert_eq!(smtlib_char(0xE000), Some('\u{E000}'));
    assert_eq!(smtlib_char(0x1F600), Some('\u{1F600}'));
    // Raw characters above the alphabet keep their scalar value.
    assert_eq!(smtlib_code_point('\u{30000}'), 0x30000);
    assert_eq!(smtlib_code_point('\u{10FFFF}'), 0x10FFFF);
}

/// The carrier block is exactly the 2,048 `char`s that hold surrogates, and
/// raw input is checked for it before unescaping, so an escape (ASCII text)
/// never trips the check. (2026-09-28 fp-strings verifier: a raw U+10D800
/// read back as U+D800.)
#[test]
fn surrogate_carriers_are_exactly_the_reserved_block() {
    use crate::smtlib_char::{
        first_surrogate_carrier, is_surrogate_carrier, SMTLIB_SURROGATE_FIRST,
        SMTLIB_SURROGATE_LAST,
    };
    for code in SMTLIB_SURROGATE_FIRST..=SMTLIB_SURROGATE_LAST {
        let carrier = smtlib_char(code).expect("a surrogate has a carrier");
        assert!(is_surrogate_carrier(carrier), "{code:x}");
        assert_eq!(
            first_surrogate_carrier(&format!("ab{carrier}")),
            Some(carrier)
        );
    }
    for raw in [
        '\u{10D7FF}',
        '\u{10E000}',
        '\u{D7FF}',
        '\u{E000}',
        '\u{30000}',
        'a',
    ] {
        assert!(!is_surrogate_carrier(raw), "{raw:?}");
    }
    let carriers = (0..=0x10_FFFF_u32)
        .filter_map(char::from_u32)
        .filter(|&c| is_surrogate_carrier(c))
        .count();
    assert_eq!(carriers, 2048);
    assert_eq!(first_surrogate_carrier(r"\u{d800}\ud800\u{DFFF}"), None);
    assert_eq!(
        first_surrogate_carrier("x\u{10D800}y\u{10DFFF}"),
        Some('\u{10D800}')
    );
    assert_eq!(first_surrogate_carrier(""), None);
}

/// `str.<` is code-point order: a surrogate sits between U+D7FF and U+E000,
/// although its carrier `char` sorts above U+2FFFF.
#[test]
fn smtlib_str_cmp_orders_surrogates_by_code_point() {
    use core::cmp::Ordering::{Equal, Greater, Less};
    let d800 = unescape_string_contents(r"\u{d800}");
    assert_eq!(smtlib_str_cmp("\u{D7FF}", &d800), Less);
    assert_eq!(smtlib_str_cmp(&d800, "\u{E000}"), Less);
    assert_eq!(smtlib_str_cmp(&d800, "\u{2FFFF}"), Less);
    assert_eq!(smtlib_str_cmp(&d800, &d800), Equal);
    assert_eq!(smtlib_str_cmp(&format!("{d800}a"), &d800), Greater);
    assert_eq!(smtlib_str_cmp("", &d800), Less);
    assert_eq!(smtlib_str_cmp("abc", "abd"), Less);
}

/// Table-driven pin of the whole `\u` grammar against z3 5.0.0.
///
/// Every expected length here was measured with
/// `(set-logic QF_S) (simplify (str.len "<literal>"))` on z3 5.0.0; ay
/// disagreed with z3 on 10 of these 16 before the decoder was corrected.
#[test]
fn test_unescape_matches_z3_lengths() {
    // (literal contents, z3's str.len)
    let cases: &[(&str, usize)] = &[
        (r"\u{41}", 1),
        (r"\u{2FFFF}", 1),
        (r"\u{30000}", 9),
        (r"\u{FFFFF}", 9),
        (r"\u{100000}", 10),
        (r"\u{}", 4),
        (r"\u{41", 5),
        (r"\u{{41}", 7),
        (r"A", 1),
        (r"\u00", 4),
        (r"\uZZZZ", 6),
        (r"\u{ZZZZ}", 8),
        (r"\u", 2),
        (r"\\", 2),
        (r"\t", 2),
        (r"\u{1F600}", 1),
        // Surrogates are SMT-LIB characters: one each, as z3 5.1.0 reads them.
        (r"\u{D800}", 1),
        (r"\uD800", 1),
    ];
    for (src, expected) in cases {
        let decoded = unescape_string_contents(src);
        assert_eq!(
            decoded.chars().count(),
            *expected,
            "str.len mismatch vs z3 for {src:?}: decoded {decoded:?}"
        );
    }
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
