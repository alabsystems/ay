// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB surface syntax helpers
//!
//! This module provides functions for printing SMT-LIB compatible output.
//! All AY crates that emit SMT-LIB text should use these helpers to ensure
//! that output is syntactically valid and round-trips through the parser.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// Quote a symbol if it cannot be written as a simple (unquoted) SMT-LIB symbol.
///
/// Returns the symbol wrapped in `|...|` if any of the following hold:
/// - The symbol is empty
/// - The symbol starts with a digit
/// - The symbol is a reserved word (`true`, `false`, keywords, etc.)
/// - The symbol contains characters not allowed in simple symbols
///
/// SMT-LIB quoted symbols cannot contain `|` or `\`. These characters are
/// sanitized to `_` before quoting to ensure valid output (#1841).
///
/// # Examples
/// ```
/// use ay_core::quote_symbol;
///
/// assert_eq!(quote_symbol("x"), "x");
/// assert_eq!(quote_symbol("myVar"), "myVar");
/// assert_eq!(quote_symbol("let"), "|let|");
/// assert_eq!(quote_symbol("123abc"), "|123abc|");
/// assert_eq!(quote_symbol("x y"), "|x y|");
/// assert_eq!(quote_symbol("foo::bar"), "|foo::bar|");
/// assert_eq!(quote_symbol("true"), "|true|");
/// assert_eq!(quote_symbol("false"), "|false|");
/// // Characters invalid in quoted symbols are sanitized
/// assert_eq!(quote_symbol("a|b"), "|a_b|");
/// assert_eq!(quote_symbol(r"a\b"), "|a_b|");
/// ```
pub fn quote_symbol(name: &str) -> String {
    // Reserved words in SMT-LIB that need quoting
    // This includes:
    // - `true` and `false` (dedicated tokens in the lexer)
    // - Core keywords and command names
    const RESERVED: &[&str] = &[
        // Boolean literals (lexer tokens)
        "true",
        "false",
        // Binding keywords
        "let",
        "forall",
        "exists",
        "match",
        "par",
        "_",
        "!",
        "as",
        // Spec constants
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "STRING",
        // Commands
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "define-fun",
        "define-fun-rec",
        "define-funs-rec",
        "define-sort",
        "echo",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option",
    ];

    let needs_quoting = name.is_empty()
        || name.starts_with(|c: char| c.is_ascii_digit())
        || RESERVED.contains(&name)
        || name.contains(|c: char| !is_symbol_char(c));

    if needs_quoting {
        // SMT-LIB quoted symbols cannot contain '|' or '\' (#1841).
        // Sanitize these characters to '_' before quoting.
        let sanitized: String = name
            .chars()
            .map(|c| if c == '|' || c == '\\' { '_' } else { c })
            .collect();
        format!("|{sanitized}|")
    } else {
        name.to_string()
    }
}

/// Check if a character is valid in an unquoted SMT-LIB symbol.
///
/// This matches the AY lexer's `Token::Symbol` regex:
/// `[a-zA-Z~!@$%^&*_+=<>.?/\-][a-zA-Z0-9~!@$%^&*_+=<>.?/\-]*`
///
/// Note: The first character has additional restrictions (cannot be a digit),
/// which is handled separately in `quote_symbol`.
pub(crate) fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '+' | '-'
                | '/'
                | '*'
                | '='
                | '%'
                | '?'
                | '!'
                | '.'
                | '$'
                | '_'
                | '~'
                | '&'
                | '^'
                | '<'
                | '>'
                | '@'
        )
}

/// Escape a string's contents for SMT-LIB 2.6 output, matching z3's convention.
///
/// SMT-LIB 2.6 string literals are sequences of Unicode code points. Only
/// printable ASCII (`0x20..=0x7E`) prints literally, with `"` doubled to `""`.
/// Backslash (`0x5C`) is a printable ASCII character and prints literally (it is
/// NOT an escape character in the standard). Every other code point — control
/// characters and all non-ASCII (BMP and astral, up to `0x2FFFF`) — is emitted
/// as a `\u{X}` escape, where `X` is the LOWERCASE, minimal-digit hex code
/// point (e.g. U+03B1 -> `\u{3b1}`, U+0009 -> `\u{9}`, U+1F600 -> `\u{1f600}`).
/// This matches z3's `(get-value)` output so the printed literal round-trips
/// through a strict SMT-LIB reader (z3 and ay's own parser).
///
/// # Examples
/// ```
/// use ay_core::escape_string_contents;
///
/// assert_eq!(escape_string_contents("hello"), "hello");
/// assert_eq!(escape_string_contents(r#"say "hi""#), r#"say ""hi"""#);
/// assert_eq!(escape_string_contents(r"path\to\file"), r"path\to\file");
/// assert_eq!(escape_string_contents("\u{03b1}"), r"\u{3b1}");
/// assert_eq!(escape_string_contents("\t"), r"\u{9}");
/// assert_eq!(escape_string_contents("\u{1f600}"), r"\u{1f600}");
/// ```
pub fn escape_string_contents(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\"\""),
            c if ('\u{20}'..='\u{7e}').contains(&c) => result.push(c),
            c => result.push_str(&format!("\\u{{{:x}}}", c as u32)),
        }
    }
    result
}

/// Format a string value as an SMT-LIB 2.6 string literal.
///
/// This escapes the contents and wraps them in double quotes.
/// Uses `""` for literal quotes per SMT-LIB 2.6 standard.
///
/// # Examples
/// ```
/// use ay_core::string_literal;
///
/// assert_eq!(string_literal("hello"), "\"hello\"");
/// assert_eq!(string_literal(r#"say "hi""#), r#""say ""hi""""#);
/// ```
pub fn string_literal(s: &str) -> String {
    format!("\"{}\"", escape_string_contents(s))
}

/// Unescape an SMT-LIB string literal's contents.
///
/// SMT-LIB 2.6 conformant: the only escapes are `""` -> `"` and the unicode
/// forms `\u{XXXX}` / `\uXXXX`. A backslash is otherwise a LITERAL character
/// (so `\\` is two backslashes, `\t` is backslash+`t`), matching z3 — decoding
/// `\\` as a single `\` flips `str.len`/membership verdicts on such literals.
/// The input should be the contents without the surrounding quotes.
///
/// # Examples
/// ```
/// use ay_core::unescape_string_contents;
///
/// assert_eq!(unescape_string_contents("hello"), "hello");
/// assert_eq!(unescape_string_contents(r#"say ""hi"""#), r#"say "hi""#);
/// // Backslash is literal (SMT-LIB 2.6): `\\` stays two backslashes.
/// assert_eq!(unescape_string_contents(r"path\\to\\file"), r"path\\to\\file");
/// assert_eq!(unescape_string_contents(r"x\u{41}y"), "xAy");
/// ```
pub fn unescape_string_contents(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            // SMT-LIB 2.6: `""` inside string contents = literal `"`
            if chars.peek() == Some(&'"') {
                chars.next(); // consume second `"`
                result.push('"');
            } else {
                // Stray quote — should not happen in well-formed input
                result.push(c);
            }
        } else if c == '\\' {
            // SMT-LIB 2.6: a backslash is a LITERAL character EXCEPT in the two
            // unicode escapes `\u{XXXX}` / `\uXXXX`. It is NOT a C-style escape.
            // Collapsing `\\` -> `\` (or `\"` -> `"`) is a SOUNDNESS bug, not a
            // cosmetic one: z3 (correctly) reads `"a\\b"` as FOUR characters,
            // while the old behaviour read THREE, flipping every str.len- (and
            // membership-) sensitive verdict on any backslash-bearing literal.
            // `\t`/`\n`/etc. are already handled correctly (backslash + letter).
            if chars.peek() == Some(&'u') {
                chars.next(); // consume 'u'
                if let Some(ch) = parse_unicode_escape(&mut chars) {
                    result.push(ch);
                } else {
                    // Malformed unicode escape — emit the `\u` literally.
                    result.push('\\');
                    result.push('u');
                }
            } else {
                // Literal backslash; the following character is decoded normally
                // on the next iteration (so `\\` yields two literal backslashes).
                result.push('\\');
            }
        } else {
            result.push(c);
        }
    }
    result
}

/// Parse a unicode escape after `\u` has been consumed.
///
/// Supports two forms per SMT-LIB 2.6:
/// - `\u{XXXX}` — 1 to 6 hex digits in braces (any Unicode code point)
/// - `\uXXXX` — exactly 4 hex digits (BMP only)
fn parse_unicode_escape(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<char> {
    if chars.peek() == Some(&'{') {
        chars.next(); // consume '{'
        let mut hex = String::new();
        while let Some(&c) = chars.peek() {
            if c == '}' {
                chars.next(); // consume '}'
                break;
            }
            if c.is_ascii_hexdigit() && hex.len() < 6 {
                hex.push(c);
                chars.next();
            } else {
                return None;
            }
        }
        if hex.is_empty() {
            return None;
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        char::from_u32(code)
    } else {
        // \uXXXX — exactly 4 hex digits
        let mut hex = String::with_capacity(4);
        for _ in 0..4 {
            if let Some(&c) = chars.peek() {
                if c.is_ascii_hexdigit() {
                    hex.push(c);
                    chars.next();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        char::from_u32(code)
    }
}

#[cfg(test)]
#[path = "smtlib_tests.rs"]
mod tests;
