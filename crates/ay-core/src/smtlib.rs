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

/// Largest code point in the SMT-LIB 2.6 Unicode Strings alphabet.
///
/// The theory fixes the alphabet at code points `0x00000..=0x2FFFF`. A `\u`
/// form denoting a value outside this range is NOT an escape sequence at all —
/// its characters are taken literally (see [`unescape_string_contents`]).
pub const SMTLIB_MAX_CODE_POINT: u32 = 0x2FFFF;

/// Why an SMT-LIB string literal could not be decoded into a Rust `String`.
///
/// Decoding fails closed rather than returning an approximate string: a decoded
/// string of the wrong length flips every `str.len`/membership verdict that
/// mentions it, which is a wrong-verdict (soundness) defect. An honest error is
/// strictly better than a confident wrong answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringDecodeError {
    /// A well-formed, in-alphabet escape denotes a Unicode *surrogate* code
    /// point (`U+D800..=U+DFFF`). These are legal SMT-LIB characters — the
    /// alphabet is defined over code points, which include surrogates — but
    /// Rust's `char`/`String` can only hold Unicode *scalar values*, so such a
    /// literal is not representable in this decoder's return type.
    SurrogateCodePoint(u32),
}

impl core::fmt::Display for StringDecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            StringDecodeError::SurrogateCodePoint(code) => write!(
                f,
                "SMT-LIB string literal denotes surrogate code point U+{code:04X}, \
                 which is not representable as a Rust char"
            ),
        }
    }
}

impl std::error::Error for StringDecodeError {}

/// Unescape an SMT-LIB string literal's contents.
///
/// SMT-LIB 2.6 conformant: the only escapes are `""` -> `"` and the unicode
/// forms `\u{d...}` / `\udddd`. A backslash is otherwise a LITERAL character
/// (so `\\` is two backslashes, `\t` is backslash+`t`), matching z3 — decoding
/// `\\` as a single `\` flips `str.len`/membership verdicts on such literals.
/// The input should be the contents without the surrounding quotes.
///
/// A `\u` form that is not a well-formed, in-alphabet escape is NOT an escape:
/// every one of its characters is literal and NOTHING is consumed. This matters
/// for soundness — see [`parse_unicode_escape`] for the exact grammar and for
/// the verdict-flipping failure mode that consuming-on-failure produced.
///
/// # Examples
/// ```
/// use ay_core::unescape_string_contents;
///
/// assert_eq!(unescape_string_contents("hello").unwrap(), "hello");
/// assert_eq!(unescape_string_contents(r#"say ""hi"""#).unwrap(), r#"say "hi""#);
/// // Backslash is literal (SMT-LIB 2.6): `\\` stays two backslashes.
/// assert_eq!(unescape_string_contents(r"path\\to\\file").unwrap(), r"path\\to\\file");
/// assert_eq!(unescape_string_contents(r"x\u{41}y").unwrap(), "xAy");
/// // Out-of-alphabet: `\u{FFFFF}` is not an escape, so it is nine characters.
/// assert_eq!(unescape_string_contents(r"\u{FFFFF}").unwrap().chars().count(), 9);
/// ```
pub fn unescape_string_contents(s: &str) -> Result<String, StringDecodeError> {
    let chars: Vec<char> = s.chars().collect();
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '"' {
            // SMT-LIB 2.6: `""` inside string contents = literal `"`. A stray
            // quote should not occur in well-formed input; pass it through.
            result.push('"');
            i += if chars.get(i + 1) == Some(&'"') { 2 } else { 1 };
        } else if c == '\\' {
            // SMT-LIB 2.6: a backslash is a LITERAL character EXCEPT in the two
            // unicode escapes. It is NOT a C-style escape. Collapsing `\\` ->
            // `\` (or `\"` -> `"`) is a SOUNDNESS bug, not a cosmetic one: z3
            // (correctly) reads `"a\\b"` as FOUR characters, while the old
            // behaviour read THREE, flipping every str.len- (and membership-)
            // sensitive verdict on any backslash-bearing literal.
            match parse_unicode_escape(&chars, i + 1) {
                Some((code, next)) => {
                    // In-alphabet by construction, so the only value `char`
                    // cannot represent is a surrogate. Fail closed rather than
                    // substituting a replacement character or dropping it:
                    // either would silently change the string's length.
                    let ch =
                        char::from_u32(code).ok_or(StringDecodeError::SurrogateCodePoint(code))?;
                    result.push(ch);
                    i = next;
                }
                None => {
                    // Not an escape: the backslash is literal and the following
                    // characters are decoded normally on later iterations.
                    result.push('\\');
                    i += 1;
                }
            }
        } else {
            result.push(c);
            i += 1;
        }
    }
    Ok(result)
}

/// Try to parse an SMT-LIB 2.6 unicode escape whose `u` sits at `start` (i.e.
/// the index just after the backslash).
///
/// Returns the denoted code point and the index just past the escape, or `None`
/// if the text at `start` is not an escape — in which case NOTHING is consumed
/// and the backslash is an ordinary character.
///
/// SMT-LIB 2.6 defines exactly two forms:
/// - `\udddd` — EXACTLY 4 hex digits
/// - `\u{d}` .. `\u{ddddd}` — 1 to 5 hex digits enclosed in braces
///
/// and in both the denoted value must lie in the alphabet
/// zero up to [`SMTLIB_MAX_CODE_POINT`]. Anything else — 6+ digits, out-of-range
/// value, a missing `}`, a non-hex character, end of input — is not an escape
/// sequence, and the standard requires its characters be taken literally.
///
/// This is soundness-critical in two independent ways, both of which were live
/// wrong-verdict defects that this function's previous version exhibited:
/// 1. Accepting an out-of-alphabet value (`\u{FFFFF}`, `\u{100000}`) or an
///    unterminated brace (`\u{41`) decodes many characters as one, so `str.len`
///    reports 1 where z3 reports 9, 10 and 5 respectively.
/// 2. Consuming input before discovering the escape is malformed silently DROPS
///    those characters (`\u{}` decoded to `\u`, losing the braces), again
///    shortening the string. Returning an index means failure consumes nothing.
fn parse_unicode_escape(chars: &[char], start: usize) -> Option<(u32, usize)> {
    if chars.get(start) != Some(&'u') {
        return None;
    }
    let after_u = start + 1;

    if chars.get(after_u) == Some(&'{') {
        let mut hex = String::with_capacity(5);
        let mut j = after_u + 1;
        loop {
            let &c = chars.get(j)?; // end of input before `}` — not an escape
            if c == '}' {
                break;
            }
            if !c.is_ascii_hexdigit() || hex.len() == 5 {
                // Non-hex, or a 6th digit: not an escape sequence.
                return None;
            }
            hex.push(c);
            j += 1;
        }
        if hex.is_empty() {
            return None; // `\u{}` is not an escape
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        if code > SMTLIB_MAX_CODE_POINT {
            return None; // outside the alphabet: not an escape
        }
        Some((code, j + 1)) // skip the closing `}`
    } else {
        // `\udddd` — exactly 4 hex digits. The maximum such value is 0xFFFF,
        // which is inside the alphabet, so the range check cannot fail here;
        // it is kept so the two branches enforce one identical contract.
        let mut hex = String::with_capacity(4);
        for k in 0..4 {
            let &c = chars.get(after_u + k)?;
            if !c.is_ascii_hexdigit() {
                return None;
            }
            hex.push(c);
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        if code > SMTLIB_MAX_CODE_POINT {
            return None;
        }
        Some((code, after_u + 4))
    }
}

#[cfg(test)]
#[path = "smtlib_tests.rs"]
mod tests;
