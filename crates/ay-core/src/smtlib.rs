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

use std::borrow::Cow;

use crate::smtlib_char::{smtlib_char, smtlib_code_point};

pub mod admitted;

/// Capacity-hint clamp for output buffers sized from caller-controlled input
/// lengths; longer outputs just grow past the hint.
const MAX_PREALLOC_BYTES: usize = 1024 * 1024;

/// Quote a symbol if it cannot be written as a simple (unquoted) SMT-LIB symbol.
///
/// Returns the symbol wrapped in `|...|` if any of the following hold:
/// - The symbol is empty
/// - The symbol starts with a digit
/// - The symbol is a reserved word (`true`, `false`, keywords, etc.)
/// - The symbol contains characters not allowed in simple symbols
///
/// Z3 5.0.0 extends quoted symbols with backslash escapes for `|` and `\`.
/// AY emits those lossless spellings instead of changing symbol identity.
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
/// assert_eq!(quote_symbol("a|b"), r"|a\|b|");
/// assert_eq!(quote_symbol(r"a\b"), r"|a\\b|");
/// ```
pub fn quote_symbol(name: &str) -> String {
    quote_symbol_owned(name, None)
}

/// Reserved words in SMT-LIB that need quoting. This includes:
/// - `true` and `false` (dedicated tokens in the lexer)
/// - Core keywords and command names
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
    "declare-sort-parameter",
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
    // Alethe proof-language reserved words. Quoting these is also valid
    // SMT-LIB, and prevents proof variables from being tokenized as
    // structural syntax by external checkers such as Carcara.
    "choice",
    "lambda",
    "cl",
    "assume",
    "step",
    "anchor",
    "declare-rare-rule",
];

/// Returns whether the SMT-LIB emitter reserves this unquoted spelling.
pub fn is_smtlib_reserved_word(name: &str) -> bool {
    RESERVED.contains(&name)
}

/// Whether [`quote_symbol`] quotes `name`: it is empty, starts with a digit,
/// reads as a signed number, is one of `RESERVED`, or holds a character
/// `is_symbol_char` refuses.
fn needs_quoting(name: &str) -> bool {
    name.is_empty()
        || name.starts_with(|c: char| c.is_ascii_digit())
        || reads_as_signed_number(name)
        || is_smtlib_reserved_word(name)
        || name.contains(|c: char| !is_symbol_char(c))
}

/// `name` as one SMT-LIB symbol token: `name` itself, borrowed, when
/// [`quote_symbol`] leaves it bare, and otherwise the `|...|` spelling
/// [`quote_symbol`] gives.
///
/// # Examples
/// ```
/// use ay_core::symbol_token;
///
/// assert_eq!(symbol_token("nil"), "nil");
/// assert_eq!(symbol_token(""), "||");
/// assert_eq!(symbol_token("a b"), "|a b|");
/// assert_eq!(symbol_token("let"), "|let|");
/// assert_eq!(symbol_token("||"), r"|\|\||");
/// ```
pub fn symbol_token(name: &str) -> Cow<'_, str> {
    if needs_quoting(name) {
        Cow::Owned(quote_symbol(name))
    } else {
        Cow::Borrowed(name)
    }
}

fn quote_symbol_owned(name: &str, owner: admitted::Owner<'_>) -> String {
    if owner.is_some() {
        let comparison_work = RESERVED.iter().fold(0usize, |work, word| {
            work.saturating_add(if word.len() == name.len() {
                word.len()
            } else {
                1
            })
        });
        if !admitted::pay(
            owner,
            name.len().saturating_add(comparison_work).saturating_add(8),
            0,
        ) {
            return String::new();
        }
    }
    if needs_quoting(name) {
        // Z3 5.0.0 accepts `\|` and `\\` inside quoted symbols. Escaping is
        // lossless; underscore substitution conflates distinct user symbols.
        let mut quoted = admitted::Buffer::with_capacity(
            owner,
            name.len().saturating_add(2).min(MAX_PREALLOC_BYTES),
        );
        if !quoted.character('|') {
            return String::new();
        }
        for character in name.chars() {
            if matches!(character, '|' | '\\') && !quoted.character('\\') {
                return String::new();
            }
            if !quoted.character(character) {
                return String::new();
            }
        }
        if !quoted.character('|') {
            return String::new();
        }
        quoted.finish()
    } else {
        admitted::text(owner, name)
    }
}

/// A sign followed by a digit, or by `.` and a digit (`-1`, `+0`, `-1.5`,
/// `-1e3`, `-.5`). SMT-LIB 2.6 allows these as simple symbols, but external
/// checkers such as Carcara and Clean's verifier lex them as numerals, so an
/// unquoted `-1` binder or constant makes the whole proof document
/// unparseable there.
fn reads_as_signed_number(name: &str) -> bool {
    let mut chars = name.chars();
    if !matches!(chars.next(), Some('-' | '+')) {
        return false;
    }
    match chars.next() {
        Some(c) if c.is_ascii_digit() => true,
        Some('.') => chars.next().is_some_and(|c| c.is_ascii_digit()),
        _ => false,
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
/// Backslash (`0x5C`) is a printable ASCII character and normally prints
/// literally (it is NOT an escape character in the standard). Every other code
/// point in the theory alphabet — control characters and all non-ASCII, up to
/// [`SMTLIB_MAX_CODE_POINT`] — is emitted as a `\u{X}` escape, where `X` is the
/// LOWERCASE, minimal-digit hex code point (e.g. U+03B1 -> `\u{3b1}`,
/// U+0009 -> `\u{9}`, U+1F600 -> `\u{1f600}`). This matches z3's `(get-value)`
/// output.
///
/// The output is an exact left inverse of [`unescape_string_contents`]: reading
/// it back yields the same sequence of code points. Two cases need care, and
/// both were live round-trip defects (`get-value` printing a literal that
/// denotes a DIFFERENT String element than the model value):
///
/// 1. A literal backslash that the reader would re-absorb. `"\u{5c}u{61}"`
///    denotes the six code points `\ u { 6 1 }`; printing them verbatim gives
///    `"\u{61}"`, which denotes the single character `a`. So a backslash whose
///    successors form a well-formed, in-alphabet `\u` escape is itself written
///    as `\u{5c}` (as z3 does). A backslash that cannot start an escape still
///    prints literally, so ordinary text such as `path\to\file` is unchanged.
/// 2. A code point ABOVE the theory alphabet. `\u{30000}` is not an escape
///    sequence at all (SMT-LIB 2.6 restricts both `\u` forms to
///    `0..=0x2FFFF`), so a conformant reader takes its nine characters
///    literally. Such code points are therefore written raw, which does
///    round-trip, rather than as a `\u{...}` form that does not.
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
/// // A backslash that would be re-absorbed as an escape is itself escaped.
/// assert_eq!(escape_string_contents(r"\u{61}"), r"\u{5c}u{61}");
/// ```
pub fn escape_string_contents(s: &str) -> String {
    escape_string_contents_owned(s, None)
}

fn escape_string_contents_owned(s: &str, owner: admitted::Owner<'_>) -> String {
    if !admitted::pay(owner, s.len().saturating_mul(2), 0) {
        return String::new();
    }
    let chars: Vec<char> = if owner.is_some() {
        let mut chars = Vec::new();
        if !admitted::reserve(&mut chars, s.chars().count(), owner) {
            return String::new();
        }
        chars.extend(s.chars());
        chars
    } else {
        s.chars().collect()
    };
    let mut result = admitted::Buffer::with_capacity(owner, s.len().min(MAX_PREALLOC_BYTES));
    let mut rest: &[char] = &chars;
    while let Some((&c, tail)) = rest.split_first() {
        if !admitted::pay(owner, if c == '\\' { 9 } else { 1 }, 0) {
            return String::new();
        }
        rest = tail;
        match c {
            '"' => {
                if !result.push("\"\"") {
                    return String::new();
                }
            }
            // A backslash the reader would absorb into a `\u` escape must be
            // written as an escape itself, or the printed literal denotes a
            // different (shorter) string than the value being printed.
            '\\' if parse_unicode_escape(tail).is_some() => {
                if !result.push("\\u{5c}") {
                    return String::new();
                }
            }
            c if ('\u{20}'..='\u{7e}').contains(&c) => {
                if !result.character(c) {
                    return String::new();
                }
            }
            // Outside the theory alphabet a `\u{...}` form is not an escape, so
            // escaping would corrupt the value. Emit the code point raw: the
            // reader takes raw characters literally, so this round-trips.
            c if smtlib_code_point(c) > SMTLIB_MAX_CODE_POINT => {
                if !result.character(c) {
                    return String::new();
                }
            }
            // A surrogate's carrier prints as the surrogate's own escape.
            c => {
                if !result.format(format_args!("\\u{{{:x}}}", smtlib_code_point(c))) {
                    return String::new();
                }
            }
        }
    }
    result.finish()
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
/// for soundness — see `parse_unicode_escape` for the exact grammar and for
/// the verdict-flipping failure mode that consuming-on-failure produced.
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
/// // Out-of-alphabet: `\u{FFFFF}` is not an escape, so it is nine characters.
/// assert_eq!(unescape_string_contents(r"\u{FFFFF}").chars().count(), 9);
/// // A surrogate is ONE character, held by its carrier (see `smtlib_char`).
/// assert_eq!(unescape_string_contents(r"\u{d800}").chars().count(), 1);
/// ```
#[must_use]
pub fn unescape_string_contents(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut result = String::with_capacity(s.len().min(MAX_PREALLOC_BYTES));
    let mut rest: &[char] = &chars;
    while let Some((&c, tail)) = rest.split_first() {
        if c == '"' {
            // SMT-LIB 2.6: `""` inside string contents = literal `"`. A stray
            // quote should not occur in well-formed input; pass it through.
            result.push('"');
            rest = match tail.split_first() {
                Some((&'"', after_pair)) => after_pair,
                _ => tail,
            };
        } else if c == '\\' {
            // SMT-LIB 2.6: a backslash is a LITERAL character EXCEPT in the two
            // unicode escapes. It is NOT a C-style escape. Collapsing `\\` ->
            // `\` (or `\"` -> `"`) is a SOUNDNESS bug, not a cosmetic one: z3
            // (correctly) reads `"a\\b"` as FOUR characters, while the old
            // behaviour read THREE, flipping every str.len- (and membership-)
            // sensitive verdict on any backslash-bearing literal.
            // `parse_unicode_escape` admits only in-alphabet code points, every
            // one of which `smtlib_char` stores (a surrogate in its carrier),
            // so an escape always decodes to exactly one character.
            let escape = parse_unicode_escape(tail)
                .and_then(|(code, after_escape)| Some((smtlib_char(code)?, after_escape)));
            match escape {
                Some((ch, after_escape)) => {
                    result.push(ch);
                    rest = after_escape;
                }
                None => {
                    // Not an escape: the backslash is literal and the following
                    // characters are decoded normally on later iterations.
                    result.push('\\');
                    rest = tail;
                }
            }
        } else {
            result.push(c);
            rest = tail;
        }
    }
    result
}

/// Try to parse an SMT-LIB 2.6 unicode escape at the start of
/// `after_backslash` (the characters just after the backslash).
///
/// Returns the denoted code point and the characters remaining past the
/// escape, or `None` if the text is not an escape — in which case NOTHING is
/// consumed and the backslash is an ordinary character.
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
///    shortening the string. Returning the remainder means failure consumes
///    nothing.
fn parse_unicode_escape(after_backslash: &[char]) -> Option<(u32, &[char])> {
    let Some((&'u', after_u)) = after_backslash.split_first() else {
        return None;
    };

    if let Some((&'{', digits)) = after_u.split_first() {
        let mut code = 0u32;
        let mut count = 0usize;
        let mut rest = digits;
        loop {
            let (&c, tail) = rest.split_first()?; // end of input before `}` — not an escape
            rest = tail;
            if c == '}' {
                break;
            }
            if !c.is_ascii_hexdigit() || count == 5 {
                // Non-hex, or a 6th digit: not an escape sequence.
                return None;
            }
            code = code.checked_mul(16)?.checked_add(c.to_digit(16)?)?;
            count += 1;
        }
        if count == 0 {
            return None; // `\u{}` is not an escape
        }
        if code > SMTLIB_MAX_CODE_POINT {
            return None; // outside the alphabet: not an escape
        }
        Some((code, rest)) // `rest` is already past the closing `}`
    } else {
        // `\udddd` — exactly 4 hex digits. The maximum such value is 0xFFFF,
        // which is inside the alphabet, so the range check cannot fail here;
        // it is kept so the two branches enforce one identical contract.
        let mut code = 0u32;
        let mut rest = after_u;
        for _ in 0..4 {
            let (&c, tail) = rest.split_first()?;
            if !c.is_ascii_hexdigit() {
                return None;
            }
            code = code.checked_mul(16)?.checked_add(c.to_digit(16)?)?;
            rest = tail;
        }
        if code > SMTLIB_MAX_CODE_POINT {
            return None;
        }
        Some((code, rest))
    }
}

#[cfg(test)]
#[path = "smtlib_tests.rs"]
mod tests;
