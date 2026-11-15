// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3's `zstring` text conventions for the string-literal C API.
//!
//! z3 5.1.0 (`src/util/zstring.cpp`, `src/api/api_seq.cpp`) reads and writes
//! string literals byte by byte, never as UTF-8:
//!
//! - `Z3_mk_string` decodes the escapes `\u{h}`..`\u{hhhhh}` (1 to 5 hex
//!   digits) and `\uhhhh` (exactly 4) when the code point is at most
//!   [`Z3_MAX_CHAR`]; every other byte, a backslash included, is the character
//!   with that byte's value (so the UTF-8 bytes of `é` are two characters).
//! - `Z3_mk_lstring` decodes no escapes: byte `b` is character `b`.
//! - `Z3_get_string` escapes every character outside `32..127`, and a backslash
//!   followed by `u`, as `\u{hex}`.
//! - `Z3_get_lstring` escapes character 0, every character `>= 256` and a
//!   backslash followed by `u`; characters `1..256` are written as one byte.
//!
//! z3py's `StringVal` sends every non-printable or non-ASCII character as
//! `\u{hex}` through `Z3_mk_string` and reads literals back with
//! `Z3_get_lstring(...).decode("latin-1")`, so both directions have to match
//! exactly for a string built through the API to mean what the caller wrote.
//!
//! Characters are stored the AY way (`ay_core::smtlib_char`): one `char` per
//! SMT-LIB character, a surrogate in its carrier.

/// The largest character z3 accepts under its default `encoding=unicode`
/// (`zstring::unicode_max_char`), which is also the top of AY's alphabet.
pub(crate) const Z3_MAX_CHAR: u32 = 0x2_FFFF;

fn hex_digit(byte: u8) -> Option<u32> {
    char::from(byte).to_digit(16)
}

/// z3's `zstring::is_escape_char` at the start of `bytes`: the code point and
/// the number of bytes the escape spans, or `None` when no escape starts here.
fn escape_at(bytes: &[u8]) -> Option<(u32, usize)> {
    if !bytes.starts_with(b"\\u") {
        return None;
    }
    if bytes.get(2) == Some(&b'{') && bytes.get(3) != Some(&b'}') {
        let mut code = 0_u32;
        for i in 0..6 {
            match bytes.get(3 + i).copied() {
                Some(b'}') => return (code <= Z3_MAX_CHAR).then_some((code, 4 + i)),
                Some(byte) => code = 16 * code + hex_digit(byte)?,
                None => return None,
            }
        }
        return None;
    }
    let digits = bytes.get(2..6)?;
    let code = digits
        .iter()
        .try_fold(0_u32, |acc, &byte| Some(16 * acc + hex_digit(byte)?))?;
    (code <= Z3_MAX_CHAR).then_some((code, 6))
}

/// The AY `char` for a code point at most [`Z3_MAX_CHAR`].
fn stored_char(code: u32) -> char {
    // Every code point `0..=0x2FFFF` is an SMT-LIB character, so the fallback
    // is unreachable; U+FFFD would only ever stand in for a broken invariant.
    ay_core::smtlib_char(code).unwrap_or(char::REPLACEMENT_CHARACTER)
}

/// The string `Z3_mk_string` builds from the bytes of its C string.
pub(crate) fn decode_escaped(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if let Some((code, len)) = escape_at(&bytes[i..]) {
            out.push(stored_char(code));
            i += len;
        } else {
            out.push(char::from(bytes[i]));
            i += 1;
        }
    }
    out
}

/// The string `Z3_mk_lstring` builds from its bytes: byte `b` is character `b`.
pub(crate) fn decode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|&byte| char::from(byte)).collect()
}

fn push_escape(out: &mut Vec<u8>, code: u32) {
    out.extend_from_slice(format!("\\u{{{code:x}}}").as_bytes());
}

/// Encode `text` the way z3 does, escaping a character when `escape(code)`
/// holds or when it is a backslash directly followed by `u`.
fn encode_with(text: &str, escape: impl Fn(u32) -> bool) -> Vec<u8> {
    let codes: Vec<u32> = text.chars().map(ay_core::smtlib_code_point).collect();
    let mut out = Vec::with_capacity(codes.len());
    for (i, &code) in codes.iter().enumerate() {
        let backslash_u = code == u32::from(b'\\') && codes.get(i + 1) == Some(&u32::from(b'u'));
        match u8::try_from(code) {
            Ok(byte) if !escape(code) && !backslash_u => out.push(byte),
            _ => push_escape(&mut out, code),
        }
    }
    out
}

/// `Z3_get_string`'s text (`zstring::encode`): printable ASCII only.
pub(crate) fn encode_escaped(text: &str) -> String {
    let bytes = encode_with(text, |code| !(32..127).contains(&code));
    // Every byte is printable ASCII or part of an ASCII escape.
    bytes.into_iter().map(char::from).collect()
}

/// `Z3_get_lstring`'s bytes: characters `1..256` as one byte each.
pub(crate) fn encode_lstring(text: &str) -> Vec<u8> {
    encode_with(text, |code| code == 0 || code >= 256)
}

/// Whether `sort` ranges over z3's character alphabet (strings, characters,
/// regular languages, sequences or arrays of them).
fn uses_char_alphabet(sort: &ay_dpll::api::Sort) -> bool {
    use ay_dpll::api::Sort;
    match sort {
        Sort::String | Sort::RegLan | Sort::Char => true,
        Sort::Seq(element) => uses_char_alphabet(element),
        Sort::Array(array) => {
            uses_char_alphabet(&array.index_sort) || uses_char_alphabet(&array.element_sort)
        }
        _ => false,
    }
}

/// Refuse a just-built term that involves z3's character alphabet while z3's
/// `encoding` global is not `unicode` (see
/// [`super::global_params::string_encoding_is_unicode`]): sets
/// `Z3_INVALID_ARG` and returns true. Checks the term's sort and its
/// arguments' sorts, so `str.len` of a string is refused as well as the
/// string.
pub(crate) fn refuse_under_non_unicode_encoding(
    ctx: &mut super::Z3Context,
    ast: super::Z3_ast,
) -> bool {
    refuse_for_encoding(ctx, ast, super::global_params::string_encoding_is_unicode())
}

/// [`refuse_under_non_unicode_encoding`] with the encoding given.
pub(crate) fn refuse_for_encoding(
    ctx: &mut super::Z3Context,
    ast: super::Z3_ast,
    unicode: bool,
) -> bool {
    if ast == 0 || unicode {
        return false;
    }
    let Some(decoded) = super::checked_ast_to_pub(ctx, ast) else {
        return false;
    };
    let term = decoded.term;
    let mut sorts = vec![super::public_sort(ctx, decoded)];
    sorts.extend(
        ctx.solver
            .term_children(term)
            .into_iter()
            .map(|child| ctx.solver.term_sort(child)),
    );
    if !sorts.iter().any(uses_char_alphabet) {
        return false;
    }
    ctx.last_error = super::Z3_INVALID_ARG;
    ctx.error_msg = Some(
        "string terms are unsupported while the global parameter encoding is not unicode: \
         z3 then uses a smaller character alphabet (bmp: 0xFFFF, ascii: 255), and AY \
         implements the unicode alphabet only"
            .to_string(),
    );
    true
}

/// [`refuse_under_non_unicode_encoding`] for parsed assertions: refuses
/// (`Z3_INVALID_ARG`, true) when any subterm of `terms` involves the
/// character alphabet.
pub(crate) fn refuse_parsed_under_non_unicode_encoding(
    ctx: &mut super::Z3Context,
    operation: &str,
    terms: &[ay_dpll::api::Term],
) -> bool {
    if super::global_params::string_encoding_is_unicode() {
        return false;
    }
    let mut seen = std::collections::HashSet::new();
    let mut stack = terms.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if uses_char_alphabet(&ctx.solver.term_sort(term)) {
            ctx.last_error = super::Z3_INVALID_ARG;
            ctx.error_msg = Some(format!(
                "{operation}: string terms are unsupported while the global parameter \
                 encoding is not unicode (AY implements the unicode alphabet only)"
            ));
            return true;
        }
        stack.extend(ctx.solver.term_children(term));
    }
    false
}

#[cfg(test)]
#[path = "zstring_tests.rs"]
mod zstring_tests;
