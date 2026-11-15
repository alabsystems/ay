// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB characters as AY stores them.
//!
//! The SMT-LIB 2.6 string alphabet is every code point `0..=0x2FFFF`, surrogates
//! included; a Rust `char` holds only Unicode scalar values. [`smtlib_char`] and
//! [`smtlib_code_point`] are the one bijection between the two, and the order and
//! successor helpers below are the code-point order every `str.<` / `re.range` /
//! alphabet walk must use.

use crate::smtlib::SMTLIB_MAX_CODE_POINT;

/// First code point of the UTF-16 surrogate block `U+D800..=U+DFFF`.
pub const SMTLIB_SURROGATE_FIRST: u32 = 0xD800;

/// Last code point of the UTF-16 surrogate block `U+D800..=U+DFFF`.
pub const SMTLIB_SURROGATE_LAST: u32 = 0xDFFF;

/// Offset from a surrogate code point to the `char` that carries it.
///
/// The carriers `U+10D800..=U+10DFFF` lie in supplementary private-use area B,
/// far above the theory alphabet, so no in-alphabet character is displaced.
const SURROGATE_CARRIER_OFFSET: u32 = 0x10_0000;

/// The `char` AY stores for the SMT-LIB character with code point `code`, or
/// `None` when `code` is outside the theory alphabet `0..=0x2FFFF`.
///
/// # Why a carrier
///
/// The SMT-LIB 2.6 string alphabet is every code point `0..=0x2FFFF`, and that
/// INCLUDES the 2,048 surrogate code points `U+D800..=U+DFFF`: z3 decides
/// `(= (str.len (str.from_code 55296)) 1)` sat, and `(re.range "\u{d7ff}"
/// "\u{e000}")` has 2,050 members. A Rust `char` holds only Unicode *scalar
/// values*, which exclude surrogates, so AY stores each surrogate code point
/// `s` in the `char` `s + 0x10_0000`, its *carrier*. Every other code point is
/// stored as itself. A string therefore keeps exactly one `char` per SMT-LIB
/// character, so lengths, positions, equality and concatenation need no
/// translation. Only a place that reads a character's CODE POINT —
/// `str.to_code`, `str.from_code`, `str.<`, `re.range`, alphabet enumeration,
/// printing — must go through this function and [`smtlib_code_point`].
///
/// The carrier block is therefore RESERVED: a character in it always means
/// the surrogate it carries. Text that arrives from outside AY — a raw
/// (unescaped) character in an SMT-LIB string literal, a code point or UTF-8
/// text handed to the z3 C API — is refused when it holds one
/// ([`first_surrogate_carrier`]), because the input meant the code point
/// `0x10D800..=0x10DFFF` itself (or, read as z3 reads raw bytes, four
/// characters), never a surrogate.
///
/// # Examples
/// ```
/// use ay_core::{smtlib_char, smtlib_code_point};
///
/// assert_eq!(smtlib_char(0x41), Some('A'));
/// let surrogate = smtlib_char(0xD800).expect("surrogates are SMT-LIB characters");
/// assert_eq!(smtlib_code_point(surrogate), 0xD800);
/// assert_eq!(smtlib_char(0x30000), None);
/// ```
#[must_use]
pub const fn smtlib_char(code: u32) -> Option<char> {
    if code > SMTLIB_MAX_CODE_POINT {
        return None;
    }
    if code >= SMTLIB_SURROGATE_FIRST && code <= SMTLIB_SURROGATE_LAST {
        return char::from_u32(code + SURROGATE_CARRIER_OFFSET);
    }
    char::from_u32(code)
}

/// The SMT-LIB code point of a character AY stores; the inverse of
/// [`smtlib_char`].
///
/// A surrogate carrier reads back as its surrogate. A raw character above the
/// theory alphabet keeps its scalar value, which callers recognise as outside
/// the alphabet by comparing against [`SMTLIB_MAX_CODE_POINT`].
#[must_use]
pub const fn smtlib_code_point(c: char) -> u32 {
    let scalar = c as u32;
    if is_surrogate_carrier(c) {
        scalar - SURROGATE_CARRIER_OFFSET
    } else {
        scalar
    }
}

/// Whether `c` is a surrogate carrier (`U+10D800..=U+10DFFF`), i.e. a `char`
/// that [`smtlib_code_point`] reads back as a surrogate.
#[must_use]
pub const fn is_surrogate_carrier(c: char) -> bool {
    let scalar = c as u32;
    scalar >= SMTLIB_SURROGATE_FIRST + SURROGATE_CARRIER_OFFSET
        && scalar <= SMTLIB_SURROGATE_LAST + SURROGATE_CARRIER_OFFSET
}

/// The first character of RAW input text that is a surrogate carrier, if any.
///
/// For the boundaries where text enters AY undecoded: an SMT-LIB string
/// literal's contents before unescaping, and the strings and code points of
/// the z3 C API. Such a character is the code point `0x10D800..=0x10DFFF`,
/// outside the SMT-LIB alphabet and distinct from every SMT-LIB character;
/// stored as-is it would read back as a surrogate (`U+10D800` as `U+D800`),
/// so `(= "<U+10D800>" "\u{d800}")` would be `sat`. No `char` is free to hold
/// it apart from every in-alphabet character and every other raw character
/// (the surrogates took the 2,048 the alphabet lacks), so the boundary
/// refuses the input instead. An escape such as `\u{d800}` is plain ASCII
/// text before unescaping and is never reported.
///
/// # Examples
/// ```
/// use ay_core::first_surrogate_carrier;
///
/// assert_eq!(first_surrogate_carrier(r"ab\u{d800}"), None);
/// assert_eq!(first_surrogate_carrier("a\u{10D800}"), Some('\u{10D800}'));
/// assert_eq!(first_surrogate_carrier("\u{10D7FF}\u{10E000}"), None);
/// ```
#[must_use]
pub fn first_surrogate_carrier(raw: &str) -> Option<char> {
    raw.chars().find(|&c| is_surrogate_carrier(c))
}

/// Order two stored characters by SMT-LIB code point.
///
/// `char`'s own `Ord` is NOT this order once a surrogate carrier is involved:
/// the carrier of `U+D800` sorts above `U+2FFFF` as a `char`, while its code
/// point lies between `U+D7FF` and `U+E000`.
#[must_use]
pub fn smtlib_char_cmp(a: char, b: char) -> core::cmp::Ordering {
    smtlib_code_point(a).cmp(&smtlib_code_point(b))
}

/// The SMT-LIB lexicographic order on strings (`str.<`, `str.<=`): by code
/// point, a proper prefix before its extensions.
///
/// Rust's `str` order compares UTF-8 bytes, which agrees with code-point order
/// only while no surrogate carrier is involved.
#[must_use]
pub fn smtlib_str_cmp(a: &str, b: &str) -> core::cmp::Ordering {
    a.chars()
        .map(smtlib_code_point)
        .cmp(b.chars().map(smtlib_code_point))
}

/// The stored character whose code point follows `c`'s, or `None` when `c` is
/// the last character of the theory alphabet (or lies above it).
///
/// Surrogates are characters: the successor of `U+D7FF` is the carrier of
/// `U+D800`, and the successor of `U+DFFF`'s carrier is `U+E000`.
#[must_use]
pub fn smtlib_next_char(c: char) -> Option<char> {
    smtlib_char(smtlib_code_point(c).checked_add(1)?)
}
