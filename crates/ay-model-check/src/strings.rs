// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB string operations, computed exactly.
//!
//! # Why this exists
//!
//! An audit of the gate's uninterpreted-function path — instrumenting it and
//! running the whole solver test suite — showed nine INTERPRETED string
//! operators reaching it. That path ADOPTS the solver's own committed value for
//! the application, which is right for an uninterpreted symbol and wrong for
//! `str.contains`: the gate was confirming `(str.contains s t)` because the
//! solver said so, without looking at `s` or `t`.
//!
//! # Two things worth stating plainly
//!
//! **Positions are CODE POINTS, not bytes.** `str.len` counts code points, so
//! every index here does too. A `String` in Rust is UTF-8, so a byte offset
//! from `find` is not a position — mixing them is correct for ASCII and wrong
//! for everything else, which is exactly the bug that survives a test suite
//! written in ASCII.
//!
//! **The argument orders differ between operators.** `(str.contains s t)` asks
//! whether *s* contains *t*, while `(str.prefixof s t)` asks whether *s* is a
//! prefix of *t*. The haystack is the first argument in one and the second in
//! the other; the tests pin both.

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::ModelValue;

/// The SMT-LIB string alphabet: code points `0x00000`–`0x2FFFF`.
const MAX_CODE_POINT: u32 = 0x2_FFFF;

fn as_str(value: &ModelValue) -> Result<&str, String> {
    match value {
        ModelValue::Str(s) => Ok(s),
        _ => Err("expected a string value".to_string()),
    }
}

fn as_int(value: &ModelValue) -> Result<&BigInt, String> {
    match value {
        ModelValue::Int(i) => Ok(i),
        _ => Err("expected an integer value".to_string()),
    }
}

/// Code points of a string, which is the unit every SMT-LIB string position is
/// measured in.
fn points(s: &str) -> Vec<char> {
    s.chars().collect()
}

fn from_points(p: &[char]) -> String {
    p.iter().collect()
}

/// The least code-point position at or after `from` where `needle` occurs, or
/// `None`.
///
/// Two contract points the callers depend on, both falling out of the scan
/// rather than being special-cased: an EMPTY needle occurs at every position, so
/// the answer is `from` itself whenever `from <= |haystack|`; and a `from` PAST
/// the end has nothing to scan, so the answer is `None`.
fn find_at(haystack: &[char], needle: &[char], from: usize) -> Option<usize> {
    if needle.len() > haystack.len() {
        return None;
    }
    (from..=haystack.len() - needle.len()).find(|&i| haystack[i..i + needle.len()] == *needle)
}

/// Evaluate an SMT-LIB string operation over already-evaluated operands.
///
/// Every out-of-range case has a DEFINED answer in SMT-LIB — `str.substr` past
/// the end is the empty string, `str.to_int` of a non-numeral is `-1` — so
/// those are computed, not refused. Only genuinely unrepresentable cases (a
/// code point Rust cannot hold) fail closed.
pub fn eval(name: &str, args: &[ModelValue]) -> Result<ModelValue, String> {
    match (name, args) {
        // `(str.contains s t)`: does s contain t?
        ("str.contains", [s, t]) => {
            let (s, t) = (points(as_str(s)?), points(as_str(t)?));
            Ok(ModelValue::Bool(find_at(&s, &t, 0).is_some()))
        }
        // `(str.prefixof s t)`: is s a prefix of T? The subject is the SECOND
        // argument here and the first in `str.contains`.
        ("str.prefixof", [s, t]) => {
            let (s, t) = (points(as_str(s)?), points(as_str(t)?));
            Ok(ModelValue::Bool(
                s.len() <= t.len() && t[..s.len()] == s[..],
            ))
        }
        ("str.suffixof", [s, t]) => {
            let (s, t) = (points(as_str(s)?), points(as_str(t)?));
            Ok(ModelValue::Bool(
                s.len() <= t.len() && t[t.len() - s.len()..] == s[..],
            ))
        }
        // `(str.indexof s t i)`: the first occurrence of t in s at or after i.
        ("str.indexof", [s, t, i]) => {
            let (s, t) = (points(as_str(s)?), points(as_str(t)?));
            let i = as_int(i)?;
            // The standard's rule: a start outside `[0, |s|]` reports -1. Stated
            // here because it is the standard's, though `find_at` would also
            // return `None` for it.
            let Some(from) = i.to_usize().filter(|&k| k <= s.len()) else {
                return Ok(ModelValue::Int(BigInt::from(-1)));
            };
            Ok(ModelValue::Int(match find_at(&s, &t, from) {
                Some(at) => BigInt::from(at),
                None => BigInt::from(-1),
            }))
        }
        // `(str.substr s m n)`: at most n code points from position m. Out of
        // range in either argument gives the empty string.
        ("str.substr", [s, m, n]) => {
            let s = points(as_str(s)?);
            let (m, n) = (as_int(m)?, as_int(n)?);
            // The standard's rule for a negative position or length. Stated
            // explicitly, though `to_usize` below also rejects them.
            if m.is_negative() || n.is_negative() {
                return Ok(ModelValue::Str(String::new()));
            }
            let (Some(start), Some(len)) = (m.to_usize(), n.to_usize()) else {
                // Too large to be a position in any real string.
                return Ok(ModelValue::Str(String::new()));
            };
            if start >= s.len() {
                return Ok(ModelValue::Str(String::new()));
            }
            let end = start.saturating_add(len).min(s.len());
            Ok(ModelValue::Str(from_points(&s[start..end])))
        }
        // `(str.replace s t t')`: the FIRST occurrence only. An empty `t`
        // occurs at position 0, so the replacement is prepended.
        ("str.replace", [s, t, r]) => {
            let (s, t, r) = (points(as_str(s)?), points(as_str(t)?), points(as_str(r)?));
            Ok(ModelValue::Str(match find_at(&s, &t, 0) {
                Some(at) => {
                    let mut out = s[..at].to_vec();
                    out.extend_from_slice(&r);
                    out.extend_from_slice(&s[at + t.len()..]);
                    from_points(&out)
                }
                None => from_points(&s),
            }))
        }
        // `(str.replace_all s t t')`: every non-overlapping occurrence, left to
        // right. An empty `t` leaves the string ALONE here — the opposite of
        // `str.replace`, and the case where a naive loop would not terminate.
        ("str.replace_all", [s, t, r]) => {
            let (s, t, r) = (points(as_str(s)?), points(as_str(t)?), points(as_str(r)?));
            if t.is_empty() {
                return Ok(ModelValue::Str(from_points(&s)));
            }
            let mut out: Vec<char> = Vec::with_capacity(s.len());
            let mut at = 0usize;
            while let Some(found) = find_at(&s, &t, at) {
                out.extend_from_slice(&s[at..found]);
                out.extend_from_slice(&r);
                at = found + t.len();
            }
            out.extend_from_slice(&s[at..]);
            Ok(ModelValue::Str(from_points(&out)))
        }
        // `(str.to_int s)`: a NON-EMPTY run of ASCII digits, else -1. Leading
        // zeros are allowed and a sign is not: "-1" is not a numeral, so it
        // maps to -1 for being malformed, not for being negative.
        ("str.to_int", [s]) => {
            let s = as_str(s)?;
            let numeral = !s.is_empty() && s.chars().all(|c| c.is_ascii_digit());
            Ok(ModelValue::Int(if numeral {
                s.parse::<BigInt>()
                    .map_err(|_| "unparsable numeral".to_string())?
            } else {
                BigInt::from(-1)
            }))
        }
        // `(str.from_int n)`: decimal without leading zeros, or the empty
        // string for a negative argument.
        ("str.from_int", [n]) => {
            let n = as_int(n)?;
            Ok(ModelValue::Str(if n.is_negative() {
                String::new()
            } else {
                n.to_string()
            }))
        }
        ("str.to_code", [s]) => {
            let p = points(as_str(s)?);
            Ok(ModelValue::Int(match p.as_slice() {
                [c] => BigInt::from(u32::from(*c)),
                _ => BigInt::from(-1),
            }))
        }
        ("str.from_code", [n]) => {
            let n = as_int(n)?;
            let Some(code) = n.to_u32().filter(|c| *c <= MAX_CODE_POINT) else {
                return Ok(ModelValue::Str(String::new()));
            };
            match char::from_u32(code) {
                Some(c) => Ok(ModelValue::Str(c.to_string())),
                // A surrogate is in the SMT-LIB alphabet but cannot live in a
                // Rust `String`. Refusing keeps the gate from silently
                // substituting a different character.
                None => Err("code point is not representable".to_string()),
            }
        }
        ("str.is_digit", [s]) => {
            let p = points(as_str(s)?);
            Ok(ModelValue::Bool(
                matches!(p.as_slice(), [c] if c.is_ascii_digit()),
            ))
        }
        // Lexicographic by code point.
        ("str.<" | "str.<=", [_, _, ..]) => {
            let mut all = Vec::with_capacity(args.len());
            for a in args {
                all.push(points(as_str(a)?));
            }
            let strict = name == "str.<";
            Ok(ModelValue::Bool(all.windows(2).all(|pair| {
                let ordering = pair[0].cmp(&pair[1]);
                if strict {
                    ordering == core::cmp::Ordering::Less
                } else {
                    ordering != core::cmp::Ordering::Greater
                }
            })))
        }
        _ => Err(format!("unsupported string operation {name}")),
    }
}

/// Whether [`eval`] handles `name` at this arity.
#[must_use]
pub fn handles(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("str.contains" | "str.prefixof" | "str.suffixof", 2)
            | (
                "str.indexof" | "str.substr" | "str.replace" | "str.replace_all",
                3
            )
            | (
                "str.to_int" | "str.from_int" | "str.to_code" | "str.from_code" | "str.is_digit",
                1
            )
    ) || (matches!(name, "str.<" | "str.<=") && arity >= 2)
}

#[cfg(test)]
#[path = "strings_tests.rs"]
mod tests;
