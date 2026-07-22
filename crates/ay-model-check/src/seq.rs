// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB sequence (`Seq`) semantics for the independent gate.
//!
//! Element values are arbitrary [`ModelValue`]s; element equality goes through
//! [`crate::value_eq`], so an unevaluable element comparison makes the whole
//! operation unevaluable (fail closed). Operations whose result is
//! under-specified in SMT-LIB on the given inputs (e.g. `seq.nth` out of range)
//! return `Err` (unevaluable), never a fabricated value.

use crate::{value_eq, ModelValue};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

/// Evaluate a named sequence operator over already-evaluated arguments.
pub(crate) fn eval(name: &str, args: &[ModelValue]) -> Result<ModelValue, String> {
    match name {
        "seq.empty" => Ok(ModelValue::Seq(Vec::new())),
        "seq.unit" => {
            let x = arg(args, 0)?;
            Ok(ModelValue::Seq(vec![x.clone()]))
        }
        "seq.++" => {
            let mut out = Vec::new();
            for a in args {
                out.extend(as_seq(a)?.iter().cloned());
            }
            Ok(ModelValue::Seq(out))
        }
        "seq.len" => {
            let s = as_seq(arg(args, 0)?)?;
            Ok(ModelValue::Int(BigInt::from(s.len())))
        }
        "seq.nth" => {
            let s = as_seq(arg(args, 0)?)?;
            let i = as_index(arg(args, 1)?)?;
            // Out of range is under-specified in SMT-LIB ⇒ unevaluable.
            match usize_in_range(i, s.len()) {
                Some(idx) => Ok(s[idx].clone()),
                None => Err("seq.nth index out of range (under-specified)".to_string()),
            }
        }
        "seq.at" => {
            let s = as_seq(arg(args, 0)?)?;
            let i = as_index(arg(args, 1)?)?;
            // (seq.at s i) = the unit subsequence at i, or empty if out of range.
            match usize_in_range(i, s.len()) {
                Some(idx) => Ok(ModelValue::Seq(vec![s[idx].clone()])),
                None => Ok(ModelValue::Seq(Vec::new())),
            }
        }
        "seq.extract" => {
            let s = as_seq(arg(args, 0)?)?;
            let offset = as_int(arg(args, 1)?)?;
            let length = as_int(arg(args, 2)?)?;
            Ok(ModelValue::Seq(extract(s, &offset, &length)))
        }
        "seq.prefixof" => {
            let p = as_seq(arg(args, 0)?)?;
            let s = as_seq(arg(args, 1)?)?;
            Ok(ModelValue::Bool(is_prefix(p, s)?))
        }
        "seq.suffixof" => {
            let p = as_seq(arg(args, 0)?)?;
            let s = as_seq(arg(args, 1)?)?;
            Ok(ModelValue::Bool(is_suffix(p, s)?))
        }
        "seq.contains" => {
            let s = as_seq(arg(args, 0)?)?;
            let sub = as_seq(arg(args, 1)?)?;
            Ok(ModelValue::Bool(find_from(s, sub, 0)?.is_some()))
        }
        "seq.indexof" => {
            let s = as_seq(arg(args, 0)?)?;
            let sub = as_seq(arg(args, 1)?)?;
            let offset = as_int(arg(args, 2)?)?;
            let off = match nonneg_offset(&offset, s.len()) {
                Some(o) => o,
                // Negative offset / past the end ⇒ -1 (not found).
                None => return Ok(ModelValue::Int(BigInt::from(-1))),
            };
            match find_from(s, sub, off)? {
                Some(p) => Ok(ModelValue::Int(BigInt::from(p))),
                None => Ok(ModelValue::Int(BigInt::from(-1))),
            }
        }
        "seq.replace" => {
            let s = as_seq(arg(args, 0)?)?;
            let src = as_seq(arg(args, 1)?)?;
            let dst = as_seq(arg(args, 2)?)?;
            Ok(ModelValue::Seq(replace_first(s, src, dst)?))
        }
        "seq.last_indexof" => {
            let s = as_seq(arg(args, 0)?)?;
            let sub = as_seq(arg(args, 1)?)?;
            match rfind(s, sub)? {
                Some(p) => Ok(ModelValue::Int(BigInt::from(p))),
                None => Ok(ModelValue::Int(BigInt::from(-1))),
            }
        }
        "seq.replace_all" => {
            let s = as_seq(arg(args, 0)?)?;
            let src = as_seq(arg(args, 1)?)?;
            let dst = as_seq(arg(args, 2)?)?;
            Ok(ModelValue::Seq(replace_all(s, src, dst)?))
        }
        // Everything else (seq.map, seq.fold_left, ...) is intentionally left
        // unimplemented ⇒ unevaluable (fail closed).
        _ => Err(format!("unsupported sequence operator {name}")),
    }
}

// --- core string-like algorithms on element slices ------------------------

/// Does `sub` occur in `s` starting exactly at `s[at..]`?
fn match_at(s: &[ModelValue], sub: &[ModelValue], at: usize) -> Result<bool, String> {
    if at + sub.len() > s.len() {
        return Ok(false);
    }
    for (k, e) in sub.iter().enumerate() {
        if !value_eq(&s[at + k], e)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// First start-position `>= from` at which `sub` occurs in `s`, if any.
/// An empty `sub` matches at `from` (when `from <= len`).
fn find_from(s: &[ModelValue], sub: &[ModelValue], from: usize) -> Result<Option<usize>, String> {
    if sub.is_empty() {
        return Ok(if from <= s.len() { Some(from) } else { None });
    }
    if sub.len() > s.len() {
        return Ok(None);
    }
    let last = s.len() - sub.len();
    let mut p = from;
    while p <= last {
        if match_at(s, sub, p)? {
            return Ok(Some(p));
        }
        p += 1;
    }
    Ok(None)
}

fn is_prefix(p: &[ModelValue], s: &[ModelValue]) -> Result<bool, String> {
    if p.len() > s.len() {
        return Ok(false);
    }
    match_at(s, p, 0)
}

fn is_suffix(p: &[ModelValue], s: &[ModelValue]) -> Result<bool, String> {
    if p.len() > s.len() {
        return Ok(false);
    }
    match_at(s, p, s.len() - p.len())
}

fn replace_first(
    s: &[ModelValue],
    src: &[ModelValue],
    dst: &[ModelValue],
) -> Result<Vec<ModelValue>, String> {
    // SMT-LIB: replacing an empty `src` inserts `dst` at the front.
    if src.is_empty() {
        let mut out = dst.to_vec();
        out.extend_from_slice(s);
        return Ok(out);
    }
    match find_from(s, src, 0)? {
        Some(p) => {
            let mut out = Vec::with_capacity(s.len() + dst.len());
            out.extend_from_slice(&s[..p]);
            out.extend_from_slice(dst);
            out.extend_from_slice(&s[p + src.len()..]);
            Ok(out)
        }
        None => Ok(s.to_vec()),
    }
}

/// `(seq.last_indexof s sub)`: the GREATEST start-position `p` at which `sub`
/// occurs in `s`, or `None` (⇒ `-1`) when it never does. Independent right-to-
/// left scan (this crate's own `match_at`), NOT a port of the solver's forward
/// `seq.indexof` loop — the two must be able to disagree for a bug to surface.
///
/// SMT-LIB corners (validated by hand-computed value tests, since z3 4.15.4 is
/// NOT a usable oracle here: it computes wrong `seq.last_indexof` values —
/// neither 0 nor 1 for the rightmost of `[5,5]` — see tests):
///   * empty `sub` matches at the end ⇒ `Some(|s|)`;
///   * `|sub| > |s|` ⇒ `None`;
///   * ties resolve to the RIGHTMOST match.
fn rfind(s: &[ModelValue], sub: &[ModelValue]) -> Result<Option<usize>, String> {
    if sub.is_empty() {
        // Empty needle occurs at every position; the last is |s|.
        return Ok(Some(s.len()));
    }
    if sub.len() > s.len() {
        return Ok(None);
    }
    // Highest possible start, scanning downward for the first (⇒ rightmost) hit.
    for p in (0..=(s.len() - sub.len())).rev() {
        if match_at(s, sub, p)? {
            return Ok(Some(p));
        }
    }
    Ok(None)
}

/// `(seq.replace_all s src dst)`: replace every NON-OVERLAPPING left-to-right
/// occurrence of `src` in `s` by `dst`. An empty `src` leaves `s` unchanged
/// (there is no first position to anchor an infinite expansion). Built on this
/// crate's own `match_at` — independent of the solver evaluator's inline loop.
fn replace_all(
    s: &[ModelValue],
    src: &[ModelValue],
    dst: &[ModelValue],
) -> Result<Vec<ModelValue>, String> {
    if src.is_empty() {
        return Ok(s.to_vec());
    }
    let mut out: Vec<ModelValue> = Vec::with_capacity(s.len());
    let mut i = 0usize;
    while i < s.len() {
        if i + src.len() <= s.len() && match_at(s, src, i)? {
            out.extend_from_slice(dst);
            i += src.len();
        } else {
            out.push(s[i].clone());
            i += 1;
        }
    }
    Ok(out)
}

/// `(seq.extract s offset length)`: the maximal subsequence of `s` of length at
/// most `length`, starting at `offset`, when `0 <= offset < |s|` and
/// `length > 0`; otherwise the empty sequence.
fn extract(s: &[ModelValue], offset: &BigInt, length: &BigInt) -> Vec<ModelValue> {
    if offset.is_negative() || length.is_negative() || length.is_zero() {
        return Vec::new();
    }
    let Some(off) = offset.to_usize() else {
        return Vec::new();
    };
    if off >= s.len() {
        return Vec::new();
    }
    let avail = s.len() - off;
    let take = length.to_usize().unwrap_or(avail).min(avail);
    s[off..off + take].to_vec()
}

// --- small helpers --------------------------------------------------------

fn arg(args: &[ModelValue], i: usize) -> Result<&ModelValue, String> {
    args.get(i)
        .ok_or_else(|| "sequence operator: missing argument".to_string())
}

fn as_seq(v: &ModelValue) -> Result<&[ModelValue], String> {
    match v {
        ModelValue::Seq(xs) => Ok(xs),
        _ => Err("expected a sequence operand".to_string()),
    }
}

fn as_int(v: &ModelValue) -> Result<BigInt, String> {
    match v {
        ModelValue::Int(n) => Ok(n.clone()),
        _ => Err("expected an integer operand".to_string()),
    }
}

/// An index argument: an integer, returned as `BigInt`.
fn as_index(v: &ModelValue) -> Result<BigInt, String> {
    as_int(v)
}

/// `Some(idx)` iff `0 <= i < len`.
fn usize_in_range(i: BigInt, len: usize) -> Option<usize> {
    if i.is_negative() {
        return None;
    }
    i.to_usize().filter(|&idx| idx < len)
}

/// Clamp a (possibly out-of-range) search offset: `Some(o)` iff `0 <= off <= len`.
fn nonneg_offset(offset: &BigInt, len: usize) -> Option<usize> {
    if offset.is_negative() {
        return None;
    }
    offset.to_usize().filter(|&o| o <= len)
}
