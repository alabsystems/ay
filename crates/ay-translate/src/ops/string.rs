// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String and regex operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Term};

use super::expect_result;
use crate::TranslationHost;

/// String binary predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrPredicate {
    Contains,
    PrefixOf,
    SuffixOf,
}

/// String concatenation. Panics on malformed input; see [`try_concat`].
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_concat(ctx, a, b), "string.concat")
}

/// Fallible [`concat()`] returning a `SolverError` instead of panicking.
pub fn try_concat<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_concat(a, b)
}

/// String length, returning Int. Panics on malformed input; see [`try_len`].
pub fn len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_len(ctx, s), "string.len")
}

/// Fallible [`len`] returning a `SolverError` instead of panicking.
pub fn try_len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_len(s)
}

/// Character at index, returning a length-1 String. Panics on malformed input; see [`try_at`].
pub fn at<V>(ctx: &mut impl TranslationHost<V>, s: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_at(ctx, s, idx), "string.at")
}

/// Fallible [`at`] returning a `SolverError` instead of panicking.
pub fn try_at<V>(ctx: &mut impl TranslationHost<V>, s: Term, idx: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_at(s, idx)
}

/// Substring extraction. Panics on malformed input; see [`try_substr`].
pub fn substr<V>(ctx: &mut impl TranslationHost<V>, s: Term, offset: Term, len: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_substr(ctx, s, offset, len), "string.substr")
}

/// Fallible [`substr`] returning a `SolverError` instead of panicking.
pub fn try_substr<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    offset: Term,
    len: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_substr(s, offset, len)
}

/// String predicate (contains, prefixof, suffixof). Panics on malformed input; see
/// [`try_predicate`].
pub fn predicate<V>(ctx: &mut impl TranslationHost<V>, pred: StrPredicate, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match pred {
        StrPredicate::Contains => (
            ctx.solver().try_str_contains(a, b),
            "string.predicate.contains",
        ),
        StrPredicate::PrefixOf => (
            ctx.solver().try_str_prefixof(a, b),
            "string.predicate.prefixof",
        ),
        StrPredicate::SuffixOf => (
            ctx.solver().try_str_suffixof(a, b),
            "string.predicate.suffixof",
        ),
    };
    expect_result(result, tag)
}

/// Fallible [`predicate`] returning a `SolverError` instead of panicking.
pub fn try_predicate<V>(
    ctx: &mut impl TranslationHost<V>,
    pred: StrPredicate,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match pred {
        StrPredicate::Contains => ctx.solver().try_str_contains(a, b),
        StrPredicate::PrefixOf => ctx.solver().try_str_prefixof(a, b),
        StrPredicate::SuffixOf => ctx.solver().try_str_suffixof(a, b),
    }
}

/// String index-of, returning Int (-1 if not found). Panics on malformed input; see
/// [`try_indexof`].
pub fn indexof<V>(ctx: &mut impl TranslationHost<V>, s: Term, t: Term, start: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_indexof(ctx, s, t, start), "string.indexof")
}

/// Fallible [`indexof`] returning a `SolverError` instead of panicking.
pub fn try_indexof<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    t: Term,
    start: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_indexof(s, t, start)
}

/// String replacement (first occurrence). Panics on malformed input; see [`try_replace`].
pub fn replace<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_replace(ctx, s, from, to), "string.replace")
}

/// Fallible [`replace`] returning a `SolverError` instead of panicking.
pub fn try_replace<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    from: Term,
    to: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_replace(s, from, to)
}

/// String replace-all. Panics on malformed input; see [`try_replace_all`].
pub fn replace_all<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_replace_all(ctx, s, from, to), "string.replace_all")
}

/// Fallible [`replace_all`] returning a `SolverError` instead of panicking.
pub fn try_replace_all<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    from: Term,
    to: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_replace_all(s, from, to)
}

/// String to integer conversion. Panics on malformed input; see [`try_to_int`].
pub fn to_int<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_int(ctx, s), "string.to_int")
}

/// Fallible [`to_int`] returning a `SolverError` instead of panicking.
pub fn try_to_int<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_to_int(s)
}

/// Integer to string conversion. Panics on malformed input; see [`try_from_int`].
pub fn from_int<V>(ctx: &mut impl TranslationHost<V>, n: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_from_int(ctx, n), "string.from_int")
}

/// Fallible [`from_int`] returning a `SolverError` instead of panicking.
pub fn try_from_int<V>(ctx: &mut impl TranslationHost<V>, n: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_from_int(n)
}

/// String to regex conversion. Panics on malformed input; see [`try_to_re`].
pub fn to_re<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_re(ctx, s), "string.to_re")
}

/// Fallible [`to_re`] returning a `SolverError` instead of panicking.
pub fn try_to_re<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_to_re(s)
}

/// Regex membership test. Panics on malformed input; see [`try_in_re`].
pub fn in_re<V>(ctx: &mut impl TranslationHost<V>, s: Term, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_in_re(ctx, s, re), "string.in_re")
}

/// Fallible [`in_re`] returning a `SolverError` instead of panicking.
pub fn try_in_re<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    re: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_str_in_re(s, re)
}

/// Kleene star of a regex. Panics on malformed input; see [`try_re_star`].
pub fn re_star<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_re_star(ctx, re), "string.re_star")
}

/// Fallible [`re_star`] returning a `SolverError` instead of panicking.
pub fn try_re_star<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_re_star(re)
}

/// Kleene plus of a regex. Panics on malformed input; see [`try_re_plus`].
pub fn re_plus<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_re_plus(ctx, re), "string.re_plus")
}

/// Fallible [`re_plus`] returning a `SolverError` instead of panicking.
pub fn try_re_plus<V>(ctx: &mut impl TranslationHost<V>, re: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_re_plus(re)
}

/// Union of two regexes. Panics on malformed input; see [`try_re_union`].
pub fn re_union<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_re_union(ctx, a, b), "string.re_union")
}

/// Fallible [`re_union`] returning a `SolverError` instead of panicking.
pub fn try_re_union<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_re_union(a, b)
}

/// Concatenation of two regexes. Panics on malformed input; see [`try_re_concat`].
pub fn re_concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_re_concat(ctx, a, b), "string.re_concat")
}

/// Fallible [`re_concat`] returning a `SolverError` instead of panicking.
pub fn try_re_concat<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_re_concat(a, b)
}

/// String constant. Infallible — no fallible variant needed.
pub fn string_const<V>(ctx: &mut impl TranslationHost<V>, value: &str) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().string_const(value)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "string_tests.rs"]
mod tests;
