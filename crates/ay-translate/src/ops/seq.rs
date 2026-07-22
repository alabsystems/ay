// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Sequence predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqPredicate {
    Contains,
    PrefixOf,
    SuffixOf,
}

/// Empty sequence constant for the given element sort. Infallible — no fallible variant needed.
pub fn empty<V>(ctx: &mut impl TranslationHost<V>, element_sort: Sort) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().seq_empty(element_sort)
}

/// Unit sequence containing a single element. Panics on malformed input; see [`try_unit`].
pub fn unit<V>(ctx: &mut impl TranslationHost<V>, elem: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_unit(ctx, elem), "seq.unit")
}

/// Fallible [`unit()`] returning a `SolverError` instead of panicking.
pub fn try_unit<V>(ctx: &mut impl TranslationHost<V>, elem: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_seq_unit(elem)
}

/// Sequence concatenation. Panics on malformed input; see [`try_concat`].
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_concat(ctx, a, b), "seq.concat")
}

/// Fallible `concat`() returning a `SolverError` instead of panicking.
pub fn try_concat<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_seq_concat(a, b)
}

/// Sequence length, returning Int. Panics on malformed input; see [`try_len`].
pub fn len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_len(ctx, s), "seq.len")
}

/// Fallible [`len`] returning a `SolverError` instead of panicking.
pub fn try_len<V>(ctx: &mut impl TranslationHost<V>, s: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_seq_len(s)
}

/// Element at index, returning the element sort. Panics on malformed input; see [`try_nth`].
pub fn nth<V>(ctx: &mut impl TranslationHost<V>, s: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_nth(ctx, s, idx), "seq.nth")
}

/// Fallible [`nth`] returning a `SolverError` instead of panicking.
pub fn try_nth<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    idx: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_seq_nth(s, idx)
}

/// Subsequence extraction. Panics on malformed input; see [`try_extract`].
pub fn extract<V>(ctx: &mut impl TranslationHost<V>, s: Term, offset: Term, len: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_extract(ctx, s, offset, len), "seq.extract")
}

/// Fallible [`extract`] returning a `SolverError` instead of panicking.
pub fn try_extract<V>(
    ctx: &mut impl TranslationHost<V>,
    s: Term,
    offset: Term,
    len: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_seq_extract(s, offset, len)
}

/// Sequence predicate (contains, prefixof, suffixof). Panics on malformed input; see
/// [`try_predicate`].
pub fn predicate<V>(ctx: &mut impl TranslationHost<V>, pred: SeqPredicate, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match pred {
        SeqPredicate::Contains => (
            ctx.solver().try_seq_contains(a, b),
            "seq.predicate.contains",
        ),
        SeqPredicate::PrefixOf => (
            ctx.solver().try_seq_prefixof(a, b),
            "seq.predicate.prefixof",
        ),
        SeqPredicate::SuffixOf => (
            ctx.solver().try_seq_suffixof(a, b),
            "seq.predicate.suffixof",
        ),
    };
    expect_result(result, tag)
}

/// Fallible [`predicate`] returning a `SolverError` instead of panicking.
pub fn try_predicate<V>(
    ctx: &mut impl TranslationHost<V>,
    pred: SeqPredicate,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match pred {
        SeqPredicate::Contains => ctx.solver().try_seq_contains(a, b),
        SeqPredicate::PrefixOf => ctx.solver().try_seq_prefixof(a, b),
        SeqPredicate::SuffixOf => ctx.solver().try_seq_suffixof(a, b),
    }
}

/// Sequence index-of, returning Int (-1 if not found). Panics on malformed input; see
/// [`try_indexof`].
pub fn indexof<V>(ctx: &mut impl TranslationHost<V>, s: Term, t: Term, start: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_indexof(ctx, s, t, start), "seq.indexof")
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
    ctx.solver().try_seq_indexof(s, t, start)
}

/// Sequence replacement (first occurrence). Panics on malformed input; see [`try_replace`].
pub fn replace<V>(ctx: &mut impl TranslationHost<V>, s: Term, from: Term, to: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_replace(ctx, s, from, to), "seq.replace")
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
    ctx.solver().try_seq_replace(s, from, to)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "seq_tests.rs"]
mod tests;
