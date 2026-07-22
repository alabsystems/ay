// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Read from array at index (select). Panics on malformed input; see [`try_select`] for the
/// fallible variant.
pub fn select<V>(ctx: &mut impl TranslationHost<V>, arr: Term, idx: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_select(ctx, arr, idx), "array.select")
}

/// Fallible [`select`] returning a `SolverError` instead of panicking.
pub fn try_select<V>(
    ctx: &mut impl TranslationHost<V>,
    arr: Term,
    idx: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_select(arr, idx)
}

/// Write to array at index (store). Panics on malformed input; see [`try_store`] for the
/// fallible variant.
pub fn store<V>(ctx: &mut impl TranslationHost<V>, arr: Term, idx: Term, val: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_store(ctx, arr, idx, val), "array.store")
}

/// Fallible [`store`] returning a `SolverError` instead of panicking.
pub fn try_store<V>(
    ctx: &mut impl TranslationHost<V>,
    arr: Term,
    idx: Term,
    val: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_store(arr, idx, val)
}

/// Create a constant array. Panics on malformed input; see [`try_const_array`] for the
/// fallible variant.
pub fn const_array<V>(ctx: &mut impl TranslationHost<V>, idx_sort: Sort, val: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_const_array(ctx, idx_sort, val), "array.const_array")
}

/// Fallible [`const_array`] returning a `SolverError` instead of panicking.
pub fn try_const_array<V>(
    ctx: &mut impl TranslationHost<V>,
    idx_sort: Sort,
    val: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_const_array(idx_sort, val)
}
