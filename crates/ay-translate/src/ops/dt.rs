// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype operations.
//!
//! Provides constructor application, field selection, and constructor testing
//! for algebraic datatypes (structs and enums).

use std::hash::Hash;

use ay_dpll::api::{DatatypeSort, SolverError, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Declare a datatype with the solver. Panics on malformed input; see [`try_declare`].
pub fn declare<V>(ctx: &mut impl TranslationHost<V>, dt: &DatatypeSort)
where
    V: Eq + Hash,
{
    expect_result(try_declare(ctx, dt), "dt.declare");
}

/// Fallible [`declare`] returning a `SolverError` instead of panicking.
pub fn try_declare<V>(
    ctx: &mut impl TranslationHost<V>,
    dt: &DatatypeSort,
) -> Result<(), SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_declare_datatype(dt)
}

/// Apply a datatype constructor. Panics on malformed input; see [`try_constructor`].
///
/// Requires the datatype to have been previously declared via [`declare`].
pub fn constructor<V>(
    ctx: &mut impl TranslationHost<V>,
    dt: &DatatypeSort,
    ctor_name: &str,
    args: &[Term],
) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_constructor(ctx, dt, ctor_name, args), "dt.constructor")
}

/// Fallible [`constructor`] returning a `SolverError` instead of panicking.
pub fn try_constructor<V>(
    ctx: &mut impl TranslationHost<V>,
    dt: &DatatypeSort,
    ctor_name: &str,
    args: &[Term],
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_datatype_constructor(dt, ctor_name, args)
}

/// Select a field from a datatype expression. Panics on malformed input; see [`try_selector`].
///
/// The `selector_name` must match a field name from the datatype declaration.
pub fn selector<V>(
    ctx: &mut impl TranslationHost<V>,
    selector_name: &str,
    expr: Term,
    result_sort: Sort,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        try_selector(ctx, selector_name, expr, result_sort),
        "dt.selector",
    )
}

/// Fallible [`selector`] returning a `SolverError` instead of panicking.
pub fn try_selector<V>(
    ctx: &mut impl TranslationHost<V>,
    selector_name: &str,
    expr: Term,
    result_sort: Sort,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver()
        .try_datatype_selector(selector_name, expr, result_sort)
}

/// Test if an expression was constructed with a specific constructor. Panics on malformed
/// input; see [`try_tester`].
///
/// Returns a Bool term that is true iff `expr` matches `ctor_name`.
pub fn tester<V>(ctx: &mut impl TranslationHost<V>, ctor_name: &str, expr: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_tester(ctx, ctor_name, expr), "dt.tester")
}

/// Fallible [`tester`] returning a `SolverError` instead of panicking.
pub fn try_tester<V>(
    ctx: &mut impl TranslationHost<V>,
    ctor_name: &str,
    expr: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_datatype_tester(ctor_name, expr)
}

#[cfg(test)]
#[path = "dt_tests.rs"]
mod tests;
