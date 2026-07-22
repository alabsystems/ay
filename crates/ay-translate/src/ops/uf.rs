// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Uninterpreted function operations.

use std::hash::Hash;

use ay_dpll::api::{FuncDecl, SolverError, Sort, Term};

use super::expect_result;
use crate::TranslationHost;

/// Declare or retrieve an uninterpreted function.
///
/// Uses the context's function declaration cache so repeated calls
/// with the same name return the same `FuncDecl` without re-declaring.
///
/// # Arguments
/// * `ctx` - Translation context
/// * `name` - Function name
/// * `domain` - Argument sorts
/// * `range` - Return sort
///
/// # Returns
/// A function declaration that can be applied to arguments.
pub fn declare<V>(
    ctx: &mut impl TranslationHost<V>,
    name: &str,
    domain: &[Sort],
    range: Sort,
) -> FuncDecl
where
    V: Eq + Hash,
{
    ctx.declare_or_get_fun(name, domain, range)
}

/// Define a non-recursive function for inline expansion.
///
/// `params` are already-created parameter variables and `body` must be built
/// using those variables. The returned function handle can be applied with
/// [`apply`]. Hosts backed by [`crate::TranslationState`] also cache the
/// definition by name for later `FuncApp` translation.
pub fn define<V>(
    ctx: &mut impl TranslationHost<V>,
    name: &str,
    params: &[(&str, Term)],
    range: Sort,
    body: Term,
) -> FuncDecl
where
    V: Eq + Hash,
{
    expect_result(try_define(ctx, name, params, range, body), "uf.define")
}

/// Fallible [`define`] returning a `SolverError` instead of panicking.
pub fn try_define<V>(
    ctx: &mut impl TranslationHost<V>,
    name: &str,
    params: &[(&str, Term)],
    range: Sort,
    body: Term,
) -> Result<FuncDecl, SolverError>
where
    V: Eq + Hash,
{
    ctx.try_define_fun_body(name, params, range, body)
}

/// Apply an uninterpreted function to arguments.
///
/// # Arguments
/// * `ctx` - Translation context
/// * `func` - The function declaration
/// * `args` - Arguments to apply
///
/// # Returns
/// The function application term.
pub fn apply<V>(ctx: &mut impl TranslationHost<V>, func: &FuncDecl, args: &[Term]) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_apply(ctx, func, args), "uf.apply")
}

/// Fallible [`apply`] returning a `SolverError` instead of panicking.
pub fn try_apply<V>(
    ctx: &mut impl TranslationHost<V>,
    func: &FuncDecl,
    args: &[Term],
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_apply(func, args)
}

#[cfg(test)]
#[path = "uf_tests.rs"]
mod tests;
