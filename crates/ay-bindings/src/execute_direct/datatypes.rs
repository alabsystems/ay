// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Sort lowering and datatype operations under the definition registry.
//!
//! The native lane resolves a datatype by NAME (a declared datatype lowers to
//! `Uninterpreted(name)`, a constructor application is looked up by name), so
//! the definition behind each name is fixed here, once, by the program's
//! `declare-datatype` commands, and every sort lowered afterwards, whether on
//! a constant, a binder, a function signature, or a datatype term, must be
//! structurally equal to it. That keeps a term from being lowered under a
//! definition other than the one the checked expression API authenticated it
//! against, whatever order the declarations arrived in.

use ay_dpll::api::{Sort as ApiSort, Term};

use super::context::ExecutionContext;
use super::translate::translate_expr;
use super::ExecuteError;
use crate::expr::dt::{authenticate_definitions, Unregistered};
use crate::expr::{Expr, ExprValue};
use crate::sort::{DatatypeSort, Sort, SortInner};

/// Translate ay_bindings::Sort to ay_dpll::api::Sort under the context's
/// datatype registry.
///
/// Every datatype definition in `sort` must be structurally equal to the one
/// declared under its name in `ctx` (a shared node is compared by identity);
/// an undeclared datatype, a definition that differs from the declared one,
/// or a same-named definition shadowing an enclosing one is refused. This is
/// the backstop behind `AYProgram::try_declare_datatype`: a datatype term or
/// variable is lowered only under the definition the checked expression API
/// authenticated it against, whatever order the declarations arrived in.
pub(super) fn translate_sort(ctx: &ExecutionContext, sort: &Sort) -> Result<ApiSort, ExecuteError> {
    authenticate_sort(ctx, sort)?;
    lower_sort(sort)
}

/// [`translate_sort`]'s registry check alone.
pub(super) fn authenticate_sort(ctx: &ExecutionContext, sort: &Sort) -> Result<(), ExecuteError> {
    let undeclared = authenticate_definitions(
        "lower_sort",
        sort,
        &ctx.datatype_definitions,
        Unregistered::Refuse,
    )
    .map_err(|error| ExecuteError::SortTranslation(error.to_string()))?;
    match undeclared.first().and_then(|sort| sort.datatype_sort()) {
        Some(dt) => Err(ExecuteError::SortTranslation(format!(
            "datatype `{}` is not declared; declare it before its first use",
            dt.name
        ))),
        None => Ok(()),
    }
}

/// Translate ay_bindings::Sort to ay_dpll::api::Sort without a registry.
///
/// Uses the From impl from sort.rs for supported sorts. Datatype sorts
/// are translated to `Sort::Uninterpreted(name)` which is how the SMT-LIB
/// parser represents declared datatypes internally.
///
/// A [`SortInner::DatatypeRef`] outside a declaration of the datatype it
/// names is refused: lowering it would produce a bare sort name that the
/// solver cannot tell apart from the datatype, or from an unrelated sort.
pub(super) fn lower_sort(sort: &Sort) -> Result<ApiSort, ExecuteError> {
    if let Some(name) = sort.dangling_datatype_ref() {
        return Err(ExecuteError::SortTranslation(format!(
            "datatype reference `{name}` is not inside a declaration of `{name}`"
        )));
    }
    translate_checked_sort(sort)
}

/// [`lower_sort`] after the caller has resolved every datatype reference.
fn translate_checked_sort(sort: &Sort) -> Result<ApiSort, ExecuteError> {
    match sort.inner() {
        // Datatype sorts map to Uninterpreted(name) — the DeclareDatatype
        // constraint registers the actual DT structure with the solver.
        SortInner::Datatype(dt) => Ok(ay_core::Sort::Uninterpreted(dt.name.clone())),
        _ => Ok(ay_core::Sort::from(sort)),
    }
}

/// Bridge a ay_bindings DatatypeSort to ay_core DatatypeSort.
///
/// Both crates define identical DatatypeSort structures but with different
/// Sort types for fields. This function converts by translating each field sort.
pub(super) fn bridge_datatype(dt: &DatatypeSort) -> Result<ay_core::DatatypeSort, ExecuteError> {
    // A field may refer to this declaration (a recursive datatype) or to a
    // datatype declared around the reference; nothing else.
    if let Some(name) = crate::sort::dangling_datatype_ref_in_declaration(dt) {
        return Err(ExecuteError::SortTranslation(format!(
            "datatype reference `{name}` in the declaration of `{}` names no enclosing datatype",
            dt.name
        )));
    }
    let constructors = dt
        .constructors
        .iter()
        .map(|ctor| {
            let fields: Result<Vec<_>, _> = ctor
                .fields
                .iter()
                .map(|f| {
                    let sort = translate_checked_sort(&f.sort)?;
                    Ok(ay_core::DatatypeField::new(&f.name, sort))
                })
                .collect();
            Ok(ay_core::DatatypeConstructor::new(&ctor.name, fields?))
        })
        .collect::<Result<Vec<_>, ExecuteError>>()?;
    Ok(ay_core::DatatypeSort::new(&dt.name, constructors))
}

/// Execute a `declare-datatype` command: the definitions nested in the
/// fields must already be declared and equal to their declarations; an equal
/// repeat of this one is idempotent; a different one under the name is
/// refused.
pub(super) fn declare_datatype(
    ctx: &mut ExecutionContext,
    dt: &DatatypeSort,
) -> Result<(), ExecuteError> {
    let definition = Sort::from_inner(SortInner::Datatype(dt.clone()));
    let new = authenticate_definitions(
        "declare_datatype",
        &definition,
        &ctx.datatype_definitions,
        Unregistered::Refuse,
    )
    .map_err(|error| ExecuteError::SortTranslation(error.to_string()))?;
    if new.is_empty() {
        return Ok(());
    }
    let core_dt = bridge_datatype(dt)?;
    ctx.solver
        .try_declare_datatype(&core_dt)
        .map_err(|e| ExecuteError::ConstraintExecution(e.to_string()))?;
    ctx.declared_datatypes.insert(dt.name.clone(), core_dt);
    ctx.datatype_definitions.insert(dt.name.clone(), definition);
    Ok(())
}

/// Translate a datatype constructor, selector or tester. The descriptor the
/// checked expression API authenticated the term against (its own sort for a
/// constructor, the receiver's sort for a selector or tester) must be the
/// definition registered under its name, or the solver would answer under a
/// different datatype.
pub(super) fn translate_datatype_op(
    ctx: &mut ExecutionContext,
    expr: &Expr,
) -> Result<Term, ExecuteError> {
    match expr.value() {
        ExprValue::DatatypeConstructor {
            datatype_name,
            constructor_name,
            args,
        } => {
            authenticate_sort(ctx, expr.sort())?;
            let core_dt = ctx
                .declared_datatypes
                .get(datatype_name)
                .ok_or_else(|| {
                    ExecuteError::ExprTranslation(format!(
                        "undeclared datatype '{datatype_name}' in constructor application"
                    ))
                })?
                .clone();
            let translated_args: Result<Vec<_>, _> =
                args.iter().map(|a| translate_expr(ctx, a)).collect();
            ctx.solver
                .try_datatype_constructor(&core_dt, constructor_name, &translated_args?)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
        ExprValue::DatatypeSelector {
            selector_name,
            expr: inner,
            ..
        } => {
            authenticate_sort(ctx, inner.sort())?;
            let translated = translate_expr(ctx, inner)?;
            let result_sort = translate_sort(ctx, expr.sort())?;
            ctx.solver
                .try_datatype_selector(selector_name, translated, result_sort)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
        ExprValue::DatatypeTester {
            constructor_name,
            expr: inner,
            ..
        } => {
            authenticate_sort(ctx, inner.sort())?;
            let translated = translate_expr(ctx, inner)?;
            ctx.solver
                .try_datatype_tester(constructor_name, translated)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
        _ => Err(ExecuteError::Internal(format!(
            "translate_datatype_op did not handle expression: {expr}"
        ))),
    }
}
