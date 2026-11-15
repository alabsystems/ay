// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A stopped validation carries no expression, key, or mathematical answer.

use super::SynthesisBudget;
use std::fmt::{self, Write};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ValidationStopped;

pub(super) type ValidationResult<T> = Result<T, ValidationStopped>;

pub(super) fn check(budget: &SynthesisBudget) -> ValidationResult<()> {
    if budget.expired() {
        Err(ValidationStopped)
    } else {
        Ok(())
    }
}

pub(super) fn run<T>(
    budget: &SynthesisBudget,
    operation: impl FnOnce() -> ValidationResult<T>,
) -> ValidationResult<T> {
    check(budget)?;
    let result = operation();
    check(budget)?;
    result
}

pub(super) fn simplify(
    expr: &crate::ChcExpr,
    budget: &SynthesisBudget,
) -> ValidationResult<crate::ChcExpr> {
    expr.simplify_constants_checked(|| budget.expired())
        .ok_or(ValidationStopped)
}

pub(super) fn substitute(
    expr: &crate::ChcExpr,
    substitutions: &[(crate::ChcVar, crate::ChcExpr)],
    budget: &SynthesisBudget,
) -> ValidationResult<crate::ChcExpr> {
    expr.substitute_checked(substitutions, || budget.expired())
        .ok_or(ValidationStopped)
}

/// Preserve every byte of a completed Debug key. A failed write discards the
/// entire buffer; unlike diagnostic prefixes, it never becomes an identity.
pub(super) fn debug_key(
    value: &impl fmt::Debug,
    budget: &SynthesisBudget,
) -> ValidationResult<String> {
    struct Writer<'a> {
        text: String,
        budget: &'a SynthesisBudget,
    }

    impl Write for Writer<'_> {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            check(self.budget).map_err(|_| fmt::Error)?;
            self.text.push_str(text);
            Ok(())
        }
    }

    check(budget)?;
    let mut writer = Writer {
        text: String::new(),
        budget,
    };
    write!(&mut writer, "{value:?}").map_err(|_| ValidationStopped)?;
    check(budget)?;
    Ok(writer.text)
}

/// Copy map entries between polls; a large clone cannot hide cancellation.
pub(super) fn clone_map<K: Clone + Eq + std::hash::Hash, V: Clone>(
    values: &ay_core::kani_compat::DetHashMap<K, V>,
    budget: &SynthesisBudget,
) -> ValidationResult<ay_core::kani_compat::DetHashMap<K, V>> {
    let mut copy = ay_core::kani_compat::DetHashMap::default();
    for (key, value) in values {
        check(budget)?;
        copy.insert(key.clone(), value.clone());
    }
    check(budget)?;
    Ok(copy)
}

pub(super) fn conjuncts<'a>(
    expr: &'a crate::ChcExpr,
    budget: &SynthesisBudget,
) -> ValidationResult<Vec<&'a crate::ChcExpr>> {
    expr.conjuncts_checked(|| budget.expired())
        .ok_or(ValidationStopped)
}

pub(super) fn any<T>(
    values: impl IntoIterator<Item = T>,
    budget: &SynthesisBudget,
    mut predicate: impl FnMut(T) -> ValidationResult<bool>,
) -> ValidationResult<bool> {
    for value in values {
        check(budget)?;
        if predicate(value)? {
            return Ok(true);
        }
    }
    check(budget)?;
    Ok(false)
}
pub(super) fn all<T>(
    values: impl IntoIterator<Item = T>,
    budget: &SynthesisBudget,
    mut predicate: impl FnMut(T) -> ValidationResult<bool>,
) -> ValidationResult<bool> {
    for value in values {
        check(budget)?;
        if !predicate(value)? {
            return Ok(false);
        }
    }
    check(budget)?;
    Ok(true)
}

/// Same conservative depth fallback as the canonical name query, with explicit
/// cancellation between nodes. This has no authority to simplify a formula.
pub(super) fn contains_var_name(
    expr: &crate::ChcExpr,
    name: &str,
    budget: &SynthesisBudget,
) -> ValidationResult<bool> {
    use crate::ChcExpr;
    let mut pending = vec![(expr, 0)];
    while let Some((node, depth)) = pending.pop() {
        check(budget)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return Ok(true);
        }
        match node {
            ChcExpr::Var(var) if var.name == name => return Ok(true),
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args.iter().rev() {
                    check(budget)?;
                    pending.push((arg.as_ref(), depth + 1));
                }
            }
            ChcExpr::ConstArray(_, value) => pending.push((value, depth + 1)),
            _ => {}
        }
    }
    Ok(false)
}

pub(super) fn cloned<'a, T: Clone + 'a>(
    values: impl IntoIterator<Item = &'a T>,
    budget: &SynthesisBudget,
) -> ValidationResult<Vec<T>> {
    let mut copy = Vec::new();
    for value in values {
        check(budget)?;
        copy.push(value.clone());
    }
    check(budget)?;
    Ok(copy)
}

pub(super) fn bindings(
    vars: &[crate::ChcVar],
    args: &[crate::ChcExpr],
    budget: &SynthesisBudget,
) -> ValidationResult<Vec<(crate::ChcVar, crate::ChcExpr)>> {
    let mut result = Vec::new();
    for (var, arg) in vars.iter().zip(args) {
        check(budget)?;
        result.push((var.clone(), arg.clone()));
    }
    check(budget)?;
    Ok(result)
}
