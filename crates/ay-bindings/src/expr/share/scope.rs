// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lexical sharing boundaries and complete generated-name avoidance.

use super::{node_id, Expr};
use crate::expr::ExprValue;
use crate::sort::{Sort, SortInner};
use std::collections::HashSet;

pub(super) fn is_barrier(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Forall { .. } | ExprValue::Exists { .. }
    )
}

/// Every source symbol is reserved, including names inside opaque quantifiers.
/// Otherwise an enclosing let could capture a free symbol in their matrices.
/// Function and datatype symbols also share SMT's term namespace with lets.
pub(super) fn reserved_names(root: &Expr, binders: &[(String, Sort)]) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut sorts = HashSet::new();
    for (name, sort) in binders {
        names.insert(name.clone());
        sort_names(sort, &mut names, &mut sorts);
    }
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(expr) = pending.pop() {
        // A raw Expr can share its value Arc while carrying different outer
        // sort metadata. Do not let value memoization hide that metadata.
        sort_names(expr.sort(), &mut names, &mut sorts);
        if !seen.insert(node_id(expr)) {
            continue;
        }
        match expr.value() {
            ExprValue::Var { name } | ExprValue::FuncApp { name, .. } => {
                names.insert(name.clone());
            }
            ExprValue::Forall { vars, .. } | ExprValue::Exists { vars, .. } => {
                for (name, sort) in vars {
                    names.insert(name.clone());
                    sort_names(sort, &mut names, &mut sorts);
                }
            }
            ExprValue::DatatypeConstructor {
                datatype_name,
                constructor_name,
                ..
            }
            | ExprValue::DatatypeTester {
                datatype_name,
                constructor_name,
                ..
            } => {
                names.insert(datatype_name.clone());
                names.insert(constructor_name.clone());
            }
            ExprValue::DatatypeSelector {
                datatype_name,
                selector_name,
                ..
            } => {
                names.insert(datatype_name.clone());
                names.insert(selector_name.clone());
            }
            ExprValue::ConstArray { index_sort, .. } => {
                sort_names(index_sort, &mut names, &mut sorts);
            }
            _ => {}
        }
        pending.extend(expr.children());
    }
    names
}

fn sort_names(root: &Sort, names: &mut HashSet<String>, seen: &mut HashSet<*const SortInner>) {
    let mut pending = vec![root];
    while let Some(sort) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(sort.inner())) {
            continue;
        }
        match sort.inner() {
            SortInner::Array(array) => {
                pending.push(&array.index_sort);
                pending.push(&array.element_sort);
            }
            SortInner::Datatype(datatype) => {
                names.insert(datatype.name.clone());
                for constructor in &datatype.constructors {
                    names.insert(constructor.name.clone());
                    for field in &constructor.fields {
                        names.insert(field.name.clone());
                        pending.push(&field.sort);
                    }
                }
            }
            SortInner::Uninterpreted(name) | SortInner::DatatypeRef(name) => {
                names.insert(name.clone());
            }
            SortInner::Seq(element) => pending.push(element),
            _ => {}
        }
    }
}
