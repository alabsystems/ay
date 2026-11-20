// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recursive payload spelling shared by both source identities.
//!
//! A datatype sort is spelled by reference, `Datatype("name";@<id>)`, where
//! `<id>` is its constructor list's content address ([`crate::ChcDtId`]).
//! Every list a spelling references is recorded in [`DatatypeRefs`]; the
//! normalized input then defines each one once. Inline spelling repeated the
//! whole nested definition at every occurrence: `2^k` text for `O(k)` types.

use super::*;
use crate::ChcDtConstructors;
use std::collections::BTreeSet;

/// Datatype constructor lists referenced by a spelling.
#[derive(Default)]
pub(super) struct DatatypeRefs(BTreeSet<ChcDtConstructors>);

impl DatatypeRefs {
    fn note(&mut self, constructors: &ChcDtConstructors) {
        if !self.0.contains(constructors) {
            self.0.insert(constructors.clone());
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Spell every list in `refs`, and every list those definitions reference,
/// once each, in content-address order: `(id, constructor parts)`.
///
/// Each list is spelled once however many sorts share it, so the cost is the
/// size of the datatype DAG, not of its tree expansion.
pub(super) fn datatype_definitions<P: Progress>(
    refs: DatatypeRefs,
    progress: &mut P,
) -> Result<Vec<(crate::ChcDtId, String)>, P::Error> {
    progress.poll()?;
    let mut definitions: BTreeMap<ChcDtConstructors, String> = BTreeMap::new();
    let mut pending: Vec<ChcDtConstructors> = refs.0.into_iter().collect();
    while let Some(constructors) = pending.pop() {
        progress.poll()?;
        if definitions.contains_key(&constructors) {
            continue;
        }
        let mut children = DatatypeRefs::default();
        let parts = constructor_parts(&constructors, progress, &mut children)?;
        definitions.insert(constructors, parts);
        pending.extend(
            children
                .0
                .into_iter()
                .filter(|child| !definitions.contains_key(child)),
        );
    }
    progress.poll()?;
    Ok(definitions
        .into_iter()
        .map(|(constructors, parts)| (constructors.id(), parts))
        .collect())
}

/// `"ctor"("selector":sort,...)|...`, the spelling a definition has always used.
fn constructor_parts<P: Progress>(
    constructors: &ChcDtConstructors,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    let mut ctor_parts = Vec::new();
    for constructor in constructors.iter() {
        progress.poll()?;
        let mut selectors = Vec::new();
        for selector in &constructor.selectors {
            progress.poll()?;
            selectors.push(format!(
                "{}:{}",
                json_string(&selector.name),
                normalized_sort(&selector.sort, progress, refs)?
            ));
        }
        progress.poll()?;
        ctor_parts.push(format!(
            "{}({})",
            json_string(&constructor.name),
            selectors.join(",")
        ));
    }
    progress.poll()?;
    Ok(ctor_parts.join("|"))
}

pub(super) fn predicate_app<P: Progress>(
    pred: PredicateId,
    args: &[ChcExpr],
    pred_names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    progress.poll()?;
    let pred = pred_names
        .get(&pred.index())
        .cloned()
        .unwrap_or_else(|| fallback_predicate_name(pred));
    let mut children = Vec::new();
    for arg in args {
        children.push(expression(arg, pred_names, progress, refs)?);
    }
    progress.poll()?;
    let result = format!("{pred}({})", children.join(","));
    progress.poll()?;
    Ok(result)
}

pub(super) fn expression<P: Progress>(
    expr: &ChcExpr,
    pred_names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    progress.poll()?;
    let result = match expr {
        ChcExpr::ArrayLambda(lambda) => array_lambda(lambda, pred_names, progress, refs)?,
        ChcExpr::Bool(value) => format!("bool:{value}"),
        ChcExpr::Int(value) => format!("int:{value}"),
        ChcExpr::Real(numer, denom) => format!("real:{numer}/{denom}"),
        ChcExpr::BitVec(value, width) => format!("bv{width}:{value}"),
        ChcExpr::Var(var) => format!(
            "var:{}:{}",
            json_string(&var.name),
            normalized_sort(&var.sort, progress, refs)?
        ),
        ChcExpr::Op(op, args) => {
            let mut children = Vec::new();
            for arg in args {
                children.push(expression(arg, pred_names, progress, refs)?);
            }
            progress.poll()?;
            if is_commutative_op(*op) {
                progress.sort(&mut children, |s| Key::text(s))?;
            }
            progress.poll()?;
            format!("op:{op:?}({})", children.join(","))
        }
        ChcExpr::PredicateApp(name, pred, args) => {
            let pred = pred_names
                .get(&pred.index())
                .cloned()
                .unwrap_or_else(|| fallback_predicate_name(*pred));
            let mut children = Vec::new();
            for arg in args {
                children.push(expression(arg, pred_names, progress, refs)?);
            }
            progress.poll()?;
            format!(
                "pred-expr:{pred}:{}({})",
                json_string(name),
                children.join(",")
            )
        }
        ChcExpr::FuncApp(_, _, args) if args.len() == 1 => {
            unary_functions(expr, pred_names, progress, refs)?
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let mut children = Vec::new();
            for arg in args {
                children.push(expression(arg, pred_names, progress, refs)?);
            }
            progress.poll()?;
            format!(
                "func:{}:{}({})",
                json_string(name),
                normalized_sort(sort, progress, refs)?,
                children.join(",")
            )
        }
        ChcExpr::ConstArrayMarker(sort) => {
            format!(
                "const-array-marker:{}",
                normalized_sort(sort, progress, refs)?
            )
        }
        ChcExpr::IsTesterMarker(name) => format!("is-tester:{}", json_string(name)),
        ChcExpr::ConstArray(key_sort, value) => format!(
            "const-array:{}:{}",
            normalized_sort(key_sort, progress, refs)?,
            expression(value, pred_names, progress, refs)?
        ),
    };
    progress.poll()?;
    Ok(result)
}

/// Write a unary chain once instead of copying its complete suffix at every
/// level. Reference definitions are collected in a set, so visiting the sorts
/// before the leaf changes neither their final order nor any canonical byte.
fn unary_functions<P: Progress>(
    mut expr: &ChcExpr,
    pred_names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    let mut result = String::new();
    let mut closings = 0usize;
    while let ChcExpr::FuncApp(name, sort, args) = expr {
        let [argument] = args.as_slice() else {
            break;
        };
        progress.poll()?;
        let name = json_string(name);
        let sort = normalized_sort(sort, progress, refs)?;
        progress.poll()?;
        result.push_str("func:");
        result.push_str(&name);
        result.push(':');
        result.push_str(&sort);
        result.push('(');
        closings += 1;
        expr = argument;
    }
    let leaf = expression(expr, pred_names, progress, refs)?;
    progress.poll()?;
    result.push_str(&leaf);
    for _ in 0..closings {
        progress.poll()?;
        result.push(')');
    }
    progress.poll()?;
    Ok(result)
}

pub(super) fn normalized_sort<P: Progress>(
    sort: &ChcSort,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    progress.poll()?;
    let result = match sort {
        ChcSort::Bool => "Bool".to_string(),
        ChcSort::Int => "Int".to_string(),
        ChcSort::Real => "Real".to_string(),
        ChcSort::BitVec(width) => format!("BitVec({width})"),
        ChcSort::Array(key, value) => format!(
            "Array({},{})",
            normalized_sort(key, progress, refs)?,
            normalized_sort(value, progress, refs)?
        ),
        ChcSort::Uninterpreted(name) => format!("Uninterpreted({})", json_string(name)),
        ChcSort::Datatype { name, constructors } => match progress.datatype_spelling() {
            DatatypeSpelling::ReferenceV2 => {
                refs.note(constructors);
                format!("Datatype({};@{})", json_string(name), constructors.id())
            }
            DatatypeSpelling::InlineV1 => format!(
                "Datatype({};{})",
                json_string(name),
                constructor_parts(constructors, progress, refs)?
            ),
        },
    };
    progress.poll()?;
    Ok(result)
}

pub(super) fn is_commutative_op(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::And
            | ChcOp::Or
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Mul
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::BvAdd
            | ChcOp::BvMul
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
    )
}

fn array_lambda<P: Progress>(
    lambda: &crate::expr::ChcArrayLambda,
    names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    let mut formals = Vec::new();
    for formal in lambda.formals() {
        progress.poll()?;
        formals.push(format!(
            "{}:{}",
            json_string(&formal.name),
            normalized_sort(&formal.sort, progress, refs)?
        ));
    }
    let mut captures = Vec::new();
    for capture in lambda.captures() {
        captures.push(expression(capture, names, progress, refs)?);
    }
    Ok(format!(
        "array-lambda({}:{};[{}];{};[{}])",
        json_string(&lambda.binder().name),
        normalized_sort(&lambda.binder().sort, progress, refs)?,
        formals.join(","),
        expression(lambda.body(), names, progress, refs)?,
        captures.join(",")
    ))
}
