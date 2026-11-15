// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::records::OperationKind;
use crate::{ChcOp, ChcVar};
use std::collections::{BTreeMap, BTreeSet};

mod authenticate;
pub(super) use authenticate::authenticate;

pub(super) enum Value {
    Scalar(Arc<ChcExpr>, ChcSort),
    Record(Vec<Arc<ChcExpr>>, ChcSort),
}

impl Value {
    pub(super) fn sort(&self) -> &ChcSort {
        match self {
            Self::Scalar(_, sort) | Self::Record(_, sort) => sort,
        }
    }

    pub(super) fn scalar(self) -> Option<(Arc<ChcExpr>, ChcSort)> {
        match self {
            Self::Scalar(expr, sort) => Some((expr, sort)),
            _ => None,
        }
    }

    pub(super) fn boolean(self, control: &SourceControl<'_>) -> Option<Arc<ChcExpr>> {
        control.poll()?;
        let (expr, sort) = self.scalar()?;
        (sort == ChcSort::Bool).then_some(expr)
    }

    pub(super) fn append(self, out: &mut Vec<ChcExpr>, control: &SourceControl<'_>) -> Option<()> {
        match self {
            Self::Scalar(expr, _) => out.push(copy_root(&expr, control)?),
            Self::Record(fields, _) => {
                for field in fields {
                    out.push(copy_root(&field, control)?);
                }
            }
        }
        control.poll()
    }
}

pub(super) struct Context<'a, 'c> {
    registry: &'a Registry,
    functions: &'a RetainedFunctions,
    layouts: &'a Layouts,
    reserved: &'a BTreeSet<&'a str>,
    variables: BTreeMap<String, (ChcSort, Vec<Arc<ChcExpr>>)>,
    fresh: usize,
    pub(super) control: &'a SourceControl<'c>,
}

impl<'a, 'c> Context<'a, 'c> {
    pub(super) fn new(
        registry: &'a Registry,
        functions: &'a RetainedFunctions,
        layouts: &'a Layouts,
        reserved: &'a BTreeSet<&'a str>,
        control: &'a SourceControl<'c>,
    ) -> Self {
        Self {
            registry,
            functions,
            layouts,
            reserved,
            variables: BTreeMap::new(),
            fresh: 0,
            control,
        }
    }

    fn variable(&mut self, var: &ChcVar) -> Option<Value> {
        if self.functions.contains(&var.name, self.control)? {
            return None;
        }
        self.registry.validate_sort(&var.sort).ok()?;
        self.control.bytes(
            sort_bytes(&var.sort)?
                .checked_mul(2)?
                .checked_add(var.name.len())?,
        )?;
        if !matches!(var.sort, ChcSort::Datatype { .. }) {
            return Some(Value::Scalar(
                Arc::new(ChcExpr::Var(var.clone())),
                var.sort.clone(),
            ));
        }
        if let Some((sort, fields)) = self.variables.get(&var.name) {
            self.control.charge(fields.len())?;
            if sort != &var.sort {
                return None;
            }
            return Some(Value::Record(fields.clone(), sort.clone()));
        }
        let layout = self.layouts.get(&var.sort)?;
        self.control.charge(layout.leaves.len().checked_mul(2)?)?;
        let mut fields = Vec::new();
        fields.try_reserve_exact(layout.leaves.len()).ok()?;
        for sort in &layout.leaves {
            let name = loop {
                self.control.charge(1)?;
                let ordinal = self.fresh;
                self.fresh = self.fresh.checked_add(1)?;
                let name = format!("ay!record!{ordinal}");
                if !self.reserved.contains(name.as_str()) {
                    break name;
                }
            };
            self.control
                .bytes(name.len().checked_add(sort_bytes(sort)?)?)?;
            fields.push(Arc::new(ChcExpr::Var(ChcVar::new(name, sort.clone()))));
        }
        self.variables
            .insert(var.name.clone(), (var.sort.clone(), fields.clone()));
        Some(Value::Record(fields, var.sort.clone()))
    }

    pub(super) fn rewrite(&mut self, expr: &ChcExpr, depth: usize) -> Option<Value> {
        self.control.charge(1)?;
        if depth > 64 {
            return None;
        }
        let result = match expr {
            ChcExpr::Bool(_) => Value::Scalar(Arc::new(expr.clone()), ChcSort::Bool),
            ChcExpr::BitVec(value, width) if valid_literal(*value, *width) => {
                self.control.bytes(sort_bytes(&ChcSort::BitVec(*width))?)?;
                Value::Scalar(Arc::new(expr.clone()), ChcSort::BitVec(*width))
            }
            ChcExpr::Var(var) => self.variable(var)?,
            ChcExpr::Op(op, args) => {
                let children = self.children(args, depth)?;
                self.operation(*op, children)?
            }
            ChcExpr::FuncApp(name, claimed, args) => {
                self.registry.validate_sort(claimed).ok()?;
                self.control
                    .bytes(name.len().checked_add(sort_bytes(claimed)?)?)?;
                let children = self.children(args, depth)?;
                self.function(name, claimed, children)?
            }
            ChcExpr::ConstArray(key, value) => {
                if !matches!(key, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)) {
                    return None;
                }
                self.control.bytes(sort_bytes(key)?.checked_mul(2)?)?;
                let (value, element) = self.rewrite(value, depth + 1)?.scalar()?;
                let sort = ChcSort::Array(Box::new(key.clone()), Box::new(element));
                self.registry.validate_sort(&sort).ok()?;
                Value::Scalar(Arc::new(ChcExpr::ConstArray(key.clone(), value)), sort)
            }
            _ => return None,
        };
        self.control.poll()?;
        Some(result)
    }

    pub(super) fn premise(&mut self, premise: &UniversalPremise) -> Option<UniversalPremise> {
        if premise.binder_count() == 1 {
            // Preserve existing singleton names and projection order.
            self.control
                .bytes(premise.binder().name.len().checked_add(128)?)?;
            let matrix = self.rewrite(premise.matrix(), 0)?.boolean(self.control)?;
            return Some(UniversalPremise::new(
                premise.binder().clone(),
                copy_root(&matrix, self.control)?,
            ));
        }
        self.control
            .charge(premise.binder_count().checked_mul(3)?)?;
        let mut binders = Vec::new();
        let mut replacements = Vec::new();
        for binder in premise.binders() {
            let name = loop {
                self.control.charge(1)?;
                let ordinal = self.fresh;
                self.fresh = self.fresh.checked_add(1)?;
                let name = format!("ay!record!{ordinal}");
                if !self.reserved.contains(name.as_str()) {
                    break name;
                }
            };
            self.control
                .bytes(name.len().checked_add(sort_bytes(&binder.sort)?)?)?;
            let fresh = ChcVar::new(name, binder.sort.clone());
            replacements.push(ChcExpr::var(fresh.clone()));
            binders.push(fresh);
        }
        let bindings: Vec<_> = premise.binders().zip(replacements.iter()).collect();
        let renamed =
            super::super::source_premises::simultaneous(premise.matrix(), &bindings, self.control)?;
        let matrix = self.rewrite(&renamed, 0)?.boolean(self.control)?;
        UniversalPremise::with_binders(binders, copy_root(&matrix, self.control)?).ok()
    }

    fn children(&mut self, args: &[Arc<ChcExpr>], depth: usize) -> Option<Vec<Value>> {
        self.control.charge(args.len())?;
        let mut children = Vec::new();
        children.try_reserve_exact(args.len()).ok()?;
        for arg in args {
            children.push(self.rewrite(arg, depth + 1)?);
        }
        Some(children)
    }

    fn function(&self, name: &str, claimed: &ChcSort, children: Vec<Value>) -> Option<Value> {
        let sorts = child_sorts(&children, self.control)?;
        if self.functions.contains(name, self.control)? {
            let actual = self
                .functions
                .application(name, &sorts, claimed, self.control)?;
            // Scalar signatures are authenticated *before* consuming product
            // values: record arguments cannot be laundered into a UF domain.
            self.control.charge(children.len())?;
            let mut args = Vec::new();
            args.try_reserve_exact(children.len()).ok()?;
            for child in children {
                let (expr, sort) = child.scalar()?;
                self.control.poll()?;
                if !matches!(sort, ChcSort::Bool | ChcSort::BitVec(_)) {
                    return None;
                }
                args.push(expr);
            }
            self.control.bytes(name.len())?;
            return Some(Value::Scalar(
                Arc::new(ChcExpr::FuncApp(name.to_owned(), actual.clone(), args)),
                actual,
            ));
        }
        let resolved = self.registry.resolve_application(name, &sorts).ok()?;
        if resolved.sort != claimed {
            return None;
        }
        self.control.bytes(sort_bytes(resolved.sort)?)?;
        let actual = resolved.sort.clone();
        match resolved.kind {
            OperationKind::Constructor => {
                let count = self.layouts.get(&actual)?.leaves.len();
                self.control.charge(count)?;
                let mut fields = Vec::new();
                fields.try_reserve_exact(count).ok()?;
                for child in children {
                    self.control.poll()?;
                    match child {
                        Value::Scalar(value, _) => fields.push(value),
                        Value::Record(values, _) => {
                            for value in values {
                                self.control.poll()?;
                                fields.push(value);
                            }
                        }
                    }
                }
                if fields.len() != count {
                    return None;
                }
                Some(Value::Record(fields, actual))
            }
            OperationKind::Selector { field } => {
                let mut children = children.into_iter();
                let Value::Record(fields, receiver) = children.next()? else {
                    return None;
                };
                if children.next().is_some() {
                    return None;
                }
                let range = self.layouts.get(&receiver)?.fields.get(field)?.clone();
                let selected = fields.get(range)?;
                self.control.charge(selected.len())?;
                if matches!(actual, ChcSort::Datatype { .. }) {
                    let mut copied = Vec::new();
                    copied.try_reserve_exact(selected.len()).ok()?;
                    for value in selected {
                        self.control.poll()?;
                        copied.push(Arc::clone(value));
                    }
                    Some(Value::Record(copied, actual))
                } else {
                    let [value] = selected else {
                        return None;
                    };
                    Some(Value::Scalar(Arc::clone(value), actual))
                }
            }
        }
    }

    fn operation(&self, op: ChcOp, children: Vec<Value>) -> Option<Value> {
        let sorts = child_sorts(&children, self.control)?;
        let result = operation_sort(op, &sorts, self.registry, self.control)?;
        if matches!(op, ChcOp::Eq | ChcOp::Ne)
            && matches!(sorts.first(), Some(ChcSort::Datatype { .. }))
        {
            return self.record_comparison(op, children);
        }
        if op == ChcOp::Ite && matches!(result, ChcSort::Datatype { .. }) {
            let mut children = children.into_iter();
            let condition = children.next()?.boolean(self.control)?;
            let Value::Record(left, _) = children.next()? else {
                return None;
            };
            let Value::Record(right, _) = children.next()? else {
                return None;
            };
            if children.next().is_some() || left.len() != right.len() {
                return None;
            }
            self.control.charge(left.len().checked_mul(4)?)?;
            let mut fields = Vec::new();
            fields.try_reserve_exact(left.len()).ok()?;
            for (left, right) in left.into_iter().zip(right) {
                self.control.poll()?;
                fields.push(Arc::new(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![Arc::clone(&condition), left, right],
                )));
            }
            return Some(Value::Record(fields, result));
        }
        self.control.charge(children.len())?;
        let mut args = Vec::new();
        args.try_reserve_exact(children.len()).ok()?;
        for child in children {
            args.push(child.scalar()?.0);
        }
        Some(Value::Scalar(Arc::new(ChcExpr::Op(op, args)), result))
    }

    fn record_comparison(&self, op: ChcOp, children: Vec<Value>) -> Option<Value> {
        let mut children = children.into_iter();
        let Value::Record(left, _) = children.next()? else {
            return None;
        };
        let Value::Record(right, _) = children.next()? else {
            return None;
        };
        if children.next().is_some() || left.len() != right.len() || left.is_empty() {
            return None;
        }
        self.control.charge(left.len().checked_mul(4)?)?;
        let mut comparisons = Vec::new();
        comparisons.try_reserve_exact(left.len()).ok()?;
        for (left, right) in left.into_iter().zip(right) {
            self.control.poll()?;
            comparisons.push(Arc::new(ChcExpr::Op(op, vec![left, right])));
        }
        let expr = if comparisons.len() == 1 {
            comparisons.pop()?
        } else {
            Arc::new(ChcExpr::Op(
                if op == ChcOp::Eq {
                    ChcOp::And
                } else {
                    ChcOp::Or
                },
                comparisons,
            ))
        };
        Some(Value::Scalar(expr, ChcSort::Bool))
    }
}

fn child_sorts(children: &[Value], control: &SourceControl<'_>) -> Option<Vec<ChcSort>> {
    control.charge(children.len())?;
    let mut sorts = Vec::new();
    sorts.try_reserve_exact(children.len()).ok()?;
    for child in children {
        control.bytes(sort_bytes(child.sort())?)?;
        sorts.push(child.sort().clone());
    }
    Some(sorts)
}

fn operation_sort(
    op: ChcOp,
    sorts: &[ChcSort],
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<ChcSort> {
    control.charge(sorts.len())?;
    let result = match (op, sorts) {
        (ChcOp::Eq | ChcOp::Ne, [left, right]) if left == right => ChcSort::Bool,
        (ChcOp::Ite, [ChcSort::Bool, left, right]) if left == right => {
            control.bytes(sort_bytes(left)?)?;
            left.clone()
        }
        _ => crate::pdr::validate_qf_operation(op, sorts).ok()?,
    };
    registry.validate_sort(&result).ok()?;
    Some(result)
}

pub(super) fn copy_root(expr: &ChcExpr, control: &SourceControl<'_>) -> Option<ChcExpr> {
    control.charge(1)?;
    match expr {
        ChcExpr::Var(var) => control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?,
        ChcExpr::Op(_, args) => control.charge(args.len())?,
        ChcExpr::FuncApp(name, sort, args) => {
            control.bytes(name.len().checked_add(sort_bytes(sort)?)?)?;
            control.charge(args.len())?;
        }
        _ => {}
    }
    Some(expr.clone())
}

fn valid_literal(value: u128, width: u32) -> bool {
    (1..=crate::MAX_BITVECTOR_WIDTH).contains(&width) && (width >= 128 || value < (1_u128 << width))
}
