// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete borrowed source names and lexical free-variable walks.

use super::*;
use crate::quantified::records::sort_bytes;
use std::collections::{BTreeMap, BTreeSet};

const MAX_DEPTH: usize = 64;

pub(super) struct Names<'a> {
    used: BTreeSet<&'a str>,
    next: usize,
}

impl<'a> Names<'a> {
    pub(super) fn new(
        problem: &'a QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Result<Self> {
        let mut out = Self {
            used: BTreeSet::new(),
            next: 0,
        };
        for predicate in problem.source_problem().predicates() {
            out.insert(&predicate.name, control)?;
        }
        // Global functions retain their identity across all occurrences. An
        // unused declaration must reserve its name just like a used one.
        for name in problem.functions.names() {
            out.insert(name, control)?;
        }
        // Include unused declarations and sibling fields, not just operations
        // on this path. Embedded record names must resolve to this same table.
        for (name, constructors) in problem.source_problem().datatype_defs() {
            out.insert(name, control)?;
            for (constructor, fields) in constructors {
                out.insert(constructor, control)?;
                for (field, _) in fields {
                    out.insert(field, control)?;
                }
            }
        }
        for (clause, premises) in problem
            .source_problem()
            .clauses()
            .iter()
            .zip(problem.premises())
        {
            clause_expressions(clause, control, |expr| out.expression(expr, control))?;
            for premise in premises {
                for binder in premise.binders() {
                    out.insert(&binder.name, control)?;
                }
                out.expression(premise.matrix(), control)?;
            }
        }
        control.poll().ok_or_else(refused)?;
        Ok(out)
    }

    fn insert(&mut self, name: &'a str, control: &SourceControl<'_>) -> Result<()> {
        control
            .charge(name.len().checked_add(1).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        control.bytes(128).ok_or_else(refused)?;
        self.used.insert(name);
        Ok(())
    }

    fn expression(&mut self, root: &'a ChcExpr, control: &SourceControl<'_>) -> Result<()> {
        walk(root, control, |expr, _| {
            match expr {
                ChcExpr::Var(variable) => self.insert(&variable.name, control)?,
                ChcExpr::FuncApp(name, _, _) => self.insert(name, control)?,
                _ => {}
            }
            Ok(())
        })
    }

    pub(super) fn fresh(&mut self, control: &SourceControl<'_>) -> Result<String> {
        loop {
            control.charge(1).ok_or_else(refused)?;
            // Fixed prefix plus at most twenty decimal digits on 64-bit hosts.
            control.bytes(64).ok_or_else(refused)?;
            let name = format!("ay_qcex_{}", self.next);
            self.next = self.next.checked_add(1).ok_or_else(refused)?;
            if !self.used.contains(name.as_str()) {
                return Ok(name);
            }
        }
    }
}

pub(super) fn clause_expressions<'a>(
    clause: &'a HornClause,
    control: &SourceControl<'_>,
    mut visit: impl FnMut(&'a ChcExpr) -> Result<()>,
) -> Result<()> {
    for (_, arguments) in &clause.body.predicates {
        control.charge(1).ok_or_else(refused)?;
        for expression in arguments {
            visit(expression)?;
        }
    }
    if let Some(constraint) = &clause.body.constraint {
        visit(constraint)?;
    }
    if let ClauseHead::Predicate(_, arguments) = &clause.head {
        for expression in arguments {
            visit(expression)?;
        }
    }
    control.poll().ok_or_else(refused)
}

pub(super) fn free_variables<'a>(
    clause: &'a HornClause,
    premises: &'a [UniversalPremise],
    control: &SourceControl<'_>,
) -> Result<Vec<&'a ChcVar>> {
    let mut variables = BTreeMap::new();
    clause_expressions(clause, control, |expr| {
        collect(expr, None, &mut variables, control)
    })?;
    for premise in premises {
        collect(premise.matrix(), Some(premise), &mut variables, control)?;
    }
    control
        .bytes(
            variables
                .len()
                .checked_mul(std::mem::size_of::<&ChcVar>())
                .ok_or_else(refused)?,
        )
        .ok_or_else(refused)?;
    let mut out = Vec::new();
    out.try_reserve_exact(variables.len())
        .map_err(|_| refused())?;
    out.extend(variables.into_values());
    Ok(out)
}

fn collect<'a>(
    expr: &'a ChcExpr,
    premise: Option<&UniversalPremise>,
    variables: &mut BTreeMap<&'a str, &'a ChcVar>,
    control: &SourceControl<'_>,
) -> Result<()> {
    walk(expr, control, |node, _| {
        let ChcExpr::Var(variable) = node else {
            return Ok(());
        };
        control
            .charge(variable.name.len().checked_add(1).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        control
            .bytes(sort_bytes(&variable.sort).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        if let Some(premise) = premise {
            for binder in premise.binders() {
                control
                    .charge(binder.name.len().checked_add(1).ok_or_else(refused)?)
                    .ok_or_else(refused)?;
                if binder.name == variable.name {
                    return if binder.sort == variable.sort {
                        Ok(())
                    } else {
                        Err(refused())
                    };
                }
            }
        }
        control.bytes(128).ok_or_else(refused)?;
        if let Some(old) = variables.insert(&variable.name, variable) {
            if old.sort != variable.sort {
                return Err(refused());
            }
        }
        Ok(())
    })
}

/// Source admission already authenticated operators/sorts. This independent
/// occurrence walk bounds every recursive formatter and each explicit stack.
fn walk<'a>(
    root: &'a ChcExpr,
    control: &SourceControl<'_>,
    mut visit: impl FnMut(&'a ChcExpr, usize) -> Result<()>,
) -> Result<()> {
    control.charge(1).ok_or_else(refused)?;
    let mut pending = vec![(root, 0usize)];
    while let Some((node, depth)) = pending.pop() {
        control.charge(1).ok_or_else(refused)?;
        if depth > MAX_DEPTH {
            return Err(refused());
        }
        visit(node, depth)?;
        let children: &[std::sync::Arc<ChcExpr>] = match node {
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => args,
            ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) | ChcExpr::Var(_) => &[],
            _ => return Err(refused()),
        };
        control.charge(children.len()).ok_or_else(refused)?;
        pending.try_reserve(children.len()).map_err(|_| refused())?;
        pending.extend(
            children
                .iter()
                .rev()
                .map(|child| (child.as_ref(), depth + 1)),
        );
    }
    control.poll().ok_or_else(refused)
}

pub(super) fn expression_cost(expr: &ChcExpr, control: &SourceControl<'_>) -> Result<usize> {
    let mut output = 0usize;
    walk(expr, control, |node, depth| {
        let mut bytes = 256usize;
        let (name, sort) = match node {
            ChcExpr::Var(variable) => (Some(variable.name.as_str()), Some(&variable.sort)),
            ChcExpr::FuncApp(name, sort, _) => (Some(name.as_str()), Some(sort)),
            ChcExpr::ConstArray(sort, _) => (None, Some(sort)),
            _ => (None, None),
        };
        if let Some(name) = name {
            bytes = bytes
                .checked_add(name.len().checked_mul(4).ok_or_else(refused)?)
                .ok_or_else(refused)?;
        }
        if let Some(sort) = sort {
            bytes = bytes
                .checked_add(sort_bytes(sort).ok_or_else(refused)?)
                .ok_or_else(refused)?;
        }
        output = output
            .checked_add(bytes)
            .filter(|bytes| *bytes <= MAX_OUTPUT_BYTES)
            .ok_or_else(refused)?;
        // Each ancestor's legacy String representation may copy this node.
        control
            .bytes(bytes.checked_mul(depth + 2).ok_or_else(refused)?)
            .ok_or_else(refused)?;
        Ok(())
    })?;
    Ok(output)
}
