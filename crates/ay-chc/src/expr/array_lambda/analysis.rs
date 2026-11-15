// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete, bounded closure discovery and matrix typing.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::expr::{dag, ChcExpr, ChcSort, ChcVar, MAX_PREPROCESSING_NODES};
use crate::{ChcError, ChcResult, MAX_BITVECTOR_WIDTH};

fn limit() -> ChcError {
    ChcError::Verification("array lambda exceeds the complete-inspection budget".into())
}

pub(super) fn validate_sort(sort: &ChcSort) -> ChcResult<()> {
    let mut pending = vec![(sort, 0usize)];
    let mut visited = HashSet::new();
    while let Some((sort, depth)) = pending.pop() {
        if depth >= 256 {
            return Err(limit());
        }
        if !visited.insert(std::ptr::from_ref(sort)) {
            continue;
        }
        if visited.len() > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        match sort {
            ChcSort::BitVec(width) if *width == 0 || *width > MAX_BITVECTOR_WIDTH => {
                return Err(ChcError::InvalidBitVectorWidth {
                    width: *width,
                    max: MAX_BITVECTOR_WIDTH,
                });
            }
            ChcSort::Array(key, value) => {
                pending.extend([(key.as_ref(), depth + 1), (value.as_ref(), depth + 1)])
            }
            ChcSort::Datatype { constructors, .. } => {
                for constructor in constructors.iter() {
                    if pending.len().saturating_add(constructor.selectors.len())
                        > MAX_PREPROCESSING_NODES
                    {
                        return Err(limit());
                    }
                    pending.extend(
                        constructor
                            .selectors
                            .iter()
                            .map(|selector| (&selector.sort, depth + 1)),
                    );
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub(super) fn free_variables(root: &ChcExpr) -> ChcResult<Vec<ChcVar>> {
    let mut variables = BTreeSet::new();
    let mut result = Vec::new();
    let mut visited = HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if !visited.insert(std::ptr::from_ref(node)) {
            continue;
        }
        if visited.len() > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        if let ChcExpr::Var(variable) = node {
            if variables.insert(variable.clone()) {
                result.push(variable.clone());
            }
        }
        if pending.len().saturating_add(dag::children(node).len()) > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        pending.extend(dag::children(node).iter().rev().map(Arc::as_ref));
    }
    Ok(result)
}

pub(super) fn function_symbols(root: &ChcExpr) -> ChcResult<BTreeSet<String>> {
    let mut symbols = BTreeSet::new();
    let mut visited = HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if !visited.insert(std::ptr::from_ref(node)) {
            continue;
        }
        if visited.len() > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        match node {
            ChcExpr::FuncApp(name, ..) | ChcExpr::PredicateApp(name, ..) => {
                symbols.insert(name.clone());
            }
            ChcExpr::ArrayLambda(lambda) => pending.push(lambda.body()),
            _ => {}
        }
        if pending.len().saturating_add(dag::children(node).len()) > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        pending.extend(dag::children(node).iter().rev().map(Arc::as_ref));
    }
    Ok(symbols)
}

/// Complete postorder typing. A nested template was checked at construction;
/// this pass checks its environment after any intervening substitution.
pub(super) fn validate_matrix(root: &ChcExpr) -> ChcResult<ChcSort> {
    let mut sorts: HashMap<*const ChcExpr, ChcSort> = HashMap::new();
    let mut pending = vec![(root, false)];
    while let Some((node, expanded)) = pending.pop() {
        let key = std::ptr::from_ref(node);
        if sorts.contains_key(&key) {
            continue;
        }
        if sorts.len().saturating_add(pending.len()) > MAX_PREPROCESSING_NODES {
            return Err(limit());
        }
        let children = dag::children(node);
        if !expanded {
            pending.push((node, true));
            pending.extend(children.iter().rev().map(|child| (child.as_ref(), false)));
            continue;
        }
        let child_sorts = children
            .iter()
            .map(|child| {
                sorts
                    .get(&std::ptr::from_ref(child.as_ref()))
                    .cloned()
                    .ok_or_else(limit)
            })
            .collect::<ChcResult<Vec<_>>>()?;
        let sort = match node {
            ChcExpr::Op(op, _) => {
                crate::pdr::validate_qf_operation(*op, &child_sorts).map_err(|error| {
                    ChcError::Verification(format!("ill-typed array lambda: {error}"))
                })?
            }
            ChcExpr::PredicateApp(..)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {
                return Err(ChcError::Verification(
                    "array lambda contains a relation or parser marker".into(),
                ));
            }
            ChcExpr::ArrayLambda(lambda) if !lambda.captures_are_well_typed() => {
                return Err(ChcError::Verification(
                    "array lambda capture sort mismatch".into(),
                ));
            }
            ChcExpr::Var(variable) => {
                validate_sort(&variable.sort)?;
                variable.sort.clone()
            }
            ChcExpr::FuncApp(_, sort, _) => {
                validate_sort(sort)?;
                sort.clone()
            }
            ChcExpr::ConstArray(key, _) => {
                validate_sort(key)?;
                let value = child_sorts.first().cloned().ok_or_else(limit)?;
                ChcSort::Array(Box::new(key.clone()), Box::new(value))
            }
            _ => node.sort(),
        };
        validate_sort(&sort)?;
        sorts.insert(key, sort);
    }
    sorts.remove(&std::ptr::from_ref(root)).ok_or_else(limit)
}

/// Tree printers are exact and may revisit shared nodes. Refuse a template
/// whose expanded spelling would exceed a complete, checked finite bound.
/// The environments are ordinary children; nested templates contribute their
/// own already checked code as well.
pub(super) fn validate_rendering_bound(root: &ChcExpr) -> ChcResult<()> {
    const MAX_TEMPLATE_NODES: usize = 65_536;
    const MAX_TEMPLATE_DEPTH: usize = 256;
    let mut sizes: HashMap<*const ChcExpr, (usize, usize)> = HashMap::new();
    let mut pending = vec![(root, false)];
    while let Some((node, expanded)) = pending.pop() {
        let key = std::ptr::from_ref(node);
        if sizes.contains_key(&key) {
            continue;
        }
        if sizes.len().saturating_add(pending.len()) > MAX_TEMPLATE_NODES {
            return Err(limit());
        }
        if dag::children(node).len() >= MAX_TEMPLATE_NODES {
            return Err(limit());
        }
        let mut children: Vec<_> = dag::children(node).iter().map(Arc::as_ref).collect();
        if let ChcExpr::ArrayLambda(lambda) = node {
            children.push(lambda.body());
        }
        if !expanded {
            pending.push((node, true));
            pending.extend(children.iter().rev().map(|child| (*child, false)));
            continue;
        }
        let mut size = 1usize;
        let mut depth = 1usize;
        for child in children {
            let (child_size, child_depth) = sizes
                .get(&std::ptr::from_ref(child))
                .copied()
                .ok_or_else(limit)?;
            size = size.checked_add(child_size).ok_or_else(limit)?;
            depth = depth.max(child_depth.checked_add(1).ok_or_else(limit)?);
        }
        if size > MAX_TEMPLATE_NODES || depth > MAX_TEMPLATE_DEPTH {
            return Err(limit());
        }
        sizes.insert(key, (size, depth));
    }
    Ok(())
}
