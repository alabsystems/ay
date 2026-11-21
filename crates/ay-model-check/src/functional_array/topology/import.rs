// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete admission precedes construction, including unreachable nodes.

use super::super::{array_key, cell, scalar_cost, supported_sort};
use super::{
    ArraySnapshot, ArrayValue, Budget, FunctionalArrayError, ModelValue, Node, SnapshotKind,
    SnapshotNode, Sort, MAX_NODES,
};
use num_traits::Signed;
use std::mem::size_of;
use std::sync::Arc;

impl ArraySnapshot {
    /// Import a complete topological DATA batch, never native model authority.
    /// Every node is validated even if unreachable from root. All edges must
    /// point backwards; forward/cyclic/missing edges refuse the whole batch.
    /// Raw Store/Range structure is retained, including empty-range captures.
    /// All refusal zeros the caller's existing work ledger; no allowance resets.
    pub fn from_topology(
        nodes: &[SnapshotNode<'_>],
        root: usize,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<Arc<Self>, FunctionalArrayError> {
        let mut budget = Budget::new(work, stop);
        let result = import(nodes, root, &mut budget);
        budget.finish(result)
    }
}

fn import(
    nodes: &[SnapshotNode<'_>],
    root: usize,
    budget: &mut Budget<'_, '_>,
) -> Result<Arc<ArraySnapshot>, FunctionalArrayError> {
    budget.pay(1)?;
    if nodes.len() > MAX_NODES {
        return Err(FunctionalArrayError::Resource);
    }
    if nodes.is_empty() || root >= nodes.len() {
        return Err(FunctionalArrayError::Value);
    }
    let mut depths = Vec::new();
    budget.reserve(&mut depths, nodes.len())?;
    for (index, description) in nodes.iter().enumerate() {
        validate_export(*description, budget)?;
        depths.push(depth(*description, index, nodes, &depths, budget)?);
    }
    // The complete unused-data census is finished before ANY snapshot lands.
    let mut built = Vec::new();
    budget.reserve(&mut built, nodes.len())?;
    for (description, depth) in nodes.iter().zip(&depths) {
        budget.poll()?;
        let node = copy_node(description.kind, &built, budget)?;
        budget.poll()?;
        built.push(Arc::new(ArraySnapshot {
            sort: description.sort.clone(),
            depth: *depth,
            node,
        }));
    }
    budget.poll()?;
    built.get(root).cloned().ok_or(FunctionalArrayError::Value)
}

pub(super) fn validate_export(
    description: SnapshotNode<'_>,
    budget: &mut Budget<'_, '_>,
) -> Result<(), FunctionalArrayError> {
    budget.pay(1)?;
    let element = element_sort(description.sort)?;
    // Arc header, snapshot and the shallow authenticated array-sort clone.
    budget.storage(size_of::<ArraySnapshot>() + 3 * size_of::<Sort>() + 2 * size_of::<usize>())?;
    match description.kind {
        SnapshotKind::Finite(value) => {
            budget.stores(value.store.len())?;
            let backing = value
                .store
                .len()
                .checked_mul(size_of::<(ModelValue, ModelValue)>())
                .ok_or(FunctionalArrayError::Resource)?;
            budget.storage(backing)?;
            scalar(&value.default, element, budget)?;
            for (index, datum) in &value.store {
                index_value(index, description.sort, budget)?;
                scalar(datum, element, budget)?;
            }
        }
        SnapshotKind::Periodic(values) => {
            if !matches!(description.sort, Sort::Array(sort) if sort.index_sort == Sort::Int)
                || values.is_empty()
            {
                return Err(FunctionalArrayError::Sort);
            }
            budget.stores(values.len())?;
            budget.storage(
                values
                    .len()
                    .checked_mul(size_of::<ModelValue>())
                    .ok_or(FunctionalArrayError::Resource)?,
            )?;
            for value in values {
                scalar(value, element, budget)?;
            }
        }
        SnapshotKind::Store { index, value, .. } => {
            index_value(index, description.sort, budget)?;
            scalar(value, element, budget)?;
        }
        SnapshotKind::Range {
            lo, hi, source_lo, ..
        } => {
            if !matches!(description.sort, Sort::Array(sort) if matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64))
            {
                return Err(FunctionalArrayError::Sort);
            }
            for bound in [lo, hi, source_lo] {
                budget.storage(8)?;
                if bound.is_negative() || bound.bits() > 64 {
                    return Err(FunctionalArrayError::Value);
                }
            }
        }
    }
    budget.poll()
}

fn element_sort(sort: &Sort) -> Result<&Sort, FunctionalArrayError> {
    let Sort::Array(array) = sort else {
        return Err(FunctionalArrayError::Sort);
    };
    if !supported_sort(sort)
        || matches!(&array.element_sort, Sort::BitVec(width) if width.width == 0)
    {
        return Err(FunctionalArrayError::Sort);
    }
    Ok(&array.element_sort)
}

fn scalar(
    value: &ModelValue,
    sort: &Sort,
    budget: &mut Budget<'_, '_>,
) -> Result<(), FunctionalArrayError> {
    budget.pay(1)?;
    budget.storage(scalar_cost(value)?)?;
    cell(value, sort)
}

fn index_value(
    value: &ModelValue,
    sort: &Sort,
    budget: &mut Budget<'_, '_>,
) -> Result<(), FunctionalArrayError> {
    budget.storage(scalar_cost(value)?)?;
    array_key(value, sort).map(|_| ())
}

fn parent_depth(
    parent: usize,
    index: usize,
    sort: &Sort,
    nodes: &[SnapshotNode<'_>],
    depths: &[usize],
    budget: &mut Budget<'_, '_>,
) -> Result<usize, FunctionalArrayError> {
    budget.pay(8)?;
    if parent >= index {
        return Err(FunctionalArrayError::Value);
    }
    let prior = nodes.get(parent).ok_or(FunctionalArrayError::Value)?;
    // Prior/current sorts were already admitted as shallow BV64 arrays.
    if prior.sort != sort {
        return Err(FunctionalArrayError::Sort);
    }
    depths
        .get(parent)
        .copied()
        .ok_or(FunctionalArrayError::Value)
}

fn depth(
    node: SnapshotNode<'_>,
    index: usize,
    nodes: &[SnapshotNode<'_>],
    depths: &[usize],
    budget: &mut Budget<'_, '_>,
) -> Result<usize, FunctionalArrayError> {
    let previous = match node.kind {
        SnapshotKind::Finite(_) | SnapshotKind::Periodic(_) => 0,
        SnapshotKind::Store { base, .. } => {
            parent_depth(base, index, node.sort, nodes, depths, budget)?
        }
        SnapshotKind::Range {
            destination,
            source,
            ..
        } => {
            let left = parent_depth(destination, index, node.sort, nodes, depths, budget)?;
            let right = parent_depth(source, index, node.sort, nodes, depths, budget)?;
            left.max(right)
        }
    };
    previous
        .checked_add(1)
        .filter(|n| *n <= 64)
        .ok_or(FunctionalArrayError::Resource)
}

fn copy_node(
    kind: SnapshotKind<'_>,
    built: &[Arc<ArraySnapshot>],
    budget: &mut Budget<'_, '_>,
) -> Result<Node, FunctionalArrayError> {
    let get = |index| built.get(index).cloned().ok_or(FunctionalArrayError::Value);
    match kind {
        SnapshotKind::Finite(value) => {
            let mut store = Vec::new();
            // Its complete backing and all scalar copies were prepaid by the
            // validation pass, before any owned snapshot construction.
            store
                .try_reserve_exact(value.store.len())
                .map_err(|_| FunctionalArrayError::Allocation)?;
            for pair in &value.store {
                budget.poll()?;
                store.push((pair.0.clone(), pair.1.clone()));
            }
            budget.poll()?;
            Ok(Node::Finite(ArrayValue {
                default: value.default.clone(),
                store,
            }))
        }
        SnapshotKind::Periodic(values) => {
            let mut owned = Vec::new();
            owned
                .try_reserve_exact(values.len())
                .map_err(|_| FunctionalArrayError::Allocation)?;
            for value in values {
                budget.poll()?;
                owned.push(value.clone());
            }
            Ok(Node::Periodic(owned))
        }
        SnapshotKind::Store { base, index, value } => Ok(Node::Store {
            base: get(base)?,
            index: index.clone(),
            value: value.clone(),
        }),
        SnapshotKind::Range {
            destination,
            source,
            lo,
            hi,
            source_lo,
        } => Ok(Node::Range {
            destination: get(destination)?,
            source: get(source)?,
            lo: lo.clone(),
            hi: hi.clone(),
            source_lo: source_lo.clone(),
        }),
    }
}
