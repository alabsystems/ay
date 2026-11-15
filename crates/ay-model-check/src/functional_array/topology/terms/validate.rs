// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use num_traits::Signed;

use super::{
    Admission, BigInt, ModelValue, Result, SnapshotKind, SnapshotTermError, SnapshotTopology, Sort,
};

pub(super) fn element(sort: &Sort) -> Result<&Sort> {
    let Sort::Array(array) = sort else {
        return Err(SnapshotTermError::UnsupportedSort);
    };
    if !matches!(&array.index_sort, Sort::BitVec(width) if width.width == 64)
        || !matches!(&array.element_sort, Sort::Bool | Sort::BitVec(_))
        || matches!(&array.element_sort, Sort::BitVec(width) if !(1..=128).contains(&width.width))
    {
        return Err(SnapshotTermError::UnsupportedSort);
    }
    Ok(&array.element_sort)
}

pub(super) fn complete(
    topology: &SnapshotTopology<'_>,
    admission: &mut Admission<'_>,
) -> Result<()> {
    admission.pay(1, 0)?;
    let nodes = topology.nodes();
    if nodes.is_empty() || nodes.len() > super::super::MAX_NODES || topology.root() >= nodes.len() {
        return Err(SnapshotTermError::InvalidTopology);
    }
    let mut depths = Vec::new();
    admission.reserve(&mut depths, nodes.len())?;
    let mut stores = 0usize;
    for (index, node) in nodes.iter().enumerate() {
        admission.pay(64, 0)?;
        let element = element(node.sort)?;
        let mut previous = 0;
        match node.kind {
            SnapshotKind::Finite(value) => {
                stores = stores
                    .checked_add(value.store.len())
                    .filter(|n| *n <= super::super::MAX_STORES)
                    .ok_or(SnapshotTermError::ResourceLimit)?;
                scalar(&value.default, element, admission)?;
                for (key, datum) in &value.store {
                    scalar(key, &Sort::bitvec(64), admission)?;
                    scalar(datum, element, admission)?;
                }
            }
            SnapshotKind::Store {
                base,
                index: key,
                value,
            } => {
                previous = parent(base, index, node.sort, topology, &depths, admission)?;
                scalar(key, &Sort::bitvec(64), admission)?;
                scalar(value, element, admission)?;
            }
            SnapshotKind::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                let left = parent(destination, index, node.sort, topology, &depths, admission)?;
                let right = parent(source, index, node.sort, topology, &depths, admission)?;
                previous = left.max(right);
                for bound in [lo, hi, source_lo] {
                    unsigned(bound, 64, admission)?;
                }
            }
        }
        let depth = previous
            .checked_add(1)
            .filter(|depth| *depth <= 64)
            .ok_or(SnapshotTermError::InvalidTopology)?;
        depths.push(depth);
    }
    Ok(())
}

fn parent(
    parent: usize,
    current: usize,
    sort: &Sort,
    topology: &SnapshotTopology<'_>,
    depths: &[usize],
    admission: &mut Admission<'_>,
) -> Result<usize> {
    admission.pay(64, 0)?;
    if parent >= current {
        return Err(SnapshotTermError::InvalidTopology);
    }
    let node = topology
        .nodes()
        .get(parent)
        .ok_or(SnapshotTermError::InvalidTopology)?;
    if node.sort != sort {
        return Err(SnapshotTermError::InvalidTopology);
    }
    depths
        .get(parent)
        .copied()
        .ok_or(SnapshotTermError::InvalidTopology)
}

fn scalar(value: &ModelValue, sort: &Sort, admission: &mut Admission<'_>) -> Result<()> {
    admission.pay(64, 0)?;
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool) => Ok(()),
        (ModelValue::BitVec { value, width }, Sort::BitVec(sort)) if *width == sort.width => {
            unsigned(value, *width, admission)
        }
        _ => Err(SnapshotTermError::InvalidTopology),
    }
}

fn unsigned(value: &BigInt, width: u32, admission: &mut Admission<'_>) -> Result<()> {
    admission.pay(64, 0)?;
    if value.is_negative() || value.bits() > u64::from(width) {
        return Err(SnapshotTermError::InvalidTopology);
    }
    Ok(())
}
