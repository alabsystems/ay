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
    if !crate::functional_array::supported_sort(sort)
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
                    scalar(key, index_sort(node.sort)?, admission)?;
                    scalar(datum, element, admission)?;
                }
            }
            SnapshotKind::Periodic(values) => {
                if index_sort(node.sort)? != &Sort::Int || values.is_empty() {
                    return Err(SnapshotTermError::InvalidTopology);
                }
                stores = stores
                    .checked_add(values.len())
                    .filter(|n| *n <= super::super::MAX_STORES)
                    .ok_or(SnapshotTermError::ResourceLimit)?;
                admission.pay(
                    values
                        .len()
                        .checked_mul(std::mem::size_of::<ModelValue>())
                        .ok_or(SnapshotTermError::ResourceLimit)?,
                    0,
                )?;
                for value in values {
                    scalar(value, element, admission)?;
                }
            }
            SnapshotKind::Store {
                base,
                index: key,
                value,
            } => {
                previous = parent(base, index, node.sort, topology, &depths, admission)?;
                scalar(key, index_sort(node.sort)?, admission)?;
                scalar(value, element, admission)?;
            }
            SnapshotKind::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                if !matches!(index_sort(node.sort)?, Sort::BitVec(width) if width.width == 64) {
                    return Err(SnapshotTermError::UnsupportedSort);
                }
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

fn index_sort(sort: &Sort) -> Result<&Sort> {
    match sort {
        Sort::Array(array) => Ok(&array.index_sort),
        _ => Err(SnapshotTermError::UnsupportedSort),
    }
}

fn scalar(value: &ModelValue, sort: &Sort, admission: &mut Admission<'_>) -> Result<()> {
    admission.pay(64, 0)?;
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool) => Ok(()),
        (ModelValue::Int(value), Sort::Int) => {
            let bytes = usize::try_from(value.bits().max(1).div_ceil(8))
                .map_err(|_| SnapshotTermError::ResourceLimit)?;
            admission.pay(bytes, bytes)
        }
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
