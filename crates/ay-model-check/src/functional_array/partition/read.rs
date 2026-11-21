// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{fixed, key, FunctionalArrayError, Meter, ModelValue, SnapshotKind, SnapshotTopology};

pub(super) fn value<'a>(
    topology: &'a SnapshotTopology<'a>,
    mut index: u64,
    meter: &mut Meter<'_>,
) -> Result<&'a ModelValue, FunctionalArrayError> {
    let mut node = topology.root();
    loop {
        meter.pay(128)?;
        let description = topology
            .nodes()
            .get(node)
            .ok_or(FunctionalArrayError::Value)?;
        let next = match description.kind {
            // Periodic snapshots have integer indices; this partition certifies BV64 copies.
            SnapshotKind::Periodic(_) => return Err(FunctionalArrayError::Sort),
            SnapshotKind::Finite(value) => {
                // Chronological finite stores: last matching write wins.
                for (at, cell) in value.store.iter().rev() {
                    if key(at, meter)? == index {
                        return Ok(cell);
                    }
                }
                return Ok(&value.default);
            }
            SnapshotKind::Store {
                base,
                index: at,
                value,
            } => {
                if key(at, meter)? == index {
                    return Ok(value);
                }
                base
            }
            SnapshotKind::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                let lo = fixed(lo, meter)?;
                let hi = fixed(hi, meter)?;
                let source_lo = fixed(source_lo, meter)?;
                if lo <= index && index < hi {
                    meter.pay(128)?;
                    index = index.wrapping_sub(lo).wrapping_add(source_lo);
                    source
                } else {
                    destination
                }
            }
        };
        // Topology already validated this; keep the local backwards check so
        // traversal cannot cycle even if the borrowed representation changes.
        if next >= node {
            return Err(FunctionalArrayError::Value);
        }
        node = next;
    }
}
