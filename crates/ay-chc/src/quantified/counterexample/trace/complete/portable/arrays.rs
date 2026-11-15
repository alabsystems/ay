// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete ordered array DATA; no sampling, lambda text, or native aliases.

use super::*;
use ay_model_check::{ArrayValue, ModelValue, SnapshotKind, SnapshotNode};
use num_bigint::BigInt;

mod decode;
pub(super) use decode::import;

const TOPOLOGY_WORK: usize = 1_048_576;

pub(super) struct Catalog<'a> {
    originals: Vec<&'a Arc<ArraySnapshot>>,
    pub(super) graphs: Vec<wire::Graph>,
    nodes: usize,
    stores: usize,
    work: usize,
}

impl<'a> Catalog<'a> {
    pub(super) fn new(control: &SourceControl<'_>, count: usize) -> Option<Self> {
        control.debit(TOPOLOGY_WORK, TOPOLOGY_WORK)?;
        let mut originals = Vec::new();
        let mut graphs = Vec::new();
        reserve(&mut originals, count, control)?;
        reserve(&mut graphs, count, control)?;
        Some(Self {
            originals,
            graphs,
            nodes: 0,
            stores: 0,
            work: TOPOLOGY_WORK,
        })
    }

    pub(super) fn value(
        &mut self,
        snapshot: &'a Arc<ArraySnapshot>,
        expected: &crate::ChcSort,
        control: &SourceControl<'_>,
    ) -> Option<wire::Value> {
        control.debit(self.originals.len().checked_add(1)?, 0)?;
        if !acquire::snapshot_sort(expected, snapshot.sort()) {
            return None;
        }
        if let Some(graph) = self
            .originals
            .iter()
            .position(|old| Arc::ptr_eq(old, snapshot))
        {
            return Some(wire::Value::Functional { graph });
        }
        let topology = snapshot
            .topology(&mut self.work, &mut || control.poll().is_none())
            .ok()?;
        self.nodes = self.nodes.checked_add(topology.nodes().len())?;
        if self.nodes > wire::MAX_NODES {
            return None;
        }
        let ay_core::Sort::Array(sort) = snapshot.sort() else {
            return None;
        };
        let element = scalar::element(&sort.element_sort, control)?;
        let mut nodes = Vec::new();
        reserve(&mut nodes, topology.nodes().len(), control)?;
        for node in topology.nodes() {
            control.debit(1, 0)?;
            nodes.push(self.node(node.kind, element, control)?);
        }
        let graph = self.graphs.len();
        self.originals.push(snapshot);
        self.graphs.push(wire::Graph {
            element,
            root: topology.root(),
            nodes,
        });
        control.poll()?;
        Some(wire::Value::Functional { graph })
    }

    fn node(
        &mut self,
        kind: SnapshotKind<'_>,
        element: wire::Element,
        control: &SourceControl<'_>,
    ) -> Option<wire::Node> {
        match kind {
            SnapshotKind::Finite(value) => {
                self.stores = self.stores.checked_add(value.store.len())?;
                if self.stores > wire::MAX_STORES {
                    return None;
                }
                let default = scalar::export(&value.default, element, control)?;
                let mut stores = Vec::new();
                reserve(&mut stores, value.store.len(), control)?;
                for (index, value) in &value.store {
                    stores.push(wire::Store {
                        index: index_value(index, control)?,
                        value: scalar::export(value, element, control)?,
                    });
                }
                Some(wire::Node::Finite { default, stores })
            }
            SnapshotKind::Store { base, index, value } => Some(wire::Node::Store {
                base,
                index: index_value(index, control)?,
                value: scalar::export(value, element, control)?,
            }),
            SnapshotKind::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => Some(wire::Node::Range {
                destination,
                source,
                lo: scalar::unsigned(lo, control)?,
                hi: scalar::unsigned(hi, control)?,
                source_lo: scalar::unsigned(source_lo, control)?,
            }),
            _ => None,
        }
    }
}

fn index_value(value: &ModelValue, control: &SourceControl<'_>) -> Option<u64> {
    let ModelValue::BitVec { width: 64, value } = value else {
        return None;
    };
    scalar::unsigned(value, control)
}

pub(super) fn reserve<T>(
    values: &mut Vec<T>,
    extra: usize,
    control: &SourceControl<'_>,
) -> Option<()> {
    let records = values.len().checked_mul(2)?.checked_add(extra)?;
    control.debit(extra, records.checked_mul(std::mem::size_of::<T>())?)?;
    values.try_reserve_exact(extra).ok()?;
    control.poll()
}
