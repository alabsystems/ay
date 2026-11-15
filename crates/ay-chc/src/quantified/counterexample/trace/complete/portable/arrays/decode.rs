// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Every raw node is admitted, even unused nodes and empty-range captures.

use super::*;

enum Owned {
    Finite(ArrayValue),
    Store {
        base: usize,
        index: ModelValue,
        value: ModelValue,
    },
    Range {
        destination: usize,
        source: usize,
        lo: BigInt,
        hi: BigInt,
        source_lo: BigInt,
    },
}

pub(in crate::quantified::counterexample::trace::complete::portable) fn import(
    graphs: &[wire::Graph],
    control: &SourceControl<'_>,
) -> Option<Vec<Arc<ArraySnapshot>>> {
    control.debit(graphs.len(), 0)?;
    if graphs.len() > wire::MAX_NODES {
        return None;
    }
    let mut nodes = 0usize;
    let mut stores = 0usize;
    for graph in graphs {
        nodes = nodes.checked_add(graph.nodes.len())?;
        for node in &graph.nodes {
            control.debit(1, 0)?;
            if let wire::Node::Finite {
                stores: entries, ..
            } = node
            {
                stores = stores.checked_add(entries.len())?;
            }
        }
    }
    if nodes > wire::MAX_NODES || stores > wire::MAX_STORES {
        return None;
    }
    let mut work = if graphs.is_empty() {
        0
    } else {
        control.debit(TOPOLOGY_WORK, TOPOLOGY_WORK)?;
        TOPOLOGY_WORK
    };
    let mut snapshots = Vec::new();
    reserve(&mut snapshots, graphs.len(), control)?;
    for graph in graphs {
        snapshots.push(graph_import(graph, &mut work, control)?);
    }
    control.poll()?;
    Some(snapshots)
}

fn graph_import(
    graph: &wire::Graph,
    work: &mut usize,
    control: &SourceControl<'_>,
) -> Option<Arc<ArraySnapshot>> {
    let sort = scalar::sort(graph.element, control)?;
    let mut owned = Vec::new();
    reserve(&mut owned, graph.nodes.len(), control)?;
    for node in &graph.nodes {
        owned.push(decode(node, graph.element, control)?);
    }
    let mut nodes = Vec::new();
    reserve(&mut nodes, owned.len(), control)?;
    for node in &owned {
        control.debit(1, 0)?;
        let kind = match node {
            Owned::Finite(value) => SnapshotKind::Finite(value),
            Owned::Store { base, index, value } => SnapshotKind::Store {
                base: *base,
                index,
                value,
            },
            Owned::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => SnapshotKind::Range {
                destination: *destination,
                source: *source,
                lo,
                hi,
                source_lo,
            },
        };
        nodes.push(SnapshotNode { sort: &sort, kind });
    }
    let result =
        ArraySnapshot::from_topology(&nodes, graph.root, work, &mut || control.poll().is_none())
            .ok()?;
    drop(nodes);
    drop(owned);
    drop(sort);
    control.poll()?;
    Some(result)
}

fn decode(node: &wire::Node, element: wire::Element, control: &SourceControl<'_>) -> Option<Owned> {
    control.debit(1, 64)?;
    match node {
        wire::Node::Finite { default, stores } => {
            let default = scalar::import(default, element, control)?;
            let mut entries = Vec::new();
            reserve(&mut entries, stores.len(), control)?;
            for store in stores {
                control.debit(1, 32)?;
                entries.push((
                    ModelValue::bitvec(store.index.into(), 64),
                    scalar::import(&store.value, element, control)?,
                ));
            }
            Some(Owned::Finite(ArrayValue {
                default,
                store: entries,
            }))
        }
        wire::Node::Store { base, index, value } => Some(Owned::Store {
            base: *base,
            index: ModelValue::bitvec((*index).into(), 64),
            value: scalar::import(value, element, control)?,
        }),
        wire::Node::Range {
            destination,
            source,
            lo,
            hi,
            source_lo,
        } => Some(Owned::Range {
            destination: *destination,
            source: *source,
            lo: BigInt::from(*lo),
            hi: BigInt::from(*hi),
            source_lo: BigInt::from(*source_lo),
        }),
    }
}
