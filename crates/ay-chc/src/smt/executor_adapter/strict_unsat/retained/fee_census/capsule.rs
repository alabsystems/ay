// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Small exact source capsules for diagnostics, never replay/price authority.
//! Only the existing solved snapshot is borrowed. No solver, recognizer,
//! owner callback/debit, clock, global scan or unbounded rendering is added.

use super::Census;
use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use ay_dpll::api::SerializableProofBundle;
use num_traits::ToPrimitive;

pub(super) const CAPSULES: usize = 8;
const NODES: usize = 32;
const EDGES: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Shape {
    array: bool,
    index_boolean: bool,
    index_width: u32,
    boolean: bool,
    width: u32,
}
const EMPTY_SHAPE: Shape = Shape {
    array: false,
    index_boolean: false,
    index_width: 0,
    boolean: false,
    width: 0,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Empty,
    Bool(bool),
    Bv(u128, u32),
    Variable,
    Not,
    App { bytes: [u8; 32], len: usize },
}
#[derive(Clone, Copy, Debug)]
struct Node {
    id: TermId,
    shape: Shape,
    kind: Kind,
    first: usize,
    count: usize,
}
const EMPTY_NODE: Node = Node {
    id: TermId::SENTINEL,
    shape: EMPTY_SHAPE,
    kind: Kind::Empty,
    first: 0,
    count: 0,
};

#[derive(Clone, Copy, Debug)]
pub(super) struct Capsule {
    row: usize,
    step: usize,
    roots: [TermId; NODES],
    root_count: usize,
    nodes: [Node; NODES],
    node_count: usize,
    edges: [TermId; EDGES],
    edge_count: usize,
    complete: bool,
}
pub(super) const EMPTY: Capsule = Capsule {
    row: 0,
    step: 0,
    roots: [TermId::SENTINEL; NODES],
    root_count: 0,
    nodes: [EMPTY_NODE; NODES],
    node_count: 0,
    edges: [TermId::SENTINEL; EDGES],
    edge_count: 0,
    complete: false,
};

pub(super) fn record(
    census: &mut Census,
    snapshot: &SerializableProofBundle,
    roots: &[TermId],
    step: usize,
) {
    if census.capsule_count == CAPSULES {
        census.capsule_overflow = true;
        return;
    }
    let mut capsule = read(&snapshot.term_entries, roots);
    capsule.row = census.row;
    capsule.step = step;
    census.capsules[census.capsule_count] = capsule;
    census.capsule_count += 1;
}

fn scalar(sort: &Sort) -> Option<(bool, u32)> {
    match sort {
        Sort::Bool => Some((true, 0)),
        Sort::BitVec(word) if (1..=128).contains(&word.width) => Some((false, word.width)),
        _ => None,
    }
}
fn shape(sort: &Sort) -> Option<Shape> {
    if let Sort::Array(array) = sort {
        let (index_boolean, index_width) = scalar(&array.index_sort)?;
        let (boolean, width) = scalar(&array.element_sort)?;
        Some(Shape {
            array: true,
            index_boolean,
            index_width,
            boolean,
            width,
        })
    } else {
        let (boolean, width) = scalar(sort)?;
        Some(Shape {
            boolean,
            width,
            ..EMPTY_SHAPE
        })
    }
}

fn kind(data: &TermData, actual: Shape) -> Option<Kind> {
    match data {
        TermData::Const(Constant::Bool(value)) if !actual.array && actual.boolean => {
            Some(Kind::Bool(*value))
        }
        TermData::Const(Constant::BitVec { value, width })
            if !actual.array && !actual.boolean && *width == actual.width =>
        {
            let value = value.to_u128()?;
            (*width == 128 || value < (1u128 << *width)).then_some(Kind::Bv(value, *width))
        }
        TermData::Var(..) => Some(Kind::Variable),
        TermData::Not(_) if !actual.array && actual.boolean => Some(Kind::Not),
        TermData::App(Symbol::Named(name), _) => {
            if name.is_empty() || name.len() > 32 || !name.bytes().all(|c| c.is_ascii_graphic()) {
                return None;
            }
            let mut bytes = [0; 32];
            bytes[..name.len()].copy_from_slice(name.as_bytes());
            Some(Kind::App {
                bytes,
                len: name.len(),
            })
        }
        _ => None,
    }
}

fn read(entries: &[(TermData, Sort)], roots: &[TermId]) -> Capsule {
    let mut result = EMPTY;
    if roots.is_empty() || roots.len() > NODES {
        return result;
    }
    result.roots[..roots.len()].copy_from_slice(roots);
    result.root_count = roots.len();
    let mut pending = [TermId::SENTINEL; EDGES];
    pending[..roots.len()].copy_from_slice(roots);
    let mut queued = roots.len();
    while queued > 0 {
        queued -= 1;
        let id = pending[queued];
        if result.nodes[..result.node_count]
            .iter()
            .any(|node| node.id == id)
        {
            continue;
        }
        if result.node_count == NODES {
            return result;
        }
        let Some((data, sort)) = entries.get(id.index()) else {
            return result;
        };
        let Some(shape) = shape(sort) else {
            return result;
        };
        let Some(kind) = kind(data, shape) else {
            return result;
        };
        let children = match data {
            TermData::Const(_) | TermData::Var(..) => &[][..],
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::App(_, args) => args.as_slice(),
            _ => return result,
        };
        if children.len() > EDGES - result.edge_count || children.len() > EDGES - queued {
            return result;
        }
        let first = result.edge_count;
        result.edges[first..first + children.len()].copy_from_slice(children);
        result.edge_count += children.len();
        result.nodes[result.node_count] = Node {
            id,
            shape,
            kind,
            first,
            count: children.len(),
        };
        result.node_count += 1;
        pending[queued..queued + children.len()].copy_from_slice(children);
        queued += children.len();
    }
    let mut state = [0; NODES];
    result.complete = (0..result.node_count).all(|node| acyclic(&result, node, &mut state));
    result
}

// This marks cyclic capsules incomplete, not a semantic validation verdict.
fn acyclic(capsule: &Capsule, index: usize, state: &mut [u8; NODES]) -> bool {
    match state[index] {
        1 => return false,
        2 => return true,
        _ => {}
    }
    state[index] = 1;
    let node = capsule.nodes[index];
    for child in &capsule.edges[node.first..node.first + node.count] {
        let Some(child) = capsule.nodes[..capsule.node_count]
            .iter()
            .position(|n| n.id == *child)
        else {
            return false;
        };
        if !acyclic(capsule, child, state) {
            return false;
        }
    }
    state[index] = 2;
    true
}

pub(super) fn dump(census: &Census) {
    eprintln!(
        "retained-capsule-inventory case={} count={} overflow={} diagnostic_only=true",
        census.case, census.capsule_count, census.capsule_overflow
    );
    for capsule in &census.capsules[..census.capsule_count] {
        eprintln!("retained-capsule case={} row={} step={} roots={} nodes={} edges={} complete={} diagnostic_only=true",
            census.case, capsule.row, capsule.step, capsule.root_count,
            capsule.node_count, capsule.edge_count, capsule.complete);
        for (index, id) in capsule.roots[..capsule.root_count].iter().enumerate() {
            eprintln!(
                "retained-capsule-root case={} row={} step={} slot={} term={}",
                census.case,
                capsule.row,
                capsule.step,
                index,
                id.index()
            );
        }
        for node in &capsule.nodes[..capsule.node_count] {
            dump_node(census.case, capsule, node);
            for (slot, child) in capsule.edges[node.first..node.first + node.count]
                .iter()
                .enumerate()
            {
                eprintln!(
                    "retained-capsule-edge case={} row={} step={} parent={} slot={} child={}",
                    census.case,
                    capsule.row,
                    capsule.step,
                    node.id.index(),
                    slot,
                    child.index()
                );
            }
        }
    }
}
fn dump_node(case: &str, capsule: &Capsule, node: &Node) {
    let (kind, value, width, name) = match &node.kind {
        Kind::Bool(value) => ("BoolConst", u128::from(*value), 0, "-"),
        Kind::Bv(value, width) => ("BvConst", *value, *width, "-"),
        Kind::Variable => ("Var", 0, 0, "-"),
        Kind::Not => ("Not", 0, 0, "-"),
        Kind::App { bytes, len } => (
            "App",
            0,
            0,
            std::str::from_utf8(&bytes[..*len]).unwrap_or("-"),
        ),
        Kind::Empty => ("Empty", 0, 0, "-"),
    };
    eprintln!("retained-capsule-node case={} row={} step={} term={} kind={} value={} const_width={} op={} array={} index_boolean={} index_width={} boolean={} width={} arity={}",
        case, capsule.row, capsule.step, node.id.index(), kind, value, width, name,
        node.shape.array, node.shape.index_boolean, node.shape.index_width,
        node.shape.boolean, node.shape.width, node.count);
}

#[cfg(test)]
mod tests;
