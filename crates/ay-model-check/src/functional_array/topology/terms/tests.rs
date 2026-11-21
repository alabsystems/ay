// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ArraySnapshot, Evaluator, ModelView, SnapshotNode};
use num_traits::One;
use std::sync::Arc;

mod integer;
mod resources;

struct Empty;
impl ModelView for Empty {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

struct Sink {
    work: usize,
    bytes: usize,
    refused: bool,
    calls: usize,
}
impl Sink {
    fn new() -> Self {
        Self {
            work: 1_000_000_000,
            bytes: 1_000_000_000,
            refused: false,
            calls: 0,
        }
    }
    fn pay(&mut self, work: usize, bytes: usize) -> bool {
        self.calls += 1;
        if self.refused {
            return false;
        }
        match (self.work.checked_sub(work), self.bytes.checked_sub(bytes)) {
            (Some(work), Some(bytes)) => {
                self.work = work;
                self.bytes = bytes;
                true
            }
            _ => {
                self.refused = true;
                false
            }
        }
    }
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}
fn sort(width: u32) -> Sort {
    Sort::array(Sort::bitvec(64), Sort::bitvec(width))
}
fn data(
    default: ModelValue,
    cells: Vec<(ModelValue, ModelValue)>,
    sort: &Sort,
) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default,
            store: cells,
        },
        sort,
        &mut 1_000_000,
    )
    .expect("fixture DATA")
}
fn byte(default: u64, cells: &[(u64, u64)]) -> Arc<ArraySnapshot> {
    data(
        bv(default, 8),
        cells.iter().map(|&(i, v)| (bv(i, 64), bv(v, 8))).collect(),
        &sort(8),
    )
}
fn convert(root: &ArraySnapshot, terms: &mut TermStore, sink: &mut Sink) -> TermId {
    let topology = root
        .topology_with_progress(&mut |w, b| sink.pay(w, b))
        .expect("direct prepaid export");
    let term = topology
        .try_to_term_with_progress(terms, &mut |w, b| sink.pay(w, b))
        .expect("whole closed constructor");
    drop(topology);
    assert!(sink.pay(0, 0), "original sink after topology disposal");
    term
}
fn captured(terms: &TermStore, root: TermId) -> Arc<ArraySnapshot> {
    // A separate bounded independent DATA oracle, not production publication.
    Evaluator::new(terms, &Empty)
        .capture_array_snapshot(root)
        .expect("independent complete capture")
}
fn same_scalar(left: &ModelValue, right: &ModelValue) {
    match (left, right) {
        (ModelValue::Bool(left), ModelValue::Bool(right)) => assert_eq!(left, right),
        (
            ModelValue::BitVec {
                value: left,
                width: lw,
            },
            ModelValue::BitVec {
                value: right,
                width: rw,
            },
        ) => {
            assert_eq!(lw, rw);
            assert_eq!(left, right);
        }
        _ => panic!("exact admitted scalar"),
    }
}
fn reads(left: &ArraySnapshot, right: &ArraySnapshot, indices: &[u64]) {
    for &index in indices {
        same_scalar(
            &left
                .read(&bv(index, 64), &mut 1_000_000)
                .expect("original DATA read"),
            &right
                .read(&bv(index, 64), &mut 1_000_000)
                .expect("constructed DATA read"),
        );
    }
}
fn app_args<'a>(terms: &'a TermStore, id: TermId, expected: &str) -> &'a [TermId] {
    let TermData::App(Symbol::Named(name), args) = terms.get(id) else {
        panic!("named grammar")
    };
    assert_eq!(name.as_str(), expected);
    args
}

#[test]
fn closed_finite_bv128_keeps_every_ordered_override_and_exact_default() {
    let maximum = (BigInt::one() << 128u32) - BigInt::one();
    let full = ModelValue::BitVec {
        value: maximum,
        width: 128,
    };
    let root = data(
        full.clone(),
        vec![
            (bv(u64::MAX, 64), bv(7, 128)),
            (bv(u64::MAX, 64), full.clone()),
        ],
        &sort(128),
    );
    let mut terms = TermStore::new();
    let id = convert(&root, &mut terms, &mut Sink::new());
    let outer = app_args(&terms, id, "store");
    let inner = app_args(&terms, outer[0], "store");
    app_args(&terms, inner[0], "const-array");
    let rebuilt = captured(&terms, id);
    let finite = rebuilt
        .finite_value(&mut 1_000_000)
        .expect("finite")
        .expect("complete value");
    let ModelValue::Array(value) = finite else {
        panic!("array")
    };
    assert_eq!(value.store.len(), 2);
    same_scalar(&value.default, &full);
    same_scalar(&value.store[0].1, &bv(7, 128));
    same_scalar(&value.store[1].1, &full);
    reads(&root, &rebuilt, &[0, 1, u64::MAX]);
}

#[test]
fn closed_bool_finite_and_store_use_exact_scalar_sorts() {
    let array_sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let root = data(
        ModelValue::Bool(false),
        vec![(bv(0, 64), ModelValue::Bool(true))],
        &array_sort,
    );
    let mut terms = TermStore::new();
    let id = convert(&root, &mut terms, &mut Sink::new());
    assert_eq!(terms.sort(id), &array_sort);
    reads(&root, &captured(&terms, id), &[0, 1, u64::MAX]);
}

#[test]
fn closed_shared_prewrite_range_preserves_modular_source_index_and_maximum() {
    let old = byte(7, &[(0, 9), (u64::MAX, 11)]);
    let root = ArraySnapshot::range_copy(
        Arc::clone(&old),
        old,
        &bv(1, 64),
        &bv(3, 64),
        &bv(u64::MAX, 64),
        &mut 1000,
    )
    .expect("range DATA");
    let mut terms = TermStore::new();
    let id = convert(&root, &mut terms, &mut Sink::new());
    let recipe = crate::recognize_range_lambda(&terms, id).expect("exact closed range grammar");
    assert_eq!(
        recipe.source, recipe.destination,
        "one captured shared complete graph"
    );
    let rebuilt = captured(&terms, id);
    reads(&root, &rebuilt, &[0, 1, 2, 3, u64::MAX]);
    same_scalar(
        &rebuilt.read(&bv(1, 64), &mut 1000).expect("source MAX"),
        &bv(11, 8),
    );
    same_scalar(
        &rebuilt
            .read(&bv(2, 64), &mut 1000)
            .expect("source wraps zero"),
        &bv(9, 8),
    );
}

#[test]
fn closed_nested_ranges_and_newest_store_keep_original_captures() {
    let old = byte(1, &[(0, 2), (1, 3)]);
    let first = ArraySnapshot::range_copy(
        Arc::clone(&old),
        Arc::clone(&old),
        &bv(1, 64),
        &bv(4, 64),
        &bv(0, 64),
        &mut 1000,
    )
    .expect("first");
    let second =
        ArraySnapshot::range_copy(first, old, &bv(2, 64), &bv(5, 64), &bv(1, 64), &mut 1000)
            .expect("second");
    let root =
        ArraySnapshot::store(second, &bv(2, 64), &bv(99, 8), &mut 1000).expect("newest store");
    let mut terms = TermStore::new();
    let id = convert(&root, &mut terms, &mut Sink::new());
    app_args(&terms, id, "store");
    reads(&root, &captured(&terms, id), &[0, 1, 2, 3, 4, 5, u64::MAX]);
}

#[test]
fn closed_empty_range_still_constructs_both_full_captured_graphs() {
    let array_sort = sort(8);
    let destination = ArrayValue {
        default: bv(7, 8),
        store: vec![],
    };
    let source = ArrayValue {
        default: bv(9, 8),
        store: vec![(bv(u64::MAX, 64), bv(11, 8))],
    };
    let lo = BigInt::from(3);
    let hi = BigInt::from(1);
    let offset = BigInt::from(u64::MAX);
    let topology = SnapshotTopology {
        root: 2,
        nodes: vec![
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&destination),
            },
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&source),
            },
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Range {
                    destination: 0,
                    source: 1,
                    lo: &lo,
                    hi: &hi,
                    source_lo: &offset,
                },
            },
        ],
    };
    let mut terms = TermStore::new();
    let mut sink = Sink::new();
    let id = topology
        .try_to_term_with_progress(&mut terms, &mut |w, b| sink.pay(w, b))
        .expect("empty closed DATA");
    let recipe = crate::recognize_range_lambda(&terms, id).expect("range retained");
    app_args(&terms, recipe.source, "store");
    assert_ne!(recipe.source, recipe.destination);
    same_scalar(
        &captured(&terms, id)
            .read(&bv(0, 64), &mut 1000)
            .expect("destination"),
        &bv(7, 8),
    );
}

#[test]
fn closed_fresh_binder_never_captures_existing_visible_names() {
    let mut terms = TermStore::new();
    let reserved = terms.mk_var("__ay_range_pin!0", Sort::bitvec(64));
    let root = ArraySnapshot::range_copy(
        byte(1, &[]),
        byte(2, &[]),
        &bv(1, 64),
        &bv(2, 64),
        &bv(0, 64),
        &mut 1000,
    )
    .expect("range");
    let id = convert(&root, &mut terms, &mut Sink::new());
    let recipe = crate::recognize_range_lambda(&terms, id).expect("range");
    assert_ne!(reserved, recipe.bound);
    let TermData::Var(old, _) = terms.get(reserved) else {
        panic!("fixture variable")
    };
    let TermData::Var(fresh, _) = terms.get(recipe.bound) else {
        panic!("bound variable")
    };
    assert_ne!(old, fresh);
    reads(&root, &captured(&terms, id), &[0, 1, 2]);
}
