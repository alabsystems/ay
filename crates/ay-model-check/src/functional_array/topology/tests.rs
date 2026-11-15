// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::ToPrimitive;
use std::cell::Cell;
use std::sync::Arc;

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}
fn sort() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::bitvec(8))
}
fn finite(default: u64, cells: &[(u64, u64)]) -> ArrayValue {
    ArrayValue {
        default: bv(default, 8),
        store: cells.iter().map(|&(i, v)| (bv(i, 64), bv(v, 8))).collect(),
    }
}
fn read(data: &ArraySnapshot, index: u64, work: &mut usize) -> u64 {
    let ModelValue::BitVec { value, width: 8 } = data.read(&bv(index, 64), work).expect("read")
    else {
        panic!("typed byte");
    };
    value.to_u64().expect("byte")
}
fn leaf<'a>(sort: &'a Sort, value: &'a ArrayValue) -> SnapshotNode<'a> {
    SnapshotNode {
        sort,
        kind: SnapshotKind::Finite(value),
    }
}

#[test]
fn topology_roundtrip_preserves_shared_ranges_stores_and_full_modular_reads() {
    let mut work = 1_000_000;
    let old = ArraySnapshot::finite(finite(7, &[(0, 9), (u64::MAX, 11)]), &sort(), &mut work)
        .expect("base");
    let range = ArraySnapshot::range_copy(
        Arc::clone(&old),
        Arc::clone(&old),
        &bv(1, 64),
        &bv(3, 64),
        &bv(u64::MAX, 64),
        &mut work,
    )
    .expect("range");
    let root = ArraySnapshot::store(range, &bv(0, 64), &bv(42, 8), &mut work).expect("store");
    let topology = root.topology(&mut work, &mut || false).expect("borrow");
    assert_eq!(topology.nodes().len(), 3);
    let SnapshotKind::Range {
        destination,
        source,
        ..
    } = topology.nodes()[1].kind
    else {
        panic!("range node");
    };
    assert_eq!(
        destination, source,
        "one shared old assignment, not deep copies"
    );
    let copied =
        ArraySnapshot::from_topology(topology.nodes(), topology.root(), &mut work, &mut || false)
            .expect("import");
    for index in [0, 1, 2, 3, u64::MAX] {
        assert_eq!(
            read(&root, index, &mut work),
            read(&copied, index, &mut work)
        );
    }
    assert!(root
        .same_function(&copied, &mut work)
        .expect("structural agreement"));
    assert!(work < 1_000_000, "one cumulative caller ledger, no reset");
}

#[test]
fn topology_import_keeps_raw_store_shape_and_every_overwritten_finite_entry() {
    let sort = sort();
    let value = finite(1, &[(2, 3), (2, 4)]);
    let index = bv(2, 64);
    let datum = bv(5, 8);
    let nodes = [
        leaf(&sort, &value),
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Store {
                base: 0,
                index: &index,
                value: &datum,
            },
        },
    ];
    let mut work = 100_000;
    let root = ArraySnapshot::from_topology(&nodes, 1, &mut work, &mut || false).expect("data");
    let topology = root.topology(&mut work, &mut || false).expect("borrow");
    assert_eq!(
        topology.nodes().len(),
        2,
        "not normalized into a replacement finite node"
    );
    let SnapshotKind::Finite(stores) = topology.nodes()[0].kind else {
        panic!("finite");
    };
    assert_eq!(
        stores.store.len(),
        2,
        "oldest-first repeated overrides retained"
    );
    assert!(matches!(
        topology.nodes()[1].kind,
        SnapshotKind::Store { base: 0, .. }
    ));
    assert_eq!(read(&root, 2, &mut work), 5);
}

#[test]
fn topology_empty_range_retains_both_complete_captures_without_authority() {
    let sort = sort();
    let dst = finite(7, &[]);
    let src = finite(9, &[]);
    let lo = BigInt::from(3);
    let hi = BigInt::from(1);
    let offset = BigInt::from(u64::MAX);
    let nodes = [
        leaf(&sort, &dst),
        leaf(&sort, &src),
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Range {
                destination: 0,
                source: 1,
                lo: &lo,
                hi: &hi,
                source_lo: &offset,
            },
        },
    ];
    let mut work = 100_000;
    let root =
        ArraySnapshot::from_topology(&nodes, 2, &mut work, &mut || false).expect("data only");
    let topology = root.topology(&mut work, &mut || false).expect("borrow");
    assert_eq!(topology.nodes().len(), 3);
    assert!(matches!(
        topology.nodes()[2].kind,
        SnapshotKind::Range { source: 1, .. }
    ));
    assert_eq!(read(&root, 2, &mut work), 7);
    assert!(
        root.finite_value(&mut work).expect("inspection").is_none(),
        "retained range does not invent a finite-array representation or seal"
    );
}

#[test]
fn topology_unreachable_malformed_capture_refuses_the_entire_import() {
    let sort = sort();
    let good = finite(7, &[]);
    let bad = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![],
    };
    let mut work = 100_000;
    assert!(matches!(
        ArraySnapshot::from_topology(
            &[leaf(&sort, &good), leaf(&sort, &bad)],
            0,
            &mut work,
            &mut || false
        ),
        Err(FunctionalArrayError::Value)
    ));
    assert_eq!(
        work, 0,
        "unreachable data is validated and refusal remains sticky"
    );
}

#[test]
fn topology_self_forward_missing_edges_and_cycles_refuse_without_partial_data() {
    let sort = sort();
    let value = finite(1, &[]);
    let index = bv(0, 64);
    let datum = bv(2, 8);
    for base in [1, 2, usize::MAX] {
        let nodes = [
            leaf(&sort, &value),
            SnapshotNode {
                sort: &sort,
                kind: SnapshotKind::Store {
                    base,
                    index: &index,
                    value: &datum,
                },
            },
        ];
        let mut work = 100_000;
        assert!(matches!(
            ArraySnapshot::from_topology(&nodes, 1, &mut work, &mut || false),
            Err(FunctionalArrayError::Value)
        ));
        assert_eq!(work, 0);
    }
}

#[test]
fn topology_exact_parent_and_capture_sorts_are_not_coerced() {
    let sort = sort();
    let bool_sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let old = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![],
    };
    let index = bv(0, 64);
    let datum = bv(2, 8);
    let nodes = [
        leaf(&bool_sort, &old),
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Store {
                base: 0,
                index: &index,
                value: &datum,
            },
        },
    ];
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 1, &mut 100_000, &mut || false),
        Err(FunctionalArrayError::Sort)
    ));
    let wrong_index = bv(0, 32);
    let finite_value = finite(0, &[]);
    let nodes = [
        leaf(&sort, &finite_value),
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Store {
                base: 0,
                index: &wrong_index,
                value: &datum,
            },
        },
    ];
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 1, &mut 100_000, &mut || false),
        Err(FunctionalArrayError::Sort)
    ));
}

#[test]
fn topology_overwritten_bad_values_and_unchosen_bounds_are_not_skipped() {
    let sort = sort();
    let bad = ModelValue::BitVec {
        value: BigInt::from(-1),
        width: 8,
    };
    let value = ArrayValue {
        default: bv(0, 8),
        store: vec![(bv(2, 64), bad), (bv(2, 64), bv(3, 8))],
    };
    assert!(matches!(
        ArraySnapshot::from_topology(&[leaf(&sort, &value)], 0, &mut 100_000, &mut || false),
        Err(FunctionalArrayError::Value)
    ));
    let valid = finite(0, &[]);
    let lo = BigInt::from(3);
    let hi = BigInt::from(1);
    let invalid = BigInt::from(1u128 << 64);
    let nodes = [
        leaf(&sort, &valid),
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Range {
                destination: 0,
                source: 0,
                lo: &lo,
                hi: &hi,
                source_lo: &invalid,
            },
        },
    ];
    assert!(
        matches!(
            ArraySnapshot::from_topology(&nodes, 1, &mut 100_000, &mut || false),
            Err(FunctionalArrayError::Value)
        ),
        "empty interval cannot waive its unused offset"
    );
}

#[test]
fn topology_depth_and_population_limits_refuse_before_landing() {
    let sort = sort();
    let value = finite(0, &[]);
    let index = bv(0, 64);
    let datum = bv(1, 8);
    let mut nodes = vec![leaf(&sort, &value)];
    for base in 0..64 {
        nodes.push(SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Store {
                base,
                index: &index,
                value: &datum,
            },
        });
    }
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 64, &mut 1_000_000, &mut || false),
        Err(FunctionalArrayError::Resource)
    ));
    let oversized = vec![leaf(&sort, &value); MAX_NODES + 1];
    assert!(matches!(
        ArraySnapshot::from_topology(&oversized, 0, &mut 1_000_000, &mut || false),
        Err(FunctionalArrayError::Resource)
    ));
}

#[test]
fn topology_zero_original_work_and_callback_reset_cannot_renew_budget() {
    let sort = sort();
    let value = finite(0, &[]);
    let nodes = [leaf(&sort, &value)];
    let mut work = 0;
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || false),
        Err(FunctionalArrayError::Resource)
    ));
    let calls = Cell::new(0);
    let mut work = 100_000;
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || {
            calls.set(calls.get() + 1);
            true
        }),
        Err(FunctionalArrayError::Resource)
    ));
    assert_eq!(calls.get(), 1, "initial stop before scratch allocation");
    assert_eq!(work, 0);
    assert!(ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || false).is_err());
}

#[test]
fn topology_mid_export_cancellation_is_sticky_on_the_same_original_ledger() {
    let mut work = 100_000;
    let root = ArraySnapshot::finite(finite(7, &[(0, 9)]), &sort(), &mut work).expect("base");
    let calls = Cell::new(0);
    assert!(matches!(
        root.topology(&mut work, &mut || {
            let next = calls.get() + 1;
            calls.set(next);
            next == 3
        }),
        Err(FunctionalArrayError::Resource)
    ));
    assert_eq!(work, 0);
    assert!(root.topology(&mut work, &mut || false).is_err());
}

#[test]
fn topology_borrowed_export_exposes_exact_values_not_reparsed_model_text() {
    let mut work = 100_000;
    let root = ArraySnapshot::finite(finite(7, &[(0, 9)]), &sort(), &mut work).expect("base");
    let topology = root.topology(&mut work, &mut || false).expect("borrow");
    let SnapshotKind::Finite(value) = topology.nodes()[0].kind else {
        panic!("finite");
    };
    let Node::Finite(original) = &root.node else {
        panic!("finite");
    };
    assert!(
        std::ptr::eq(value, original),
        "complete data borrowed without print/parse"
    );
    assert_eq!(topology.root(), 0);
    // The API exposes data indices only, not source/query/evidence fields.
}

#[test]
fn topology_payload_byte_ceiling_refuses_before_any_owned_snapshot_copy() {
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(u32::MAX));
    let value = ArrayValue {
        default: ModelValue::BitVec {
            value: BigInt::from(0),
            width: u32::MAX,
        },
        store: vec![],
    };
    let mut work = usize::MAX;
    assert!(matches!(
        ArraySnapshot::from_topology(&[leaf(&sort, &value)], 0, &mut work, &mut || false),
        Err(FunctionalArrayError::Resource)
    ));
    assert_eq!(work, 0);
}

#[test]
fn topology_terminal_cancellation_refuses_after_scratch_cleanup() {
    let sort = sort();
    let value = finite(0, &[(1, 2)]);
    let nodes = [leaf(&sort, &value)];
    let calls = Cell::new(0);
    let mut work = 100_000;
    ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || {
        calls.set(calls.get() + 1);
        false
    })
    .expect("baseline data, no authority");
    let final_call = calls.get();
    calls.set(0);
    assert!(matches!(
        ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || {
            let next = calls.get() + 1;
            calls.set(next);
            next == final_call
        }),
        Err(FunctionalArrayError::Resource)
    ));
    assert_eq!(calls.get(), final_call);
    assert_eq!(work, 0);
}
