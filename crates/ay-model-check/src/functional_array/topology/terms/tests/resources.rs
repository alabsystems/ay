// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn closed_conversion_validates_unused_bad_scalars_and_widths_before_interning() {
    for width in [0, 129, u32::MAX] {
        let array_sort = sort(width);
        let value = ArrayValue {
            default: ModelValue::BitVec {
                value: 0.into(),
                width,
            },
            store: vec![],
        };
        let topology = SnapshotTopology {
            root: 0,
            nodes: vec![SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&value),
            }],
        };
        let mut terms = TermStore::new();
        let before = terms.len();
        assert_eq!(
            topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
            Err(SnapshotTermError::UnsupportedSort)
        );
        assert_eq!(terms.len(), before);
    }
    let array_sort = sort(8);
    let good = ArrayValue {
        default: bv(0, 8),
        store: vec![],
    };
    let bad = ArrayValue {
        default: bv(0, 8),
        store: vec![
            (
                bv(0, 64),
                ModelValue::BitVec {
                    value: (-1).into(),
                    width: 8,
                },
            ),
            (bv(0, 64), bv(1, 8)),
        ],
    };
    let topology = SnapshotTopology {
        root: 0,
        nodes: vec![
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&good),
            },
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&bad),
            },
        ],
    };
    let mut terms = TermStore::new();
    let before = terms.len();
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
        Err(SnapshotTermError::InvalidTopology)
    );
    assert_eq!(terms.len(), before);
}

#[test]
fn closed_conversion_self_forward_missing_edges_and_mixed_sorts_refuse() {
    let array_sort = sort(8);
    let other_sort = sort(16);
    let value = ArrayValue {
        default: bv(0, 8),
        store: vec![],
    };
    let index = bv(0, 64);
    let datum = bv(1, 8);
    for base in [1, 2, usize::MAX] {
        let topology = SnapshotTopology {
            root: 1,
            nodes: vec![
                SnapshotNode {
                    sort: &array_sort,
                    kind: SnapshotKind::Finite(&value),
                },
                SnapshotNode {
                    sort: &array_sort,
                    kind: SnapshotKind::Store {
                        base,
                        index: &index,
                        value: &datum,
                    },
                },
            ],
        };
        let mut terms = TermStore::new();
        let before = terms.len();
        assert_eq!(
            topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
            Err(SnapshotTermError::InvalidTopology)
        );
        assert_eq!(terms.len(), before);
    }
    let datum = bv(1, 16);
    let topology = SnapshotTopology {
        root: 1,
        nodes: vec![
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&value),
            },
            SnapshotNode {
                sort: &other_sort,
                kind: SnapshotKind::Store {
                    base: 0,
                    index: &index,
                    value: &datum,
                },
            },
        ],
    };
    assert_eq!(
        topology.try_to_term_with_progress(&mut TermStore::new(), &mut |_, _| true),
        Err(SnapshotTermError::InvalidTopology)
    );
}

#[test]
fn closed_empty_range_cannot_skip_invalid_offset_or_source_capture() {
    let array_sort = sort(8);
    let value = ArrayValue {
        default: bv(0, 8),
        store: vec![],
    };
    let lo = BigInt::from(3);
    let hi = BigInt::from(1);
    let bad = BigInt::one() << 64u32;
    let topology = SnapshotTopology {
        root: 1,
        nodes: vec![
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Finite(&value),
            },
            SnapshotNode {
                sort: &array_sort,
                kind: SnapshotKind::Range {
                    destination: 0,
                    source: 0,
                    lo: &lo,
                    hi: &hi,
                    source_lo: &bad,
                },
            },
        ],
    };
    let mut terms = TermStore::new();
    let before = terms.len();
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
        Err(SnapshotTermError::InvalidTopology)
    );
    assert_eq!(terms.len(), before);
}

#[test]
fn closed_conversion_zeros_work_and_bytes_shortage_stay_refused_on_same_sink() {
    let root = byte(7, &[(1, 2)]);
    let mut baseline = Sink::new();
    convert(&root, &mut TermStore::new(), &mut baseline);
    let paid_work = 1_000_000_000 - baseline.work;
    let paid_bytes = 1_000_000_000 - baseline.bytes;
    for (work, bytes) in [
        (0, 1_000_000_000),
        (paid_work - 1, 1_000_000_000),
        (1_000_000_000, paid_bytes - 1),
    ] {
        let mut sink = Sink {
            work,
            bytes,
            refused: false,
            calls: 0,
        };
        let mut terms = TermStore::new();
        let result = root
            .topology_with_progress(&mut |w, b| sink.pay(w, b))
            .map_err(|_| SnapshotTermError::ResourceLimit)
            .and_then(|topology| {
                topology.try_to_term_with_progress(&mut terms, &mut |w, b| sink.pay(w, b))
            });
        assert_eq!(result, Err(SnapshotTermError::ResourceLimit));
        assert!(sink.refused);
        assert!(!sink.pay(0, 0));
        assert!(root
            .topology_with_progress(&mut |w, b| sink.pay(w, b))
            .is_err());
    }
}

#[test]
fn closed_export_and_two_constructions_share_one_cumulative_original_sink() {
    let root = byte(7, &[(0, 9)]);
    let mut sink = Sink::new();
    let topology = root
        .topology_with_progress(&mut |w, b| sink.pay(w, b))
        .expect("export");
    let after_export = (sink.work, sink.bytes);
    let mut terms = TermStore::new();
    let first = topology
        .try_to_term_with_progress(&mut terms, &mut |w, b| sink.pay(w, b))
        .expect("first");
    let after_first = (sink.work, sink.bytes);
    let second = topology
        .try_to_term_with_progress(&mut terms, &mut |w, b| sink.pay(w, b))
        .expect("same arena");
    assert_eq!(first, second);
    assert!(after_first.0 < after_export.0 && after_first.1 < after_export.1);
    assert!(
        sink.work < after_first.0 && sink.bytes < after_first.1,
        "reuse is still traversed and prepaid"
    );
}

#[test]
fn closed_conversion_final_poll_withholds_id_after_scratch_disposal() {
    let root = byte(7, &[(0, 9)]);
    let mut work = 100_000;
    let topology = root
        .topology(&mut work, &mut || false)
        .expect("borrowed fixture");
    let mut calls = 0;
    topology
        .try_to_term_with_progress(&mut TermStore::new(), &mut |_, _| {
            calls += 1;
            true
        })
        .expect("count fixture");
    let final_call = calls;
    calls = 0;
    assert_eq!(
        topology.try_to_term_with_progress(&mut TermStore::new(), &mut |_, _| {
            calls += 1;
            calls < final_call
        }),
        Err(SnapshotTermError::ResourceLimit)
    );
    assert_eq!(calls, final_call);
}

#[test]
fn closed_direct_export_final_poll_and_midwalk_reset_cannot_renew_sink() {
    let root = byte(7, &[(0, 9)]);
    let mut calls = 0;
    root.topology_with_progress(&mut |_, _| {
        calls += 1;
        true
    })
    .expect("export count");
    let final_call = calls;
    calls = 0;
    assert!(root
        .topology_with_progress(&mut |_, _| {
            calls += 1;
            calls < final_call
        })
        .is_err());
    let mut sink = Sink::new();
    let mut stopped = true;
    assert!(root
        .topology_with_progress(&mut |w, b| {
            if stopped {
                sink.refused = true;
            }
            sink.pay(w, b)
        })
        .is_err());
    stopped = false;
    assert!(root
        .topology_with_progress(&mut |w, b| {
            if stopped {
                sink.refused = true;
            }
            sink.pay(w, b)
        })
        .is_err());
}

#[test]
fn closed_checker_snapshot_cannot_be_promoted_to_producer_by_conversion() {
    let source = TermStore::new();
    let (true_id, false_id) = source.boolean_constant_ids();
    let mut terms = TermStore::from_entries(source.entries_snapshot(), true_id, false_id, 0);
    let root = byte(7, &[]);
    let mut work = 100_000;
    let topology = root
        .topology(&mut work, &mut || false)
        .expect("fixture export");
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
        Err(SnapshotTermError::Producer(
            ControlledTermInternError::ReadOnlySnapshot
        ))
    );
}
