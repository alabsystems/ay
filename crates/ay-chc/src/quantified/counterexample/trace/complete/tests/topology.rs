// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn output(snapshot: &Arc<ArraySnapshot>) -> String {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    pins::render(
        &rendered,
        &bindings(&rendered, snapshot),
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap()
}

#[test]
fn complete_overwritten_stores_keep_every_capture_and_default_in_order() {
    let array = ArrayValue {
        default: bv(3, 8),
        store: vec![(bv(1, 64), bv(7, 8)), (bv(1, 64), bv(9, 8))],
    };
    let snapshot = ArraySnapshot::finite(array, &sort(), &mut 100_000).unwrap();
    let text = output(&snapshot);
    assert!(text.contains("(_ bv3 8)"));
    let old = text.find("(_ bv7 8)").unwrap();
    let new = text.find("(_ bv9 8)").unwrap();
    assert!(old < new);
    assert_eq!(text.matches("(store ").count(), 2);
}

#[test]
fn complete_empty_range_retains_both_full_captures_before_rendering() {
    let sort = sort();
    let destination = ArrayValue {
        default: bv(0, 8),
        store: vec![],
    };
    let source = ArrayValue {
        default: bv(7, 8),
        store: vec![],
    };
    let bound = 5.into();
    let offset = 0.into();
    let nodes = [
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&destination),
        },
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&source),
        },
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Range {
                destination: 0,
                source: 1,
                lo: &bound,
                hi: &bound,
                source_lo: &offset,
            },
        },
    ];
    let snapshot = ArraySnapshot::from_topology(&nodes, 2, &mut 100_000, &mut || false).unwrap();
    let text = output(&snapshot);
    assert!(text.contains("(_ bv7 8)"));
    assert!(text.contains("(_ bv0 8)"));
    assert_eq!(text.matches("(lambda ((").count(), 1);
    assert_eq!(text.matches("(_ bv5 64)").count(), 3);
}

#[test]
fn complete_unreachable_malformed_topology_cannot_become_snapshot_data() {
    let sort = sort();
    let valid = ArrayValue {
        default: bv(0, 8),
        store: vec![],
    };
    let malformed = ArrayValue {
        default: ModelValue::Bool(true),
        store: vec![],
    };
    let nodes = [
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&valid),
        },
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&malformed),
        },
    ];
    let mut work = 100_000;
    assert!(ArraySnapshot::from_topology(&nodes, 0, &mut work, &mut || false).is_err());
    assert_eq!(work, 0);
    assert!(ArraySnapshot::from_topology(&nodes[..1], 0, &mut work, &mut || false).is_err());
    assert_eq!(work, 0);
}

#[test]
fn complete_separate_equal_capture_graphs_share_one_lexical_lambda_without_public_eq() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let first = range();
    let second = range();
    assert!(!Arc::ptr_eq(&first, &second));
    let mut bindings = bindings(&rendered, &first);
    bindings[1].value = QuantifiedChcCompleteValue::FunctionalArray(second);
    let environment =
        snapshots::build(&rendered.original, &bindings, &source, &control(&token)).unwrap();
    assert_eq!(
        environment
            .definitions
            .iter()
            .filter(|node| node.body.starts_with("(lambda "))
            .count(),
        1
    );
    assert_eq!(environment.bindings[0], environment.bindings[1]);
}
