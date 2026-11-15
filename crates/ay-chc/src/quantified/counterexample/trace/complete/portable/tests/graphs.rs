// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn complete_wire_preserves_whole_range_and_shared_binding_dag() {
    let token = CancellationToken::new();
    let problem = source();
    let data = wire(&problem, &token);
    assert_eq!(data.graphs.len(), 1);
    assert_eq!(data.graphs[0].nodes.len(), 3);
    let arrays = arrays::import(&data.graphs, &control(&token)).unwrap();
    assert_scalar_eq(&read(&arrays[0], 0), &bv(9, 8));
    assert_scalar_eq(&read(&arrays[0], (1 << 40) - 1), &bv(9, 8));
    assert_scalar_eq(&read(&arrays[0], 1 << 40), &bv(0, 8));
    let rendered =
        render::render_complete(&problem, &[0, 1], &[vec![], vec![0]], &control(&token)).unwrap();
    let registry = registry(&problem, &control(&token)).unwrap();
    let values = bindings::import(&data, &rendered, &registry, &arrays, &control(&token)).unwrap();
    let roots = values
        .iter()
        .map(|entry| match &entry.value {
            QuantifiedChcCompleteValue::FunctionalArray(array) => array,
            _ => panic!("whole functional array required"),
        })
        .collect::<Vec<_>>();
    assert!(roots.iter().all(|array| Arc::ptr_eq(array, roots[0])));
    let prepared = rebuild::prepare(&problem, &data, &control(&token)).unwrap();
    assert_eq!(prepared.pinned.matches("(assert ").count(), 1);
    assert!(prepared.pinned.contains("(forall "));
    assert!(prepared.pinned.contains("(lambda (("));
}

#[test]
fn finite_defaults_store_order_and_empty_range_captures_are_complete_data() {
    let token = CancellationToken::new();
    let sort = sort();
    let base = ArrayValue {
        default: bv(0, 8),
        store: vec![(bv(2, 64), bv(1, 8)), (bv(2, 64), bv(9, 8))],
    };
    let captured = ArrayValue {
        default: bv(7, 8),
        store: Vec::new(),
    };
    let zero = 0.into();
    let nodes = [
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&base),
        },
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Finite(&captured),
        },
        SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Range {
                destination: 0,
                source: 1,
                lo: &zero,
                hi: &zero,
                source_lo: &zero,
            },
        },
    ];
    let snapshot = ArraySnapshot::from_topology(&nodes, 2, &mut 100_000, &mut || false).unwrap();
    let mut catalog = arrays::Catalog::new(&control(&token), 1).unwrap();
    catalog
        .value(
            &snapshot,
            &crate::ChcSort::Array(
                Box::new(crate::ChcSort::BitVec(64)),
                Box::new(crate::ChcSort::BitVec(8)),
            ),
            &control(&token),
        )
        .unwrap();
    let decoded = arrays::import(&catalog.graphs, &control(&token)).unwrap();
    let topology = decoded[0].topology(&mut 100_000, &mut || false).unwrap();
    assert_eq!(topology.nodes().len(), 3);
    assert!(matches!(
        topology.nodes()[2].kind,
        SnapshotKind::Range { source: 1, .. }
    ));
    assert_scalar_eq(&read(&decoded[0], 2), &bv(9, 8));
    assert_scalar_eq(&read(&decoded[0], 100), &bv(0, 8));
}

#[test]
fn all_unreachable_nodes_are_checked_before_any_root_is_returned() {
    let token = CancellationToken::new();
    let mut graph = wire(&source(), &token).graphs.remove(0);
    graph.root = 0;
    graph.nodes.push(wire::Node::Store {
        base: 0,
        index: 0,
        value: wire::Scalar::BitVec {
            width: 8,
            value: "256".into(),
        },
    });
    assert!(arrays::import(&[graph], &control(&token)).is_none());
}

#[test]
fn forward_self_missing_and_deep_edges_refuse_the_complete_graph() {
    let token = CancellationToken::new();
    for parent in [1, 3, usize::MAX] {
        let mut graph = wire(&source(), &token).graphs.remove(0);
        graph.nodes[1] = wire::Node::Store {
            base: parent,
            index: 0,
            value: wire::Scalar::BitVec {
                width: 8,
                value: "0".into(),
            },
        };
        assert!(arrays::import(&[graph], &control(&token)).is_none());
    }
    let mut graph = wire(&source(), &token).graphs.remove(0);
    graph.nodes.truncate(1);
    for index in 1..=64 {
        graph.nodes.push(wire::Node::Store {
            base: index - 1,
            index: 0,
            value: wire::Scalar::BitVec {
                width: 8,
                value: "0".into(),
            },
        });
    }
    graph.root = 64;
    assert!(arrays::import(&[graph], &control(&token)).is_none());
}

#[test]
fn malformed_scalar_width_digits_sign_and_overflow_are_not_normalized() {
    let token = CancellationToken::new();
    for (width, value) in [
        (0, "0"),
        (129, "0"),
        (8, "256"),
        (8, "-1"),
        (8, "+1"),
        (8, "01"),
        (8, ""),
        (8, "1x"),
        (128, "340282366920938463463374607431768211456"),
    ] {
        let data = wire::Scalar::BitVec {
            width,
            value: value.into(),
        };
        assert!(scalar::import(&data, wire::Element::BitVec { width }, &control(&token)).is_none());
    }
    let max = wire::Scalar::BitVec {
        width: 128,
        value: u128::MAX.to_string(),
    };
    assert_scalar_eq(
        &scalar::import(&max, wire::Element::BitVec { width: 128 }, &control(&token)).unwrap(),
        &ModelValue::bitvec(u128::MAX.into(), 128),
    );
}

#[test]
fn bool_arrays_preserve_default_and_last_store_without_bv_coercion() {
    let token = CancellationToken::new();
    let graph = wire::Graph {
        element: wire::Element::Bool,
        root: 0,
        nodes: vec![wire::Node::Finite {
            default: wire::Scalar::Bool { value: false },
            stores: vec![wire::Store {
                index: u64::MAX,
                value: wire::Scalar::Bool { value: true },
            }],
        }],
    };
    let values = arrays::import(&[graph], &control(&token)).unwrap();
    assert_scalar_eq(&read(&values[0], u64::MAX), &ModelValue::Bool(true));
    assert_scalar_eq(&read(&values[0], 0), &ModelValue::Bool(false));
    assert!(scalar::import(
        &wire::Scalar::Bool { value: true },
        wire::Element::BitVec { width: 1 },
        &control(&token)
    )
    .is_none());
}
