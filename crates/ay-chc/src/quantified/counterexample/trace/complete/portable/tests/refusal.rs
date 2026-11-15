// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn schema_unknown_duplicate_trailing_and_excessive_json_nesting_refuse() {
    let token = CancellationToken::new();
    let bytes = codec_transport::encode(&wire(&source(), &token), &control(&token)).unwrap();
    let text = String::from_utf8(bytes).unwrap();
    for changed in [
        text.replacen("{", "{\"unknown\":0,", 1),
        text.replacen("{", "{\"schema\":\"other\",", 1),
        format!("{text} false"),
        text.replace(wire::SCHEMA, "ay.unknown/v1"),
    ] {
        let decoded = codec_transport::decode::<wire::Wire>(changed.as_bytes(), &control(&token));
        assert!(
            decoded.is_none()
                || rebuild::prepare(&source(), &decoded.unwrap(), &control(&token)).is_none()
        );
    }
    let nested = format!("{}0{}", "[".repeat(17), "]".repeat(17));
    assert!(codec_transport::decode::<wire::Wire>(nested.as_bytes(), &control(&token)).is_none());
    let oversized = vec![b' '; 16 * 1024 * 1024 + 1];
    assert!(codec_transport::decode::<wire::Wire>(&oversized, &control(&token)).is_none());
}

#[test]
fn stale_source_reparsed_source_digest_and_tree_metadata_never_admit() {
    let token = CancellationToken::new();
    let problem = source();
    let mut data = wire(&problem, &token);
    let reparsed = QuantifiedChcProblem::parse_smtlib(&data.source).unwrap();
    assert!(rebuild::prepare(&reparsed, &data, &control(&token)).is_none());
    data.pinned_sha256 = "0".repeat(64);
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.steps[1].premises[0] = 1;
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.steps[0].clause_index = usize::MAX;
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.source.push(' ');
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
}

#[test]
fn original_manifest_controls_occurrence_name_order_and_sort() {
    let token = CancellationToken::new();
    let problem = source();
    for kind in 0..5 {
        let mut data = wire(&problem, &token);
        match kind {
            0 => data.steps[0].bindings[0].name.push('x'),
            1 => data.steps[1].bindings.swap(0, 1),
            2 => {
                data.steps[0].bindings.pop();
            }
            3 => data.steps[1].bindings[0].value = wire::Value::Functional { graph: 1 },
            _ => {
                data.graphs[0].element = wire::Element::Bool;
                data.graphs[0].nodes = vec![wire::Node::Finite {
                    default: wire::Scalar::Bool { value: false },
                    stores: vec![],
                }];
                data.graphs[0].root = 0;
            }
        }
        assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
    }
}

#[test]
fn unused_graphs_invalid_overwritten_stores_and_function_text_refuse() {
    let token = CancellationToken::new();
    let problem = source();
    let mut data = wire(&problem, &token);
    data.graphs.push(wire::Graph {
        element: wire::Element::Bool,
        root: 0,
        nodes: vec![wire::Node::Finite {
            default: wire::Scalar::Bool { value: false },
            stores: vec![],
        }],
    });
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.graphs[0].nodes[0] = wire::Node::Finite {
        default: wire::Scalar::BitVec {
            width: 8,
            value: "0".into(),
        },
        stores: vec![
            wire::Store {
                index: 0,
                value: wire::Scalar::BitVec {
                    width: 8,
                    value: "-1".into(),
                },
            },
            wire::Store {
                index: 0,
                value: wire::Scalar::BitVec {
                    width: 8,
                    value: "0".into(),
                },
            },
        ],
    };
    assert!(arrays::import(&data.graphs, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.functions = "(model (define-fun foreign () (_ BitVec 8) (_ bv0 8)))".into();
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
}

#[test]
fn aggregate_node_store_and_binding_limits_are_not_reset_per_graph() {
    let token = CancellationToken::new();
    let problem = source();
    let mut data = wire(&problem, &token);
    data.graphs[0].nodes = (0..=wire::MAX_NODES)
        .map(|_| wire::Node::Finite {
            default: wire::Scalar::BitVec {
                width: 8,
                value: "0".into(),
            },
            stores: vec![],
        })
        .collect();
    assert!(arrays::import(&data.graphs, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.graphs[0].nodes[0] = wire::Node::Finite {
        default: wire::Scalar::BitVec {
            width: 8,
            value: "0".into(),
        },
        stores: (0..=wire::MAX_STORES)
            .map(|_| wire::Store {
                index: 0,
                value: wire::Scalar::BitVec {
                    width: 8,
                    value: "0".into(),
                },
            })
            .collect(),
    };
    assert!(arrays::import(&data.graphs, &control(&token)).is_none());
    data = wire(&problem, &token);
    data.steps[0].bindings = (0..=MAX_BINDINGS)
        .map(|_| wire::Local {
            name: "x".into(),
            value: wire::Value::Literal {
                value: "false".into(),
            },
        })
        .collect();
    assert!(rebuild::prepare(&problem, &data, &control(&token)).is_none());
}

#[test]
fn cancellation_reset_and_exhausted_source_work_are_sticky_in_one_import() {
    let token = CancellationToken::new();
    let problem = source();
    let data = wire(&problem, &token);
    let owner = control(&token);
    token.cancel();
    assert!(owner.poll().is_none());
    token.reset();
    assert!(!token.is_cancelled());
    assert!(rebuild::prepare(&problem, &data, &owner).is_none());
    let exhausted = control(&token);
    assert!(exhausted.debit(usize::MAX, 0).is_none());
    assert!(arrays::import(&data.graphs, &exhausted).is_none());
    assert!(scalar::import(
        &wire::Scalar::Bool { value: true },
        wire::Element::Bool,
        &exhausted
    )
    .is_none());
}

#[test]
fn public_zero_cancelled_expired_and_ambient_minimum_caps_refuse_and_restore() {
    let token = CancellationToken::new();
    let problem = source();
    let bytes = codec_transport::encode(&wire(&problem, &token), &control(&token)).unwrap();
    assert!(problem
        .validate_complete_trace_artifact(&bytes, Duration::ZERO, Some(MEMORY), &token)
        .is_err());
    assert!(problem
        .validate_complete_trace_artifact(&bytes, WALL, Some(0), &token)
        .is_err());
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let _cap = SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(problem
        .validate_complete_trace_artifact(&bytes, WALL, Some(MEMORY), &token)
        .is_err());
    assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(end));
    assert_eq!(SmtContext::new().term_memory_budget, Some(0));
    token.cancel();
    assert!(problem
        .validate_complete_trace_artifact(&bytes, WALL, Some(MEMORY), &token)
        .is_err());
    drop(_cap);
    let _expired = ScopedSmtDeadline::install_until(Instant::now());
    token.reset();
    assert!(problem
        .validate_complete_trace_artifact(&bytes, WALL, Some(MEMORY), &token)
        .is_err());
}
