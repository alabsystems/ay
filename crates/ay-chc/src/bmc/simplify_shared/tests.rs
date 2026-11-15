// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

mod oracle;
use oracle::Frozen;

fn variable(name: &str, width: u32) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(width)))
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn record_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Record".into(),
        constructors: crate::ChcDtConstructors::new(vec![
            ChcDtConstructor {
                name: "mkRecord".into(),
                selectors: vec![ChcDtSelector {
                    name: "field".into(),
                    sort: ChcSort::BitVec(8),
                }],
            },
            ChcDtConstructor {
                name: "emptyRecord".into(),
                selectors: vec![],
            },
        ]),
    }
}

fn record(value: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp("mkRecord".into(), record_sort(), vec![Arc::new(value)])
}

fn field(value: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp("field".into(), ChcSort::BitVec(8), vec![Arc::new(value)])
}

fn children(expr: &ChcExpr) -> &[Arc<ChcExpr>] {
    match expr {
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            args
        }
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        _ => &[],
    }
}

fn distinct_nodes(expr: &ChcExpr) -> usize {
    let mut seen = FxHashSet::default();
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        if seen.insert(std::ptr::from_ref(node)) {
            pending.extend(children(node).iter().map(Arc::as_ref));
        }
    }
    seen.len()
}

fn doubled(
    mut leaf: Arc<ChcExpr>,
    depth: usize,
    make: impl Fn(Vec<Arc<ChcExpr>>) -> ChcExpr,
) -> ChcExpr {
    for _ in 0..depth {
        leaf = Arc::new(make(vec![Arc::clone(&leaf), leaf]));
    }
    Arc::unwrap_or_clone(leaf)
}

fn assert_shared_chain(expr: &ChcExpr, depth: usize, expected_leaf: &ChcExpr) {
    let mut node = expr;
    for _ in 0..depth {
        let args = children(node);
        assert_eq!(args.len(), 2);
        assert!(Arc::ptr_eq(&args[0], &args[1]));
        node = args[0].as_ref();
    }
    assert_eq!(node, expected_leaf);
    assert_eq!(distinct_nodes(expr), depth + 1);
}

#[test]
fn datatype_walk_preserves_bv_only_shared_dag() {
    // Never call the tree-expanding frozen oracle on this deep input.
    let depth = 48;
    let leaf = variable("x", 8);
    let input = doubled(Arc::new(leaf.clone()), depth, |args| {
        ChcExpr::Op(ChcOp::BvAdd, args)
    });
    assert_eq!(distinct_nodes(&input), depth + 1);
    let output = super::super::BmcSolver::simplify_dt_selector_apps(input);
    assert_shared_chain(&output, depth, &leaf);
}

#[test]
fn bitvector_walk_preserves_shared_opaque_and_operator_dags() {
    let leaf = variable("x", 8);
    let opaque = doubled(Arc::new(leaf.clone()), 48, |args| {
        ChcExpr::FuncApp("opaque".into(), ChcSort::BitVec(8), args)
    });
    let output = super::super::BmcSolver::simplify_bv_identities(opaque);
    assert_shared_chain(&output, 48, &leaf);

    // This also exercises the retained per-operator constant-simplifier calls.
    // Node count, not elapsed time, is the assertion.
    let input = doubled(Arc::new(leaf.clone()), 12, |args| {
        ChcExpr::Op(ChcOp::BvAdd, args)
    });
    let output = bitvector_identities(input);
    assert_shared_chain(&output, 12, &leaf);
}

#[test]
fn changed_shared_children_are_reused_across_container_variants() {
    let selected = Arc::new(field(record(ChcExpr::BitVec(7, 8))));
    let array = Arc::new(ChcExpr::ConstArray(
        ChcSort::BitVec(4),
        Arc::clone(&selected),
    ));
    let pred = Arc::new(ChcExpr::PredicateApp(
        "P".into(),
        PredicateId::new(7),
        vec![Arc::clone(&array), Arc::clone(&array)],
    ));
    let input = ChcExpr::Op(ChcOp::And, vec![Arc::clone(&pred), pred]);
    let expected = Frozen::simplify_dt_selector_apps(input.clone());
    let output = datatype_selectors(input);
    assert_eq!(output, expected);
    let predicates = children(&output);
    assert!(Arc::ptr_eq(&predicates[0], &predicates[1]));
    let arrays = children(&predicates[0]);
    assert!(Arc::ptr_eq(&arrays[0], &arrays[1]));
    assert_eq!(children(&arrays[0])[0].as_ref(), &ChcExpr::BitVec(7, 8));
    assert_eq!(distinct_nodes(&output), 4);

    let reducible = Arc::new(op(
        ChcOp::BvAdd,
        vec![variable("x", 8), ChcExpr::BitVec(0, 8)],
    ));
    let input = doubled(reducible, 32, |args| {
        ChcExpr::FuncApp("opaque".into(), ChcSort::BitVec(8), args)
    });
    assert_shared_chain(&bitvector_identities(input), 32, &variable("x", 8));
}

#[test]
fn bitvector_rules_match_frozen_shallow_oracle() {
    for width in [1, 8, 64, 128] {
        let leaves = [
            variable("x", width),
            variable("y", width),
            ChcExpr::BitVec(0, width),
            ChcExpr::BitVec(1, width),
            ChcExpr::BitVec(3, width),
        ];
        for operation in [
            ChcOp::BvAdd,
            ChcOp::BvSub,
            ChcOp::BvMul,
            ChcOp::BvUDiv,
            ChcOp::BvSDiv,
        ] {
            for lhs in &leaves {
                for rhs in &leaves {
                    let input = op(operation, vec![lhs.clone(), rhs.clone()]);
                    assert_eq!(
                        bitvector_identities(input.clone()),
                        Frozen::simplify_bv_identities(input)
                    );
                }
            }
        }
        for x in &leaves {
            for c in &leaves {
                for sum in [
                    op(ChcOp::BvAdd, vec![x.clone(), c.clone()]),
                    op(ChcOp::BvAdd, vec![c.clone(), x.clone()]),
                ] {
                    let input = op(ChcOp::BvSub, vec![sum, x.clone()]);
                    assert_eq!(
                        bitvector_identities(input.clone()),
                        Frozen::simplify_bv_identities(input)
                    );
                }
            }
        }
    }
    assert_eq!(
        bitvector_identities(op(ChcOp::BvSub, vec![variable("x", 8), variable("x", 8)])),
        ChcExpr::BitVec(0, 8)
    );
    assert_eq!(
        bitvector_identities(op(
            ChcOp::BvMul,
            vec![ChcExpr::BitVec(1, 8), variable("x", 8)]
        )),
        variable("x", 8)
    );
}

#[test]
fn extract_reentry_matches_frozen_oracle_with_fresh_roots() {
    for serial in 0..8 {
        // Selecting inside one half creates a generated extract and re-enters
        // the helper; nested concats make that happen more than once.
        let x = variable(&format!("x{serial}"), 4);
        let half = op(ChcOp::BvConcat, vec![x.clone(), variable("y", 4)]);
        let concat = op(ChcOp::BvConcat, vec![half.clone(), half]);
        for hi in 0..18 {
            for lo in 0..18 {
                let input = op(ChcOp::BvExtract(hi, lo), vec![concat.clone()]);
                assert_eq!(
                    bitvector_identities(input.clone()),
                    Frozen::simplify_bv_identities(input)
                );
            }
        }
        assert_eq!(
            bitvector_identities(op(ChcOp::BvExtract(15, 12), vec![concat])),
            x
        );
    }
}

#[test]
fn datatype_rules_match_frozen_oracle() {
    let value = variable("x", 8);
    let nested = field(record(field(record(value.clone()))));
    assert_eq!(datatype_selectors(nested.clone()), value);
    let missing = ChcExpr::FuncApp("mkRecord".into(), record_sort(), vec![]);
    let wrong_ctor = ChcExpr::FuncApp("emptyRecord".into(), record_sort(), vec![]);
    let opaque = ChcExpr::Var(ChcVar::new("r", record_sort()));
    let inputs = [
        nested,
        field(missing),
        field(wrong_ctor),
        field(opaque),
        ChcExpr::FuncApp(
            "other".into(),
            ChcSort::BitVec(8),
            vec![Arc::new(record(value.clone()))],
        ),
        ChcExpr::FuncApp("field".into(), ChcSort::BitVec(8), vec![]),
        ChcExpr::FuncApp(
            "field".into(),
            ChcSort::BitVec(8),
            vec![
                Arc::new(record(value.clone())),
                Arc::new(record(value.clone())),
            ],
        ),
        // Preserve even the old helper's name-only matching on malformed sort
        // metadata. This traversal patch does not change selector admission.
        ChcExpr::FuncApp("field".into(), ChcSort::Bool, vec![Arc::new(record(value))]),
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(field(record(ChcExpr::BitVec(9, 8))))),
    ];
    for input in inputs {
        assert_eq!(
            datatype_selectors(input.clone()),
            Frozen::simplify_dt_selector_apps(input)
        );
    }
}

#[test]
fn distinct_equal_inputs_and_separate_roots_do_not_share_memos() {
    for pass in [Pass::DatatypeSelectors, Pass::BitVectorIdentities] {
        let first = Arc::new(variable("x", 8));
        let second = Arc::new(variable("x", 8));
        assert!(!Arc::ptr_eq(&first, &second));
        let root = Arc::new(ChcExpr::FuncApp(
            "opaque".into(),
            ChcSort::BitVec(8),
            vec![Arc::clone(&first), first, second],
        ));
        let mut memo = Memo::default();
        let output = rewrite_arg(&root, pass, &mut memo);
        assert_eq!(memo.len(), 3);
        assert_eq!(memo.len(), distinct_nodes(&root));
        let args = children(&output);
        assert!(Arc::ptr_eq(&args[0], &args[1]));
        assert!(!Arc::ptr_eq(&args[0], &args[2]));
        drop(memo);
        for name in ["new_x", "new_y", "new_z"] {
            let new = ChcExpr::FuncApp(
                "opaque".into(),
                ChcSort::BitVec(8),
                vec![Arc::new(variable(name, 8))],
            );
            let result = rewrite(new, pass);
            assert_eq!(children(&result)[0].as_ref(), &variable(name, 8));
            assert!(!Arc::ptr_eq(&args[0], &children(&result)[0]));
        }
    }
}

#[test]
fn shared_and_duplicated_shallow_graphs_match_the_frozen_rules() {
    for leaf in [
        variable("x", 8),
        field(record(variable("y", 8))),
        op(ChcOp::BvAdd, vec![variable("z", 8), ChcExpr::BitVec(0, 8)]),
    ] {
        for operation in [ChcOp::BvAdd, ChcOp::BvSub, ChcOp::BvMul, ChcOp::Eq] {
            let child = Arc::new(leaf.clone());
            let shared = ChcExpr::Op(operation, vec![Arc::clone(&child), child]);
            let copied = op(operation, vec![leaf.clone(), leaf.clone()]);
            assert_eq!(
                datatype_selectors(shared.clone()),
                Frozen::simplify_dt_selector_apps(copied.clone())
            );
            assert_eq!(
                bitvector_identities(shared),
                Frozen::simplify_bv_identities(copied)
            );
        }
    }
}
