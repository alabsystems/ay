// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-F: the memoised evaluators return exactly what the plain per-occurrence
//! walks return (random shared DAGs, both scope kinds, at and around the
//! recursion limit), and an exponentially shared DAG evaluates in
//! milliseconds.

use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_core::kani_compat::DetHashMap as FxHashMap;
use proptest::prelude::*;

use super::*;
use crate::expr::dag::test_support::{random_dag, Rng};
use crate::expr::{evaluate_expr, maybe_grow_expr_stack, ChcOp, ChcSort, ChcVar};
use crate::mbp::Mbp;
use crate::SmtValue;

/// A partial model over the generator's Int and Bool variables (Real variables
/// stay unassigned: the MBP evaluators answer `None` for them either way).
fn model(seed: u64) -> FxHashMap<String, SmtValue> {
    let mut rng = Rng(seed | 1);
    let mut model = FxHashMap::default();
    for i in 0..6 {
        if rng.below(4) != 0 {
            model.insert(format!("i{i}"), SmtValue::Int(rng.below(7) as i128 - 3));
        }
    }
    for b in 0..4 {
        if rng.below(4) != 0 {
            model.insert(format!("b{b}"), SmtValue::Bool(rng.below(2) == 0));
        }
    }
    model
}

/// Distinct inner nodes of `root`, root first.
fn distinct_inner_nodes(root: &ChcExpr) -> Vec<&ChcExpr> {
    let mut seen: ay_core::kani_compat::DetHashSet<*const ChcExpr> = Default::default();
    let mut out = Vec::new();
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        if !has_children(node) || !seen.insert(node as *const ChcExpr) {
            continue;
        }
        out.push(node);
        stack.extend(children(node).iter().map(AsRef::as_ref));
    }
    out
}

type Triple = (Option<bool>, Option<i128>, Option<SmtValue>);

fn evaluate_all(mbp: &Mbp, node: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Triple {
    (
        mbp.eval_bool(node, model),
        mbp.eval_arith(node, model),
        evaluate_expr(node, model),
    )
}

/// Run `f` `k` `maybe_grow_expr_stack` frames deeper than the caller.
fn at_depth<R>(k: usize, f: impl FnOnce() -> R) -> R {
    if k == 0 {
        f()
    } else {
        maybe_grow_expr_stack(|| at_depth(k - 1, f))
    }
}

/// `x_{k+1} = x_k + x_k` over Int: an evaluator visits BOTH children, so the
/// plain walk costs 2^k while the DAG has k + 1 nodes (an `ite` chain would
/// not do: evaluation follows one branch). Value 2^k under `x0 = 1`.
fn add_chain(k: usize) -> Arc<ChcExpr> {
    let mut x = Arc::new(ChcExpr::var(ChcVar::new("x0", ChcSort::Int)));
    for _ in 0..k {
        x = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&x), Arc::clone(&x)],
        ));
    }
    x
}

/// `b_{k+1} = b_k and b_k`: `And` evaluates every conjunct while they hold.
fn and_chain(k: usize) -> Arc<ChcExpr> {
    let mut b = Arc::new(ChcExpr::var(ChcVar::new("b0", ChcSort::Bool)));
    for _ in 0..k {
        b = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&b), Arc::clone(&b)],
        ));
    }
    b
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 48, ..ProptestConfig::default() })]

    /// Plain walk (memo disabled) = memoised walk = memoised walk under an
    /// explicit scope, at the root and at inner nodes, for the three
    /// evaluators. Tree sizes up to 2^17 make the plain reference feasible
    /// while exceeding the activation threshold.
    #[test]
    fn memoised_evaluators_equal_the_plain_walks(seed in any::<u64>(), n in 1usize..400) {
        let e = random_dag(seed, n, 1 << 17);
        let m = model(seed ^ 0x9e37_79b9);
        let mbp = Mbp::new();
        let nodes = distinct_inner_nodes(&e);
        for node in nodes.iter().take(24) {
            let plain = with_memo_disabled(|| evaluate_all(&mbp, node, &m));
            let memoised = evaluate_all(&mbp, node, &m);
            prop_assert_eq!(&plain, &memoised, "implicit scope differs at {:?}", node);
            let scoped = {
                let _scope = EvalScope::enter(std::iter::once(&e), &m);
                evaluate_all(&mbp, node, &m)
            };
            prop_assert_eq!(&plain, &scoped, "explicit scope differs at {:?}", node);
        }
        prop_assert!(!memo_active(), "no memo survives its scope");
    }
}

#[test]
fn exponential_dag_evaluates_in_milliseconds() {
    let x = add_chain(60);
    let b = and_chain(60);
    let expected = 1i128 << 60;
    let mut m = FxHashMap::default();
    m.insert("x0".to_string(), SmtValue::Int(1));
    m.insert("b0".to_string(), SmtValue::Bool(true));
    let mbp = Mbp::new();
    let start = Instant::now();
    assert_eq!(mbp.eval_arith(&x, &m), Some(expected));
    assert_eq!(evaluate_expr(&x, &m), Some(SmtValue::Int(expected)));
    assert_eq!(mbp.eval_bool(&b, &m), Some(true));
    assert_eq!(evaluate_expr(&b, &m), Some(SmtValue::Bool(true)));
    let le = ChcExpr::Op(
        ChcOp::Le,
        vec![Arc::clone(&x), Arc::new(ChcExpr::Int(expected))],
    );
    assert_eq!(mbp.eval_bool(&le, &m), Some(true));
    // Implicant extraction evaluates every disjunct of every shared level.
    let formula = ChcExpr::and(
        le.clone(),
        ChcExpr::or(
            ChcExpr::Op(ChcOp::Lt, vec![Arc::clone(&x), Arc::new(ChcExpr::Int(0))]),
            le.clone(),
        ),
    );
    let implicant = mbp.get_implicant(&formula, &m);
    assert!(!implicant.is_empty());
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "2^60-tree DAG took {:?}",
        start.elapsed()
    );
    assert!(!memo_active());
}

/// A shared block (tree 2^6, height 6) under a left-deep chain that reaches
/// the recursion limit: the memo activates (the chain's ~500 block copies
/// exceed the visit threshold) and must decline exactly the nodes whose plain
/// evaluation would be cut off, whatever depth the evaluation starts at.
#[test]
fn memo_matches_the_plain_walk_at_the_recursion_limit() {
    let block = add_chain(6);
    let mut m = FxHashMap::default();
    m.insert("x0".to_string(), SmtValue::Int(1));
    let mbp = Mbp::new();
    for chain_len in [
        MAX_EXPR_RECURSION_DEPTH - 30,
        MAX_EXPR_RECURSION_DEPTH - 16,
        MAX_EXPR_RECURSION_DEPTH - 3,
        MAX_EXPR_RECURSION_DEPTH + 3,
    ] {
        let mut e = Arc::clone(&block);
        for _ in 0..chain_len {
            e = Arc::new(ChcExpr::Op(ChcOp::Add, vec![e, Arc::clone(&block)]));
        }
        for start_depth in [0usize, 12, 29, 60] {
            let plain = at_depth(start_depth, || {
                with_memo_disabled(|| evaluate_all(&mbp, &e, &m))
            });
            let memoised = at_depth(start_depth, || evaluate_all(&mbp, &e, &m));
            assert_eq!(
                plain, memoised,
                "chain {chain_len} evaluated {start_depth} frames deep"
            );
            let scoped = at_depth(start_depth, || {
                let _scope = EvalScope::enter(std::iter::once(e.as_ref()), &m);
                evaluate_all(&mbp, &e, &m)
            });
            assert_eq!(
                plain, scoped,
                "explicit scope, chain {chain_len} at {start_depth}"
            );
        }
    }
}

#[test]
fn scopes_are_torn_down_and_nested_scopes_are_no_ops() {
    // 2^14 plain visits: past the activation threshold, cheap enough plain.
    let x = add_chain(14);
    let mut m = FxHashMap::default();
    m.insert("x0".to_string(), SmtValue::Int(1));
    let mbp = Mbp::new();
    {
        let _scope = EvalScope::enter(std::iter::once(x.as_ref()), &m);
        assert!(
            memo_active(),
            "a large shared root is indexed when the scope opens (before any evaluation)"
        );
        assert_eq!(mbp.eval_arith(&x, &m), Some(1 << 14));
        assert!(memo_active(), "the chain exceeds the activation threshold");
        {
            let _inner = EvalScope::enter(std::iter::once(x.as_ref()), &m);
            assert!(memo_active(), "a nested scope leaves the open one serving");
        }
        assert!(
            memo_active(),
            "a nested scope's end does not tear the open one down"
        );
    }
    assert!(!memo_active(), "an explicit scope dies with its guard");
    assert_eq!(mbp.eval_arith(&x, &m), Some(1 << 14));
    assert!(
        !memo_active(),
        "an outermost call's scope dies with the call"
    );
}

/// A balanced tree of fresh nodes (no sharing, 2^13 inner nodes): large, but
/// an index would not save anything, so the pre-walk leaves it plain.
fn unshared_tree(depth: usize, counter: &mut usize) -> Arc<ChcExpr> {
    if depth == 0 {
        *counter += 1;
        return Arc::new(ChcExpr::var(ChcVar::new(
            format!("u{counter}"),
            ChcSort::Int,
        )));
    }
    Arc::new(ChcExpr::Op(
        ChcOp::Add,
        vec![
            unshared_tree(depth - 1, counter),
            unshared_tree(depth - 1, counter),
        ],
    ))
}

#[test]
fn large_unshared_trees_are_not_indexed_but_large_shared_dags_are() {
    let m = FxHashMap::default();
    let mut counter = 0;
    let tree = unshared_tree(13, &mut counter);
    {
        let _scope = EvalScope::enter(std::iter::once(tree.as_ref()), &m);
        assert!(!memo_active(), "no sharing: nothing to memoise");
    }
    let shared = add_chain(13);
    {
        let _scope = EvalScope::enter(std::iter::once(shared.as_ref()), &m);
        assert!(memo_active(), "2^13-tree over 14 distinct nodes is indexed");
    }
    // The outermost-call scope makes the same decision.
    let mbp = Mbp::new();
    assert_eq!(mbp.eval_arith(&tree, &m), None, "unassigned variables");
    let small = ChcExpr::add(
        ChcExpr::var(ChcVar::new("a", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    assert_eq!(mbp.eval_arith(&small, &m), None);
    assert!(!memo_active());
}
