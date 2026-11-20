// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification-lane `let`-shared executor scripts (F0g): a query wider than
//! the old admission cap is `let`-printed on the Verification lane as on the
//! Search lane, and a DAG-printed script decides exactly what its
//! tree-printed twin decides.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::logic_detection::collect_dt_declarations_for_expr_sized;
use super::*;
use crate::{ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

fn rvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

/// `2^levels · e` as a DAG of `levels + 1` nodes.
fn doubled(e: ChcExpr, levels: u32) -> ChcExpr {
    let mut node = Arc::new(e);
    for _ in 0..levels {
        node = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&node), Arc::clone(&node)],
        ));
    }
    Arc::try_unwrap(node).unwrap_or_else(|shared| (*shared).clone())
}

/// `(s < 0 ∨ s > 2^L·hi) ∧ 0 ≤ r ≤ cap`, `s = 2^L·r` shared: UNSAT iff
/// `cap ≤ hi`.
fn wide_query(hi: i64, cap: i64) -> ChcExpr {
    const LEVELS: u32 = 16;
    let s = doubled(rvar("r"), LEVELS);
    let scale = 1i64 << LEVELS;
    ChcExpr::and_all([
        ChcExpr::or(
            ChcExpr::lt(s.clone(), ChcExpr::Real(0, 1)),
            ChcExpr::gt(s, ChcExpr::Real(scale * hi, 1)),
        ),
        ChcExpr::le(ChcExpr::Real(0, 1), rvar("r")),
        ChcExpr::le(rvar("r"), ChcExpr::Real(cap, 1)),
    ])
}

/// Levels of [`ite_chain_query`] in the tests: its tree is past the cap.
const LEVELS: u32 = 15;
const LEVELS_I64: i64 = 15;

/// An IMC-reached-set-shaped query: a shared ITE "majority vote" term used
/// at every level of a chain, under a Bool flag. `c_{k+1} = ite(b, c_k + m,
/// c_k)` with `m = ite(x = y, x, y)`; the chain's tree is exponential in
/// `levels` (each level mentions `c_k` twice), its DAG linear. With
/// `0 ≤ x, y ≤ 1` and `c_0 = 0`, `c_levels ≤ levels` always, so `c_levels >
/// bound` is SAT iff `bound < levels` (b = true, x = y = 1).
fn ite_chain_query(levels: u32, bound: i64) -> ChcExpr {
    let x = rvar("x");
    let y = rvar("y");
    let m = Arc::new(ChcExpr::ite(
        ChcExpr::eq(x.clone(), y.clone()),
        x.clone(),
        y.clone(),
    ));
    let mut c = Arc::new(ChcExpr::Real(0, 1));
    for _ in 0..levels {
        let sum = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&c), Arc::clone(&m)],
        ));
        c = Arc::new(ChcExpr::Op(
            ChcOp::Ite,
            vec![Arc::new(bvar("b")), sum, Arc::clone(&c)],
        ));
    }
    let c = Arc::try_unwrap(c).unwrap_or_else(|shared| (*shared).clone());
    ChcExpr::and_all([
        ChcExpr::le(ChcExpr::Real(0, 1), x.clone()),
        ChcExpr::le(x, ChcExpr::Real(1, 1)),
        ChcExpr::le(ChcExpr::Real(0, 1), y.clone()),
        ChcExpr::le(y, ChcExpr::Real(1, 1)),
        ChcExpr::gt(c, ChcExpr::Real(bound, 1)),
    ])
}

fn tree_nodes(expr: &ChcExpr) -> usize {
    collect_dt_declarations_for_expr_sized(&[], expr)
        .unwrap()
        .1
        .tree_nodes
}

/// A complete executor script for `expr` with the printer its admitted size
/// selects (`forced_tree`: the tree printer whatever the size).
fn script(expr: &ChcExpr, forced_tree: bool) -> String {
    let mut smt = String::from("(set-logic QF_LRA)\n");
    for var in expr.vars() {
        writeln_decl(&mut smt, &var);
    }
    let conjuncts = expr.conjuncts();
    let size = if forced_tree { 0 } else { tree_nodes(expr) };
    write_executor_asserts(&mut smt, &conjuncts, size);
    smt.push_str("(check-sat)\n");
    smt
}

fn writeln_decl(smt: &mut String, var: &ChcVar) {
    smt.push_str(&format!(
        "(declare-const {} {})\n",
        quote_symbol(&var.name),
        sort_to_smtlib(&var.sort)
    ));
}

fn verdict(script: &str) -> String {
    let commands = ay_frontend::parse(script).unwrap();
    let outputs = execute_commands_via_executor(&commands, ExecutorQueryRole::Published).unwrap();
    outputs.first().cloned().unwrap_or_default()
}

#[test]
fn verification_lane_prints_shared_queries_with_lets() {
    for query in [wide_query(10, 10), ite_chain_query(LEVELS, 13)] {
        let admitted = tree_nodes(&query);
        assert!(
            admitted > logic_detection::MAX_DT_EXPR_NODES,
            "{admitted} tree nodes"
        );
        let dag = script(&query, false);
        let tree = script(&query, true);
        assert!(
            dag.contains("(let "),
            "a wide shared query must be let-printed: {admitted} tree nodes"
        );
        assert!(!tree.contains("(let "));
        assert!(
            dag.len() * 10 < tree.len(),
            "DAG script {} bytes vs tree {} bytes",
            dag.len(),
            tree.len()
        );
    }
    // A small query is printed byte for byte as before.
    let small = ChcExpr::and(
        ChcExpr::le(ChcExpr::Real(0, 1), rvar("r")),
        ChcExpr::lt(rvar("r"), ChcExpr::Real(1, 1)),
    );
    assert_eq!(script(&small, false), script(&small, true));
}

#[test]
fn verification_lane_dag_scripts_decide_like_tree_scripts() {
    let cases = [
        (wide_query(10, 10), "unsat"),
        (wide_query(10, 11), "sat"),
        (ite_chain_query(LEVELS, LEVELS_I64), "unsat"),
        (ite_chain_query(LEVELS, LEVELS_I64 - 1), "sat"),
    ];
    for (query, expected) in cases {
        let dag = verdict(&script(&query, false));
        let tree = verdict(&script(&query, true));
        assert_eq!(dag, expected, "DAG-printed Verification script");
        assert_eq!(tree, expected, "tree-printed Verification script");
    }
}

#[test]
fn verification_lane_context_decides_shared_queries_and_validates_models() {
    let model_satisfies = |query: &ChcExpr, model: &FxHashMap<String, SmtValue>| {
        matches!(
            crate::expr::evaluate_expr(query, model),
            Some(SmtValue::Bool(true))
        )
    };
    for (query, sat) in [
        (wide_query(10, 10), false),
        (wide_query(10, 11), true),
        (ite_chain_query(LEVELS, LEVELS_I64), false),
        (ite_chain_query(LEVELS, LEVELS_I64 - 1), true),
    ] {
        let ctx = SmtContext::new();
        assert_eq!(ctx.lane(), SmtLane::Verification);
        let result = ctx.check_sat_via_executor(
            &query,
            &FxHashMap::default(),
            std::time::Duration::from_secs(20),
        );
        match (sat, result) {
            (true, SmtResult::Sat(model)) => assert!(model_satisfies(&query, &model)),
            (false, SmtResult::Unsat) => {}
            (expected_sat, other) => panic!("expected sat={expected_sat}, got {other:?}"),
        }
    }
}

#[test]
fn verification_lane_labels_uf_free_real_queries_qf_lra() {
    assert_eq!(
        executor_logic(SmtLane::Verification, "QF_UFLRA", true),
        "QF_LRA"
    );
    // A query with a UF application keeps the UF label.
    assert_eq!(
        executor_logic(SmtLane::Verification, "QF_UFLRA", false),
        "QF_UFLRA"
    );
    // The Search lane keeps `detect_logic`'s label.
    assert_eq!(
        executor_logic(SmtLane::Search, "QF_UFLRA", true),
        "QF_UFLRA"
    );
    // Other labels are untouched.
    for detected in ["QF_AUFLIA", "QF_AUFLIRA", "QF_NRA", "ALL"] {
        assert_eq!(
            executor_logic(SmtLane::Verification, detected, true),
            detected
        );
    }
}

#[test]
fn an_uninterpreted_sort_constant_keeps_the_uf_label() {
    let reals = [ChcVar::new("r", ChcSort::Real)];
    assert!(declares_no_uninterpreted_symbol(true, &reals));
    assert!(!declares_no_uninterpreted_symbol(false, &reals));
    let with_sort = [
        ChcVar::new("r", ChcSort::Real),
        ChcVar::new("u", ChcSort::Uninterpreted("U".to_string())),
    ];
    assert!(!declares_no_uninterpreted_symbol(true, &with_sort));
}

#[test]
fn verification_lane_decides_real_queries_with_and_without_uf() {
    let r = rvar("r");
    // UF-free, labelled QF_LRA: 0 <= r < 1 ∧ r > 1 is UNSAT, without the
    // last conjunct SAT.
    let bounded = ChcExpr::and(
        ChcExpr::le(ChcExpr::Real(0, 1), r.clone()),
        ChcExpr::lt(r.clone(), ChcExpr::Real(1, 1)),
    );
    let f_r = ChcExpr::FuncApp("f".to_string(), ChcSort::Real, vec![r.clone().into()]);
    let cases = [
        (
            ChcExpr::and(bounded.clone(), ChcExpr::gt(r.clone(), ChcExpr::Real(1, 1))),
            false,
        ),
        (bounded.clone(), true),
        // With a UF application (labelled QF_UFLRA): f(r) = r ∧ f(r) > 1 ∧ r < 1.
        (
            ChcExpr::and_all([
                ChcExpr::eq(f_r.clone(), r.clone()),
                ChcExpr::gt(f_r, ChcExpr::Real(1, 1)),
                ChcExpr::lt(r.clone(), ChcExpr::Real(1, 1)),
            ]),
            false,
        ),
    ];
    for (query, sat) in cases {
        let ctx = SmtContext::new();
        let result = ctx.check_sat_via_executor(
            &query,
            &FxHashMap::default(),
            std::time::Duration::from_secs(20),
        );
        match (sat, result) {
            (true, SmtResult::Sat(_)) | (false, SmtResult::Unsat) => {}
            (expected_sat, other) => panic!("{query}: expected sat={expected_sat}, got {other:?}"),
        }
    }
}
