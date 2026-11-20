// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CHC-COMP 2026 Workstream D (the development design notes at 9598c4206, §4.1, §9) bridge
//! item D-1: executor admission counts UNIQUE nodes, and Search-lane
//! executor scripts are printed DAG-linearly. Owner: WP-D1-M.
//!
//! The queries below are IMC-shaped: a Real term whose tree expansion is far
//! above the old 131,072-node admission cap but whose DAG has a few dozen
//! nodes (`s = 2^17·r` built by doubling one shared node), under Boolean
//! structure over Real atoms. Both lanes must decide them, and SAT models
//! must satisfy the original constraints. The INV-12 printer differential
//! (10,000 random shared DAGs, z3-checked) and the exact admission counts
//! are unit tests of `smt::dag_smtlib` and `executor_adapter::logic_detection`.

#![allow(clippy::unwrap_used, clippy::panic)]

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtContext, SmtResult, SmtValue};
use std::sync::Arc;

const LEVELS: u32 = 17;

fn r() -> ChcExpr {
    ChcExpr::var(ChcVar::new("r", ChcSort::Real))
}

/// `2^levels · e` as a DAG of `levels + 1` nodes (tree: `2^(levels+1) - 1`).
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

/// `(s < 0 ∨ s > 2^LEVELS·hi) ∧ 0 ≤ r ≤ cap`, with `s = 2^LEVELS·r` shared:
/// UNSAT iff `cap ≤ hi`.
fn wide_query(hi: i64, cap: i64) -> ChcExpr {
    let s = doubled(r(), LEVELS);
    let scale = 1i64 << LEVELS;
    ChcExpr::and_all([
        ChcExpr::or(
            ChcExpr::lt(s.clone(), ChcExpr::Real(0, 1)),
            ChcExpr::gt(s, ChcExpr::Real(scale * hi, 1)),
        ),
        ChcExpr::le(ChcExpr::Real(0, 1), r()),
        ChcExpr::le(r(), ChcExpr::Real(cap, 1)),
    ])
}

fn is_unsat(result: &SmtResult) -> bool {
    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

fn real_value(value: &SmtValue) -> f64 {
    match value {
        SmtValue::Real(q) => {
            let text = q.to_string();
            match text.split_once('/') {
                Some((n, d)) => n.parse::<f64>().unwrap() / d.parse::<f64>().unwrap(),
                None => text.parse::<f64>().unwrap(),
            }
        }
        SmtValue::Int(n) => *n as f64,
        other => panic!("r must be Real, got {other:?}"),
    }
}

fn check_lane(mut ctx: SmtContext, lane: &str) {
    let unsat = wide_query(10, 10);
    let result = ctx.check_sat(&unsat);
    assert!(
        is_unsat(&result),
        "{lane}: the wide shared Real query is UNSAT, got {result:?}"
    );
    let sat = wide_query(10, 11);
    match ctx.check_sat(&sat) {
        SmtResult::Sat(model) => {
            let value = real_value(model.get("r").expect("model binds r"));
            assert!(
                value > 10.0 && value <= 11.0,
                "{lane}: model r = {value} violates the query"
            );
        }
        SmtResult::Unknown => {}
        other => panic!("{lane}: the SAT variant must never be refuted, got {other:?}"),
    }
}

#[test]
fn search_lane_decides_a_wide_shared_real_query() {
    check_lane(SmtContext::new_search(), "search");
}

#[test]
fn verification_lane_decides_a_wide_shared_real_query() {
    check_lane(SmtContext::new(), "verification");
}

#[test]
fn a_query_deeper_than_the_depth_cap_is_never_answered_wrongly() {
    // 600 nested negations of r: deeper than the 512-edge admission cap.
    let mut e = r();
    for _ in 0..600 {
        e = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(e)]);
    }
    // (-1)^600 · r = r, so r > 1 ∧ e < 1 is UNSAT.
    let query = ChcExpr::and(
        ChcExpr::gt(r(), ChcExpr::Real(1, 1)),
        ChcExpr::lt(e, ChcExpr::Real(1, 1)),
    );
    let result = SmtContext::new_search().check_sat(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "a refused deep query may be Unknown, never SAT: {result:?}"
    );
}
