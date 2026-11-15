// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-F: the DAG-linear candidate-term walk gives `find_equivalent_term` the
//! same answer as the per-occurrence walk it replaces, and stays linear on an
//! exponentially shared formula.

use std::time::{Duration, Instant};

use proptest::prelude::*;

use super::*;
use crate::expr::dag::test_support::{random_dag, Rng};

/// The per-occurrence walk `collect_candidate_terms` used before WP-F, kept
/// verbatim as the reference.
fn reference_candidates(expr: &ChcExpr, terms: &mut Vec<ChcExpr>) {
    crate::expr::maybe_grow_expr_stack(|| {
        if crate::expr::ExprDepthGuard::check().is_none() {
            return;
        }
        match expr {
            ChcExpr::ArrayLambda(lambda) => {
                for value in lambda.captures() {
                    reference_candidates(value, terms);
                }
            }
            ChcExpr::Int(_) => {}
            ChcExpr::Var(_) => terms.push(expr.clone()),
            ChcExpr::Op(op, args) => {
                if matches!(
                    op,
                    ChcOp::Eq | ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Ne
                ) {
                    for arg in args {
                        terms.push((**arg).clone());
                    }
                }
                if matches!(op, ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Neg) {
                    terms.push(expr.clone());
                }
                for arg in args {
                    reference_candidates(arg, terms);
                }
            }
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, _) => {}
            ChcExpr::PredicateApp(_, _, args) => {
                for arg in args {
                    reference_candidates(arg, terms);
                }
            }
            ChcExpr::FuncApp(_, _, args) => {
                terms.push(expr.clone());
                for arg in args {
                    reference_candidates(arg, terms);
                }
            }
            ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(_, _) => {}
        }
    })
}

fn int_model(seed: u64) -> FxHashMap<String, SmtValue> {
    let mut rng = Rng(seed | 1);
    let mut model = FxHashMap::default();
    for i in 0..6 {
        model.insert(format!("i{i}"), SmtValue::Int(rng.below(5) as i128 - 2));
    }
    for b in 0..4 {
        model.insert(format!("b{b}"), SmtValue::Bool(rng.below(2) == 0));
    }
    model
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    /// For every variable, the first equivalent term found in the DAG-linear
    /// candidate list is the one found in the per-occurrence list; the
    /// DAG-linear list is never longer.
    #[test]
    fn find_equivalent_term_is_unchanged_by_the_dag_walk(seed in any::<u64>(), n in 1usize..300) {
        // Tree sizes past the plain-visit budget, small enough for the reference.
        let e = random_dag(seed, n, 1 << 13);
        let model = int_model(seed ^ 0x5eed);
        let mut reference = Vec::new();
        reference_candidates(&e, &mut reference);
        let dag = Mbp::collect_candidate_terms(&e);
        prop_assert!(dag.len() <= reference.len());
        let mbp = Mbp::new();
        for i in 0..6 {
            let var = ChcVar::new(format!("i{i}"), ChcSort::Int);
            prop_assert_eq!(
                mbp.find_equivalent_term(&var, &dag, &model),
                mbp.find_equivalent_term(&var, &reference, &model),
                "variable i{}", i
            );
        }
    }
}

#[test]
fn candidate_terms_of_an_exponential_dag_stay_linear() {
    // x_{k+1} = ite(c_k, x_k + 1, x_k): tree ~2^60, DAG ~240 nodes.
    let mut x = Arc::new(ChcExpr::var(ChcVar::new("x0", ChcSort::Int)));
    for i in 0..60 {
        let plus = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&x), Arc::new(ChcExpr::Int(1))],
        ));
        x = Arc::new(ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new(format!("c{i}"), ChcSort::Bool))),
                plus,
                x,
            ],
        ));
    }
    let y = ChcVar::new("y", ChcSort::Int);
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(y.clone()), (*x).clone()),
        ChcExpr::Op(ChcOp::Le, vec![Arc::clone(&x), Arc::new(ChcExpr::Int(7))]),
    );
    let start = Instant::now();
    let terms = Mbp::collect_candidate_terms(&formula);
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "candidate walk took {:?}",
        start.elapsed()
    );
    // Plain budget (4096 child visits, at most one push each here) plus one
    // entry per distinct node.
    assert!(terms.len() < 10_000, "{} candidate terms", terms.len());
    // MBQI still finds the equivalent term for `y` under a model that makes
    // every guard false (x_60 = x0).
    let mut model = FxHashMap::default();
    model.insert("x0".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(3));
    for i in 0..60 {
        model.insert(format!("c{i}"), SmtValue::Bool(false));
    }
    let found = Mbp::new().find_equivalent_term(&y, &terms, &model);
    assert!(
        found.is_some(),
        "an equivalent term for y exists in the formula"
    );
    assert!(
        start.elapsed() < Duration::from_secs(10),
        "MBQI search took {:?}",
        start.elapsed()
    );
}
