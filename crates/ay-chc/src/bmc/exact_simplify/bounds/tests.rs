// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::{ChcProblem, ChcSort, ChcVar};

fn variable(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn chain() -> Vec<ChcExpr> {
    vec![
        ChcExpr::eq(variable("x"), variable("y")),
        ChcExpr::eq(variable("y"), variable("z")),
        ChcExpr::ge(variable("z"), ChcExpr::Int(2)),
        ChcExpr::le(variable("z"), ChcExpr::Int(4)),
    ]
}

#[test]
fn equality_chain_propagates_both_endpoints_without_losing_the_source_domain() {
    let mut env = FxHashMap::default();
    let mut live = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut live).unwrap();
    assert_eq!(collect_bounds(&chain(), &mut env, &mut names), Some(true));
    for name in ["x", "y", "z"] {
        assert_eq!(
            env[name],
            IntInterval {
                lower: Some(2),
                upper: Some(4),
            }
        );
    }
    assert_eq!(env.len(), 3);
}

#[test]
fn infeasible_interval_round_never_commits_partial_bounds() {
    let mut source = chain();
    source.push(ChcExpr::ge(variable("x"), ChcExpr::Int(5)));
    let original = FxHashMap::from_iter([("seed".to_owned(), IntInterval::exact(7))]);
    let mut env = original.clone();
    let mut live = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut live).unwrap();
    assert_eq!(collect_bounds(&source, &mut env, &mut names), Some(false));
    assert_eq!(env, original);
    assert!(!names.stopped(), "infeasibility is not a resource refusal");
}
