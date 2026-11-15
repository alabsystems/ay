// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn group() -> UniversalPremise {
    UniversalPremise::with_binders(
        (0..8)
            .map(|i| ChcVar::new(format!("index{i}"), ChcSort::BitVec(64)))
            .collect(),
        ChcExpr::Bool(true),
    )
    .unwrap()
}

#[test]
fn every_declared_binder_debits_the_shared_source_name_and_work_allowance() {
    let premise = group();
    let registry = Registry::new(&ChcProblem::new()).unwrap();
    let functions = Functions::default();
    let bytes: usize = premise.binders().map(|b| 256 + b.name.len() * 2).sum();
    let mut exact = Budget {
        nodes: MAX_NODES - 8,
        bytes: MAX_BYTES - bytes,
    };
    preflight(&premise, &registry, &functions, &mut exact).unwrap();
    assert_eq!((exact.nodes, exact.bytes), (MAX_NODES, MAX_BYTES));
    let mut short = Budget {
        nodes: 0,
        bytes: MAX_BYTES - bytes + 1,
    };
    assert!(preflight(&premise, &registry, &functions, &mut short).is_err());
    let mut short_work = Budget {
        nodes: MAX_NODES - 7,
        bytes: 0,
    };
    assert!(preflight(&premise, &registry, &functions, &mut short_work).is_err());
    let mut fresh = Budget::default();
    preflight(&premise, &registry, &functions, &mut fresh).unwrap();
    assert_eq!((fresh.nodes, fresh.bytes), (8, bytes));
}
