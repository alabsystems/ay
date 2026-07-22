// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Static lane definitions for the QF_LRA family split in #6570.
//!
//! `#6566` is scoped to registered relative slack refinements, so the
//! acceptance benchmarks for that packet must stay separate from the additive
//! `sc-*` lane. The actual benchmark measurements are done through the `ay`
//! CLI, but this test keeps the lane membership executable and reviewable in
//! the compile-safe `ay-dpll` test target.
//!
//! Part of #6570.

use std::collections::HashSet;

const REGISTERED_RELATIVE_TEMPLATE_CASES: &[&str] = &[
    "simple_startup_10nodes.bug.induct.smt2",
    "uart-23.induction.cvc.smt2",
    "rand_70_300_1155482584_11.lp.smt2",
    "tsp_rand_70_300_1155482584_7.lp.smt2",
];

const ADDITIVE_COMPOUND_CASES: &[&str] = &["sc-6.induction3.cvc.smt2", "sc-21.induction2.cvc.smt2"];

#[test]
fn qf_lra_family_lists_stay_disjoint_issue_6570() {
    let mut seen = HashSet::new();
    for name in REGISTERED_RELATIVE_TEMPLATE_CASES {
        assert!(
            !name.starts_with("sc-"),
            "relative-template lane must not include additive sc-* benchmark {name}"
        );
        assert!(seen.insert(*name), "duplicate family entry for {name}");
    }
    for name in ADDITIVE_COMPOUND_CASES {
        assert!(
            name.starts_with("sc-"),
            "additive lane should stay scoped to sc-* benchmarks, got {name}"
        );
        assert!(seen.insert(*name), "duplicate family entry for {name}");
    }
}
