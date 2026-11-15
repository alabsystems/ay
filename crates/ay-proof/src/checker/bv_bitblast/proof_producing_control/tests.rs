// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod boundaries;
mod definitions;
mod lowering;
mod readings;
mod reserved;
mod store_chain_retry;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn raw_identity() -> (TermStore, TermId, BvExpr) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("controlled-fallback", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    // A nonlinear source word exercises ordinary lowering even when affine
    // identities take the separately checked offset-cancellation route.
    let word = terms.mk_app(Symbol::named("bvmul"), [x, x], Sort::bitvec(9));
    let sum = terms.mk_app(Symbol::named("bvadd"), [word, zero], Sort::bitvec(9));
    let equality = terms.mk_app(Symbol::named("="), [word, sum], Sort::Bool);
    let leaf = BvExpr::leaf(&format!("proof_bv_{}", x.index()), 9);
    let word = BvExpr::mul(leaf.clone(), leaf);
    let expected = BvExpr::eq(word.clone(), BvExpr::add(word, BvExpr::const_val(0, 9)));
    (terms, equality, expected)
}

fn assert_every_lowering_poll(terms: &TermStore, clause: &[TermId], expected: &BvExpr) {
    let snapshot = terms.entries_snapshot();
    let mut total = 0_usize;
    let actual = lower_clause(terms, clause, deadline(), false, &mut || {
        total = total.saturating_add(1);
        true
    })
    .unwrap();
    assert_eq!(&actual, expected);
    assert!(
        total > 5 && total < 10_000,
        "small solver-free fixture: {total}"
    );
    for stop in 1..=total {
        let mut calls = 0_usize;
        assert_eq!(
            lower_clause(terms, clause, deadline(), false, &mut || {
                calls = calls.saturating_add(1);
                calls != stop
            }),
            Err(Failure::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(
        &lower_clause(terms, clause, deadline(), false, &mut || true).unwrap(),
        expected
    );
    assert_eq!(terms.entries_snapshot(), snapshot);
    assert!(!terms.strict_bv_semantics_validated(clause));
}
