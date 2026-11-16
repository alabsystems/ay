// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `EufSolver::collect_disequality_conflicts`: every disequality the closure
//! violates, not only the one `check` reports.

use super::*;

/// `x0 = x1 = .. = xn` asserted as a chain, and `count` disequalities
/// `(not (= x0 xk))` for `k = 2 .. count + 1`.
struct Chain {
    store: TermStore,
    links: Vec<TermId>,
    denied: Vec<TermId>,
}

impl Chain {
    fn new(length: usize, count: usize) -> Self {
        let mut store = TermStore::new();
        let sort = Sort::Uninterpreted("U".to_string());
        let vars: Vec<TermId> = (0..=length)
            .map(|i| store.mk_var(format!("x{i}"), sort.clone()))
            .collect();
        let links = vars
            .windows(2)
            .map(|pair| store.mk_eq(pair[0], pair[1]))
            .collect();
        let denied = (2..count + 2)
            .map(|k| store.mk_eq(vars[0], vars[k]))
            .collect();
        Self {
            store,
            links,
            denied,
        }
    }
}

#[test]
fn every_violated_disequality_is_named_with_its_own_reasons() {
    let chain = Chain::new(6, 3);
    let mut euf = EufSolver::new(&chain.store);
    for &link in &chain.links {
        euf.assert_literal(link, true);
    }
    for &denied in &chain.denied {
        euf.assert_literal(denied, false);
    }
    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));

    let conflicts = euf.collect_disequality_conflicts(16);

    assert_eq!(conflicts.len(), 3);
    for (index, conflict) in conflicts.iter().enumerate() {
        // `x0 != x(index + 2)` against the first `index + 2` links.
        let denied = TheoryLit::new(chain.denied[index], false);
        assert!(conflict.contains(&denied), "{conflict:?}");
        assert_eq!(conflict.len(), index + 3, "{conflict:?}");
        for link in &chain.links[..index + 2] {
            assert!(
                conflict.contains(&TheoryLit::new(*link, true)),
                "{conflict:?}"
            );
        }
    }
}

#[test]
fn a_disequality_the_closure_respects_is_not_named() {
    let chain = Chain::new(6, 3);
    let mut euf = EufSolver::new(&chain.store);
    // The chain is cut after `x2`: `x0 = x1 = x2` and `x3 = .. = x6`.
    for (index, &link) in chain.links.iter().enumerate() {
        if index != 2 {
            euf.assert_literal(link, true);
        }
    }
    for &denied in &chain.denied {
        euf.assert_literal(denied, false);
    }
    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));

    let conflicts = euf.collect_disequality_conflicts(16);

    // Only `x0 != x2` is violated; `x3` and `x4` are in the other class.
    assert_eq!(conflicts.len(), 1);
    assert!(conflicts[0].contains(&TheoryLit::new(chain.denied[0], false)));
}

#[test]
fn the_limit_bounds_the_number_of_conflicts() {
    let chain = Chain::new(6, 4);
    let mut euf = EufSolver::new(&chain.store);
    for &link in &chain.links {
        euf.assert_literal(link, true);
    }
    for &denied in &chain.denied {
        euf.assert_literal(denied, false);
    }
    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));

    assert_eq!(euf.collect_disequality_conflicts(2).len(), 2);
    assert_eq!(euf.collect_disequality_conflicts(0).len(), 0);
}

#[test]
fn a_consistent_assignment_names_no_conflict() {
    let chain = Chain::new(4, 2);
    let mut euf = EufSolver::new(&chain.store);
    euf.assert_literal(chain.links[0], true);
    for &denied in &chain.denied {
        euf.assert_literal(denied, false);
    }
    assert!(matches!(euf.check(), TheoryResult::Sat));

    assert_eq!(euf.collect_disequality_conflicts(16).len(), 0);
}
