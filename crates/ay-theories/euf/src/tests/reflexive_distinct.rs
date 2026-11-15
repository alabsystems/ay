// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn identical_distinct_arguments_need_only_the_distinct_literal() {
    for nonadjacent in [false, true] {
        let mut store = TermStore::new();
        let a = store.mk_var("a", Sort::Int);
        let b = store.mk_var("b", Sort::Int);
        // Raw App deliberately exercises the theory handler rather than the
        // term builder's simplification or pairwise expansion of distinct.
        let args = if nonadjacent {
            vec![a, b, a]
        } else {
            vec![a, a]
        };
        let distinct = store.mk_app(Symbol::named("distinct"), args, Sort::Bool);
        let mut euf = EufSolver::new(&store);
        assert!(euf.explain(a, a).is_empty());
        euf.assert_literal(distinct, true);
        let TheoryResult::Unsat(reasons) = euf.check() else {
            panic!("identical arguments contradict an asserted distinct");
        };
        assert_eq!(reasons, vec![TheoryLit::new(distinct, true)]);
    }
}

#[test]
fn false_reflexive_distinct_does_not_conflict() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let distinct = store.mk_app(Symbol::named("distinct"), vec![a, a], Sort::Bool);
    let mut euf = EufSolver::new(&store);
    euf.assert_literal(distinct, false);
    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
fn different_distinct_arguments_retain_the_equality_premise() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let equality = store.mk_eq(a, b);
    let distinct = store.mk_app(Symbol::named("distinct"), vec![a, b], Sort::Bool);
    let mut euf = EufSolver::new(&store);
    euf.assert_literal(distinct, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    euf.push();
    euf.assert_literal(equality, true);
    let TheoryResult::Unsat(mut reasons) = euf.check() else {
        panic!("the asserted equality contradicts distinct");
    };
    let mut expected = vec![
        TheoryLit::new(equality, true),
        TheoryLit::new(distinct, true),
    ];
    reasons.sort_unstable_by_key(|lit| (lit.term, lit.value));
    expected.sort_unstable_by_key(|lit| (lit.term, lit.value));
    assert_eq!(reasons, expected);
    euf.pop();
    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
fn reflexive_distinct_conflict_retracts_with_its_assertion() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let distinct = store.mk_app(Symbol::named("distinct"), vec![a, a], Sort::Bool);
    let mut euf = EufSolver::new(&store);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    euf.push();
    euf.assert_literal(distinct, true);
    let TheoryResult::Unsat(reasons) = euf.check() else {
        panic!("the live reflexive distinct assertion conflicts");
    };
    assert_eq!(reasons, vec![TheoryLit::new(distinct, true)]);
    euf.pop();
    assert!(matches!(euf.check(), TheoryResult::Sat));
    euf.assert_literal(distinct, false);
    assert!(matches!(euf.check(), TheoryResult::Sat));
}
