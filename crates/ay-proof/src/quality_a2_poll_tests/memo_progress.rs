// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const MEMO_STRESS_TERMS: usize = 1_024;

#[test]
fn cost_memo_fill_refuses_the_first_positive_work_charge() {
    let mut terms = TermStore::new();
    let mut root = terms.mk_var("memo_poll_root", Sort::Bool);
    for _ in 0..MEMO_STRESS_TERMS {
        root = terms.mk_app(Symbol::named("memo_poll_f"), [root], Sort::Bool);
    }

    let mut memo = TermCostMemo::default();
    let mut polls = 0_usize;
    let mut charged_work = 0;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        assert_eq!(bytes, 0, "refusal precedes the first memo allocation");
        polls += 1;
        charged_work += work;
        work == 0
    };
    let result =
        unfolded_work_memoized_with_progress(&mut memo, &terms, &[root], &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(charged_work, 1);
    assert_eq!(polls, 2, "entry poll followed by the first positive debit");
}

#[test]
fn warm_cost_memo_root_scan_still_polls_cancellation() {
    let mut terms = TermStore::new();
    let roots: Vec<_> = (0..MEMO_STRESS_TERMS)
        .map(|index| terms.mk_var(format!("memo_poll_{index}"), Sort::Bool))
        .collect();
    let mut memo = TermCostMemo::default();
    let mut unbounded = |_: usize, _: usize| true;
    unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut unbounded)
        .expect("cold memo fill succeeds");

    let mut polls = 0_usize;
    let mut charged_work = 0;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        assert_eq!(bytes, 0, "warm roots need no new memo storage");
        polls += 1;
        charged_work += work;
        work == 0
    };
    let result =
        unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(charged_work, 1);
    assert_eq!(polls, 2, "warm-root scanning remains paid and cancellable");
}

#[test]
fn cold_cost_memo_high_fanout_growth_is_charged_before_copying() {
    let mut terms = TermStore::new();
    let children: Vec<_> = (0..MEMO_STRESS_TERMS)
        .map(|index| terms.mk_var(format!("memo_child_{index}"), Sort::Bool))
        .collect();
    let root = terms.mk_app(Symbol::named("memo_high_fanout"), &children, Sort::Bool);

    let mut memo = TermCostMemo::default();
    let mut charged_work = 0;
    let mut refused_growth = false;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        charged_work += work;
        let accept = bytes < MEMO_STRESS_TERMS * size_of::<TermId>();
        refused_growth |= !accept;
        accept
    };
    let result =
        unfolded_work_memoized_with_progress(&mut memo, &terms, &[root], &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(charged_work > 0);
    assert!(
        refused_growth,
        "full replacement storage is debited before growth"
    );
}
