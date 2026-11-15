// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Constant, Sort, Symbol};

use super::*;

fn store(data: Vec<TermData>) -> TermStore {
    TermStore::from_entries(
        data.into_iter().map(|data| (data, Sort::Bool)).collect(),
        None,
        None,
        0,
    )
}

fn fixture() -> (TermStore, Vec<TermId>) {
    let terms = store(vec![
        TermData::Const(Constant::Bool(true)),
        TermData::Var("leaf".to_string(), 0),
        TermData::App(Symbol::named("f"), vec![TermId(0), TermId(1), TermId(1)]),
        TermData::Let(
            vec![("a".to_string(), TermId(2)), ("b".to_string(), TermId(1))],
            TermId(2),
        ),
        TermData::Not(TermId(3)),
        TermData::Ite(TermId(0), TermId(3), TermId(4)),
        TermData::Forall(
            vec![("q".to_string(), Sort::Int)],
            TermId(5),
            vec![vec![TermId(2), TermId(2)], Vec::new(), vec![TermId(1)]],
        ),
        TermData::Exists(
            vec![("e".to_string(), Sort::Int)],
            TermId(6),
            vec![vec![TermId(3)], vec![TermId(0), TermId(0)]],
        ),
    ]);
    (terms, vec![TermId(7), TermId(6), TermId(7), TermId(0)])
}

fn usage(terms: &TermStore, roots: &[TermId]) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0usize, 0usize, 0usize);
    unfolded_work_memoized_with_progress(
        &mut TermCostMemo::default(),
        terms,
        roots,
        &mut |w, b| {
            work = work.checked_add(w).expect("small work fixture");
            bytes = bytes.checked_add(b).expect("small allocation fixture");
            polls += 1;
            true
        },
    )
    .expect("valid graph");
    (work, bytes, polls)
}

#[test]
fn metered_unfolding_matches_legacy_oracle_and_counts_all_edge_kinds() {
    let (terms, roots) = fixture();
    let mut legacy = TermCostMemo::default();
    let expected = unfolded_work_memoized(&mut legacy, &terms, &roots, &mut |_, _| true).unwrap();
    let mut actual = TermCostMemo::default();
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut actual, &terms, &roots, &mut |_, _| true),
        Ok(expected)
    );
    assert_eq!(expected, 126);
    assert_eq!(actual.costs, legacy.costs);
    for (term, cost) in [1, 1, 4, 10, 11, 23, 33, 46].into_iter().enumerate() {
        assert_eq!(actual.costs.get(&TermId(term as u32)), Some(&cost));
    }
}

#[test]
fn metered_unfolding_refuses_every_callback_and_retains_only_valid_pure_costs() {
    let (terms, roots) = fixture();
    let (_, _, polls) = usage(&terms, &roots);
    let mut oracle = TermCostMemo::default();
    let expected = unfolded_work_memoized(&mut oracle, &terms, &roots, &mut |_, _| true).unwrap();
    for stop in 1..=polls {
        let mut memo = TermCostMemo::default();
        let mut calls = 0;
        assert_eq!(
            unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(calls, stop);
        for (term, cost) in &memo.costs {
            assert_eq!(oracle.costs.get(term), Some(cost));
        }
        assert_eq!(
            unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut |_, _| true),
            Ok(expected)
        );
    }
}

#[test]
fn metered_unfolding_uses_one_exact_cumulative_work_and_byte_allowance() {
    let (terms, roots) = fixture();
    let (work, bytes, _) = usage(&terms, &roots);
    for (work_limit, byte_limit, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let mut progress = |w, b| {
            used_work = used_work.checked_add(w).unwrap();
            used_bytes = used_bytes.checked_add(b).unwrap();
            used_work <= work_limit && used_bytes <= byte_limit
        };
        let result = unfolded_work_memoized_with_progress(
            &mut TermCostMemo::default(),
            &terms,
            &roots,
            &mut progress,
        );
        assert_eq!(result.is_ok(), accepted);
        if accepted {
            assert_eq!(
                unfolded_work_memoized_with_progress(
                    &mut TermCostMemo::default(),
                    &terms,
                    &roots,
                    &mut progress,
                ),
                Err(ProofCheckError::ResourceLimit)
            );
        }
    }
}

#[test]
fn metered_unfolding_warm_memo_still_prices_repeated_root_search_and_final_sum() {
    let (terms, roots) = fixture();
    let mut memo = TermCostMemo::default();
    let expected = unfolded_work_memoized(&mut memo, &terms, &roots, &mut |_, _| true).unwrap();
    let mut work = 0usize;
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut |w, bytes| {
            work += w;
            bytes == 0
        }),
        Ok(expected)
    );
    assert!(work > roots.len());
    let repeated = vec![TermId(7); 4_096];
    let mut remaining = work;
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &repeated, &mut |w, _| {
            if w > remaining {
                return false;
            }
            remaining -= w;
            true
        }),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn metered_unfolding_duplicate_edges_are_not_deduplicated_into_cheaper_costs() {
    let terms = store(vec![
        TermData::Var("leaf".to_string(), 0),
        TermData::App(Symbol::named("wide"), vec![TermId(0); 4_096]),
    ]);
    let mut memo = TermCostMemo::default();
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut memo,
            &terms,
            &[TermId(1), TermId(1)],
            &mut |_, _| true
        ),
        Ok(8_194)
    );
    assert_eq!(memo.costs.get(&TermId(1)), Some(&4_097));
    let mut refused_allocation = false;
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut TermCostMemo::default(),
            &terms,
            &[TermId(1)],
            &mut |_, bytes| {
                refused_allocation |= bytes >= 8_192;
                bytes < 8_192
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(
        refused_allocation,
        "child and frame growth are priced before allocation"
    );
}

#[test]
fn metered_unfolding_prices_empty_trigger_groups_despite_small_unfolded_cost() {
    let terms = store(vec![
        TermData::Var("leaf".to_string(), 0),
        TermData::Forall(Vec::new(), TermId(0), vec![Vec::new(); 4_096]),
    ]);
    let mut spent = 0usize;
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut TermCostMemo::default(),
            &terms,
            &[TermId(1)],
            &mut |work, _| {
                spent += work;
                spent <= 1_024
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(spent, 1_025);
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut TermCostMemo::default(),
            &terms,
            &[TermId(1)],
            &mut |_, _| true
        ),
        Ok(2)
    );
}

#[test]
fn metered_unfolding_missing_handles_and_cycles_refuse_without_panicking() {
    for data in [
        vec![TermData::Not(TermId(0))],
        vec![TermData::Not(TermId(1)), TermData::Not(TermId(0))],
        vec![TermData::Not(TermId::SENTINEL)],
    ] {
        let terms = store(data);
        assert_eq!(
            unfolded_work_memoized_with_progress(
                &mut TermCostMemo::default(),
                &terms,
                &[TermId(0)],
                &mut |_, _| true
            ),
            Err(ProofCheckError::ResourceLimit)
        );
    }
    let (terms, _) = fixture();
    let mut memo = TermCostMemo::default();
    memo.costs.insert(TermId::SENTINEL, 1);
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut memo,
            &terms,
            &[TermId::SENTINEL],
            &mut |_, _| true
        ),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn metered_unfolding_checks_node_sum_root_sum_and_accounting_overflow() {
    let mut data = vec![TermData::Var("leaf".to_string(), 0)];
    for index in 1..=usize::BITS {
        data.push(TermData::App(
            Symbol::named("twice"),
            vec![TermId(index - 1); 2],
        ));
    }
    let terms = store(data);
    let last_fitting = TermId(usize::BITS - 1);
    let mut memo = TermCostMemo::default();
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &[last_fitting], &mut |_, _| true),
        Ok(usize::MAX)
    );
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &[last_fitting; 2], &mut |_, _| {
            true
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(
        unfolded_work_memoized_with_progress(
            &mut memo,
            &terms,
            &[TermId(usize::BITS)],
            &mut |_, _| true
        ),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(!memo.costs.contains_key(&TermId(usize::BITS)));
    assert_eq!(mul(usize::MAX, 2), Err(ProofCheckError::ResourceLimit));
}

#[test]
fn metered_unfolding_tree_insertion_charges_before_mutating_the_memo() {
    let mut memo = TermCostMemo::default();
    for index in 0..10_000 {
        memo.costs.insert(TermId(index), 1);
    }
    let before = memo.costs.clone();
    let mut charged_bytes = 0;
    assert_eq!(
        memo_insert(&mut memo, TermId(10_000), 1, &mut |_, bytes| {
            charged_bytes += bytes;
            bytes == 0
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(memo.costs, before);
    assert!(charged_bytes > size_of::<(TermId, usize)>());
    let (mut work, mut bytes) = (0, 0);
    memo_insert(&mut memo, TermId(10_000), 1, &mut |w, b| {
        work += w;
        bytes += b;
        true
    })
    .unwrap();
    assert_eq!(memo.costs.len(), 10_001);
    assert_eq!(bytes, charged_bytes);
    assert!(
        work < 1_024,
        "ordered lookup and insertion have a logarithmic bound"
    );
}

#[test]
fn metered_unfolding_stack_allocation_and_empty_final_poll_can_be_refused() {
    let (terms, roots) = fixture();
    let mut memo = TermCostMemo::default();
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &roots, &mut |_, bytes| bytes == 0),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(memo.costs.is_empty());
    let mut calls = 0;
    assert_eq!(
        unfolded_work_memoized_with_progress(&mut memo, &terms, &[], &mut |_, _| {
            calls += 1;
            calls < 2
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls, 2);
}
