// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use ay_core::term::TermStore;
use ay_core::{Sort, TheoryResult};
use num_bigint::BigInt;

use super::{Builder, Search, DEADLINE_POLL_STEPS};
use crate::NiaSolver;

#[test]
fn a_live_stop_interrupts_a_deadline_free_search_at_existing_checkpoints() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_one = terms.mk_eq(x, one);
    let x_two = terms.mk_eq(x, two);
    let root = terms.mk_and(vec![x_one, x_two]);
    let mut builder = Builder::new(&terms);
    let clauses = builder.cnf(root, true, 0).expect("arithmetic unit clauses");
    let nvars = builder.var_term.len();
    let mut search = Search::new(builder, clauses, nvars);
    let polls = Arc::new(AtomicUsize::new(0));
    let _scope = enter_check_stop({
        let polls = Arc::clone(&polls);
        Arc::new(move || polls.fetch_add(1, Ordering::Relaxed) == 2)
    });
    assert!(!search.run(None));
    assert_eq!(polls.load(Ordering::Relaxed), 3);
    assert_eq!(search.step, 2 * DEADLINE_POLL_STEPS);
    assert_ne!(search.unsat, Vec::<u32>::new());
}

#[test]
fn a_cancelled_lane_keeps_a_fresh_search_available_after_the_scope_ends() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let root = terms.mk_eq(x, one);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(vec![root]);
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        assert!(solver.try_clausal_local_search().is_none());
        assert!(!solver.local_search_done);
        assert!(solver.bounded_enum_model.is_none());
    }
    assert!(matches!(
        solver.try_clausal_local_search(),
        Some(TheoryResult::Sat)
    ));
    assert!(solver.local_search_done);
    assert_eq!(
        solver
            .extract_model()
            .expect("checked witness")
            .values
            .get(&x),
        Some(&BigInt::from(1))
    );
}

fn all_one_roots(terms: &mut TermStore, count: usize) -> Vec<ay_core::term::TermId> {
    let one = terms.mk_int(BigInt::from(1));
    (0..count)
        .map(|i| {
            let variable = terms.mk_var(format!("canonical_{i}"), Sort::Int);
            terms.mk_eq(variable, one)
        })
        .collect()
}

#[test]
fn cancelled_first_offer_never_publishes_and_a_fresh_scope_still_accepts() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 1);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots);
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        assert!(solver.try_local_search_first_offer().is_none());
        assert!(solver.bounded_enum_model.is_none());
        assert!(!solver.local_search_done);
    }
    assert!(matches!(
        solver.try_local_search_first_offer(),
        Some(TheoryResult::Sat)
    ));
    assert!(solver.bounded_enum_model.is_some());
    assert!(
        !solver.local_search_done,
        "canonical offer is not the full lane"
    );
}

#[test]
fn cancelled_split_probe_does_not_spend_the_once_per_solve_offer() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 1);
    let flag = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots);
    solver.set_split_probe_flag(Arc::clone(&flag));
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        assert!(solver.try_split_probe().is_none());
        assert!(!flag.load(Ordering::Relaxed));
        assert!(solver.bounded_enum_model.is_none());
    }
    assert!(matches!(solver.try_split_probe(), Some(TheoryResult::Sat)));
    assert!(flag.load(Ordering::Relaxed));
    assert!(!solver.local_search_done);
}

#[test]
fn a_past_shared_cutoff_disables_canonical_offers_without_a_solve_deadline() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 1);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots.clone());
    assert!(solver.deadline.is_none());
    solver.set_local_search_deadline(ay_core::time::Instant::now());
    let flag = Arc::new(std::sync::atomic::AtomicBool::new(false));
    solver.set_split_probe_flag(Arc::clone(&flag));
    assert!(solver.try_local_search_first_offer().is_none());
    assert!(solver.try_split_probe().is_none());
    assert!(!flag.load(Ordering::Relaxed));
    assert!(!solver.local_search_done);
    assert!(solver.bounded_enum_model.is_none());
    let mut fresh = NiaSolver::new(&terms);
    fresh.set_root_assertions(roots);
    assert!(matches!(
        fresh.try_local_search_first_offer(),
        Some(TheoryResult::Sat)
    ));
}

#[test]
fn a_deadline_free_first_offer_does_not_acquire_a_clausal_search_slice() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("canonical_two", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let root = terms.mk_eq(x, two);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(vec![root]);
    assert!(
        solver.try_local_search_first_offer().is_none(),
        "neither canonical point is 2"
    );
    assert!(solver.bounded_enum_model.is_none());
    assert!(!solver.local_search_done);
    assert!(matches!(
        solver.try_clausal_local_search(),
        Some(TheoryResult::Sat)
    ));
    assert_eq!(
        solver
            .extract_model()
            .expect("checked full-lane witness")
            .values
            .get(&x),
        Some(&BigInt::from(2))
    );
}

#[test]
fn a_live_cancellation_interrupts_canonical_discovery_before_publication() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 128);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots);
    let polls = Arc::new(AtomicUsize::new(0));
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _guard_scope = check.enter();
    let _stop_scope = enter_check_stop({
        let check = check.clone();
        let polls = Arc::clone(&polls);
        Arc::new(move || {
            if polls.fetch_add(1, Ordering::Relaxed) == 31 {
                check.cancel();
            }
            false
        })
    });
    assert!(solver.try_local_search_first_offer().is_none());
    assert!(
        polls.load(Ordering::Relaxed) >= 32,
        "walk, not only entry, must poll"
    );
    assert!(solver.bounded_enum_model.is_none());
    assert!(!solver.local_search_done);
}

#[test]
fn an_observed_callback_stop_cannot_restart_the_canonical_fallback() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 128);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots);
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_secs(30));
    let polls = Arc::new(AtomicUsize::new(0));
    {
        let _scope = enter_check_stop({
            let polls = Arc::clone(&polls);
            Arc::new(move || polls.fetch_add(1, Ordering::Relaxed) == 31)
        });
        assert!(solver.try_local_search_first_offer().is_none());
    }
    assert!(polls.load(Ordering::Relaxed) >= 32);
    assert!(solver.bounded_enum_model.is_none());
    assert!(!solver.local_search_done);
    assert!(matches!(
        solver.try_local_search_first_offer(),
        Some(TheoryResult::Sat)
    ));
}

#[test]
fn exact_formula_and_shared_integer_dag_walks_observe_the_live_guard() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("shared_canonical", Sort::Int);
    let mut expression = x;
    for _ in 0..12 {
        let previous = expression;
        expression = terms.mk_app(
            ay_core::term::Symbol::named("+"),
            [previous, previous],
            Sort::Int,
        );
        let ay_core::term::TermData::App(_, children) = terms.get(expression) else {
            panic!("shared addition retained");
        };
        assert_eq!(children.as_slice(), &[previous, previous]);
    }
    let total = terms.mk_int(BigInt::from(1u32 << 12));
    let equation = terms.mk_eq(expression, total);
    let roots = all_one_roots(&mut terms, 128);
    let formula = terms.mk_and(roots.clone());
    let solver = NiaSolver::new(&terms);
    let mut assignment = crate::HashMap::default();
    assignment.insert(x, 1);
    for root in &roots {
        let ay_core::term::TermData::App(_, args) = terms.get(*root) else {
            panic!("equality root");
        };
        let variable = args
            .iter()
            .copied()
            .find(|&term| matches!(terms.get(term), ay_core::term::TermData::Var(_, _)))
            .expect("one variable in equality");
        assignment.insert(variable, 1);
    }
    for root in [equation, formula] {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let polls = Arc::new(AtomicUsize::new(0));
        {
            let _guard_scope = check.enter();
            let _stop_scope = enter_check_stop({
                let check = check.clone();
                let polls = Arc::clone(&polls);
                Arc::new(move || {
                    if polls.fetch_add(1, Ordering::Relaxed) == 31 {
                        check.cancel();
                    }
                    false
                })
            });
            let mut progress = super::SearchProgress::new(None);
            assert_eq!(
                solver.eval_formula_exact_with_progress(root, true, &assignment, &mut || progress
                    .poll(&solver)),
                None
            );
        }
        assert!(polls.load(Ordering::Relaxed) >= 32);
        assert_eq!(
            solver.eval_formula_exact(root, true, &assignment),
            Some(true)
        );
    }
}

#[test]
fn a_shared_cutoff_that_expires_inside_canonical_discovery_prevents_a_model() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 128);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots.clone());
    let end = ay_core::time::Instant::now() + std::time::Duration::from_secs(1);
    solver.set_local_search_deadline(end);
    let polls = Arc::new(AtomicUsize::new(0));
    {
        let _scope = enter_check_stop({
            let polls = Arc::clone(&polls);
            Arc::new(move || {
                if polls.fetch_add(1, Ordering::Relaxed) == 31 {
                    // Let the EXISTING fixed cutoff pass during a real walk;
                    // the callback itself never requests cancellation.
                    std::thread::sleep(
                        end.saturating_duration_since(ay_core::time::Instant::now())
                            + std::time::Duration::from_millis(1),
                    );
                }
                false
            })
        });
        assert!(solver.try_local_search_first_offer().is_none());
    }
    assert!(
        polls.load(Ordering::Relaxed) >= 32,
        "must enter discovery before the cutoff"
    );
    assert!(solver.bounded_enum_model.is_none());
    assert!(!solver.local_search_done);
    let mut fresh = NiaSolver::new(&terms);
    fresh.set_root_assertions(roots);
    assert!(matches!(
        fresh.try_local_search_first_offer(),
        Some(TheoryResult::Sat)
    ));
}

#[test]
fn cancellation_during_model_staging_publishes_no_partial_map() {
    let mut terms = TermStore::new();
    let roots = all_one_roots(&mut terms, 128);
    let mut vars = Vec::new();
    for root in &roots {
        let ay_core::term::TermData::App(_, args) = terms.get(*root) else {
            panic!("equality root");
        };
        let variable = args
            .iter()
            .copied()
            .find(|&term| matches!(terms.get(term), ay_core::term::TermData::Var(_, _)))
            .expect("one variable in equality");
        vars.push(variable);
    }
    let values = vec![1; vars.len()];
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots);
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let polls = Arc::new(AtomicUsize::new(0));
    {
        let _guard_scope = check.enter();
        let _stop_scope = enter_check_stop({
            let check = check.clone();
            let polls = Arc::clone(&polls);
            Arc::new(move || {
                if polls.fetch_add(1, Ordering::Relaxed) == 15 {
                    check.cancel();
                }
                false
            })
        });
        let mut progress = super::SearchProgress::new(None);
        assert!(solver
            .record_local_search_model(&vars, &values, &mut progress)
            .is_none());
    }
    assert!(polls.load(Ordering::Relaxed) >= 16);
    assert!(solver.bounded_enum_model.is_none());
    assert!(matches!(
        solver.try_local_search_first_offer(),
        Some(TheoryResult::Sat)
    ));
}
