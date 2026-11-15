// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact original root reuse is DATA identity, not a discounted allowance.

use super::*;

#[test]
fn repeated_predicate_and_composite_roots_keep_first_literal_and_complete_cnf() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut checkpoint = || {
        if std::time::Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    for (eb, sb) in [(8, 24), (11, 53)] {
        let mut terms = TermStore::new();
        let input = terms.mk_var("x", Sort::FloatingPoint(eb, sb));
        let normal = predicate(&mut terms, "fp.isNormal", &[input]);
        let negative = predicate(&mut terms, "fp.isNegative", &[input]);
        let root = predicate(&mut terms, "and", &[normal, negative]);
        let target = ChcVar::new("x", crate::ChcSort::BitVec(eb + sb));
        let inputs = bindings(input, &target);
        let roots = [normal, root, normal, root, normal];
        let plan = source::plan(&terms, &roots, &inputs, &mut budget).unwrap();
        plan.prepay(&mut budget).unwrap();
        let unique = encoding::build(&terms, &roots[..2], &plan, &mut budget).unwrap();
        plan.prepay(&mut budget).unwrap();
        let repeated = encoding::build(&terms, &roots, &plan, &mut budget).unwrap();
        assert_eq!(repeated.roots.len(), roots.len());
        assert_eq!(
            repeated.roots,
            [
                unique.roots[0],
                unique.roots[1],
                unique.roots[0],
                unique.roots[1],
                unique.roots[0]
            ]
        );
        assert_eq!(repeated.encoding.clauses, unique.encoding.clauses);
        assert_eq!(
            repeated.encoding.cache.next_var,
            unique.encoding.cache.next_var
        );
        assert!(!repeated.encoding.has_encoding_gap);
    }
}

#[test]
fn duplicate_reuse_polls_and_latches_the_original_stop_owner() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    for reason in [StopReason::Cancelled, StopReason::Deadline] {
        let calls = Cell::new(0usize);
        let stop_at = Cell::new(usize::MAX);
        let permit = Cell::new(true);
        let mut stop = || {
            calls.set(calls.get() + 1);
            if std::time::Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else if calls.get() == stop_at.get() && !permit.get() {
                ControlFlow::Break(reason)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
        let plan = source::plan(&terms, &[root, root], &inputs, &mut budget).unwrap();
        plan.prepay(&mut budget).unwrap();
        calls.set(0);
        encoding::build(&terms, &[root], &plan, &mut budget).unwrap();
        // Single-root finalization has exactly two polls. The duplicate's
        // first operation poll occurs at the first of those positions.
        let duplicate_poll = calls.get() - 1;
        plan.prepay(&mut budget).unwrap();
        calls.set(0);
        stop_at.set(duplicate_poll);
        permit.set(false);
        assert!(
            matches!(encoding::build(&terms, &[root, root], &plan, &mut budget),
            Err(FpAdapterError::Owner(QueryError::Interrupted(actual))) if actual == reason)
        );
        assert_eq!(calls.get(), duplicate_poll);
        permit.set(true);
        assert_eq!(budget.charge(0), Err(QueryError::Interrupted(reason)));
        assert!(
            matches!(encoding::build(&terms, &[root, root], &plan, &mut budget),
            Err(FpAdapterError::Owner(QueryError::Interrupted(actual))) if actual == reason)
        );
    }
}

#[test]
fn reuse_never_skips_an_unsupported_later_original_root() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut terms = TermStore::new();
    let first = terms.mk_bool(false);
    let unsupported = terms.mk_app(Symbol::named("user_bool"), [first], Sort::Bool);
    let roots = [first, first, unsupported, first];
    let namespace = ChcProblem::new();
    let mut checkpoint = || {
        if std::time::Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(matches!(
        lower_fp_clause(&terms, &roots, &[], &namespace, &mut budget),
        Err(FpAdapterError::Unsupported(_))
    ));
}
