// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use ay_core::resource::CheckStop;
use ay_core::term::{Symbol, TermStore};
use ay_core::time::Instant;
use ay_core::Sort;
use std::cell::Cell;
use std::ops::ControlFlow;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

// Input/EUF fixture preparation is deliberately outside this inventory-only
// constituent. Independent calibrated test grants are not production renewal.
fn fixture() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Uninterpreted("U".into()));
    let condition = terms.mk_var("condition", Sort::Bool);
    let app = terms.mk_app(Symbol::named("f"), [x, x], Sort::Uninterpreted("U".into()));
    let ite = terms.mk_ite_raw(condition, x, app);
    let negated = terms.mk_not_raw(condition);
    let all = terms.mk_forall(vec![("q".into(), Sort::Bool)], negated);
    let exists = terms.mk_exists(vec![("e".into(), Sort::Bool)], all);
    let bound = terms.mk_let(vec![("v".into(), ite)], exists);
    let root = terms.mk_app(Symbol::named("predicate"), [bound, x], Sort::Bool);
    let constant = terms.mk_bool(true);
    // TermStore::new also preallocates false: root it explicitly so the
    // all-source coverage assertion includes both canonical Boolean entries.
    let false_constant = terms.mk_bool(false);
    (terms, vec![root, constant, root, false_constant])
}

fn measured(
    euf: &EufSolver<'_>,
    roots: &[TermId],
    work_limit: u64,
    copy_limit: usize,
) -> (Result<Vec<TermId>, QueryError>, u64, usize) {
    let used = Cell::new(0u64);
    let copied = Cell::new(0usize);
    let mut sink = |units: usize, bytes: usize| {
        let next_work = used
            .get()
            .checked_add(u64::try_from(units).unwrap())
            .unwrap();
        let next_bytes = copied.get().checked_add(bytes).unwrap();
        if next_work > work_limit || next_bytes > copy_limit {
            return Err(QueryError::Exhausted);
        }
        used.set(next_work);
        copied.set(next_bytes);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(work_limit, &mut sink);
    let result = euf.try_model_terms_from_roots(roots, &mut work);
    (result, used.get(), copied.get())
}

#[test]
fn root_inventory_matches_legacy_all_children_and_sorted_order() {
    let (terms, roots) = fixture();
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&roots);
    let expected = euf.scoped_model_terms();
    let before = euf.model_term_scope.clone();
    let (actual, _, _) = measured(&euf, &roots, u64::MAX, usize::MAX);
    assert_eq!(actual.unwrap(), expected);
    // This fixture reaches every currently defined TermData variant. Matching
    // legacy output alone must not conceal an omitted child on both paths.
    assert_eq!(expected.len(), terms.len());
    assert_eq!(euf.model_term_scope, before);
    assert!(expected.windows(2).all(|pair| pair[0].0 < pair[1].0));
}

#[test]
fn quantifier_trigger_metadata_is_not_a_new_model_child() {
    let mut terms = TermStore::new();
    let body = terms.mk_var("body", Sort::Bool);
    let trigger = terms.mk_var("trigger_only", Sort::Bool);
    let root =
        terms.mk_forall_with_triggers(vec![("q".into(), Sort::Bool)], body, vec![vec![trigger]]);
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&[root]);
    let actual = measured(&euf, &[root], u64::MAX, usize::MAX).0.unwrap();
    assert_eq!(actual, euf.scoped_model_terms());
    assert!(actual.contains(&body));
    assert!(!actual.contains(&trigger));
}

#[test]
fn scoped_and_unscoped_inventory_match_legacy_without_reclosing() {
    let (terms, roots) = fixture();
    let mut euf = EufSolver::new(&terms);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(1_000_000, &mut checkpoint);
    assert_eq!(
        euf.try_scoped_model_terms(&mut work).unwrap(),
        euf.scoped_model_terms()
    );
    euf.scope_model_to_roots(&roots);
    assert_eq!(
        euf.try_scoped_model_terms(&mut work).unwrap(),
        euf.scoped_model_terms()
    );
    // A private existing scope need not itself be a transitive closure.
    let root = roots[0];
    euf.model_term_scope = Some([root].into_iter().collect());
    assert_eq!(euf.try_scoped_model_terms(&mut work).unwrap(), vec![root]);
}

#[test]
fn repeated_roots_and_shared_edges_pay_every_raw_occurrence() {
    let (terms, roots) = fixture();
    let euf = EufSolver::new(&terms);
    let once = measured(&euf, &roots[..1], u64::MAX, usize::MAX);
    let repeated = measured(&euf, &[roots[0], roots[0], roots[0]], u64::MAX, usize::MAX);
    assert_eq!(once.0.unwrap(), repeated.0.unwrap());
    assert_eq!(repeated.1 - once.1, 16);
    assert_eq!(once.2, repeated.2);
    let mut other = TermStore::new();
    let leaf = other.mk_var("shared", Sort::Bool);
    let single = other.mk_app(Symbol::named("one"), [leaf], Sort::Bool);
    let shared = other.mk_app(Symbol::named("many"), [leaf, leaf, leaf], Sort::Bool);
    let euf = EufSolver::new(&other);
    let one_edge = measured(&euf, &[single], u64::MAX, usize::MAX);
    let three_edges = measured(&euf, &[shared], u64::MAX, usize::MAX);
    assert_eq!(one_edge.0.unwrap().len(), three_edges.0.unwrap().len());
    assert_eq!(three_edges.1 - one_edge.1, 16);
    assert_eq!(one_edge.2, three_edges.2);
}

#[test]
fn malformed_root_and_nested_child_refuse_before_lookup() {
    let mut terms = TermStore::new();
    let safe = terms.mk_var("safe", Sort::Bool);
    let dead = TermId(u32::MAX);
    let inner = terms.mk_app(Symbol::named("bad_inner"), [safe, dead], Sort::Bool);
    let outer = terms.mk_app(Symbol::named("bad_outer"), [inner], Sort::Bool);
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&[safe]);
    let before = euf.model_term_scope.clone();
    for roots in [&[dead][..], &[outer][..]] {
        assert!(matches!(
            measured(&euf, roots, u64::MAX, usize::MAX).0,
            Err(QueryError::Invalid(_))
        ));
        assert_eq!(euf.model_term_scope, before);
    }
}

#[test]
fn exact_work_accepts_and_one_short_refuses_without_cache_commit() {
    let (terms, roots) = fixture();
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&roots[..1]);
    let before = euf.model_term_scope.clone();
    let (_, units, bytes) = measured(&euf, &roots, u64::MAX, usize::MAX);
    assert!(measured(&euf, &roots, units, bytes).0.is_ok());
    assert_eq!(
        measured(&euf, &roots, units - 1, bytes).0,
        Err(QueryError::Exhausted)
    );
    assert_eq!(euf.model_term_scope, before);
}

#[test]
fn exact_copy_accepts_and_one_short_refuses_before_allocation() {
    let (terms, roots) = fixture();
    let euf = EufSolver::new(&terms);
    let (_, units, bytes) = measured(&euf, &roots, u64::MAX, usize::MAX);
    assert!(measured(&euf, &roots, units, bytes).0.is_ok());
    assert_eq!(
        measured(&euf, &roots, units, bytes - 1).0,
        Err(QueryError::Exhausted)
    );
    assert!(euf.model_term_scope.is_none());
}

#[test]
fn sparse_installed_scope_prices_full_hash_capacity() {
    let (terms, roots) = fixture();
    let mut euf = EufSolver::new(&terms);
    let mut scope = ay_core::kani_compat::det_hash_set_with_capacity(4_096);
    scope.insert(roots[0]);
    let capacity = scope.capacity();
    euf.model_term_scope = Some(scope);
    let used = Cell::new(0usize);
    let mut sink = |units: usize, _: usize| {
        used.set(used.get().checked_add(units).unwrap());
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    assert_eq!(
        euf.try_scoped_model_terms(&mut work).unwrap(),
        vec![roots[0]]
    );
    assert!(used.get() >= 32 * capacity + 256);
}

#[test]
fn callback_stop_after_progress_remains_sticky_after_reset() {
    let (terms, roots) = fixture();
    let euf = EufSolver::new(&terms);
    let stopped = Cell::new(false);
    let observations = Cell::new(0usize);
    let mut checkpoint = || {
        observations.set(observations.get() + 1);
        if observations.get() == 12 {
            stopped.set(true);
        }
        if stopped.get() {
            ControlFlow::Break(ay_core::original_query::StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(1_000_000, &mut checkpoint);
    let refused = euf.try_model_terms_from_roots(&roots, &mut work);
    assert_eq!(
        refused,
        Err(QueryError::Interrupted(
            ay_core::original_query::StopReason::Cancelled
        ))
    );
    stopped.set(false);
    let count = observations.get();
    assert_eq!(euf.try_model_terms_from_roots(&roots, &mut work), refused);
    assert_eq!(observations.get(), count);
    assert!(euf.model_term_scope.is_none());
}

#[test]
fn final_post_scratch_poll_refuses_without_scope_mutation() {
    let (terms, roots) = fixture();
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&roots[..1]);
    let before = euf.model_term_scope.clone();
    let debited = Cell::new(0usize);
    let mut sink = |units: usize, _: usize| {
        debited.set(debited.get().checked_add(units).unwrap());
        if units == 0 {
            Err(QueryError::Interrupted(
                ay_core::original_query::StopReason::Deadline,
            ))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    assert_eq!(
        euf.try_model_terms_from_roots(&roots, &mut work),
        Err(QueryError::Interrupted(
            ay_core::original_query::StopReason::Deadline
        ))
    );
    assert!(debited.get() > 0);
    assert_eq!(euf.model_term_scope, before);
}

#[test]
fn empty_roots_and_empty_scope_cannot_skip_the_original_observer() {
    let (terms, _) = fixture();
    let mut euf = EufSolver::new(&terms);
    euf.model_term_scope = Some(Default::default());
    let mut checkpoint = || ControlFlow::Break(ay_core::original_query::StopReason::Cancelled);
    let mut work = WorkBudget::new(1_000_000, &mut checkpoint);
    assert!(matches!(
        euf.try_model_terms_from_roots(&[], &mut work),
        Err(QueryError::Interrupted(_))
    ));
    assert!(matches!(
        euf.try_scoped_model_terms(&mut work),
        Err(QueryError::Interrupted(_))
    ));
    assert!(euf.model_term_scope.as_ref().unwrap().is_empty());
}

#[test]
fn successive_original_owner_calls_and_clones_share_one_finite_grant() {
    let (terms, roots) = fixture();
    let euf = EufSolver::new(&terms);
    let (_, units, bytes) = measured(&euf, &roots, u64::MAX, usize::MAX);
    let raw = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&raw);
    let check: CheckStop = Arc::new(move || observed.load(Ordering::SeqCst));
    let end = Instant::now() + Duration::from_secs(20);
    let owner = OriginalAdmission::new(FiniteAdmissionGrant::new(units * 2, bytes * 2), end, check);
    let clone = owner.clone();
    let first = owner
        .with_work(|work| euf.try_model_terms_from_roots(&roots, work))
        .unwrap();
    let second = clone
        .with_work(|work| euf.try_model_terms_from_roots(&roots, work))
        .unwrap();
    assert_eq!(first, second);
    drop(first);
    drop(second);
    assert!(matches!(
        owner.with_work(|work| euf.try_model_terms_from_roots(&roots, work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    raw.store(false, Ordering::SeqCst);
    assert!(clone.check().is_err());
}

#[test]
fn deep_root_inventory_is_iterative_and_keeps_existing_cache_state() {
    let mut terms = TermStore::new();
    let mut root = terms.mk_var("deep_leaf", Sort::Bool);
    for _ in 0..4_096 {
        root = terms.mk_app(Symbol::named("deep"), [root], Sort::Bool);
    }
    let mut euf = EufSolver::new(&terms);
    euf.scope_model_to_roots(&[root]);
    let expected = euf.scoped_model_terms();
    let dirty = euf.dirty;
    let observed = terms.snapshot_stamp();
    assert_eq!(
        measured(&euf, &[root], u64::MAX, usize::MAX).0.unwrap(),
        expected
    );
    assert_eq!(euf.dirty, dirty);
    assert_eq!(terms.snapshot_stamp(), observed);
    assert_eq!(euf.scoped_model_terms(), expected);
}

#[test]
fn checked_reservation_overflow_latches_without_allocating() {
    let calls = Cell::new(0usize);
    let mut checkpoint = || {
        calls.set(calls.get() + 1);
        ControlFlow::Continue(())
    };
    let mut work = WorkBudget::new(u64::MAX, &mut checkpoint);
    assert_eq!(
        priced_vec::<TermId>(usize::MAX, &mut work),
        Err(QueryError::Exhausted)
    );
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert_eq!(calls.get(), 0);
}
