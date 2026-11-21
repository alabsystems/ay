// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

#[test]
fn unrelated_equal_balance_owner_cannot_own_terminal_proof() {
    let (mut s, conflict, _) = fixture();
    let attached = test_owner(1_000_000, 1_000_000);
    let other = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(attached.clone()).unwrap();
    let before = rows(&s);
    assert!(run(&mut s, conflict, &other).is_err());
    assert!(other.check().is_err());
    assert!(attached.check().is_ok());
    assert_eq!(rows(&s), before);
    assert!(!s.has_empty_clause);
}

#[test]
fn selected_unadmitted_proof_modes_and_poison_are_explicit_sticky_refusals() {
    for mutate in [
        (|s: &mut Solver| s.set_unsat_certificate_enabled(true)) as fn(&mut Solver),
        |s| s.cold.internal_lrat_enabled = true,
        |s| s.cold.scope_selectors.push(Variable(0)),
        |s| s.cold.proof_vars_compacted = true,
        |s| s.cold.trace_ext_conflict = true,
        |s| s.cold.finalize_sat_fail_count = 1,
        |s| s.cold.oversized_clause_poison = true,
        |s| s.cold.veripb_hints.derived.ready.push(7),
    ] {
        let (mut s, conflict, _) = fixture();
        let before = rows(&s);
        mutate(&mut s);
        let owner = test_owner(1_000_000, 1_000_000);
        s.attach_counted_admission(owner.clone()).unwrap();
        assert!(run(&mut s, conflict, &owner).is_err());
        assert!(owner.check().is_err());
        assert_eq!(rows(&s), before);
        assert!(!s.has_empty_clause);
        clean(&s);
    }
}

#[test]
fn selected_progress_callback_is_not_invoked_or_silently_disabled() {
    let (mut s, conflict, _) = fixture();
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    let calls = AtomicUsize::new(0);
    let progress = || {
        calls.fetch_add(1, Ordering::SeqCst);
        true
    };
    assert!(s
        .declare_counted_root_unsat(Some(conflict), &owner, Some(&progress))
        .is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(owner.check().is_err());
    assert!(!s.has_empty_clause);
}

#[test]
fn an_empty_marker_without_a_derived_empty_row_never_publishes_unsat() {
    let (mut s, _, _) = fixture();
    s.raise_empty_clause_flag();
    s.cold.clause_trace.as_mut().unwrap().mark_empty();
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    assert!(s.declare_counted_root_unsat(None, &owner, None).is_err());
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    assert!(owner.check().is_err());
}

#[test]
fn owned_post_proof_operation_unwind_poison_is_sticky_and_never_flushes_pending_writer() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("unwind");
    let (mut s, conflict, _) = fixture();
    pending_writer(&mut s, &path);
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    let reached = AtomicUsize::new(0);
    let result = catch_unwind(AssertUnwindSafe(|| {
        admission::prepare(&mut s, &owner, None).unwrap();
        let scope = Scope {
            solver: &mut s,
            owner: &owner,
            active: true,
            acquired: true,
            retained: false,
        };
        scope
            .solver
            .record_lrat_level0_conflict_admitted(conflict, &root::Counted(&owner))
            .unwrap();
        admission::terminal(scope.solver, &owner).unwrap();
        assert!(scope.solver.has_empty_clause);
        assert!(owner.check().is_ok());
        let n = scope.solver.trail.len();
        assert!(n > 0);
        reached.fetch_add(1, Ordering::SeqCst);
        let _ = scope.solver.trail[n]; // reached safe bounds panic, not a fabricated arena reference
    }));
    assert!(result.is_err());
    assert_eq!(reached.load(Ordering::SeqCst), 1);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    let receipt = owner.usage().unwrap();
    assert!(run(&mut s, conflict, &owner).is_err());
    assert_eq!(owner.usage().unwrap(), receipt);
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    quiet(&s, &path);
    drop(s);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
}

#[test]
fn missing_actual_conflict_id_cannot_mint_a_substitute_terminal_proof() {
    let (mut s, conflict, _) = fixture();
    s.cold.clause_ids.set(conflict.0 as usize, 0);
    let before = rows(&s);
    let next = s.cold.next_clause_id;
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    assert!(run(&mut s, conflict, &owner).is_err());
    assert!(owner.check().is_err());
    assert_eq!(rows(&s), before);
    assert_eq!(s.cold.next_clause_id, next);
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    clean(&s);
}

#[test]
fn inactive_conflict_reference_is_a_typed_refusal_not_an_arena_unwind() {
    let (mut s, _, _) = fixture();
    let before = rows(&s);
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        run(&mut s, ClauseRef(u32::MAX), &owner)
    }));
    assert!(outcome.unwrap().is_err());
    assert!(owner.check().is_err());
    assert_eq!(rows(&s), before);
    assert!(!s.has_empty_clause);
    clean(&s);
}

struct Hostile(Arc<AtomicUsize>);
impl Drop for Hostile {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("terminal observer payload destructor");
    }
}

#[test]
fn hostile_observer_payload_unwind_after_entry_retires_root_proof_without_late_flush() {
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    let observer = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            counted.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let (mut base, conflict, _) = fixture();
    base.attach_counted_admission(observer.clone()).unwrap();
    admission::prepare(&mut base, &observer, None).unwrap();
    let entry = calls.load(Ordering::SeqCst);
    calls.store(0, Ordering::SeqCst);
    assert!(matches!(
        run(&mut base, conflict, &observer).unwrap(),
        SatResult::Unsat(_)
    ));
    let total = calls.load(Ordering::SeqCst);
    let cut = entry + (total - entry) / 2;
    assert!(cut > entry && cut + 1 < total);

    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("hostile");
    let (mut s, conflict, _) = fixture();
    pending_writer(&mut s, &path);
    let calls = Arc::new(AtomicUsize::new(0));
    let called = Arc::clone(&calls);
    let drops = Arc::new(AtomicUsize::new(0));
    let dropped = Arc::clone(&drops);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            if called.fetch_add(1, Ordering::SeqCst) == cut {
                panic_any(Hostile(Arc::clone(&dropped)));
            }
            false
        }),
    )
    .unwrap();
    s.attach_counted_admission(owner.clone()).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| run(&mut s, conflict, &owner))).is_err());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverPanicked
        ))
    );
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    quiet(&s, &path);
    drop(s);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
}
