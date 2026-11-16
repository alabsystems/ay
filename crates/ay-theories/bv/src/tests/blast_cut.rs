// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bitblast_all` records what cut it short. The memory reading that cuts it
//! is not sticky, so only the record tells a partial CNF from a reading that
//! has dropped back under the ceiling since.

use super::*;

/// Enough BV comparisons to exercise entry and in-circuit stop polls.
fn comparisons(store: &mut TermStore) -> Vec<TermId> {
    (0..128)
        .map(|i| {
            let a = store.mk_var(format!("a{i}"), Sort::bitvec(8));
            let b = store.mk_var(format!("b{i}"), Sort::bitvec(8));
            store.mk_bvult(a, b)
        })
        .collect()
}

/// Clears the thread's forced memory reading, including during unwinding.
struct ForcedMemory;

impl ForcedMemory {
    fn exceeded() -> Self {
        ay_sys::force_process_memory_exceeded_for_testing(true);
        Self
    }
}

impl Drop for ForcedMemory {
    fn drop(&mut self) {
        ay_sys::force_process_memory_exceeded_for_testing(false);
    }
}

#[test]
fn a_blast_cut_by_the_memory_ceiling_stays_recorded_after_the_reading_drops() {
    let mut store = setup_store();
    let assertions = comparisons(&mut store);

    let mut whole = BvSolver::new(&store);
    let whole_clauses = whole.bitblast_all(&assertions);
    assert_eq!(whole.blast_cut(), None);

    let mut cut = BvSolver::new(&store);
    let cut_clauses = {
        let _memory = ForcedMemory::exceeded();
        cut.bitblast_all(&assertions)
    };
    assert!(
        !ay_sys::process_memory_exceeded(),
        "the reading dropped back"
    );
    assert_eq!(cut.blast_cut(), Some(BlastCut::MemoryCeiling));
    assert!(
        cut_clauses.len() < whole_clauses.len(),
        "the cut CNF is partial: {} of {} clauses",
        cut_clauses.len(),
        whole_clauses.len()
    );
}

#[test]
fn a_blast_cut_by_the_interrupt_is_recorded_as_the_interrupt() {
    let mut store = setup_store();
    let assertions = comparisons(&mut store);
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    let _ = solver.bitblast_all(&assertions);
    assert_eq!(solver.blast_cut(), Some(BlastCut::Interrupt));
}

#[test]
fn an_interrupt_observed_before_blast_keeps_its_cause_after_flag_reset() {
    let store = setup_store();
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&flag));
    flag.store(false, Ordering::Relaxed);
    assert_eq!(solver.bitblast_all(&[]).as_slice(), &[] as &[CnfClause]);
    assert_eq!(solver.blast_cut(), Some(BlastCut::Interrupt));
    assert!(!solver.encoding_complete());
    solver.reset();
    assert_eq!(solver.blast_cut(), Some(BlastCut::Interrupt));
    assert!(!solver.encoding_complete());
}

#[test]
fn a_memory_cut_inside_a_predicate_is_not_reclassified_as_interrupt() {
    use ay_core::resource::enter_check_stop;
    use std::sync::atomic::AtomicUsize;

    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(128));
    let b = store.mk_var("b", Sort::bitvec(128));
    let predicate = store.mk_bvult(a, b);
    let calls = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&calls);
    let _scope = enter_check_stop(Arc::new(move || {
        if count.fetch_add(1, Ordering::Relaxed) == 20 {
            ay_sys::force_process_memory_exceeded_for_testing(true);
        }
        false
    }));
    let mut solver = BvSolver::new(&store);
    {
        let _reset_memory = ForcedMemory;
        assert!(solver.bitblast_predicate(predicate).is_none());
    }
    assert!(solver.num_vars() > 0, "the refusal follows circuit work");
    assert_eq!(calls.load(Ordering::Relaxed), 21);
    assert!(!ay_sys::process_memory_exceeded());
    assert_eq!(solver.blast_cut(), Some(BlastCut::MemoryCeiling));
    assert!(!solver.encoding_complete());
    assert_eq!(
        solver.bitblast_all(&[predicate]).as_slice(),
        &[] as &[CnfClause]
    );
    assert_eq!(solver.blast_cut(), Some(BlastCut::MemoryCeiling));
}

#[test]
fn an_opaque_refusal_never_invents_a_typed_cut_from_later_readings() {
    use ay_core::resource::enter_check_stop;

    let store = setup_store();
    let scope = enter_check_stop(Arc::new(|| true));
    let mut solver = BvSolver::new(&store);
    assert_eq!(solver.bitblast_all(&[]).as_slice(), &[] as &[CnfClause]);
    assert!(!solver.encoding_complete());
    assert_eq!(solver.blast_cut(), None);
    drop(scope);
    let _memory = ForcedMemory::exceeded();
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert_eq!(solver.bitblast_all(&[]).as_slice(), &[] as &[CnfClause]);
    assert!(!solver.encoding_complete());
    assert_eq!(solver.blast_cut(), None, "the first cause was opaque");
}

#[test]
fn child_typed_refusal_reaches_the_original_guard_and_keeps_its_first_cause() {
    let store = setup_store();
    let parent = BvSolver::new(&store);
    let guard = parent.encoding_guard();
    let mut child = BvSolver::new(&store);
    child.inherit_encoding_guard(&guard);
    let flag = Arc::new(AtomicBool::new(false));
    child.set_interrupt(Arc::clone(&flag));
    flag.store(true, Ordering::Relaxed);
    assert!(!child.encoding_complete());
    flag.store(false, Ordering::Relaxed);
    let _memory = ForcedMemory::exceeded();
    assert_eq!(child.blast_cut(), Some(BlastCut::Interrupt));
    assert_eq!(parent.blast_cut(), Some(BlastCut::Interrupt));
    assert!(!guard.open());
    assert_eq!(parent.blast_cut(), Some(BlastCut::Interrupt));
}

#[test]
fn typed_refusal_before_root_handoff_is_preserved() {
    let store = setup_store();
    let _root = ScopedBvEncodingOwner::enter(&store).expect("healthy original root");
    let mut child = BvSolver::new(&store);
    {
        let _memory = ForcedMemory::exceeded();
        assert!(!child.encoding_complete());
    }
    let root = child.original_encoding_guard();
    assert!(root.was_stopped());
    let mut later = BvSolver::new(&store);
    later.inherit_encoding_guard(&root);
    assert!(!later.encoding_complete());
    assert_eq!(later.blast_cut(), Some(BlastCut::MemoryCeiling));
    assert_eq!(child.bitblast_all(&[]).as_slice(), &[] as &[CnfClause]);
    assert_eq!(child.blast_cut(), Some(BlastCut::MemoryCeiling));
}
