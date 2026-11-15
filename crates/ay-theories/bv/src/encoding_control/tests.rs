// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::enter_check_stop;
use num_bigint::BigInt;
use std::sync::atomic::AtomicUsize;

fn inputs(store: &mut TermStore) -> (TermId, TermId) {
    (
        store.mk_var("x", Sort::bitvec(128)),
        store.mk_var("y", Sort::bitvec(128)),
    )
}

fn stop_after(armed: &Arc<AtomicBool>, count: &Arc<AtomicUsize>) -> CheckStop {
    let armed = Arc::clone(armed);
    let count = Arc::clone(count);
    Arc::new(move || armed.load(Ordering::Relaxed) && count.fetch_add(1, Ordering::Relaxed) >= 39)
}

#[test]
fn offset_census_retains_the_original_owner_after_tls_removal() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let equality = store.mk_eq(x, y);
    let calls = Arc::new(AtomicUsize::new(0));
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&calls);
    let enabled = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || {
        enabled.load(Ordering::Relaxed) && observed.fetch_add(1, Ordering::Relaxed) == 1
    }));
    let mut solver = BvSolver::new(&store);
    let owner = solver.encoding_guard();
    drop(scope);
    armed.store(true, Ordering::Relaxed);
    solver.count_offset_equalities(&[equality]);
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    assert!(owner.was_stopped());
    armed.store(false, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
    assert!(solver.bitblast_all(&[equality]).is_empty());
    assert_eq!(calls.load(Ordering::Relaxed), 2);
}

#[test]
fn original_raw_stop_refuses_one_128_bit_predicate_and_flag_reset() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let product = store.mk_bvmul(vec![x, y]);
    let predicate = store.mk_eq(product, x);
    let flag = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&flag));
    flag.store(true, Ordering::Relaxed);
    assert!(solver.bitblast_predicate(predicate).is_none());
    flag.store(false, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
    assert!(solver.clauses().is_empty());
    assert!(solver.take_clauses().is_empty());
    assert!(solver.get_term_bits(product).is_none());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn original_callback_survives_tls_drop_and_full_encoding_reset() {
    let mut store = TermStore::new();
    let (x, _) = inputs(&mut store);
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&stopped);
    let scope = enter_check_stop(Arc::new(move || flag.load(Ordering::Relaxed)));
    let mut solver = BvSolver::new(&store);
    drop(scope);
    stopped.store(true, Ordering::Relaxed);
    assert!(solver.ensure_term_bits(x).is_none());
    stopped.store(false, Ordering::Relaxed);
    solver.reset();
    assert!(!solver.encoding_complete());
    assert!(solver.ensure_term_bits(x).is_none());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(solver.term_to_bits().is_empty());
}

#[test]
fn multiply_mid_encoding_stop_never_exports_a_partial_word_or_cnf() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let armed = Arc::new(AtomicBool::new(false));
    let count = Arc::new(AtomicUsize::new(0));
    let _scope = enter_check_stop(stop_after(&armed, &count));
    let mut solver = BvSolver::new(&store);
    let a = solver.ensure_term_bits(x).unwrap();
    let b = solver.ensure_term_bits(y).unwrap();
    let before = solver.num_vars();
    armed.store(true, Ordering::Relaxed);
    let result = solver.bitblast_mul(&a, &b);
    assert!(result.is_empty());
    assert!(
        solver.num_vars() > before,
        "stop must occur after circuit work begins"
    );
    assert_eq!(count.load(Ordering::Relaxed), 40);
    assert!(!solver.encoding_complete());
    assert!(solver.take_clauses().is_empty());
}

#[test]
fn unsigned_division_mid_rows_never_populates_the_division_cache() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let armed = Arc::new(AtomicBool::new(false));
    let count = Arc::new(AtomicUsize::new(0));
    let _scope = enter_check_stop(stop_after(&armed, &count));
    let mut solver = BvSolver::new(&store);
    solver.ensure_term_bits(x).unwrap();
    solver.ensure_term_bits(y).unwrap();
    armed.store(true, Ordering::Relaxed);
    let (q, r) = solver.bitblast_udiv_urem_cached(x, y);
    assert!(q.is_empty() && r.is_empty());
    assert!(solver.div_caches().0.is_empty());
    assert!(!solver.encoding_complete());
    assert!(solver.take_clauses().is_empty());
}

#[test]
fn signed_division_refusal_never_populates_the_signed_cache() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let flag = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&flag));
    solver.ensure_term_bits(x).unwrap();
    solver.ensure_term_bits(y).unwrap();
    flag.store(true, Ordering::Relaxed);
    let (q, r, _, _) = solver.bitblast_signed_div_rem_cached(x, y);
    assert!(q.is_empty() && r.is_empty());
    assert!(solver.div_caches().1.is_empty());
    flag.store(false, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
}

#[test]
fn delayed_refusal_does_not_mark_circuit_built_or_export_state() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let product = store.mk_bvmul(vec![x, y]);
    let flag = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&flag));
    solver.set_delay_enabled(true);
    assert_eq!(solver.ensure_term_bits(product).unwrap().len(), 128);
    assert_eq!(solver.delayed_ops().len(), 1);
    flag.store(true, Ordering::Relaxed);
    assert!(solver.build_delayed_circuit(0).is_empty());
    assert!(!solver.delayed_ops()[0].circuit_built);
    assert!(solver.take_delayed_state().is_none());
    assert!(solver.take_clauses().is_empty());
}

#[test]
fn stopped_comparison_and_mux_do_not_assert_unwind_widths() {
    let store = TermStore::new();
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(flag);
    assert_eq!(solver.bitblast_eq(&vec![1], &Vec::new()), 0);
    assert!(solver.bitwise_mux(&vec![1], &Vec::new(), 1).is_empty());
    assert!(solver
        .bitblast_udiv_urem(&vec![1], &Vec::new())
        .0
        .is_empty());
    assert!(!solver.encoding_complete());
}

#[test]
fn child_original_callback_and_raw_handle_are_not_replaced_by_parent_guard() {
    let store = TermStore::new();
    let parent = BvSolver::new(&store);
    let guard = parent.encoding_guard();
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stopped);
    let scope = enter_check_stop(Arc::new(move || observed.load(Ordering::Relaxed)));
    let mut child = BvSolver::new(&store);
    let raw = Arc::new(AtomicBool::new(false));
    child.set_interrupt(Arc::clone(&raw));
    child.inherit_encoding_guard(&guard);
    drop(scope);
    stopped.store(true, Ordering::Relaxed);
    assert!(!child.encoding_complete());
    stopped.store(false, Ordering::Relaxed);
    raw.store(false, Ordering::Relaxed);
    assert!(!guard.open());
    assert!(!parent.encoding_complete());
}

#[test]
fn late_temporary_raw_refusal_is_shared_with_the_enclosing_cleanup_guard() {
    let store = TermStore::new();
    let parent = BvSolver::new(&store);
    let guard = parent.encoding_guard();
    let mut child = BvSolver::new(&store);
    let raw = Arc::new(AtomicBool::new(false));
    child.set_interrupt(Arc::clone(&raw));
    child.inherit_encoding_guard(&guard);
    raw.store(true, Ordering::Relaxed);
    assert!(!child.encoding_complete());
    drop(child);
    raw.store(false, Ordering::Relaxed);
    assert!(!guard.open());
}

#[test]
fn healthy_full_reset_retains_normal_materialization() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let mut solver = BvSolver::new(&store);
    assert_eq!(solver.ensure_term_bits(x).unwrap().len(), 8);
    solver.reset();
    assert!(solver.encoding_complete());
    assert!(solver.term_to_bits().is_empty());
    assert_eq!(solver.ensure_term_bits(x).unwrap().len(), 8);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn healthy_constant_multiply_and_divide_keep_exact_values() {
    let mut store = TermStore::new();
    let a = store.mk_bitvec(BigInt::from(21u32), 8);
    let b = store.mk_bitvec(BigInt::from(3u32), 8);
    let mut solver = BvSolver::new(&store);
    let a_bits = solver.ensure_term_bits(a).unwrap();
    let b_bits = solver.ensure_term_bits(b).unwrap();
    let product = solver.bitblast_mul(&a_bits, &b_bits);
    let (quotient, remainder) = solver.bitblast_udiv_urem_cached(a, b);
    let mut sat = ay_sat::Solver::new(solver.num_vars() as usize);
    for clause in solver.clauses() {
        sat.add_clause(
            clause
                .literals()
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect(),
        );
    }
    let ay_sat::SatResult::Sat(model) = sat.solve().into_inner() else {
        panic!("healthy exact circuit must be satisfiable");
    };
    let value = |bits: &[CnfLit]| -> u32 {
        bits.iter().enumerate().fold(0, |n, (i, &lit)| {
            let set = model[lit.unsigned_abs() as usize - 1] == (lit > 0);
            n | (u32::from(set) << i)
        })
    };
    assert_eq!(value(&product), 63);
    assert_eq!(value(&quotient), 7);
    assert_eq!(value(&remainder), 0);
    assert!(solver.encoding_complete());
}

#[test]
fn recursive_materialization_does_not_memoize_a_stopped_root() {
    let mut store = TermStore::new();
    let (x, y) = inputs(&mut store);
    let product = store.mk_bvmul(vec![x, y]);
    let armed = Arc::new(AtomicBool::new(false));
    let count = Arc::new(AtomicUsize::new(0));
    let _scope = enter_check_stop(stop_after(&armed, &count));
    let mut solver = BvSolver::new(&store);
    solver.ensure_term_bits(x).unwrap();
    solver.ensure_term_bits(y).unwrap();
    armed.store(true, Ordering::Relaxed);
    assert!(solver.ensure_term_bits(product).is_none());
    assert!(!solver.term_to_bits().contains_key(&product));
    assert!(!solver.encoding_complete());
    assert!(solver.take_clauses().is_empty());
}

#[test]
fn repeated_self_and_same_parent_attachment_is_bounded_and_keeps_raw_identity() {
    let store = TermStore::new();
    let parent = BvSolver::new(&store);
    let guard = parent.encoding_guard();
    let mut child = BvSolver::new(&store);
    let self_guard = child.encoding_guard();
    child.inherit_encoding_guard(&self_guard);
    assert!(Arc::ptr_eq(&child.encoding, &self_guard.control));
    child.inherit_encoding_guard(&guard);
    let joined = Arc::clone(&child.encoding);
    for _ in 0..128 {
        child.inherit_encoding_guard(&guard);
        let same = child.encoding_guard();
        child.inherit_encoding_guard(&same);
        assert!(Arc::ptr_eq(&child.encoding, &joined));
    }
    let Some((original_child, original_parent)) = &child.encoding.enclosing else {
        panic!("one root attachment expected");
    };
    assert!(original_child.control.enclosing.is_none());
    assert!(original_parent.control.enclosing.is_none());
    assert!(child.encoding_complete());
    let mut raw_child = BvSolver::new(&store);
    let raw = Arc::new(AtomicBool::new(false));
    raw_child.set_interrupt(Arc::clone(&raw));
    let retained = raw_child.encoding_guard();
    raw_child.set_interrupt(Arc::new(AtomicBool::new(false)));
    raw_child.inherit_encoding_guard(&retained);
    raw.store(true, Ordering::Relaxed);
    assert!(!raw_child.encoding_complete());
}

#[test]
fn nested_or_distinct_second_parent_refuses_instead_of_growing_history() {
    let store = TermStore::new();
    let root = BvSolver::new(&store);
    let mut parent = BvSolver::new(&store);
    parent.inherit_encoding_guard(&root.encoding_guard());
    let mut child = BvSolver::new(&store);
    child.inherit_encoding_guard(&parent.encoding_guard());
    assert!(!child.encoding_complete());
    assert!(!parent.encoding_complete());
    assert!(!root.encoding_complete());
    let first = BvSolver::new(&store);
    let second = BvSolver::new(&store);
    let mut child = BvSolver::new(&store);
    child.inherit_encoding_guard(&first.encoding_guard());
    let joined = Arc::clone(&child.encoding);
    child.inherit_encoding_guard(&second.encoding_guard());
    assert!(Arc::ptr_eq(&child.encoding, &joined));
    assert!(!child.encoding_complete());
    assert!(!first.encoding_complete());
    assert!(!second.encoding_complete());
}

#[test]
fn delayed_first_raw_refusal_survives_replacement_reset_and_preexisting_guard() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let original = Arc::new(AtomicBool::new(false));
    let replacement = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    let before_first_attachment = solver.encoding_guard();
    solver.set_interrupt(Arc::clone(&original));
    solver.set_interrupt(Arc::clone(&replacement));
    assert!(before_first_attachment.open());
    assert!(solver.encoding_complete());
    original.store(true, Ordering::Relaxed);
    assert!(solver.ensure_term_bits(x).is_none());
    assert!(!before_first_attachment.open());
    assert!(!replacement.load(Ordering::Relaxed));
    original.store(false, Ordering::Relaxed);
    solver.reset();
    assert!(!solver.encoding_complete());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(solver.take_clauses().is_empty());
}

#[test]
fn healthy_reset_keeps_the_unobserved_first_raw_handle_live() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let original = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&original));
    solver.set_interrupt(Arc::new(AtomicBool::new(false)));
    assert_eq!(solver.ensure_term_bits(x).unwrap().len(), 8);
    solver.reset();
    assert!(solver.encoding_complete());
    assert!(
        solver.interrupt.is_none(),
        "healthy reset keeps its existing data policy"
    );
    original.store(true, Ordering::Relaxed);
    assert!(solver.ensure_term_bits(x).is_none());
    original.store(false, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
}

#[test]
fn current_raw_replacement_is_polled_beside_the_retained_first_handle() {
    let store = TermStore::new();
    let original = Arc::new(AtomicBool::new(false));
    let current = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&original));
    solver.set_interrupt(Arc::clone(&current));
    current.store(true, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
    assert!(!original.load(Ordering::Relaxed));
    current.store(false, Ordering::Relaxed);
    solver.reset();
    assert!(!solver.encoding_complete());
}

#[test]
fn fresh_independent_solver_does_not_retain_a_completed_original_raw_handle() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let original = Arc::new(AtomicBool::new(false));
    {
        let mut completed = BvSolver::new(&store);
        completed.set_interrupt(Arc::clone(&original));
        assert_eq!(completed.ensure_term_bits(x).unwrap().len(), 8);
        assert!(completed.encoding_complete());
    }
    original.store(true, Ordering::Relaxed);
    let independent = Arc::new(AtomicBool::new(false));
    let mut solver = BvSolver::new(&store);
    solver.set_interrupt(Arc::clone(&independent));
    assert_eq!(solver.ensure_term_bits(x).unwrap().len(), 8);
    assert!(solver.encoding_complete());
    independent.store(true, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
    independent.store(false, Ordering::Relaxed);
    assert!(!solver.encoding_complete());
}
