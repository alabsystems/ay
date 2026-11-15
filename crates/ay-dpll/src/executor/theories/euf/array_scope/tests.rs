// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::theories::euf::ArrayAxiomMode;
use ay_core::{Sort, Symbol};
use num_bigint::BigInt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn archived_array_definition() -> (Executor, TermId) {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(129));
    let array = terms.mk_var("array", array_sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 129);
    let high = terms.mk_bitvec(BigInt::from(1) << 128usize, 129);
    let key = terms.mk_bitvec(BigInt::from(7), 8);
    let base = terms.mk_const_array(Sort::bitvec(8), zero);
    let stored = terms.mk_store(base, key, high);
    let equality = terms.mk_eq_coerce_no_ite_expand(array, stored);
    let _ = terms.mk_not(equality);
    let _ = terms.mk_select(array, key);
    let scalar = terms.mk_var("scalar", Sort::Bool);
    exec.ctx.assertions = vec![scalar];
    (exec, equality)
}

fn small_equality(exec: &mut Executor) -> TermId {
    let terms = &mut exec.ctx.terms;
    let sort = Sort::array(Sort::Bool, Sort::bitvec(1));
    let left = terms.mk_var("left", sort.clone());
    let right = terms.mk_var("right", sort);
    terms.mk_eq_coerce_no_ite_expand(left, right)
}

#[test]
fn scalarized_history_does_not_reenter_generic_or_finite_generation() {
    let (mut exec, old_equality) = archived_array_definition();
    let original = exec.ctx.assertions.clone();
    let saved = exec.begin_live_array_axiom_scope(&[]);
    assert!(saved.is_none());
    assert!(!exec.term_in_array_scope(old_equality));
    let initial = exec.add_finite_index_array_closure();
    assert_eq!(initial.candidate_equalities, 0);
    let points = exec.finite_array_expansion.remaining_index_points;
    let cells = exec.finite_array_expansion.remaining_value_cells;
    exec.ensure_array_eq_ite_negations();
    exec.add_array_extensionality_axioms();
    exec.run_array_axiom_fixpoint_at(original.len(), ArrayAxiomMode::EagerAll);
    assert!(exec.array_axiom_scope.is_some());
    assert!(!exec.term_in_array_scope(old_equality));
    let final_report = exec.add_finite_index_array_closure();
    assert!(final_report.is_complete());
    assert_eq!(final_report.candidate_equalities, 0);
    assert_eq!(exec.finite_array_expansion.remaining_index_points, points);
    assert_eq!(exec.finite_array_expansion.remaining_value_cells, cells);
    assert_eq!(exec.ctx.assertions, original);
    exec.array_axiom_scope = saved;
    assert!(exec.array_axiom_scope.is_none());

    // The archived equality really was a resurrection source: without the
    // scope, the existing congruence producer adds a live clause containing it.
    let (mut unscoped, _) = archived_array_definition();
    unscoped.add_store_value_congruence_axioms();
    let resurrected = unscoped.add_finite_index_array_closure();
    assert!(resurrected.candidate_equalities > 0);
}

#[test]
fn active_and_assumption_only_equalities_still_receive_complete_closure() {
    for assumption_only in [false, true] {
        let mut exec = Executor::new();
        let equality = small_equality(&mut exec);
        let extra = if assumption_only {
            exec.ctx.assertions = vec![exec.ctx.terms.true_term()];
            vec![equality]
        } else {
            exec.ctx.assertions = vec![equality];
            Vec::new()
        };
        let saved = exec.begin_live_array_axiom_scope(&extra);
        assert!(exec.term_in_array_scope(equality));
        let report = exec.add_finite_index_array_closure_with_roots(&extra);
        assert!(report.is_complete());
        assert_eq!(report.emitted_equalities, 1);
        assert_eq!(report.emitted_index_points, 2);
        exec.array_axiom_scope = saved;
    }
}

#[test]
fn generated_axioms_admit_reused_older_subterms_before_final_closure() {
    let mut exec = Executor::new();
    let equality = small_equality(&mut exec);
    let ay_core::TermData::App(_, args) = exec.ctx.terms.get(equality) else {
        panic!("expected an array equality");
    };
    let (left, right) = (args[0], args[1]);
    let key = exec.ctx.terms.false_term();
    let read_left = exec.ctx.terms.mk_select(left, key);
    let read_right = exec.ctx.terms.mk_select(right, key);
    let reads_equal = exec.ctx.terms.mk_eq(read_left, read_right);
    let negated = exec.ctx.terms.mk_not(equality);
    let axiom = exec.ctx.terms.mk_or(vec![negated, reads_equal]);
    exec.ctx.assertions = vec![exec.ctx.terms.true_term()];
    let saved = exec.begin_live_array_axiom_scope(&[]);
    assert!(!exec.term_in_array_scope(axiom));
    assert!(!exec.term_in_array_scope(equality));
    exec.push_array_axiom_assertion_site(axiom, "array_cong_select");
    assert!(exec.term_in_array_scope(axiom));
    assert!(exec.term_in_array_scope(equality));
    assert!(exec.term_in_array_scope(read_left));
    let report = exec.add_finite_index_array_closure();
    assert!(report.is_complete());
    assert_eq!(report.emitted_equalities, 1);
    exec.array_axiom_scope = saved;
}

#[test]
fn live_ite_reuses_its_required_negation_without_admitting_dormant_ites() {
    for active in [false, true] {
        let mut exec = Executor::new();
        let equality = small_equality(&mut exec);
        let negated = exec.ctx.terms.mk_not(equality);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 1);
        let one = exec.ctx.terms.mk_bitvec(BigInt::from(1), 1);
        let choice = exec.ctx.terms.mk_ite_raw(equality, zero, one);
        let assertion = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [choice, zero], Sort::Bool);
        exec.ctx.assertions = if active {
            vec![assertion]
        } else {
            vec![exec.ctx.terms.true_term()]
        };
        let saved = exec.begin_live_array_axiom_scope(&[]);
        assert!(!exec.term_in_array_scope(negated));
        exec.ensure_array_eq_ite_negations();
        assert_eq!(exec.term_in_array_scope(negated), active);
        let initial_len = exec.ctx.assertions.len();
        exec.add_array_extensionality_axioms();
        assert_eq!(exec.ctx.assertions.len() > initial_len, active);
        exec.array_axiom_scope = saved;
    }
}

#[test]
fn both_fixpoint_drivers_restore_the_caller_scope_even_when_interrupted() {
    for incremental in [false, true] {
        for full in [false, true] {
            for interrupted in [false, true] {
                let mut exec = Executor::new();
                let scalar = exec.ctx.terms.mk_var("scalar", Sort::Bool);
                let sentinel = exec.ctx.terms.mk_var("outer", Sort::Bool);
                exec.ctx.assertions = vec![scalar];
                exec.array_axiom_scope = Some((HashSet::from_iter([sentinel]), usize::MAX));
                let outer = exec.array_axiom_scope.clone();
                let saved = exec.begin_live_array_axiom_scope(&[]);
                let scoped = exec.array_axiom_scope.clone();
                assert_eq!(saved, outer);
                exec.incremental_mode = incremental;
                let interrupt = Arc::new(AtomicBool::new(interrupted));
                exec.set_interrupt(Arc::clone(&interrupt));
                if full {
                    exec.run_array_axiom_fixpoint_at(1, ArrayAxiomMode::EagerAll);
                } else {
                    exec.run_array_axiom_fixpoint_5();
                }
                assert_eq!(exec.array_axiom_scope, scoped);
                exec.array_axiom_scope = saved;
                assert_eq!(exec.array_axiom_scope, outer);
                interrupt.store(false, Ordering::Relaxed);
            }
        }
    }
}

#[test]
fn nested_fixpoints_return_reused_generated_nodes_to_the_outer_scope() {
    for full in [false, true] {
        let mut exec = Executor::new();
        let equality = small_equality(&mut exec);
        let ay_core::TermData::App(_, args) = exec.ctx.terms.get(equality) else {
            panic!("expected an array equality");
        };
        let (left, right) = (args[0], args[1]);
        let key = exec.ctx.terms.false_term();
        let read_left = exec.ctx.terms.mk_select(left, key);
        let read_right = exec.ctx.terms.mk_select(right, key);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 1);
        let observed = exec.ctx.terms.mk_eq(read_left, zero);
        let reads_equal = exec.ctx.terms.mk_eq(read_left, read_right);
        let negated = exec.ctx.terms.mk_not(equality);
        let cached_axiom = exec.ctx.terms.mk_or(vec![negated, reads_equal]);
        exec.ctx.assertions = vec![equality, observed];
        let saved = exec.begin_live_array_axiom_scope(&[]);
        assert!(!exec.term_in_array_scope(read_right));
        assert!(!exec.term_in_array_scope(cached_axiom));
        exec.incremental_mode = true;
        if full {
            exec.run_array_axiom_fixpoint_at(2, ArrayAxiomMode::EagerAll);
        } else {
            exec.run_array_axiom_fixpoint_5();
        }
        assert!(exec.ctx.assertions.contains(&cached_axiom));
        assert!(exec.term_in_array_scope(read_right));
        assert!(exec.term_in_array_scope(cached_axiom));
        exec.array_axiom_scope = saved;
    }
}
