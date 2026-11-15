// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn bool_proxy_repair_and_existing_condition_links_abort_without_committing_partial_pairs() {
    for (body, target) in [
        (
            "(assert (fp.isZero (ite b x y)))",
            IncrementalFpPhase::BoolRepair,
        ),
        (
            "(assert (fp.isZero (ite b x y)))",
            IncrementalFpPhase::BoolLink,
        ),
        (
            "(assert b) (assert (fp.isZero (ite b x y)))",
            IncrementalFpPhase::ConditionLink,
        ),
    ] {
        let mut executor = setup(body);
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        let visits = Cell::new(0);
        let result = executor
            .try_solve_fp_incremental_observed(&|phase| {
                if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                    visits.set(visits.get() + 1);
                    if visits.get() == 2 {
                        flag.store(true, Ordering::Relaxed);
                    }
                }
            })
            .unwrap();
        assert_eq!(visits.get(), 2, "{target:?} must have real work");
        assert!(matches!(result, Some(SolveResult::Unknown)));
        shell(&executor, 1);
        revoked(&executor, UnknownOrigin::InterruptFlag);
        flag.store(false, Ordering::Relaxed);
        assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
        let state = executor.incr_fp_state.as_ref().unwrap();
        if matches!(target, IncrementalFpPhase::ConditionLink) {
            // An already named b links directly, before the free-Bool proxy
            // cache. It must not be mistaken for a later repair obligation.
            assert!(state.linked_bool_inputs.is_empty());
            assert!(state
                .tseitin_state
                .term_to_var
                .contains_key(&executor.ctx.assertions[0]));
        } else {
            assert!(!state.linked_bool_inputs.is_empty());
        }
    }
}

#[test]
fn cancellation_after_a_persistent_push_rebuilds_at_the_original_depth_then_pop_retracts() {
    let mut executor = simple();
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
    executor
        .execute_all(&parse("(declare-const c Bool) (push 1) (assert (and b c))").unwrap())
        .unwrap();
    let state = executor.incr_fp_state.as_ref().unwrap();
    assert_eq!(state.scope_depth, 2);
    assert!(state.persistent_sat.is_some());
    let roots = executor.ctx.assertions.clone();
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&flag));
    let definitions = Cell::new(0);
    let result = executor
        .try_solve_fp_incremental_observed(&|phase| {
            if matches!(phase, IncrementalFpPhase::GlobalDefinition) {
                definitions.set(definitions.get() + 1);
                if definitions.get() == 2 {
                    flag.store(true, Ordering::Relaxed);
                }
            }
        })
        .unwrap();
    assert_eq!(definitions.get(), 2);
    assert!(matches!(result, Some(SolveResult::Unknown)));
    assert_eq!(executor.ctx.assertions, roots);
    shell(&executor, 2);
    revoked(&executor, UnknownOrigin::InterruptFlag);
    flag.store(false, Ordering::Relaxed);
    // Drop the Boolean scope while the SAT owner is the empty shell.
    executor.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    shell(&executor, 1);
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
    executor
        .execute_all(&parse("(push 1) (assert (not (fp.isZero x)))").unwrap())
        .unwrap();
    assert!(rebuild(&mut executor).is_unsat());
    executor.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
}

#[test]
fn semantic_foreign_and_conversion_declines_remain_distinct_from_resource_refusal() {
    for body in [
        "(declare-fun f ((_ FloatingPoint 5 11)) Bool)
         (assert (f x)) (assert (f y)) (assert (fp.isZero x))",
        "(assert (= ((_ fp.to_ubv 8) RNE x) #x00))",
    ] {
        let mut executor = setup(body);
        let result = executor.try_solve_fp_incremental().unwrap();
        assert!(result.is_none(), "ordinary semantic fallback: {body}");
        assert!(!executor.fp_recorded_resource_stop());
        let state = executor.incr_fp_state.as_ref().unwrap();
        assert!(state.disabled);
        assert!(state.persistent_sat.is_none());
        assert!(state.fp_cache.term_to_fp.is_empty());
    }
}

#[test]
fn real_exhausted_term_budget_aborts_before_admission_and_revokes_old_model() {
    let mut executor = simple();
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Sat
    ));
    executor.set_term_memory_limit(Some(0));
    let admitted = Cell::new(false);
    let result = executor
        .try_solve_fp_incremental_observed(&|phase| {
            if matches!(phase, IncrementalFpPhase::Admission) {
                admitted.set(true);
            }
        })
        .unwrap();
    assert!(matches!(result, Some(SolveResult::Unknown)));
    assert!(!admitted.get());
    shell(&executor, 1);
    revoked(&executor, UnknownOrigin::MemoryBudget);
    executor.set_term_memory_limit(None);
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
}
