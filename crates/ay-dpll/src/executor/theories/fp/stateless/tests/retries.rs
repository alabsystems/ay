// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::theories::fp::FlattenOutcome;

fn interrupted_attempt(executor: &mut Executor, interrupt: &AtomicBool) -> Result<SolveResult> {
    let loaded = Cell::new(0);
    let result = executor.solve_fp_stateless_observed(&|phase| {
        if matches!(phase, FpPhase::SatLoad) {
            loaded.set(loaded.get() + 1);
            if loaded.get() == 2 {
                interrupt.store(true, Ordering::Relaxed);
            }
        }
    });
    assert_eq!(loaded.get(), 2);
    assert!(result.as_ref().unwrap().is_unknown());
    // The real source has recovered BEFORE the enclosing retry adapter sees
    // the Unknown. Only captured provenance can keep that adapter terminal.
    interrupt.store(false, Ordering::Relaxed);
    result
}

fn pinned() -> Executor {
    setup(
        "(set-logic QF_FPLRA)
         (declare-const r Real)
         (declare-const x (_ FloatingPoint 5 11))
         (assert (= r 1.0))
         (assert (fp.eq ((_ to_fp 5 11) RNE r) x))",
    )
}

fn array() -> Executor {
    setup(
        "(set-logic QF_ABVFP)
         (declare-const mem (Array (_ BitVec 8) (_ BitVec 16)))
         (assert (fp.isZero ((_ to_fp 5 11) (select mem #x00))))",
    )
}

#[test]
fn pinned_real_stop_is_terminal_after_original_roots_are_restored() {
    let mut executor = pinned();
    let roots = executor.ctx.assertions.clone();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let result = executor
        .try_fp_pin_unsat_probe_with(&mut |branch| {
            assert_ne!(branch.ctx.assertions, roots);
            interrupted_attempt(branch, &interrupt)
        })
        .unwrap();
    assert!(matches!(result, Some(SolveResult::Unknown)));
    assert_eq!(executor.ctx.assertions, roots);
    assert_revoked(&executor, UnknownOrigin::InterruptFlag);
}

#[test]
fn flattened_array_stop_is_not_a_license_to_try_another_transform() {
    let mut executor = array();
    let roots = executor.ctx.assertions.clone();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let result = executor
        .try_flatten_constant_index_reads_with(&mut |branch| {
            assert_ne!(branch.ctx.assertions, roots);
            interrupted_attempt(branch, &interrupt)
        })
        .unwrap();
    assert!(matches!(
        result,
        FlattenOutcome::Decided(SolveResult::Unknown)
    ));
    assert_eq!(executor.ctx.assertions, roots);
    assert_revoked(&executor, UnknownOrigin::InterruptFlag);
}

fn record_recovered_stop(executor: &mut Executor, origin: UnknownOrigin) {
    match origin {
        UnknownOrigin::InterruptFlag => {
            let interrupt = Arc::new(AtomicBool::new(true));
            executor.set_interrupt(Arc::clone(&interrupt));
            assert!(executor.should_abort_theory_loop());
            interrupt.store(false, Ordering::Relaxed);
        }
        UnknownOrigin::MemoryBudget => {
            // The executor-local term ceiling is deterministic: no real OOM
            // or process-wide memory knob is involved.
            executor.set_term_memory_limit(Some(0));
            assert!(executor.should_abort_theory_loop());
            executor.set_term_memory_limit(None);
        }
        _ => {
            // Deterministic work exhaustion has no live flag to poll. The
            // Incomplete control below exercises the same diagnostic channel.
            executor.record_unknown_from_origin(origin);
            executor.last_result = Some(SolveResult::Unknown);
        }
    }
    assert_eq!(executor.unknown_origin(), Some(origin));
    assert!(!executor.should_abort_theory_loop());
}

#[test]
fn flattened_array_recorded_stop_prevents_solving_after_capture() {
    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::DeterministicResourceBudget,
    ] {
        let mut executor = array();
        let roots = executor.ctx.assertions.clone();
        record_recovered_stop(&mut executor, origin);
        let calls = Cell::new(0);
        let result = executor
            .try_flatten_constant_index_reads_with(&mut |_| {
                calls.set(calls.get() + 1);
                Ok(SolveResult::Unknown)
            })
            .unwrap();
        assert!(matches!(
            result,
            FlattenOutcome::Decided(SolveResult::Unknown)
        ));
        assert_eq!(calls.get(), 0, "{origin:?}");
        assert_eq!(executor.ctx.assertions, roots);
        assert_revoked(&executor, origin);
    }
}

#[test]
fn flattened_array_model_refusal_preserves_recovered_stop_not_incompleteness() {
    use crate::executor::model::Model;
    use crate::executor::theories::fp::flatten_reads;

    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::IncompleteSolverLane,
    ] {
        let mut executor = setup(
            "(set-logic QF_ABVFP)
             (declare-const mem (Array (_ BitVec 8) (_ BitVec 16)))
             (declare-fun g ((_ FloatingPoint 5 11)) Bool)
             (assert (g ((_ to_fp 5 11) (select mem #x00))))",
        );
        let roots = executor.ctx.assertions.clone();
        let plan = flatten_reads::plan(&mut executor.ctx.terms, &roots).unwrap();
        let mut calls = 0;
        let result = executor
            .try_flatten_constant_index_reads_with(&mut |branch| {
                calls += 1;
                assert_ne!(branch.ctx.assertions, roots);
                assert_eq!(branch.ctx.assertions, plan.assertions);
                record_recovered_stop(branch, origin);
                // Stage a rejected provider candidate, not a real solver
                // verdict: array reconstruction succeeds, but the rewritten
                // Boolean UF has no SAT assignment, so transport must refuse.
                let mut model = Model::empty();
                model.bv_model = Some(ay_bv::BvModel {
                    values: plan
                        .cells
                        .iter()
                        .map(|cell| (cell.fresh, num_bigint::BigInt::from(0)))
                        .collect(),
                    term_to_bits: Default::default(),
                    bool_overrides: Default::default(),
                });
                branch.last_model = Some(model);
                branch.last_model_validated = true;
                assert!(branch.attach_flattened_array_model(&plan.cells));
                Ok(SolveResult::Sat)
            })
            .unwrap();
        if origin == UnknownOrigin::IncompleteSolverLane {
            assert!(matches!(result, FlattenOutcome::Undecided));
        } else {
            assert!(matches!(
                result,
                FlattenOutcome::Decided(SolveResult::Unknown)
            ));
        }
        assert_eq!(calls, 1);
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(
            executor.statistics().get_string("abvfp_flatten.status"),
            Some("fired: array or Boolean-UF model incomplete")
        );
        assert!(!executor.last_model_validated);
        assert_revoked(&executor, origin);
    }
}

#[test]
fn ordinary_incompleteness_keeps_existing_transform_fallbacks() {
    let mut executor = pinned();
    let roots = executor.ctx.assertions.clone();
    let result = executor
        .try_fp_pin_unsat_probe_with(&mut |branch| {
            branch.last_unknown_reason = Some(UnknownReason::Incomplete);
            Ok(SolveResult::Unknown)
        })
        .unwrap();
    assert!(result.is_none());
    assert_eq!(executor.ctx.assertions, roots);

    let mut executor = array();
    let roots = executor.ctx.assertions.clone();
    let result = executor
        .try_flatten_constant_index_reads_with(&mut |branch| {
            branch.last_unknown_reason = Some(UnknownReason::Incomplete);
            Ok(SolveResult::Unknown)
        })
        .unwrap();
    assert!(matches!(result, FlattenOutcome::Undecided));
    assert_eq!(executor.ctx.assertions, roots);
}
