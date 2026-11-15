// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn malformed_persistent_model_discards_the_trial_without_resource_misclassification() {
    for interrupting in [false, true] {
        let mut executor = simple();
        assert!(matches!(
            executor.try_solve_fp_incremental().unwrap(),
            Some(SolveResult::Sat)
        ));
        assert!(executor.last_model.is_some());
        let roots = executor.ctx.assertions.clone();
        let stamp = executor.ctx.source_context_stamp();
        // isZero uses exponent/fraction only. Corrupting only this cached sign
        // does not change its already-defined clauses or SAT result, but must
        // prevent publication of a purported complete FP model.
        let state = executor.incr_fp_state.as_mut().unwrap();
        assert!(state.persistent_sat.is_some());
        assert_eq!(state.fp_cache.term_to_fp.len(), 1);
        state.fp_cache.term_to_fp.values_mut().next().unwrap().sign = 0;
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        let extracted = Cell::new(0);
        let committed = Cell::new(0);
        let result = executor
            .try_solve_fp_incremental_observed(&|phase| match phase {
                IncrementalFpPhase::ModelExtracted => {
                    extracted.set(extracted.get() + 1);
                    flag.store(interrupting, Ordering::Relaxed);
                }
                IncrementalFpPhase::Commit => {
                    committed.set(committed.get() + 1);
                    flag.store(false, Ordering::Relaxed);
                }
                _ => {}
            })
            .unwrap();
        assert!(matches!(result, Some(SolveResult::Unknown)));
        assert_eq!(extracted.get(), 1);
        assert_eq!(committed.get(), 1);
        let origin = if interrupting {
            UnknownOrigin::InterruptFlag
        } else {
            UnknownOrigin::IncompleteSolverLane
        };
        revoked(&executor, origin);
        shell(&executor, 1);
        assert_eq!(executor.fp_recorded_resource_stop(), interrupting);
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(executor.ctx.source_context_stamp(), stamp);
        assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
    }
}
