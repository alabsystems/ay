// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn malformed_stateless_assignment_revokes_as_incomplete_unless_a_stop_wins() {
    for interrupting in [false, true] {
        let mut executor = simple();
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
        assert!(executor.last_model.is_some());
        let roots = executor.ctx.assertions.clone();
        let stamp = executor.ctx.source_context_stamp();
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        let stop = FpStop::from_executor(&executor);
        let prepared = prepare::prepare(&executor.ctx.terms, &roots, &stop, &|_| {})
            .unwrap_or_else(|_| panic!("the original scalar FP fixture must encode"));
        assert!(!prepared.encoding.cache.term_to_fp.is_empty());
        let extracted = Cell::new(0);
        let published = Cell::new(false);
        // Deliberately incomplete decoder input, not a claimed SAT witness.
        let result =
            executor
                .finish_fp_stateless(SatResult::Sat(Vec::new()), &prepared, &stop, &|phase| {
                    match phase {
                        FpPhase::ModelExtracted => {
                            extracted.set(extracted.get() + 1);
                            flag.store(interrupting, Ordering::Relaxed);
                        }
                        FpPhase::Publication => published.set(true),
                        _ => {}
                    }
                })
                .unwrap();
        assert!(result.is_unknown());
        assert_eq!(extracted.get(), 1);
        assert!(!published.get());
        let origin = if interrupting {
            UnknownOrigin::InterruptFlag
        } else {
            UnknownOrigin::IncompleteSolverLane
        };
        assert_revoked(&executor, origin);
        assert!(!executor.last_model_validated);
        assert_eq!(executor.fp_recorded_resource_stop(), interrupting);
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(executor.ctx.source_context_stamp(), stamp);
        flag.store(false, Ordering::Relaxed);
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
    }
}
