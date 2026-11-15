// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::parse;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn malformed_simple_fp_model_precedes_real_completion_and_preserves_stop_priority() {
    for interrupting in [false, true] {
        let mut executor = Executor::new();
        executor.execute_all(&parse(
            "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11)) (assert (fp.isZero x))"
        ).unwrap()).unwrap();
        let roots = executor.ctx.assertions.clone();
        let stamp = executor.ctx.source_context_stamp();
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        let stop = FpStop::from_executor(&executor);
        let encoding = executor
            .encode_fp_assertions_controlled(&roots, &[], &stop, &|_| {})
            .unwrap();
        assert!(!encoding.term_to_fp.is_empty());
        let extracted = Cell::new(0);
        let result = executor.finish_fp_simple(
            SatResult::Sat(Vec::new()),
            &encoding,
            &[],
            &stop,
            &|phase| {
                assert!(matches!(phase, FpRealPhase::ModelExtracted));
                extracted.set(extracted.get() + 1);
                flag.store(interrupting, Ordering::Relaxed);
            },
        );
        assert_eq!(extracted.get(), 1);
        if interrupting {
            assert!(matches!(
                result,
                Err(FpRealError::Stopped(UnknownOrigin::InterruptFlag))
            ));
            flag.store(false, Ordering::Relaxed);
            assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
        } else {
            assert!(matches!(result, Err(FpRealError::ModelDecode)));
            assert_eq!(stop.check(), Ok(()));
        }
        assert!(executor.last_model.is_none());
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(executor.ctx.source_context_stamp(), stamp);
    }
}
