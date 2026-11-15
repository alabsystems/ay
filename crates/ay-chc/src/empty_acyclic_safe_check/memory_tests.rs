// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::resource_observation::{ResourceRefusal, ScopedResourceObservation};

#[test]
fn raw_independent_executor_carries_finite_cap_and_latches_before_cleanup() {
    let observation = ScopedResourceObservation::install();
    let _cap = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(1));
    let result = decide(
        "(set-logic QF_LIA) (declare-const memory_unique Int) (assert (= memory_unique 0)) (check-sat)",
        Instant::now() + Duration::from_secs(20), None,
    );
    assert_eq!(result, Err(NotConfirmed::Budget));
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
}
