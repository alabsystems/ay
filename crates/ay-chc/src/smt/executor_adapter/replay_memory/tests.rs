// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn explicit_and_inherited_caps_take_the_minimum_without_reinterpreting_zero() {
    for inherited in [None, Some(0), Some(7), Some(usize::MAX)] {
        let _scope = SmtContext::scoped_thread_term_memory_budget(inherited);
        for explicit in [None, Some(0), Some(3), Some(11), Some(usize::MAX)] {
            let expected = match (explicit, inherited) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            };
            assert_eq!(ReplayMemory::capture(explicit).term_limit(), expected);
        }
    }
}

#[test]
fn captured_zero_refuses_work_even_after_its_thread_scope_is_restored() {
    let _outer = SmtContext::scoped_thread_term_memory_budget(None);
    let bounded = {
        let _zero = SmtContext::scoped_thread_term_memory_budget(Some(0));
        ReplayMemory::capture(Some(usize::MAX))
    };
    let calls = Cell::new(0);
    assert!(bounded
        .phase(|| {
            calls.set(calls.get() + 1);
            Some(())
        })
        .is_none());
    assert_eq!(calls.get(), 0);
    assert_eq!(SmtContext::current_thread_term_memory_budget(), None);
    assert!(ReplayMemory::capture(None).phase(|| Some(())).is_some());
}

#[test]
fn exact_store_boundary_is_inclusive_and_does_not_reset_live_accounting() {
    let _scope = SmtContext::scoped_thread_term_memory_budget(None);
    let terms = ay_core::TermStore::new();
    let bytes = terms.true_memory_bytes();
    assert!(bytes > 0);
    assert!(ReplayMemory::capture(Some(bytes))
        .check_terms(&terms)
        .is_some());
    assert!(ReplayMemory::capture(Some(bytes - 1))
        .check_terms(&terms)
        .is_none());
    assert_eq!(terms.true_memory_bytes(), bytes);
    assert!(ReplayMemory::capture(Some(bytes))
        .check_terms(&terms)
        .is_some());
}

#[test]
fn every_raw_entry_refuses_an_inherited_zero_before_solver_work() {
    use super::super::{
        check_unsat_smtlib_via_executor, smtlib_first_verdict_via_executor,
        smtlib_first_verdict_via_executor_until, smtlib_strict_unsat_cert_via_executor,
        smtlib_strict_unsat_cert_via_executor_until,
    };
    let _scope = SmtContext::scoped_thread_term_memory_budget(Some(0));
    let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(30);
    for script in ["(assert false) (check-sat)", "(check-sat)", "(invalid"] {
        assert!(!check_unsat_smtlib_via_executor(script));
        assert!(smtlib_first_verdict_via_executor(script, None).is_none());
        assert!(
            smtlib_first_verdict_via_executor_until(script, deadline, Some(usize::MAX)).is_none()
        );
        assert!(smtlib_strict_unsat_cert_via_executor(script, None).is_none());
        assert!(smtlib_strict_unsat_cert_via_executor_until(script, deadline).is_none());
    }
}
