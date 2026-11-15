// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[path = "tests/completed_check.rs"]
mod completed_check;
mod native_datatype;
#[path = "tests/presentation.rs"]
mod presentation;

const UNSAT: &str = "(set-logic QF_LIA)\n\
    (declare-const x Int)\n\
    (assert (> x 5))\n\
    (assert (< x 3))\n\
    (check-sat)\n";

const SAT: &str = "(set-logic QF_LIA)\n\
    (declare-const x Int)\n\
    (assert (> x 5))\n\
    (check-sat)\n";

fn live_deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn bounded_certificate() -> StrictUnsatCert {
    smtlib_strict_unsat_cert_via_executor_until(UNSAT, live_deadline())
        .expect("live exact contradiction must retain native strict evidence")
}

#[test]
fn strict_absolute_adapter_refuses_expired_entry() {
    for script in [UNSAT, SAT, "(invalid unmatched"] {
        assert!(smtlib_strict_unsat_cert_via_executor_until(script, Instant::now()).is_none());
    }
}

#[test]
fn legacy_zero_and_absent_timeout_remain_unbounded() {
    assert_eq!(solver_config(None).timeout, None);
    assert_eq!(solver_config(Some(Duration::ZERO)).timeout, None);
    let duration = Duration::from_millis(123);
    assert_eq!(solver_config(Some(duration)).timeout, Some(duration));
    let cert = smtlib_strict_unsat_cert_via_executor(UNSAT, Some(Duration::ZERO))
        .expect("zero retains the legacy unset-timeout behavior");
    assert!(ay_dpll::api::re_check_bundle_strict(&cert.bundle)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn strict_solver_config_inherits_only_the_term_store_cap() {
    let duration = Duration::from_millis(123);
    for cap in [None, Some(0), Some(1), Some(usize::MAX)] {
        let _scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(cap);
        for timeout in [None, Some(Duration::ZERO), Some(duration)] {
            let config = solver_config(timeout);
            assert_eq!(config.term_memory_limit, cap);
            assert_eq!(config.memory_limit, None);
            assert_eq!(config.timeout, timeout.filter(|timeout| !timeout.is_zero()));
            assert_eq!(config.learned_clause_limit, None);
            assert_eq!(config.clause_db_bytes_limit, None);
        }
    }
}

#[test]
fn strict_absolute_adapter_retains_exact_independent_proof_checks() {
    let cert = bounded_certificate();
    assert!(matches!(
        cert.strict_verdict,
        ay_dpll::api::StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    let checked = ay_dpll::api::re_check_bundle_strict(&cert.bundle)
        .expect("returned native bundle must independently replay");
    assert!(checked.quality.is_complete());
    assert_eq!(cert.bundle.obligation_assertions.len(), 2);
    assert_eq!(
        ordered_unique_assumes(&checked.assume_terms),
        cert.bundle.obligation_assertions
    );
}

#[test]
fn strict_absolute_adapter_rejects_satisfiable_neighbor() {
    assert!(smtlib_strict_unsat_cert_via_executor_until(SAT, live_deadline()).is_none());
}

#[test]
fn strict_absolute_bundle_still_rejects_source_and_proof_mutations() {
    let cert = bounded_certificate();
    let mut missing_source = cert.bundle.clone();
    missing_source.obligation_assertions.clear();
    assert!(ay_dpll::api::re_check_bundle_strict(&missing_source).is_err());
    let mut missing_step = cert.bundle;
    missing_step.steps.pop().expect("nonempty fixture proof");
    assert!(ay_dpll::api::re_check_bundle_strict(&missing_step).is_err());
}

#[test]
fn bounded_query_rejects_script_timeout_but_legacy_shape_is_unchanged() {
    for value in ["0", "1", "60000"] {
        let script = format!("(set-option :timeout {value})\n(assert false)\n(check-sat)\n");
        assert!(parse_plain_query(&script, ReplayLimit::Legacy).is_some());
        assert!(parse_plain_query(&script, ReplayLimit::Until(live_deadline())).is_none());
        assert!(smtlib_strict_unsat_cert_via_executor_until(&script, live_deadline()).is_none());
    }
}

#[test]
fn timeout_classifier_handles_attribute_shape_and_exact_keyword() {
    for keyword in [":timeout", "timeout"] {
        assert!(is_timeout_override(
            &ay_frontend::Command::SetOptionAttribute(keyword.into())
        ));
    }
    for keyword in [":timeout-extra", ":max-memory", ":produce-proofs"] {
        assert!(!is_timeout_override(
            &ay_frontend::Command::SetOptionAttribute(keyword.into())
        ));
    }
    assert!(!is_timeout_override(&ay_frontend::Command::CheckSat));
}

#[test]
fn bounded_query_preserves_plain_shape_and_source_text() {
    let script = format!("{UNSAT}(exit)\n");
    let legacy = parse_plain_query(&script, ReplayLimit::Legacy).unwrap();
    let bounded = parse_plain_query(&script, ReplayLimit::Until(live_deadline())).unwrap();
    assert_eq!(legacy.logic, bounded.logic);
    assert_eq!(legacy.body, bounded.body);
    assert!(bounded.body.contains("(assert (> x 5))"));
    assert!(bounded.body.contains("(assert (< x 3))"));
}

#[test]
fn bounded_query_keeps_rejecting_non_plain_authority() {
    for script in [
        "(assert false) (check-sat) (check-sat)",
        "(assert true) (check-sat) (assert false)",
        "(assert false) (check-sat-assuming ())",
        "(assert false) (assert-soft true :weight 1) (check-sat)",
        "(assert false) (minimize 0) (check-sat)",
        "(assert false) (set-logic QF_LIA) (check-sat)",
    ] {
        assert!(parse_plain_query(script, ReplayLimit::Legacy).is_none());
        assert!(parse_plain_query(script, ReplayLimit::Until(live_deadline())).is_none());
    }
}

#[test]
fn strict_cancellable_adapter_refuses_inherited_precancel() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child().child());
    parent.cancel();
    for script in [UNSAT, SAT, "(invalid unmatched"] {
        let limit = ReplayLimit::Cancellable {
            deadline: live_deadline(),
            cancellation: &cancellation,
        };
        assert!(smtlib_strict_unsat_cert_via_executor_with_limit(script, limit).is_none());
    }
    parent.reset();
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    assert!(smtlib_strict_unsat_cert_via_executor_with_limit(UNSAT, limit).is_none());
}

#[test]
fn strict_cancellable_adapter_keeps_live_exact_proof_authority() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    let cert = smtlib_strict_unsat_cert_via_executor_with_limit(UNSAT, limit)
        .expect("live owned cancellation must not change native strict acceptance");
    let checked = ay_dpll::api::re_check_bundle_strict(&cert.bundle).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(
        ordered_unique_assumes(&checked.assume_terms),
        cert.bundle.obligation_assertions
    );
    assert!(!cancellation.is_cancelled());
    assert!(!parent.is_cancelled());
    let mut mutated = cert.bundle;
    mutated.obligation_assertions.clear();
    assert!(ay_dpll::api::re_check_bundle_strict(&mutated).is_err());
}

#[test]
fn strict_cancellable_adapter_rejects_sat_and_timeout_override() {
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    for script in [SAT, "(set-option :timeout 0) (assert false) (check-sat)"] {
        let limit = ReplayLimit::Cancellable {
            deadline: live_deadline(),
            cancellation: &cancellation,
        };
        assert!(smtlib_strict_unsat_cert_via_executor_with_limit(script, limit).is_none());
    }
    assert!(!token.is_cancelled());
}
