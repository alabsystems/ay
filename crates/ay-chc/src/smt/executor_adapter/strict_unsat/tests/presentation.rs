// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn native_only_skips_renderer_but_existing_adapters_keep_diagnostics() {
    let rendered = Cell::new(0);
    for (mode, expected) in [
        (StrictPresentation::NativeOnly, None),
        (
            StrictPresentation::WithAletheDiagnostic,
            Some("diagnostic".to_string()),
        ),
    ] {
        let actual = optional_presentation(mode, ReplayLimit::Until(live_deadline()), || {
            rendered.set(rendered.get() + 1);
            Some("diagnostic".to_string())
        });
        assert_eq!(actual, expected);
    }
    assert_eq!(rendered.get(), 1, "native-only must not call the renderer");
    // Exercise the actual adapter too, not just the injected dispatch seam.
    let native =
        smtlib_strict_unsat_cert_native_only_with_limit(UNSAT, ReplayLimit::Until(live_deadline()))
            .unwrap();
    assert!(native.alethe.is_none());
    let diagnostic = smtlib_strict_unsat_cert_via_executor_with_limit(
        UNSAT,
        ReplayLimit::Until(live_deadline()),
    )
    .unwrap();
    assert!(
        diagnostic.alethe.is_some(),
        "the existing simple-LIA adapter still emits its diagnostic"
    );
    let legacy = smtlib_strict_unsat_cert_via_executor(UNSAT, None).unwrap();
    assert!(legacy.alethe.is_some());
    assert_eq!(
        serde_json::to_vec(&native.bundle).unwrap(),
        serde_json::to_vec(&diagnostic.bundle).unwrap()
    );
    assert_eq!(
        native.bundle.obligation_assertions,
        diagnostic.bundle.obligation_assertions
    );
    let checked = ay_dpll::api::re_check_bundle_strict(&native.bundle).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(
        ordered_unique_assumes(&checked.assume_terms),
        native.bundle.obligation_assertions
    );
}

#[test]
fn native_only_preserves_exact_source_and_proof_mutation_refusal() {
    let cert =
        smtlib_strict_unsat_cert_native_only_with_limit(UNSAT, ReplayLimit::Until(live_deadline()))
            .unwrap();
    let bytes = serde_json::to_vec(&cert.bundle).unwrap();
    let roundtrip: ay_dpll::api::SerializableProofBundle = serde_json::from_slice(&bytes).unwrap();
    assert!(ay_dpll::api::re_check_bundle_strict(&roundtrip)
        .unwrap()
        .quality
        .is_complete());
    let mut missing_source = roundtrip.clone();
    missing_source.obligation_assertions.clear();
    assert!(ay_dpll::api::re_check_bundle_strict(&missing_source).is_err());
    let mut missing_step = roundtrip;
    missing_step.steps.pop().expect("nonempty real proof");
    assert!(ay_dpll::api::re_check_bundle_strict(&missing_step).is_err());
    for script in [
        SAT,
        "(assert false) (check-sat) (check-sat)",
        "(set-option :timeout 0) (assert false) (check-sat)",
    ] {
        assert!(smtlib_strict_unsat_cert_native_only_with_limit(
            script,
            ReplayLimit::Until(live_deadline())
        )
        .is_none());
    }
}

#[test]
fn native_only_keeps_expired_cancelled_and_memory_refusals_terminal() {
    for mode in [
        StrictPresentation::NativeOnly,
        StrictPresentation::WithAletheDiagnostic,
    ] {
        let called = Cell::new(false);
        assert!(
            optional_presentation(mode, ReplayLimit::Until(Instant::now()), || {
                called.set(true);
                Some("too late".into())
            })
            .is_none()
        );
        assert!(!called.get());
    }
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(
        UNSAT,
        ReplayLimit::Until(Instant::now())
    )
    .is_none());
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    parent.cancel();
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(UNSAT, limit).is_none());
    parent.reset();
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(UNSAT, limit).is_none());
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(
        UNSAT,
        ReplayLimit::Until(live_deadline())
    )
    .is_none());
}

#[test]
fn presentation_after_a_completed_check_never_refuses_it() {
    // #completed-check-accepted: presentation runs after the native check
    // completed. A stop during rendering keeps what was rendered; a stop
    // before it omits the text. Neither is a refusal of the certificate (the
    // return type no longer has one).
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    assert_eq!(
        optional_presentation(StrictPresentation::WithAletheDiagnostic, limit, || {
            parent.cancel();
            Some("completed after cancellation".into())
        }),
        Some("completed after cancellation".into())
    );
    assert_eq!(
        optional_presentation(StrictPresentation::WithAletheDiagnostic, limit, || panic!(
            "a cancelled limit must not start the renderer"
        )),
        None
    );
    assert_eq!(
        optional_presentation(StrictPresentation::NativeOnly, limit, || panic!(
            "not invoked"
        )),
        None
    );
}

#[test]
fn native_only_does_not_disable_explicit_source_strict_wire_policy() {
    // This established datatype fixture has native authority but its optional
    // external presentation is not enough to meet an explicit strict-wire ask.
    let source = "(declare-datatype D ((a) (b))) (declare-const x D) \
        (assert (= x a)) (assert (= x b)) (check-sat)";
    let native = smtlib_strict_unsat_cert_native_only_with_limit(
        source,
        ReplayLimit::Until(live_deadline()),
    )
    .unwrap();
    assert!(native.alethe.is_none());
    assert!(ay_dpll::api::re_check_bundle_strict(&native.bundle)
        .unwrap()
        .quality
        .is_complete());
    let wire = format!("(set-option :check-proofs-strict true) {source}");
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(
        &wire,
        ReplayLimit::Until(live_deadline())
    )
    .is_none());
    // A supported explicit wire request still succeeds; no blanket rejection.
    let wire = UNSAT.replace(
        "(declare-const",
        "(set-option :check-proofs-strict true)\n(declare-const",
    );
    assert!(smtlib_strict_unsat_cert_native_only_with_limit(
        &wire,
        ReplayLimit::Until(live_deadline())
    )
    .is_some());
}
