// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-free admission and cancellation tests for ground replay planning.

#![cfg(test)]

use super::*;
use crate::pdr::{ChcReplayObligation, ChcReplayObligationKind};
use std::cell::Cell;

mod dispatch;
mod validation;

fn artifact_error(reason: Reason) -> ArtifactError {
    ArtifactError {
        reason,
        reason_code: reason.code(),
        detail: "synthetic export refusal".to_owned(),
    }
}

fn obligations() -> Vec<ChcReplayObligation> {
    vec![ChcReplayObligation {
        name: "retained-trace".to_owned(),
        kind: ChcReplayObligationKind::TraceValidity,
        clause_index: 7,
        smtlib: "(assert true)\n(check-sat)\n".to_owned(),
    }]
}

fn retained_progress<'a>(callback: &'a mut dyn FnMut() -> bool) -> ChcResult<ReplayProgress<'a>> {
    ReplayProgress::new_retained_for_rows(
        ReplayLimit::Until(ay_core::time::Instant::now() + std::time::Duration::from_secs(60)),
        callback,
        1,
    )
}

fn live_progress<'a>(callback: &'a mut dyn FnMut() -> bool) -> ReplayProgress<'a> {
    retained_progress(callback).expect("live retained replay progress")
}

fn assert_interrupted<T>(result: ChcResult<T>) {
    let Err(error) = result else {
        panic!("interrupted work must not return a plan or validated evidence");
    };
    assert!(
        error.to_string().contains("interrupted"),
        "expected interruption, got {error}"
    );
}

fn assert_ground(plan: CheckedReplayPlan, expected_format: Format, expected_bytes: &[u8]) {
    let CheckedReplayPlan::GroundDerivation {
        format,
        artifact_bytes,
    } = plan
    else {
        panic!("ground export must not become an SMT plan");
    };
    assert_eq!(format, expected_format);
    assert_eq!(artifact_bytes, expected_bytes);
}

fn assert_smt(plan: CheckedReplayPlan) {
    let CheckedReplayPlan::Smt(actual) = plan else {
        panic!("legacy SMT fallback must remain an SMT plan");
    };
    assert_eq!(actual, obligations());
}

#[test]
fn precancellation_precedes_export_and_fallback_for_every_selection() {
    for preferred in [
        None,
        Some(Format::SmtlibV1),
        Some(Format::GroundDerivationV1),
        Some(Format::GroundDerivationV2),
    ] {
        let allowed = Cell::new(true);
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            allowed.get()
        };
        let mut progress = live_progress(&mut callback);
        allowed.set(false);
        assert_interrupted(select_plan(
            preferred,
            |_, _| panic!("pre-refusal must prevent export"),
            || panic!("pre-refusal must prevent fallback"),
            &mut progress,
        ));
        let stopped_at = calls.get();
        assert_interrupted(progress.check());
        assert!(!progress.poll());
        assert_eq!(calls.get(), stopped_at, "a refusal remains sticky");
    }
}

#[test]
fn typed_export_interruption_is_terminal_even_with_misleading_diagnostics() {
    for preferred in [
        Format::SmtlibV1,
        Format::GroundDerivationV1,
        Format::GroundDerivationV2,
    ] {
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let mut progress = live_progress(&mut callback);
        let mut exported = Vec::new();
        assert_interrupted(select_plan(
            Some(preferred),
            |format, _| {
                exported.push(format);
                let mut error = artifact_error(Reason::Interrupted);
                error.reason_code = "unsupported_uninterpreted_function";
                error.detail = "ordinary rejection diagnostic".to_owned();
                Err(error)
            },
            || panic!("typed interruption must not invoke SMT fallback"),
            &mut progress,
        ));
        let expected = if preferred == Format::SmtlibV1 {
            Format::GroundDerivationV1
        } else {
            preferred
        };
        assert_eq!(exported, [expected], "interruption must not probe V2");
        let stopped_at = calls.get();
        assert_interrupted(progress.check());
        assert_eq!(calls.get(), stopped_at);
    }
}

#[test]
fn typed_v2_interruption_after_ordinary_v1_rejection_never_falls_back() {
    let mut callback = || true;
    let mut progress = live_progress(&mut callback);
    let mut exported = Vec::new();
    assert_interrupted(select_plan(
        Some(Format::SmtlibV1),
        |format, _| {
            exported.push(format);
            Err(artifact_error(if format == Format::GroundDerivationV1 {
                Reason::UnsupportedUninterpretedFunction
            } else {
                Reason::Interrupted
            }))
        },
        || panic!("V2 interruption must not invoke SMT fallback"),
        &mut progress,
    ));
    assert_eq!(
        exported,
        [Format::GroundDerivationV1, Format::GroundDerivationV2]
    );
    assert!(!progress.poll());
}

#[test]
fn exporter_cannot_ignore_a_one_time_callback_refusal_and_publish_bytes() {
    let allowed = Cell::new(true);
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allowed.get()
    };
    let mut progress = live_progress(&mut callback);
    assert_interrupted(select_plan(
        Some(Format::SmtlibV1),
        |format, poll| {
            assert_eq!(format, Format::GroundDerivationV1);
            allowed.set(false);
            assert!(!poll());
            assert!(!poll(), "export-local retries cannot revive progress");
            Ok(Some(b"must not escape".to_vec()))
        },
        || panic!("ignored callback refusal must not invoke fallback"),
        &mut progress,
    ));
    let stopped_at = calls.get();
    assert!(!progress.poll());
    assert_eq!(calls.get(), stopped_at);
}

#[test]
fn refusal_after_opaque_export_precedes_every_return_shape() {
    for result in [
        Ok(Some(b"opaque bytes".to_vec())),
        Ok(None),
        Err(artifact_error(Reason::UnsupportedUninterpretedFunction)),
    ] {
        let allowance = Cell::new(true);
        let mut callback = || allowance.get();
        let mut progress = live_progress(&mut callback);
        let mut result = Some(result);
        assert_interrupted(select_plan(
            Some(Format::SmtlibV1),
            |_, _| {
                allowance.set(false);
                result.take().expect("export must run only once")
            },
            || panic!("post-export refusal must precede SMT fallback"),
            &mut progress,
        ));
        allowance.set(true);
        assert_interrupted(progress.check());
    }
}

#[test]
fn refusal_after_opaque_fallback_precedes_success_and_ordinary_error() {
    for fallback_result in [
        Ok(obligations()),
        Err(verification_error("ordinary fallback error")),
    ] {
        let allowance = Cell::new(true);
        let mut callback = || allowance.get();
        let mut progress = live_progress(&mut callback);
        assert_interrupted(select_plan(
            None,
            |_, _| panic!("explicit SMT selection must not export ground bytes"),
            || {
                allowance.set(false);
                fallback_result
            },
            &mut progress,
        ));
        allowance.set(true);
        assert!(!progress.poll());
    }
}

#[test]
fn every_default_upgrade_boundary_including_publication_is_interruptible() {
    let run = |stop_at: usize, calls: &Cell<usize>| {
        let armed = Cell::new(false);
        let mut callback = || {
            if !armed.get() {
                return true;
            }
            calls.set(calls.get() + 1);
            calls.get() != stop_at
        };
        let mut progress = live_progress(&mut callback);
        armed.set(true);
        select_plan(
            Some(Format::SmtlibV1),
            |format, _| match format {
                Format::GroundDerivationV1 => {
                    Err(artifact_error(Reason::UnsupportedUninterpretedFunction))
                }
                Format::GroundDerivationV2 => Ok(Some(b"v2 bytes".to_vec())),
                Format::SmtlibV1 | Format::CompactGroundDerivationV1 => {
                    panic!("not a recursive ground export format")
                }
            },
            || panic!("upgrade success or interruption must never invoke fallback"),
            &mut progress,
        )
    };
    let total = Cell::new(0);
    assert_ground(
        run(usize::MAX, &total).expect("live upgrade"),
        Format::GroundDerivationV2,
        b"v2 bytes",
    );
    assert!(
        total.get() >= 6,
        "must cover both exports and final plan admission"
    );
    for stop_at in 1..=total.get() {
        let calls = Cell::new(0);
        assert_interrupted(run(stop_at, &calls));
        assert_eq!(calls.get(), stop_at, "no callback after refusal {stop_at}");
    }
}

#[test]
fn a_callback_panic_caught_by_an_inner_exporter_cannot_enable_fallback() {
    for outcome in [
        Err(artifact_error(Reason::ValidationPanicked)),
        Ok(Some(vec![1, 2, 3])),
    ] {
        let calls = std::cell::Cell::new(0);
        let panic_now = Cell::new(false);
        let mut callback = || {
            calls.set(calls.get() + 1);
            assert!(
                !panic_now.get(),
                "ordinary caller panic caught by the simulated inner guard"
            );
            true
        };
        let mut progress = live_progress(&mut callback);
        let mut exports = 0;
        let result = select_plan(
            Some(Format::SmtlibV1),
            |format, callback| {
                exports += 1;
                assert_eq!(format, Format::GroundDerivationV1);
                panic_now.set(true);
                assert!(
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| callback())).is_err()
                );
                // Simulate either a converted validation error or a lying
                // success. Neither may restart progress after the panic.
                outcome.clone()
            },
            || panic!("a caught callback panic must not select SMT fallback"),
            &mut progress,
        );
        assert_interrupted(result);
        assert_eq!(exports, 1);
        let stopped_at = calls.get();
        assert!(!progress.poll());
        assert_eq!(
            calls.get(),
            stopped_at,
            "a caught panic cannot resume the callback"
        );
    }
}
