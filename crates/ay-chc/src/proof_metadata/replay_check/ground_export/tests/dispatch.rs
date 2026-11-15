// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Always-continue selection retains formats, bytes, fallback and diagnostics.

#![cfg(test)]

use super::*;

#[test]
fn explicit_ground_formats_and_default_v1_retain_exact_payloads() {
    for preferred in [
        Format::GroundDerivationV1,
        Format::GroundDerivationV2,
        Format::SmtlibV1,
    ] {
        let mut callback = || true;
        let mut progress = ReplayProgress::new(&mut callback);
        let mut exported = Vec::new();
        let plan = select_plan(
            Some(preferred),
            |format, poll| {
                exported.push(format);
                assert!(poll());
                Ok(Some(vec![0, 255, 17, 0]))
            },
            || panic!("ground success must not run SMT fallback"),
            &mut progress,
        )
        .expect("live ground export");
        let expected = if preferred == Format::SmtlibV1 {
            Format::GroundDerivationV1
        } else {
            preferred
        };
        assert_eq!(exported, [expected]);
        assert_ground(plan, expected, &[0, 255, 17, 0]);
    }
}

#[test]
fn ordinary_v1_rejection_upgrades_even_with_interruption_text() {
    let mut callback = || true;
    let mut progress = ReplayProgress::new(&mut callback);
    let mut exported = Vec::new();
    let plan = select_plan(
        Some(Format::SmtlibV1),
        |format, _| {
            exported.push(format);
            if format == Format::GroundDerivationV1 {
                let mut error = artifact_error(Reason::UnsupportedUninterpretedFunction);
                error.reason_code = "interrupted";
                error.detail =
                    "diagnostic mentions interrupted, but typed reason is ordinary".to_owned();
                Err(error)
            } else {
                Ok(Some(b"finite UF observations".to_vec()))
            }
        },
        || panic!("successful V2 upgrade must not invoke fallback"),
        &mut progress,
    )
    .expect("typed ordinary rejection permits upgrade");
    assert_eq!(
        exported,
        [Format::GroundDerivationV1, Format::GroundDerivationV2]
    );
    assert_ground(plan, Format::GroundDerivationV2, b"finite UF observations");
}

#[test]
fn explicit_smt_and_absent_ground_payloads_preserve_single_fallback() {
    for preferred in [
        None,
        Some(Format::SmtlibV1),
        Some(Format::GroundDerivationV1),
        Some(Format::GroundDerivationV2),
    ] {
        let mut callback = || true;
        let mut progress = ReplayProgress::new(&mut callback);
        let mut exported = Vec::new();
        let fallbacks = Cell::new(0);
        let plan = select_plan(
            preferred,
            |format, _| {
                exported.push(format);
                Ok(None)
            },
            || {
                fallbacks.set(fallbacks.get() + 1);
                Ok(obligations())
            },
            &mut progress,
        )
        .expect("absent ground evidence retains legacy trace fallback");
        let expected: Vec<_> = preferred
            .map(|format| {
                if format == Format::SmtlibV1 {
                    Format::GroundDerivationV1
                } else {
                    format
                }
            })
            .into_iter()
            .collect();
        assert_eq!(exported, expected, "absence must not trigger V2 probing");
        assert_eq!(fallbacks.get(), 1);
        assert_smt(plan);
    }
}

#[test]
fn ordinary_rejections_preserve_smt_fallback_without_explicit_version_probing() {
    for preferred in [
        Format::GroundDerivationV1,
        Format::GroundDerivationV2,
        Format::SmtlibV1,
    ] {
        let mut callback = || true;
        let mut progress = ReplayProgress::new(&mut callback);
        let mut exported = Vec::new();
        let plan = select_plan(
            Some(preferred),
            |format, _| {
                exported.push(format);
                Err(artifact_error(Reason::UnsupportedUninterpretedFunction))
            },
            || Ok(obligations()),
            &mut progress,
        )
        .expect("ordinary export rejection permits the legacy SMT trace");
        let expected = if preferred == Format::SmtlibV1 {
            vec![Format::GroundDerivationV1, Format::GroundDerivationV2]
        } else {
            vec![preferred]
        };
        assert_eq!(exported, expected);
        assert_smt(plan);
    }
}

#[test]
fn absent_payload_preserves_the_original_fallback_error() {
    for preferred in [
        None,
        Some(Format::GroundDerivationV1),
        Some(Format::SmtlibV1),
    ] {
        let mut callback = || true;
        let mut progress = ReplayProgress::new(&mut callback);
        let result = select_plan(
            preferred,
            |_, _| Ok(None),
            || Err(crate::ChcError::Parse("original trace error".to_owned())),
            &mut progress,
        );
        assert!(
            matches!(result, Err(crate::ChcError::Parse(detail)) if detail == "original trace error")
        );
    }
}

#[test]
fn failed_upgrade_keeps_both_reasons_and_absent_v2_keeps_v1_reason() {
    for v2_absent in [false, true] {
        let mut callback = || true;
        let mut progress = ReplayProgress::new(&mut callback);
        let mut exported = Vec::new();
        let result = select_plan(
            Some(Format::SmtlibV1),
            |format, _| {
                exported.push(format);
                if format == Format::GroundDerivationV2 && v2_absent {
                    return Ok(None);
                }
                let mut error = artifact_error(Reason::UnsupportedUninterpretedFunction);
                error.detail = if format == Format::GroundDerivationV1 {
                    "first refusal"
                } else {
                    "second refusal"
                }
                .to_owned();
                Err(error)
            },
            || Err(verification_error("trace refusal")),
            &mut progress,
        );
        let Err(error) = result else {
            panic!("failed exports and fallback cannot produce a plan");
        };
        let message = error.to_string();
        assert!(message.contains("first refusal") && message.contains("trace refusal"));
        assert_eq!(message.contains("second refusal"), !v2_absent);
        assert_eq!(
            exported,
            [Format::GroundDerivationV1, Format::GroundDerivationV2]
        );
    }
}
