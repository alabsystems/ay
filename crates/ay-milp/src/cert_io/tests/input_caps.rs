// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE EMIT/VERIFY ASYMMETRY, pinned.
//!
//! This build can emit a `.ayc` that its own `parse` refuses to read: a
//! completed optimality tree on `khb05250` is ~655 MB and ~23 M lines, which
//! the old caps of 512 MiB and 8,000,000 lines refused (they are now 1 GiB and
//! 32,000,000 lines, since the `opttree` block is streamed; a larger tree can
//! still outgrow them). Until 2026-08-28 there was no test anywhere for either
//! cap, the emitter did not know they existed, and the
//! refusal came back as `REFUTED` — the checker publishing a verdict about
//! evidence it had not read, alongside a CLAIMS census naming nothing refuted.
//!
//! Both caps are enforced by the same `preflight_input`, so the LINE cap is
//! what these tests drive: 32,000,001 newlines is a 32 MB `String` and runs in
//! milliseconds, where the byte cap would need a 1 GiB allocation to say the
//! same thing about the same code path.

use super::*;

pub(super) fn oversize_input_is_unverified_not_refuted() {
    // One line over the line cap, and NOTHING else wrong with it: this is the
    // point. If the caps ever start reporting a grammar error, that is a
    // different (and false) claim about the artifact.
    let too_many_lines = "\n".repeat(MAX_AYC_INPUT_LINES);
    assert_eq!(
        too_many_lines.bytes().filter(|&b| b == b'\n').count() + 1,
        MAX_AYC_INPUT_LINES + 1,
        "the fixture must be exactly one line over the cap"
    );

    match parse(&too_many_lines) {
        Err(CertIoError::InputTooLarge {
            limit,
            actual,
            ref what,
        }) => {
            assert_eq!(limit, MAX_AYC_INPUT_LINES);
            assert_eq!(actual, MAX_AYC_INPUT_LINES + 1);
            assert!(
                what.contains("line parser cap"),
                "the error must name WHICH cap: {what}"
            );
        }
        other => panic!("expected InputTooLarge, got {other:?}"),
    }

    // THE VERDICT, which is the part that was wrong. `check` never reaches the
    // model, so the model text is irrelevant here — and that is exactly why
    // REFUTED was unearned.
    let report = check(&too_many_lines, "");
    assert_eq!(
        report.status(),
        CheckStatus::Unverified,
        "an input the checker did not read is UNVERIFIED, never REFUTED"
    );
    assert_ne!(report.status(), CheckStatus::Verified);
    assert!(
        report.status().exit_code() != 0,
        "still a non-zero exit: not reading it is not a pass"
    );
    assert!(
        report.notes().iter().any(|n| n.contains("NOT READ")),
        "the note must say the certificate was not read: {:?}",
        report.notes()
    );
    assert!(
        report
            .notes()
            .iter()
            .any(|n| n.contains("limit of THIS CHECKER")),
        "the note must attribute the refusal to the checker, not the artifact: {:?}",
        report.notes()
    );
    assert!(
        report.claims().is_empty(),
        "nothing was parsed, so no claim may be reported"
    );
}

pub(super) fn a_genuinely_malformed_certificate_is_still_refuted() {
    // THE CONTROL. The reclassification above must not have weakened the
    // ordinary path: something inside the caps that is not an AYC is still a
    // refutation, exit 20.
    let report = check("this is not a certificate\n", "");
    assert_eq!(
        report.status(),
        CheckStatus::Refuted,
        "an in-cap non-certificate is still REFUTED"
    );
    assert_eq!(report.status().exit_code(), 20);
}

pub(super) fn the_emitter_can_see_the_caps_the_parser_enforces() {
    // The asymmetry itself: before 2026-08-28 the emission side had no way to
    // ask this question at all.
    assert_eq!(MAX_AYC_INPUT_BYTES, 1024 * 1024 * 1024);
    assert!(parser_cap_excess("%AYC 1\n").is_none());

    let over_lines = "\n".repeat(MAX_AYC_INPUT_LINES);
    let why = parser_cap_excess(&over_lines).expect("an over-cap text is reported as over-cap");
    assert!(why.contains("line parser cap"), "{why}");
    assert!(
        why.contains(&(MAX_AYC_INPUT_LINES + 1).to_string()),
        "the warning must quote what actually arrived: {why}"
    );

    // The scan short-circuit must not create a blind spot: one byte under the
    // line cap cannot BE over the line cap (a line costs at least a newline),
    // and the boundary above is the exact case where the scan must still run.
    let just_under = "\n".repeat(MAX_AYC_INPUT_LINES - 1);
    assert_eq!(
        just_under.bytes().filter(|&b| b == b'\n').count() + 1,
        MAX_AYC_INPUT_LINES,
        "the boundary fixture must sit exactly ON the cap"
    );
    assert!(
        parser_cap_excess(&just_under).is_none(),
        "exactly at the cap is inside it"
    );
}
