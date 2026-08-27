// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
fn assert_checked_run_invariants(checked: &super::ChcCheckedReplayRun) {
    assert!(checked.manifest().trust_full_verifier_admissible());
    assert_eq!(
        checked.manifest().cache_admission_status(),
        "admit-checked-proof-evidence"
    );
    let metadata = checked.proof_run().metadata();
    let summary = checked.summary();
    assert!(metadata.trust_full_verifier_admissible());
    assert_eq!(metadata.replay_status(), "replayable");
    assert_eq!(metadata.transcript_status(), "replayable");
    assert!(metadata
        .trust_full_verifier_non_admission_reason()
        .is_none());

    let transcript_sha256 = metadata
        .checked_transcript_sha256()
        .expect("checked metadata should carry the transcript digest");
    let replay_log_sha256 = metadata
        .checked_replay_log_sha256()
        .expect("checked metadata should carry the replay-log digest");
    let checked_report_sha256 = metadata
        .checked_report_sha256()
        .expect("checked metadata should carry the report digest");
    assert!(is_lower_sha256(transcript_sha256));
    assert!(is_lower_sha256(replay_log_sha256));
    assert!(is_lower_sha256(checked_report_sha256));
    assert_eq!(
        checked_report_sha256,
        sha256_hex(checked.checked_report_bytes())
    );
    assert_eq!(replay_log_sha256, sha256_hex(checked.replay_log_bytes()));
    if let Some(run_log_bytes) = checked.run_log_bytes() {
        assert_eq!(transcript_sha256, sha256_hex(run_log_bytes));
    }
    assert_eq!(
        metadata
            .checked_summary_identity_sha256()
            .expect("checked metadata should carry the summary identity"),
        summary.identity_sha256()
    );
    assert_eq!(summary.problem.sha256, sha256_hex(checked.problem_bytes()));
    assert_eq!(
        summary.certificate.sha256,
        sha256_hex(checked.certificate_bytes())
    );
    assert_eq!(summary.replay_log.sha256, replay_log_sha256);
    assert_eq!(
        summary.problem.sha256,
        checked.proof_run().problem().normalized_input_sha256()
    );
    assert_eq!(
        checked.manifest().checked_replay_summary(),
        Some(summary),
        "the admitted manifest must carry this exact checked summary"
    );
}
