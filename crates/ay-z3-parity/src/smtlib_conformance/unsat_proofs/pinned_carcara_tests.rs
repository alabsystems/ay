// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The UNSAT proof gate refuses a Carcara `valid` over a proof on which that
//! verdict is not evidence (`ay_core::pinned_carcara`): both when it runs the
//! checker (`checker_fixture_row`) and when it re-reads a stored receipt
//! (`validate_receipt_rows`).

use super::*;
use ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF;

const CLEAN_PROOF: &str = "(assume t0 p)\n(step t1 (cl) :rule resolution :premises (t0))\n";

fn observation() -> ProcessObservation {
    ProcessObservation {
        stdin_complete: true,
        timed_out: false,
        memout: false,
        stdout_truncated: false,
        stderr_truncated: false,
    }
}

/// Pinned Carcara's transcript for a proof it accepts: exit 0, `valid`, no
/// stderr.
fn clean_valid_transcript() -> CapturedProcess {
    CapturedProcess {
        stdout: "valid\n".to_string(),
        stderr: String::new(),
        stdout_valid: true,
        stderr_valid: true,
        exit_code: Some(0),
        success: true,
        process: observation(),
    }
}

fn case(id: String, input_sha256: String, outcome: ValidatorCaseOutcome) -> ValidatorCase {
    ValidatorCase {
        id,
        input_sha256,
        expected: String::new(),
        observed: String::new(),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome,
    }
}

/// A receipt whose every binding is consistent and whose only passing row is
/// the first fixture's Carcara replay, a clean literal `valid` over `proof`
/// (the retained proof bytes, or none).
fn receipt_passing_the_first_replay(proof: Option<&str>) -> Vec<ValidatorCase> {
    let mut rows = vec![case(
        "carcara.identity".to_string(),
        checker_identity_input_sha(CARCARA_SHA256, CARCARA_VERSION_OUTPUT),
        ValidatorCaseOutcome::Fail,
    )];
    for (index, fixture) in FIXTURES.into_iter().enumerate() {
        let problem = fixture.problem.as_bytes();
        let retained = if index == 0 { proof } else { None };
        let proof_sha = retained.map_or_else(
            || missing_proof_sha(fixture),
            |text| sha256_bytes(text.as_bytes()),
        );
        rows.push(case(
            format!("fixture.{}.ay", fixture.id),
            sha256_bytes(problem),
            ValidatorCaseOutcome::Fail,
        ));
        let mut checker = case(
            format!("fixture.{}.carcara", fixture.id),
            checker_binding_sha(problem, &proof_sha),
            ValidatorCaseOutcome::Unavailable,
        );
        if index == 0 {
            checker.outcome = ValidatorCaseOutcome::Pass;
            checker.stdout = Some("valid\n".to_string());
            checker.stderr = Some(String::new());
            checker.exit_code = Some(0);
            checker.process = Some(observation());
        }
        rows.push(checker);
        let mut proof_row = case(
            format!("fixture.{}.proof", fixture.id),
            proof_binding_sha(problem, &proof_sha),
            ValidatorCaseOutcome::Fail,
        );
        proof_row.stdout = retained.map(str::to_string);
        rows.push(proof_row);
    }
    if let Some(proof) = proof {
        let corrupted = corrupt_first_rule(proof.as_bytes()).expect("a rule to corrupt");
        rows.push(case(
            "control.corrupt-proof".to_string(),
            checker_binding_sha(FIXTURES[0].problem.as_bytes(), &sha256_bytes(&corrupted)),
            ValidatorCaseOutcome::Fail,
        ));
        rows.push(case(
            "control.foreign-problem".to_string(),
            checker_binding_sha(FOREIGN_PROBLEM.as_bytes(), &sha256_bytes(proof.as_bytes())),
            ValidatorCaseOutcome::Fail,
        ));
    } else {
        for id in ["control.corrupt-proof", "control.foreign-problem"] {
            rows.push(case(
                id.to_string(),
                String::new(),
                ValidatorCaseOutcome::Fail,
            ));
        }
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    rows
}

/// NEGATIVE CONTROL: a checker transcript that is a clean literal `valid`
/// does not pass the fixture when the proof rests on an `evaluate` step
/// pinned Carcara misjudges (it prints `valid` for this refutation of a
/// satisfiable problem); the same transcript over a clean proof passes.
#[test]
fn a_valid_transcript_over_a_misjudged_proof_fails_the_fixture() {
    let valid = clean_valid_transcript();
    let row = checker_fixture_row(
        FIXTURES[0],
        FALSE_VALID_CONTROL_PROOF.as_bytes(),
        clean_valid_transcript(),
    );
    assert_eq!(row.outcome, ValidatorCaseOutcome::Fail, "{}", row.observed);
    assert!(
        row.observed.ends_with(
            ";pinned-carcara-misjudged-evaluate-steps=1;pinned-carcara-misread-binders=0"
        ),
        "{}",
        row.observed
    );
    let row = checker_fixture_row(FIXTURES[0], CLEAN_PROOF.as_bytes(), valid);
    assert_eq!(row.outcome, ValidatorCaseOutcome::Pass, "{}", row.observed);
    assert!(
        row.observed.ends_with(";strict-verdict=valid"),
        "{}",
        row.observed
    );
}

/// NEGATIVE CONTROL for a stored receipt: a passing Carcara row is rejected
/// when the retained proof rests on an `evaluate` step pinned Carcara
/// misjudges, and when no proof was retained to scan at all; the same receipt
/// over a clean proof validates.
#[test]
fn a_receipt_counting_valid_over_a_misjudged_or_missing_proof_is_rejected() {
    assert_eq!(
        validate_receipt_rows(
            &receipt_passing_the_first_replay(Some(CLEAN_PROOF)),
            CARCARA_SHA256,
        ),
        Ok(())
    );
    let misjudged = validate_receipt_rows(
        &receipt_passing_the_first_replay(Some(FALSE_VALID_CONTROL_PROOF)),
        CARCARA_SHA256,
    )
    .expect_err("a valid over a misjudged proof");
    assert!(
        misjudged.contains("has invalid independent replay evidence"),
        "{misjudged}"
    );
    let missing = validate_receipt_rows(&receipt_passing_the_first_replay(None), CARCARA_SHA256)
        .expect_err("a valid over no retained proof");
    assert!(
        missing.contains("has invalid independent replay evidence"),
        "{missing}"
    );
}
