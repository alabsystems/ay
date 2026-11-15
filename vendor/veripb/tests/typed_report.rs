// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The in-process consumer must distinguish checked claims from weaker runs.

use std::path::{Path, PathBuf};

use veripb::{CheckReport, RunOutcome, args::Args, check};
use veripb_checker::checked_result::{CheckedClaim, StatementAssurance};
use veripb_rules::{Bound, ConclusionResult};

fn corpus(name: &str) -> CheckReport {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/instances/correct/version3");
    check(Args {
        formula: root.join(format!("{name}.opb")),
        derivation: root.join(format!("{name}.pbp")),
        ..Args::default()
    })
    .expect("the existing positive corpus must check")
}

fn temporary_case(formula: &str, proof: &str) -> (tempfile::TempDir, Args) {
    let dir = tempfile::tempdir().unwrap();
    let formula_path = dir.path().join("formula.opb");
    let proof_path = dir.path().join("proof.pbp");
    std::fs::write(&formula_path, formula).unwrap();
    std::fs::write(&proof_path, proof).unwrap();
    (
        dir,
        Args {
            formula: formula_path,
            derivation: proof_path,
            ..Args::default()
        },
    )
}

#[test]
fn completed_bounds_are_typed_and_match_the_legacy_verdict() {
    let report = corpus("conclusion_BOUNDS");
    assert!(report.is_fully_verified());
    let statement = report.statements().last().unwrap();
    assert_eq!(statement.assurance(), StatementAssurance::Verified);
    match statement.claim() {
        CheckedClaim::Conclusion {
            result: ConclusionResult::Bounds,
            lower_bound_or_count: Some(Bound::Bounded(lower)),
            upper_bound: Some(Bound::Bounded(upper)),
        } => {
            assert_eq!(lower.to_string(), "2");
            assert_eq!(upper.to_string(), "2");
        }
        other => panic!("wrong typed claim: {other:?}"),
    }
    let mut text = Vec::new();
    report.write_to(&mut text).unwrap();
    assert_eq!(
        String::from_utf8(text).unwrap(),
        "s VERIFIED BOUNDS 2 <= obj <= 2\n"
    );
}

#[test]
fn no_conclusion_is_not_a_certificate() {
    let (_dir, args) = temporary_case(
        "1 x1 >= 1 ;\n",
        "pseudo-Boolean proof version 3.0\nf 1;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n",
    );
    let report = check(args).unwrap();
    assert_eq!(report.outcome(), RunOutcome::Verified);
    assert!(!report.is_fully_verified());
    assert!(matches!(
        report.statements()[0].claim(),
        CheckedClaim::Conclusion {
            result: ConclusionResult::None,
            ..
        }
    ));
}

#[test]
fn an_unproved_assertion_is_not_a_verified_certificate() {
    let report = corpus("conclusion_BOUNDS_optimal");
    assert_eq!(report.outcome(), RunOutcome::Verified);
    assert!(!report.is_fully_verified());
    assert!(
        report
            .statements()
            .iter()
            .any(|statement| statement.assurance() == StatementAssurance::UnderAssertions)
    );
}

#[test]
fn silent_and_explicit_weakening_remain_distinct_from_a_full_certificate() {
    let formula = "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n";
    let proof = "pseudo-Boolean proof version 3.0\nf 2;\nsol x1 x2;\ndel id 2;\noutput NONE;\nconclusion SAT;\nend pseudo-Boolean proof;\n";
    for unchecked in [false, true] {
        let proof = if unchecked {
            proof.replace("conclusion SAT;", "conclusion SAT : x1 x2;")
        } else {
            proof.to_owned()
        };
        let (_dir, mut args) = temporary_case(formula, &proof);
        args.unchecked_deletion = unchecked;
        let report = check(args).unwrap();
        assert!(!report.is_fully_verified());
        assert_eq!(
            report.statements()[0].assurance(),
            StatementAssurance::UnderWeakenedGuarantees
        );
        assert_eq!(
            report.outcome(),
            if unchecked {
                RunOutcome::Verified
            } else {
                RunOutcome::WeakenedGuarantees
            }
        );
    }
}

#[test]
fn unchecked_deletion_does_not_disqualify_a_sound_unsat_refutation() {
    let (_dir, mut args) = temporary_case(
        "1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n1 x2 >= 1 ;\n",
        "pseudo-Boolean proof version 3.0\nf 3;\ndel id 3;\nrup >= 1;\noutput NONE;\nconclusion UNSAT;\nend pseudo-Boolean proof;\n",
    );
    args.unchecked_deletion = true;
    let report = check(args).unwrap();
    assert!(report.is_fully_verified());
    assert_eq!(
        report.statements()[0].assurance(),
        StatementAssurance::Verified
    );
}

#[test]
fn a_false_step_after_a_valid_conclusion_returns_no_report() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/instances/correct/version3");
    let formula = std::fs::read_to_string(root.join("conclusion_BOUNDS.opb")).unwrap();
    let proof = std::fs::read_to_string(root.join("conclusion_BOUNDS.pbp"))
        .unwrap()
        .replace(
            "end pseudo-Boolean proof;",
            "rup >= 1;\nend pseudo-Boolean proof;",
        );
    let (_dir, args) = temporary_case(&formula, &proof);
    assert!(check(args).is_err());
}

#[test]
fn report_output_failure_propagates() {
    struct FailingWriter;
    impl std::io::Write for FailingWriter {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("controlled output failure"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    assert!(
        corpus("conclusion_BOUNDS")
            .write_to(&mut FailingWriter)
            .is_err()
    );
}

#[test]
fn an_implicit_output_is_distinct_from_a_checked_output_file() {
    let proof = "pseudo-Boolean proof version 3.0\nf 1;\noutput EQUISATISFIABLE IMPLICIT;\nconclusion NONE;\nend pseudo-Boolean proof;\n";
    let (dir, mut args) = temporary_case("1 x1 >= 1 ;\n", proof);
    let output = dir.path().join("out.opb");
    // This file is contradictory and must never be certified just because an
    // IMPLICIT claim about the core set succeeded without reading it.
    std::fs::write(&output, "1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n").unwrap();
    args.output_formula = Some(output.clone());
    let implicit = check(args).unwrap();
    assert!(implicit.is_fully_verified());
    assert!(!implicit.checked_output_file());
    assert!(matches!(
        implicit.statements()[0].claim(),
        CheckedClaim::Output {
            output_type: veripb_rules::OutputType::Implicit,
            ..
        }
    ));

    let explicit_proof = proof.replace("IMPLICIT", "FILE");
    std::fs::write(dir.path().join("proof.pbp"), explicit_proof).unwrap();
    let explicit_args = || Args {
        formula: dir.path().join("formula.opb"),
        derivation: dir.path().join("proof.pbp"),
        output_formula: Some(output.clone()),
        ..Args::default()
    };
    assert!(check(explicit_args()).is_err());
    std::fs::write(&output, "1 x1 >= 1 ;\n").unwrap();
    let explicit = check(explicit_args()).unwrap();
    assert!(explicit.is_fully_verified());
    assert!(explicit.checked_output_file());
}

#[test]
fn lenient_input_headers_cannot_establish_a_fully_verified_certificate() {
    let (dir, mut args) = temporary_case(
        "p cnf 1 2\n1 0\n",
        "pseudo-Boolean proof version 3.0\nf 1;\nsol x1;\noutput NONE;\nconclusion SAT;\nend pseudo-Boolean proof;\n",
    );
    args.formula = dir.path().join("formula.opb");
    args.cnf = true;
    assert!(check(args).is_err());
    let lenient = check(Args {
        formula: dir.path().join("formula.opb"),
        derivation: dir.path().join("proof.pbp"),
        cnf: true,
        lenient_header_counts: true,
        ..Args::default()
    })
    .unwrap();
    assert_eq!(lenient.outcome(), RunOutcome::Verified);
    assert_eq!(
        lenient.input_admission(),
        veripb::InputAdmission::LenientHeaderCounts
    );
    assert!(!lenient.is_fully_verified());
}

#[test]
fn bypassed_output_path_checks_cannot_establish_a_fully_verified_certificate() {
    let proof = "pseudo-Boolean proof version 3.0\nf 1;\nsol x1;\noutput NONE;\nconclusion SAT;\nend pseudo-Boolean proof;\n";
    let (dir, mut args) = temporary_case("1 x1 >= 1 ;\n", proof);
    let formula = args.formula.clone();
    args.elaborate = Some(Some(formula.clone()));
    assert!(check(args).is_err());
    assert_eq!(std::fs::read_to_string(&formula).unwrap(), "1 x1 >= 1 ;\n");

    let report = check(Args {
        formula,
        derivation: dir.path().join("proof.pbp"),
        ignore_file_path_check: true,
        ..Args::default()
    })
    .unwrap();
    assert_eq!(report.outcome(), RunOutcome::Verified);
    assert_eq!(
        report.input_admission(),
        veripb::InputAdmission::UncheckedOutputPaths
    );
    assert!(!report.is_fully_verified());
}
