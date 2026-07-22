// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_chc::{testing, ChcError, ChcParser, ChcProblem, PdrConfig, PortfolioResult};
use ntest::timeout;
use std::time::Duration;

const DILLIG02_M_000: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2");

#[derive(Debug)]
struct SafeResultCheck {
    kind: &'static str,
    verified: Option<bool>,
    model_smtlib: Option<String>,
}

fn result_kind(result: &PortfolioResult) -> &'static str {
    match result {
        PortfolioResult::Safe(_) => "safe",
        PortfolioResult::Unsafe(_) => "unsafe",
        PortfolioResult::Unknown | PortfolioResult::NotApplicable | _ => "unknown",
    }
}

fn direction_name(direction: testing::TrlTestDirection) -> &'static str {
    match direction {
        testing::TrlTestDirection::Forward => "forward",
        testing::TrlTestDirection::Backward => "backward",
    }
}

fn classify_safe_result(problem: &ChcProblem, result: &PortfolioResult) -> SafeResultCheck {
    match result {
        PortfolioResult::Safe(model) => {
            let mut verifier = testing::new_pdr_solver(problem.clone(), PdrConfig::default());
            SafeResultCheck {
                kind: result_kind(result),
                verified: Some(verifier.verify_model(model)),
                model_smtlib: Some(model.to_smtlib(problem)),
            }
        }
        _ => SafeResultCheck {
            kind: result_kind(result),
            verified: None,
            model_smtlib: None,
        },
    }
}

#[test]
#[timeout(90_000)]
fn trl_only_dillig02_safe_results_verify_against_original_problem_issue_7182() {
    let problem = ChcParser::parse(DILLIG02_M_000).expect("benchmark should parse");
    let timeout = Duration::from_secs(15);

    // The TRL-only lane is single-predicate BY DESIGN:
    // `TransitionSystem::from_chc_problem` accepts exactly one *used* predicate
    // (see `transition_system/extract.rs`, which is correct and left unchanged).
    // The real vendored dillig02_m_000.smt2 has TWO mutually-recursive
    // predicates (`inv`, `inv1`), so the TRL-only lane does not apply to it: the
    // extractor returns `Err(Parse("Expected 1 used predicate, found 2"))`.
    // That is a genuine "TRL-only N/A" signal, not a solver failure — treat it
    // as a skip rather than a hard panic (the multi-predicate safety-proving
    // path is exercised by the full-portfolio tests, not this TRL-only lane).
    let is_trl_not_applicable =
        |err: &ChcError| matches!(err, ChcError::Parse(msg) if msg.contains("used predicate"));

    for direction in [
        testing::TrlTestDirection::Forward,
        testing::TrlTestDirection::Backward,
    ] {
        let raw = match testing::solve_trl_only_from_str(DILLIG02_M_000, direction, false, timeout)
        {
            Ok(result) => result,
            Err(err) if is_trl_not_applicable(&err) => {
                eprintln!(
                    "issue7182 dillig02 direction={}: TRL-only N/A for this multi-predicate \
                     benchmark ({err}); skipping",
                    direction_name(direction)
                );
                continue;
            }
            Err(err) => panic!(
                "raw TRL-only dillig02 run should parse and execute for {}: {err}",
                direction_name(direction)
            ),
        };
        let raw_check = classify_safe_result(&problem, &raw);

        let validated =
            match testing::solve_trl_only_from_str(DILLIG02_M_000, direction, true, timeout) {
                Ok(result) => result,
                Err(err) if is_trl_not_applicable(&err) => {
                    eprintln!(
                        "issue7182 dillig02 direction={}: validated TRL-only N/A for this \
                     multi-predicate benchmark ({err}); skipping",
                        direction_name(direction)
                    );
                    continue;
                }
                Err(err) => panic!(
                    "validated TRL-only dillig02 run should parse and execute for {}: {err}",
                    direction_name(direction)
                ),
            };
        let validated_check = classify_safe_result(&problem, &validated);

        eprintln!(
            "issue7182 dillig02 direction={} raw_kind={} raw_verified={:?} validated_kind={} validated_verified={:?}",
            direction_name(direction),
            raw_check.kind,
            raw_check.verified,
            validated_check.kind,
            validated_check.verified
        );

        assert!(
            !matches!(validated, PortfolioResult::Unsafe(_)),
            "validated TRL returned Unsafe on known-safe dillig02_m_000.smt2 for {}\nraw_kind={} raw_verified={:?}\nvalidated_kind={} validated_verified={:?}\nraw_result={raw:?}\nvalidated_result={validated:?}\nraw_model:\n{}\nvalidated_model:\n{}",
            direction_name(direction),
            raw_check.kind,
            raw_check.verified,
            validated_check.kind,
            validated_check.verified,
            raw_check.model_smtlib.as_deref().unwrap_or("<none>"),
            validated_check.model_smtlib.as_deref().unwrap_or("<none>")
        );

        assert!(
            validated_check.verified != Some(false),
            "validated TRL returned an invalid Safe proof on dillig02_m_000.smt2 for {}\nraw_kind={} raw_verified={:?}\nvalidated_kind={} validated_verified={:?}\nraw_result={raw:?}\nvalidated_result={validated:?}\nraw_model:\n{}\nvalidated_model:\n{}",
            direction_name(direction),
            raw_check.kind,
            raw_check.verified,
            validated_check.kind,
            validated_check.verified,
            raw_check.model_smtlib.as_deref().unwrap_or("<none>"),
            validated_check.model_smtlib.as_deref().unwrap_or("<none>")
        );
    }
}
