// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_chc::testing::{solve_trl_only_from_str, TrlTestDirection};
use ay_chc::PortfolioResult;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

const BENCHMARKS: &[&str] = &[
    "dillig12_m_000.smt2",
    "phases_m_000.smt2",
    "half_true_modif_m_000.smt2",
    "s_multipl_09_000.smt2",
];

#[derive(Debug, Default)]
struct DirectionSummary {
    safe: usize,
    unsafe_: usize,
    unknown: usize,
}

fn benchmark_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/chc-comp/2025/extra-small-lia")
}

fn result_kind(result: &PortfolioResult) -> &'static str {
    match result {
        PortfolioResult::Safe(_) => "safe",
        PortfolioResult::Unsafe(_) => "unsafe",
        PortfolioResult::Unknown | PortfolioResult::NotApplicable | _ => "unknown",
    }
}

fn update_summary(summary: &mut DirectionSummary, result: &PortfolioResult) {
    match result {
        PortfolioResult::Safe(_) => summary.safe += 1,
        PortfolioResult::Unsafe(_) => summary.unsafe_ += 1,
        PortfolioResult::Unknown | PortfolioResult::NotApplicable | _ => summary.unknown += 1,
    }
}

fn direction_name(direction: TrlTestDirection) -> &'static str {
    match direction {
        TrlTestDirection::Forward => "forward",
        TrlTestDirection::Backward => "backward",
    }
}

fn is_polarity_flip(raw: &PortfolioResult, validated: &PortfolioResult) -> bool {
    matches!(
        (result_kind(raw), result_kind(validated)),
        ("safe", "unsafe") | ("unsafe", "safe")
    )
}

fn main() -> ExitCode {
    let timeout = Duration::from_secs(15);
    let mut forward_summary = DirectionSummary::default();
    let mut backward_summary = DirectionSummary::default();
    let mut had_error = false;

    for benchmark in BENCHMARKS {
        let path = benchmark_dir().join(benchmark);
        let input = match fs::read_to_string(&path) {
            Ok(input) => input,
            Err(err) => {
                eprintln!("trl-hard-tail-matrix benchmark={benchmark} read_error={err}");
                return ExitCode::FAILURE;
            }
        };

        for direction in [TrlTestDirection::Forward, TrlTestDirection::Backward] {
            let raw = match solve_trl_only_from_str(&input, direction, false, timeout) {
                Ok(result) => result,
                Err(err) => {
                    eprintln!(
                        "trl-hard-tail-matrix benchmark={benchmark} direction={} raw_error={err}",
                        direction_name(direction)
                    );
                    return ExitCode::FAILURE;
                }
            };
            let validated = match solve_trl_only_from_str(&input, direction, true, timeout) {
                Ok(result) => result,
                Err(err) => {
                    eprintln!(
                        "trl-hard-tail-matrix benchmark={benchmark} direction={} validated_error={err}",
                        direction_name(direction)
                    );
                    return ExitCode::FAILURE;
                }
            };

            let summary = match direction {
                TrlTestDirection::Forward => &mut forward_summary,
                TrlTestDirection::Backward => &mut backward_summary,
            };
            update_summary(summary, &validated);

            let raw_kind = result_kind(&raw);
            let validated_kind = result_kind(&validated);
            eprintln!(
                "trl-hard-tail-matrix benchmark={benchmark} direction={} raw={raw_kind} validated={validated_kind}",
                direction_name(direction)
            );
            if is_polarity_flip(&raw, &validated) {
                had_error = true;
                eprintln!(
                    "trl-hard-tail-matrix benchmark={benchmark} direction={} polarity_flip raw={raw_kind} validated={validated_kind}",
                    direction_name(direction)
                );
            }
        }
    }

    eprintln!(
        "trl-hard-tail-summary direction=forward safe={} unsafe={} unknown={}",
        forward_summary.safe, forward_summary.unsafe_, forward_summary.unknown
    );
    eprintln!(
        "trl-hard-tail-summary direction=backward safe={} unsafe={} unknown={}",
        backward_summary.safe, backward_summary.unsafe_, backward_summary.unknown
    );

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
