// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn run(fzn: &str, options: &PortfolioOptions, started: Instant) -> (Result<()>, String, String) {
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("FlatZinc model must parse");
    let mut out = Vec::new();
    let mut err = Vec::new();
    let result = solve_portfolio(&model, options, started, &mut out, &mut err);
    (
        result,
        String::from_utf8(out).expect("solution stream is UTF-8"),
        String::from_utf8(err).expect("stderr is UTF-8"),
    )
}

/// The CP order encoding of `var 0..4000000` exceeds the engine's 2^20
/// literal capacity, so the CP engine declines. The portfolio must hand the
/// model to the SMT path and answer, not stop with UNKNOWN or an error; with
/// any worker count, since the portfolio workers decline too.
#[test]
fn a_cp_capacity_decline_is_answered_by_the_smt_path() {
    let started = Instant::now();
    for workers in [1, 8] {
        let options = PortfolioOptions {
            parallel_workers: workers,
            ..PortfolioOptions::default()
        };
        let (result, out, err) = run(
            "var 0..4000000: x :: output_var;\nconstraint int_ge(x, 3);\nsolve minimize x;\n",
            &options,
            started,
        );
        assert!(result.is_ok(), "-p {workers}: {result:?}");
        assert!(err.contains("CP backend declined"), "-p {workers}: {err}");
        assert!(!err.contains("Error"), "-p {workers}: {err}");
        assert!(
            out.ends_with("x = 3;\n----------\n==========\n"),
            "-p {workers}: the SMT path must prove the optimum 3: {out}"
        );

        let (result, out, err) = run(
            "var 0..4000000: x :: output_var;\nconstraint int_ge(x, 3999999);\nsolve satisfy;\n",
            &options,
            started,
        );
        assert!(result.is_ok(), "-p {workers}: {result:?}");
        assert!(err.contains("CP backend declined"), "-p {workers}: {err}");
        let value: i64 = out
            .lines()
            .find_map(|line| line.strip_prefix("x = ")?.strip_suffix(';')?.parse().ok())
            .unwrap_or_else(|| panic!("-p {workers}: no solution printed: {out}"));
        assert!(
            (3_999_999..=4_000_000).contains(&value),
            "-p {workers}: x = {value} violates the model"
        );
        assert!(out.contains("----------\n"), "{out}");
    }
}

/// A model the CP engine accepts stays on the CP path: no decline note.
#[test]
fn a_model_within_cp_capacity_is_solved_by_cp() {
    let (result, out, err) = run(
        "var 1..3: x :: output_var;\nconstraint int_ne(x, 1);\nsolve minimize x;\n",
        &PortfolioOptions {
            parallel_workers: 1,
            ..PortfolioOptions::default()
        },
        Instant::now(),
    );
    assert!(result.is_ok(), "{result:?}");
    assert!(!err.contains("declined"), "{err}");
    assert!(out.ends_with("x = 2;\n----------\n==========\n"), "{out}");
}

/// `-t` bounds the whole run: the backend that starts late gets what is left.
#[test]
fn the_smt_fallback_gets_what_remains_of_the_time_limit() {
    assert_eq!(
        remaining_timeout_ms(10_000, Duration::from_millis(2_500)),
        7_500
    );
    // Spent or overspent: at least 1 ms, never 0 and never a wrap-around.
    assert_eq!(remaining_timeout_ms(10_000, Duration::from_secs(10)), 1);
    assert_eq!(remaining_timeout_ms(10_000, Duration::from_secs(3_600)), 1);
    assert_eq!(
        remaining_timeout_ms(u64::MAX, Duration::from_millis(1)),
        u64::MAX - 1
    );
}

/// A run whose limit is already spent when the CP engine declines must not
/// claim anything it did not prove: either UNKNOWN or the proved optimum.
#[test]
fn a_spent_time_limit_after_a_decline_never_overclaims() {
    let started = Instant::now()
        .checked_sub(Duration::from_secs(60))
        .unwrap_or_else(Instant::now);
    let (result, out, _err) = run(
        "var 0..4000000: x :: output_var;\nconstraint int_ge(x, 3);\nsolve minimize x;\n",
        &PortfolioOptions {
            timeout_ms: Some(1_000),
            parallel_workers: 1,
            ..PortfolioOptions::default()
        },
        started,
    );
    assert!(result.is_ok(), "{result:?}");
    assert!(
        out == "=====UNKNOWN=====\n"
            || out.ends_with("x = 3;\n----------\n==========\n")
            || (out.ends_with("----------\n") && !out.contains("==========")),
        "{out}"
    );
}
