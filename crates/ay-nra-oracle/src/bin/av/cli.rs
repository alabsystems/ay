// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SuiteSelection {
    All,
    A,
    B,
    C,
    D,
    E,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReferenceRequirement {
    PathFree,
    Required,
}

#[derive(Debug, Eq, PartialEq)]
struct AvArgs {
    path: Option<std::path::PathBuf>,
    cases: u64,
    seed: u64,
    suite: SuiteSelection,
}

#[derive(Debug, thiserror::Error)]
enum AvArgError {
    #[error("{flag} requires a value")]
    MissingValue { flag: String },
    #[error("invalid {flag} value {value:?}: expected u64")]
    InvalidInteger { flag: &'static str, value: String },
    #[error("invalid --only value {0:?}: expected a, b, c, d, or e")]
    InvalidSuite(String),
    #[error("unknown argument {0:?}")]
    UnknownArgument(String),
    #[error("argument {0} was supplied more than once")]
    DuplicateArgument(String),
    #[error("--z3 requires a non-empty path")]
    EmptyZ3Path,
    #[error("--z3 PATH is required unless --only a or --only e is selected")]
    MissingZ3,
    #[error("--cases is too large for suite D")]
    CasesTooLarge,
    #[error("--cases must be greater than zero for reference suites")]
    ZeroCases,
    #[error("--cases is not used by suite {0}")]
    IrrelevantCases(&'static str),
    #[error("--seed is not used by suite {0}")]
    IrrelevantSeed(&'static str),
    #[error("--z3 is not used by suite {0}")]
    IrrelevantZ3(&'static str),
}

fn usage() -> &'static str {
    "usage: av [--only a|b|c|d|e] [--cases N] [--seed S] [--z3 PATH]\n\
     --z3 PATH is required for the default run and suites b, c, and d\n\
     the default run covers suites a-d; suite e is opt-in"
}

fn parse_args(args: &[String]) -> Result<AvArgs, AvArgError> {
    let mut parsed = AvArgs {
        path: None,
        cases: 600,
        seed: 12345,
        suite: SuiteSelection::All,
    };
    let mut seen = std::collections::BTreeSet::new();
    let mut cases_supplied = false;
    let mut seed_supplied = false;
    let mut i = 1;
    while i < args.len() {
        let flag = &args[i];
        let value = || {
            args.get(i + 1)
                .filter(|value| !value.starts_with("--"))
                .ok_or_else(|| AvArgError::MissingValue { flag: flag.clone() })
        };
        if !seen.insert(flag.clone()) {
            return Err(AvArgError::DuplicateArgument(flag.clone()));
        }
        match flag.as_str() {
            "--z3" => {
                let path = value()?;
                if path.trim().is_empty() {
                    return Err(AvArgError::EmptyZ3Path);
                }
                parsed.path = Some(std::path::PathBuf::from(path.as_str()));
            }
            "--cases" => {
                let raw = value()?;
                parsed.cases = raw.parse().map_err(|_| AvArgError::InvalidInteger {
                    flag: "--cases",
                    value: raw.clone(),
                })?;
                cases_supplied = true;
            }
            "--seed" => {
                let raw = value()?;
                parsed.seed = raw.parse().map_err(|_| AvArgError::InvalidInteger {
                    flag: "--seed",
                    value: raw.clone(),
                })?;
                seed_supplied = true;
            }
            "--only" => {
                parsed.suite = match value()?.as_str() {
                    "a" => SuiteSelection::A,
                    "b" => SuiteSelection::B,
                    "c" => SuiteSelection::C,
                    "d" => SuiteSelection::D,
                    "e" => SuiteSelection::E,
                    other => return Err(AvArgError::InvalidSuite(other.to_owned())),
                };
            }
            _ => return Err(AvArgError::UnknownArgument(flag.clone())),
        }
        i += 2;
    }
    if matches!(parsed.suite, SuiteSelection::All | SuiteSelection::D) {
        parsed
            .cases
            .checked_mul(2)
            .ok_or(AvArgError::CasesTooLarge)?;
    }
    match parsed.suite {
        SuiteSelection::A if cases_supplied => return Err(AvArgError::IrrelevantCases("a")),
        SuiteSelection::E if cases_supplied => return Err(AvArgError::IrrelevantCases("e")),
        SuiteSelection::A if seed_supplied => return Err(AvArgError::IrrelevantSeed("a")),
        SuiteSelection::E if seed_supplied => return Err(AvArgError::IrrelevantSeed("e")),
        SuiteSelection::A if parsed.path.is_some() => return Err(AvArgError::IrrelevantZ3("a")),
        SuiteSelection::E if parsed.path.is_some() => return Err(AvArgError::IrrelevantZ3("e")),
        SuiteSelection::All | SuiteSelection::B | SuiteSelection::C | SuiteSelection::D
            if parsed.cases == 0 =>
        {
            return Err(AvArgError::ZeroCases);
        }
        _ => {}
    }
    if matches!(
        parsed.suite,
        SuiteSelection::All | SuiteSelection::B | SuiteSelection::C | SuiteSelection::D
    ) && parsed.path.is_none()
    {
        return Err(AvArgError::MissingZ3);
    }
    Ok(parsed)
}

#[expect(
    unsafe_code,
    reason = "an operator-selected native reference requires an explicit trusted-ABI assertion"
)]
fn main() {
    // #govern: see crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();
    let raw_args: Vec<String> = std::env::args().collect();
    let args = match parse_args(&raw_args) {
        Ok(args) => args,
        Err(e) => {
            eprintln!("error: {e}\n{}", usage());
            std::process::exit(64);
        }
    };

    if matches!(args.suite, SuiteSelection::All | SuiteSelection::A) {
        suite_a();
    }
    if args.suite == SuiteSelection::A {
        report(ReferenceRequirement::PathFree, 0);
        return;
    }
    if args.suite == SuiteSelection::E {
        suite_e();
        report(ReferenceRequirement::PathFree, 0);
        return;
    }

    let Some(path) = args.path.as_ref() else {
        eprintln!("error: --z3 PATH is required for this suite\n{}", usage());
        std::process::exit(64);
    };
    // SAFETY: this developer verifier deliberately executes the
    // operator-selected reference library as trusted native code. Its CLI
    // contract requires `path` to name a genuine, ABI-compatible libz3.
    let mut z3 = match unsafe { Z3::open_trusted_reference(path) } {
        Ok(z) => z,
        Err(e) => {
            eprintln!("FATAL: requested reference libz3 is unavailable: {e}");
            eprintln!("The verifier refuses to report a clean run without its reference.");
            std::process::exit(2);
        }
    };
    if matches!(args.suite, SuiteSelection::All | SuiteSelection::B) {
        suite_b(&mut z3, args.cases, args.seed);
    }
    if matches!(args.suite, SuiteSelection::All | SuiteSelection::C) {
        suite_c(&mut z3, args.cases, args.seed ^ 0x5555);
    }
    if matches!(args.suite, SuiteSelection::All | SuiteSelection::D) {
        let Some(d_cases) = args.cases.checked_mul(2) else {
            eprintln!("error: --cases is too large for suite D");
            std::process::exit(64);
        };
        suite_d(&mut z3, d_cases, args.seed ^ 0xAAAA);
    }
    if let Err(e) = z3.recycle() {
        z3_error("AV/finalize", &format!("releasing reference vectors: {e}"));
    }
    report(ReferenceRequirement::Required, z3.reference_failure_count());
}

fn report(reference: ReferenceRequirement, binding_failures: u64) {
    let checks = CHECKS.load(AtomicOrdering::Relaxed);
    let reference_checks = REFERENCE_CHECKS.load(AtomicOrdering::Relaxed);
    let failures = FAILURES.load(AtomicOrdering::Relaxed);
    let reference_errors = REFERENCE_ERRORS.load(AtomicOrdering::Relaxed);
    println!(
        "\n==== AV SUMMARY: {checks} checks ({reference_checks} reference), {failures} FAILURES, \
         {reference_errors} REFERENCE ERRORS, {binding_failures} BINDING FAILURES ===="
    );
    let missing_reference = reference == ReferenceRequirement::Required && reference_checks == 0;
    if reference_errors > 0 || binding_failures > 0 || missing_reference {
        if missing_reference {
            eprintln!("FATAL: no reference comparison completed");
        }
        std::process::exit(2);
    }
    if failures > 0 {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod cli_tests {
    use super::{parse_args, SuiteSelection};

    fn args(rest: &[&str]) -> Vec<String> {
        std::iter::once("av")
            .chain(rest.iter().copied())
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn parses_exact_suite_selection() {
        let parsed = parse_args(&args(&[
            "--only", "c", "--cases", "17", "--seed", "9", "--z3", "/libz3",
        ]))
        .expect("valid arguments");
        assert_eq!(parsed.suite, SuiteSelection::C);
        assert_eq!(parsed.cases, 17);
        assert_eq!(parsed.seed, 9);
    }

    #[test]
    fn rejects_malformed_and_unknown_arguments() {
        assert!(parse_args(&args(&["--cases", "many"])).is_err());
        assert!(parse_args(&args(&["--only", "z"])).is_err());
        assert!(parse_args(&args(&["--mystery", "1"])).is_err());
        assert!(parse_args(&args(&["--seed"])).is_err());
        assert!(parse_args(&args(&["--only", "a", "--only", "e"])).is_err());
        assert!(parse_args(&args(&["--only", "b", "--z3", ""])).is_err());
    }

    #[test]
    fn requires_z3_only_for_reference_suites() {
        assert!(parse_args(&args(&[])).is_err());
        assert!(parse_args(&args(&["--only", "b"])).is_err());
        assert!(parse_args(&args(&["--only", "c"])).is_err());
        assert!(parse_args(&args(&["--only", "d"])).is_err());
        assert!(parse_args(&args(&["--only", "a"])).is_ok());
        assert!(parse_args(&args(&["--only", "e"])).is_ok());
        assert!(parse_args(&args(&["--only", "a", "--cases", "1"])).is_err());
        assert!(parse_args(&args(&["--only", "e", "--cases", "1"])).is_err());
        assert!(parse_args(&args(&["--only", "a", "--seed", "1"])).is_err());
        assert!(parse_args(&args(&["--only", "e", "--seed", "1"])).is_err());
        assert!(parse_args(&args(&["--only", "a", "--z3", "/z3"])).is_err());
        assert!(parse_args(&args(&["--only", "e", "--z3", "/z3"])).is_err());
        assert!(parse_args(&args(&["--only", "b", "--cases", "0", "--z3", "/z3"])).is_err());
    }
}
