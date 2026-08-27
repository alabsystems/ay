// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::path::PathBuf;

const DEFAULT_MAX_COST: usize = 420;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Command {
    Probe {
        z3: PathBuf,
    },
    Golden {
        z3: Option<PathBuf>,
        heavy: bool,
    },
    Selftest {
        z3: PathBuf,
        seed: u64,
        cases: u64,
        max_cost: usize,
    },
    Fuzz {
        z3: PathBuf,
        seed: u64,
        cases: u64,
        start: u64,
        dump: Option<PathBuf>,
        progress: u64,
        max_cost: usize,
    },
    Repro {
        z3: PathBuf,
        seed: u64,
        index: u64,
        max_cost: usize,
    },
    Dbg {
        z3: PathBuf,
        coeffs: String,
    },
    Growth {
        cases: u64,
    },
    AnumGrowth {
        cases: u64,
    },
    FactorCost {
        cases: u64,
    },
    BqGrowth,
    Declines {
        seed: u64,
        cases: u64,
    },
}

#[derive(Debug, thiserror::Error, Eq, PartialEq)]
pub(crate) enum ArgError {
    #[error("a command is required")]
    MissingCommand,
    #[error("unknown command {0:?}")]
    UnknownCommand(String),
    #[error("unknown option {0:?}")]
    UnknownOption(String),
    #[error("option {flag} is not valid for {command}")]
    IrrelevantOption { flag: &'static str, command: String },
    #[error("option {0} was supplied more than once")]
    DuplicateOption(&'static str),
    #[error("{0} requires a value")]
    MissingValue(&'static str),
    #[error("{0} requires a non-empty value")]
    EmptyValue(&'static str),
    #[error("invalid {flag} value {value:?}: expected a non-negative integer")]
    InvalidInteger { flag: &'static str, value: String },
    #[error("{0} requires --z3 PATH")]
    MissingZ3(String),
    #[error("{command} requires {flag}")]
    MissingOption { command: String, flag: &'static str },
    #[error("golden accepts either --z3 PATH or --no-z3, not both")]
    ConflictingGoldenReference,
    #[error("invalid rational coefficient {0:?}")]
    InvalidCoefficient(String),
    #[error("{0} requires --cases greater than zero")]
    ZeroCases(String),
    #[error("fuzz range overflows u64: --start plus --cases is too large")]
    RangeOverflow,
}

#[derive(Default)]
struct RawOptions {
    z3: Option<PathBuf>,
    seed: Option<u64>,
    cases: Option<u64>,
    start: Option<u64>,
    index: Option<u64>,
    progress: Option<u64>,
    dump: Option<PathBuf>,
    max_cost: Option<usize>,
    coeffs: Option<String>,
    heavy: bool,
    no_z3: bool,
}

fn known_command(command: &str) -> bool {
    matches!(
        command,
        "probe"
            | "golden"
            | "selftest"
            | "fuzz"
            | "repro"
            | "dbg"
            | "growth"
            | "anum-growth"
            | "factor-cost"
            | "bq-growth"
            | "declines"
    )
}

fn option_allowed(command: &str, flag: &str) -> bool {
    match command {
        "probe" => matches!(flag, "--z3"),
        "golden" => matches!(flag, "--z3" | "--heavy" | "--no-z3"),
        "selftest" => matches!(flag, "--z3" | "--seed" | "--cases" | "--max-cost"),
        "fuzz" => matches!(
            flag,
            "--z3" | "--seed" | "--cases" | "--start" | "--dump" | "--progress" | "--max-cost"
        ),
        "repro" => matches!(flag, "--z3" | "--seed" | "--case" | "--max-cost"),
        "dbg" => matches!(flag, "--z3" | "--coeffs"),
        "growth" | "anum-growth" | "factor-cost" => matches!(flag, "--cases"),
        "bq-growth" => false,
        "declines" => matches!(flag, "--seed" | "--cases"),
        _ => false,
    }
}

fn value<'a>(args: &'a [String], i: usize, flag: &'static str) -> Result<&'a str, ArgError> {
    let value = args.get(i + 1).ok_or(ArgError::MissingValue(flag))?;
    if value.is_empty() || value.starts_with("--") {
        return Err(ArgError::MissingValue(flag));
    }
    Ok(value)
}

fn integer<T: std::str::FromStr>(flag: &'static str, value: &str) -> Result<T, ArgError> {
    value.parse().map_err(|_| ArgError::InvalidInteger {
        flag,
        value: value.to_owned(),
    })
}

fn required_z3(raw: &mut RawOptions, command: &str) -> Result<PathBuf, ArgError> {
    raw.z3
        .take()
        .ok_or_else(|| ArgError::MissingZ3(command.to_owned()))
}

fn validate_coefficients(spec: &str) -> Result<(), ArgError> {
    for token in spec.split(',') {
        if crate::z3::parse_rational(token.trim()).is_none() {
            return Err(ArgError::InvalidCoefficient(token.to_owned()));
        }
    }
    Ok(())
}

fn parse_options(command: &str, args: &[String]) -> Result<RawOptions, ArgError> {
    let mut raw = RawOptions::default();
    let mut seen = BTreeSet::new();
    let mut i = 1;
    while i < args.len() {
        let flag: &'static str = match args[i].as_str() {
            "--z3" => "--z3",
            "--seed" => "--seed",
            "--cases" => "--cases",
            "--start" => "--start",
            "--case" => "--case",
            "--progress" => "--progress",
            "--dump" => "--dump",
            "--max-cost" => "--max-cost",
            "--coeffs" => "--coeffs",
            "--heavy" => "--heavy",
            "--no-z3" => "--no-z3",
            other => return Err(ArgError::UnknownOption(other.to_owned())),
        };
        if !option_allowed(command, flag) {
            return Err(ArgError::IrrelevantOption {
                flag,
                command: command.to_owned(),
            });
        }
        if !seen.insert(flag) {
            return Err(ArgError::DuplicateOption(flag));
        }
        i = apply_option(&mut raw, args, i, flag)?;
    }
    Ok(raw)
}

fn apply_option(
    raw: &mut RawOptions,
    args: &[String],
    i: usize,
    flag: &'static str,
) -> Result<usize, ArgError> {
    match flag {
        "--z3" => {
            let path = value(args, i, flag)?;
            if path.trim().is_empty() {
                return Err(ArgError::EmptyValue(flag));
            }
            raw.z3 = Some(PathBuf::from(path));
            Ok(i + 2)
        }
        "--seed" => {
            raw.seed = Some(integer(flag, value(args, i, flag)?)?);
            Ok(i + 2)
        }
        "--cases" => {
            raw.cases = Some(integer(flag, value(args, i, flag)?)?);
            Ok(i + 2)
        }
        "--start" => {
            raw.start = Some(integer(flag, value(args, i, flag)?)?);
            Ok(i + 2)
        }
        "--case" => {
            raw.index = Some(integer(flag, value(args, i, flag)?)?);
            Ok(i + 2)
        }
        "--progress" => {
            raw.progress = Some(integer(flag, value(args, i, flag)?)?);
            Ok(i + 2)
        }
        "--dump" => {
            raw.dump = Some(PathBuf::from(value(args, i, flag)?));
            Ok(i + 2)
        }
        "--max-cost" => {
            let parsed: usize = integer(flag, value(args, i, flag)?)?;
            raw.max_cost = Some(if parsed == 0 { usize::MAX } else { parsed });
            Ok(i + 2)
        }
        "--coeffs" => {
            raw.coeffs = Some(value(args, i, flag)?.to_owned());
            Ok(i + 2)
        }
        "--heavy" => {
            raw.heavy = true;
            Ok(i + 1)
        }
        "--no-z3" => {
            raw.no_z3 = true;
            Ok(i + 1)
        }
        other => Err(ArgError::UnknownOption(other.to_owned())),
    }
}

fn build_golden(raw: &mut RawOptions) -> Result<Command, ArgError> {
    if raw.no_z3 && raw.z3.is_some() {
        return Err(ArgError::ConflictingGoldenReference);
    }
    if raw.no_z3 {
        Ok(Command::Golden {
            z3: None,
            heavy: raw.heavy,
        })
    } else {
        Ok(Command::Golden {
            z3: Some(required_z3(raw, "golden")?),
            heavy: raw.heavy,
        })
    }
}

fn build_dbg(raw: &mut RawOptions) -> Result<Command, ArgError> {
    let z3 = required_z3(raw, "dbg")?;
    let coeffs = raw.coeffs.take().ok_or_else(|| ArgError::MissingOption {
        command: "dbg".to_owned(),
        flag: "--coeffs LIST",
    })?;
    validate_coefficients(&coeffs)?;
    Ok(Command::Dbg { z3, coeffs })
}

fn build_command(command: &str, mut raw: RawOptions) -> Result<Command, ArgError> {
    let seed = raw.seed.unwrap_or(1);
    let cases = raw.cases.unwrap_or(100_000);
    let max_cost = raw.max_cost.unwrap_or(DEFAULT_MAX_COST);
    match command {
        "probe" => Ok(Command::Probe {
            z3: required_z3(&mut raw, command)?,
        }),
        "golden" => build_golden(&mut raw),
        "selftest" => {
            if cases == 0 {
                return Err(ArgError::ZeroCases(command.to_owned()));
            }
            Ok(Command::Selftest {
                z3: required_z3(&mut raw, command)?,
                seed,
                cases,
                max_cost,
            })
        }
        "fuzz" => {
            if cases == 0 {
                return Err(ArgError::ZeroCases(command.to_owned()));
            }
            let start = raw.start.unwrap_or(0);
            start.checked_add(cases).ok_or(ArgError::RangeOverflow)?;
            Ok(Command::Fuzz {
                z3: required_z3(&mut raw, command)?,
                seed,
                cases,
                start,
                dump: raw.dump,
                progress: raw.progress.unwrap_or(50_000),
                max_cost,
            })
        }
        "repro" => Ok(Command::Repro {
            z3: required_z3(&mut raw, command)?,
            seed,
            index: raw.index.unwrap_or(0),
            max_cost,
        }),
        "dbg" => build_dbg(&mut raw),
        "growth" => Ok(Command::Growth { cases }),
        "anum-growth" => Ok(Command::AnumGrowth { cases }),
        "factor-cost" => Ok(Command::FactorCost { cases }),
        "bq-growth" => Ok(Command::BqGrowth),
        "declines" => Ok(Command::Declines { seed, cases }),
        other => Err(ArgError::UnknownCommand(other.to_owned())),
    }
}

pub(crate) fn parse_args(args: &[String]) -> Result<Command, ArgError> {
    let command = args.first().ok_or(ArgError::MissingCommand)?.as_str();
    if !known_command(command) {
        return Err(ArgError::UnknownCommand(command.to_owned()));
    }
    build_command(command, parse_options(command, args)?)
}

pub(crate) fn usage() -> &'static str {
    "ay-nra-oracle — differential oracle for AY's exact univariate / real-algebraic layer

  ay-nra-oracle probe --z3 PATH                       sanity-check the libz3 binding
  ay-nra-oracle golden --no-z3 [--heavy]              path-free fixtures
  ay-nra-oracle golden --z3 PATH [--heavy]             fixtures plus live z3
  ay-nra-oracle selftest --z3 PATH [--cases n]         prove every check can fail
  ay-nra-oracle fuzz --z3 PATH [options]               differential campaign
  ay-nra-oracle repro --z3 PATH --seed S --case I      replay one case verbosely
  ay-nra-oracle dbg --z3 PATH --coeffs a,b,c,...       dump both views of one poly
  ay-nra-oracle growth [--cases n]                     measure gcd coefficient growth
  ay-nra-oracle anum-growth [--cases n]                measure algebraic-number growth
  ay-nra-oracle factor-cost [--cases n]                measure factorization cost
  ay-nra-oracle bq-growth                               measure dyadic denominator growth
  ay-nra-oracle declines [--seed S --cases n]          explain modular gcd declines

fuzz options:
  --seed <u64>        run seed (default 1)
  --cases <u64>       number of cases (default 100000; must be > 0)
  --start <u64>       first case index (default 0)
  --dump <dir>        write each divergence as JSON here
  --progress <n>      progress line every n cases (0 = silent, default 50000)
  --max-cost <n>      per-case work budget (0 = unbounded, default 420)
  --z3 <path>         trusted reference libz3 (required by differential modes)"
}

#[cfg(test)]
mod tests {
    use super::{parse_args, ArgError, Command};

    fn args(rest: &[&str]) -> Vec<String> {
        rest.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn enforces_reference_paths_and_path_free_golden() {
        assert!(matches!(
            parse_args(&args(&["probe"])),
            Err(ArgError::MissingZ3(_))
        ));
        assert!(matches!(
            parse_args(&args(&["golden", "--no-z3"])),
            Ok(Command::Golden { z3: None, .. })
        ));
        assert!(matches!(
            parse_args(&args(&["golden"])),
            Err(ArgError::MissingZ3(_))
        ));
        assert!(matches!(
            parse_args(&args(&["golden", "--no-z3", "--z3", "/libz3"])),
            Err(ArgError::ConflictingGoldenReference)
        ));
    }

    #[test]
    fn rejects_malformed_overflow_zero_irrelevant_and_duplicate_options() {
        assert!(parse_args(&args(&["fuzz", "--z3", "/z3", "--cases", "nope"])).is_err());
        assert!(parse_args(&args(&[
            "fuzz",
            "--z3",
            "/z3",
            "--cases",
            "18446744073709551616",
        ]))
        .is_err());
        assert!(parse_args(&args(&[
            "fuzz",
            "--z3",
            "/z3",
            "--start",
            "18446744073709551615",
            "--cases",
            "1",
        ]))
        .is_err());
        assert!(matches!(
            parse_args(&args(&["fuzz", "--z3", "/z3", "--cases", "0"])),
            Err(ArgError::ZeroCases(_))
        ));
        assert!(matches!(
            parse_args(&args(&["selftest", "--z3", "/z3", "--cases", "0"])),
            Err(ArgError::ZeroCases(_))
        ));
        assert!(parse_args(&args(&["unknown"])).is_err());
        assert!(parse_args(&args(&["fuzz", "--z3", "/z3", "--mystery"])).is_err());
        assert!(parse_args(&args(&["probe", "--seed", "1", "--z3", "/z3"])).is_err());
        assert!(parse_args(&args(&["probe", "--z3", "/a", "--z3", "/b"])).is_err());
        assert!(parse_args(&args(&["probe", "--z3", ""])).is_err());
        assert!(parse_args(&args(&["dbg", "--z3", "/z3"])).is_err());
        assert!(parse_args(&args(&["dbg", "--z3", "/z3", "--coeffs", "1,nope,2"])).is_err());
    }

    #[test]
    fn preserves_zero_progress_and_unbounded_cost() {
        let parsed = parse_args(&args(&[
            "fuzz",
            "--z3",
            "/z3",
            "--progress",
            "0",
            "--max-cost",
            "0",
        ]))
        .expect("valid fuzz arguments");
        assert!(matches!(
            parsed,
            Command::Fuzz {
                progress: 0,
                max_cost: usize::MAX,
                ..
            }
        ));
    }
}
