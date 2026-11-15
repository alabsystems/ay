// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use ay_drat_check::checker::{backward::BackwardChecker, DratChecker, Stats};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Forward,
    Backward,
}

/// What the command line asks for.
#[derive(Debug, Eq, PartialEq)]
enum Invocation<'a> {
    Provenance,
    Check {
        cnf: &'a Path,
        proof: &'a Path,
        mode: Mode,
    },
    Usage,
}

/// Classify the argument vector (program name first). An empty vector — which
/// `execve` permits — is a usage error, not a panic.
fn parse_invocation(args: &[OsString]) -> Invocation<'_> {
    let (first, second, third, extra) = (args.get(1), args.get(2), args.get(3), args.get(4));
    match (first, second, third, extra) {
        (Some(flag), None, _, _) if flag == "--provenance" => Invocation::Provenance,
        (Some(cnf), Some(proof), None, _) => Invocation::Check {
            cnf: Path::new(cnf),
            proof: Path::new(proof),
            mode: Mode::Forward,
        },
        (Some(cnf), Some(proof), Some(flag), None) if flag == "--backward" => Invocation::Check {
            cnf: Path::new(cnf),
            proof: Path::new(proof),
            mode: Mode::Backward,
        },
        _ => Invocation::Usage,
    }
}

fn main() -> ExitCode {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

    let args = env::args_os().collect::<Vec<_>>();
    let result = match parse_invocation(&args) {
        Invocation::Provenance => {
            print_exact_provenance();
            return ExitCode::SUCCESS;
        }
        Invocation::Check { cnf, proof, mode } => run(cnf, proof, mode),
        Invocation::Usage => {
            usage(args.first());
            Err("invalid command line".to_owned())
        }
    };

    match result {
        Ok(()) => {
            println!("s VERIFIED");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("c {error}");
            println!("s NOT VERIFIED");
            ExitCode::FAILURE
        }
    }
}

fn print_exact_provenance() {
    let source_identity = option_env!("AY_TEST_SOURCE_IDENTITY").unwrap_or("unbound");
    let build_identity = option_env!("AY_TEST_BUILD_IDENTITY").unwrap_or("unbound");
    println!(
        "{{\"schema\":\"ay-exact-binary-provenance-v1\",\"source_identity\":\"{source_identity}\",\"build_identity\":\"{build_identity}\"}}"
    );
}

fn usage(program: Option<&OsString>) {
    let program = program.map_or(Path::new("ay-drat-check"), Path::new);
    eprintln!(
        "usage: {} FORMULA.cnf PROOF.drat [--backward]",
        program.display()
    );
}

fn run(cnf_path: &Path, proof_path: &Path, mode: Mode) -> Result<(), String> {
    let cnf_data = fs::read(cnf_path)
        .map_err(|error| format!("cannot read {}: {error}", cnf_path.display()))?;
    let cnf = ay_drat_check::cnf_parser::parse_cnf(&cnf_data[..])
        .map_err(|error| format!("cannot parse {}: {error}", cnf_path.display()))?;
    if cnf.num_vars > ay_drat_check::checker::MAX_DENSE_VARS {
        return Err(format!(
            "cannot check {}: variable count {} exceeds dense checker maximum {}",
            cnf_path.display(),
            cnf.num_vars,
            ay_drat_check::checker::MAX_DENSE_VARS
        ));
    }

    let proof_data = fs::read(proof_path)
        .map_err(|error| format!("cannot read {}: {error}", proof_path.display()))?;
    let steps = ay_drat_check::drat_parser::parse_drat(&proof_data)
        .map_err(|error| format!("cannot parse {}: {error}", proof_path.display()))?;

    let stats = match mode {
        Mode::Forward => {
            let mut checker = DratChecker::new(cnf.num_vars, true);
            checker
                .verify(&cnf.clauses, &steps)
                .map_err(|error| format!("forward verification failed: {error}"))?;
            checker.stats().clone()
        }
        Mode::Backward => {
            let mut checker = BackwardChecker::new(cnf.num_vars, true);
            checker
                .verify(&cnf.clauses, &steps)
                .map_err(|error| format!("backward verification failed: {error}"))?;
            checker.stats().clone()
        }
    };
    print_stats(mode, &stats);
    Ok(())
}

fn print_stats(mode: Mode, stats: &Stats) {
    eprintln!("c mode={mode:?} stats={stats:?}");
}

#[cfg(test)]
mod tests {
    use super::{parse_invocation, Invocation, Mode};
    use std::ffi::OsString;
    use std::path::Path;

    fn argv(words: &[&str]) -> Vec<OsString> {
        words.iter().map(OsString::from).collect()
    }

    /// `execve` may start a process with no arguments at all; the dispatcher
    /// used to hit `unreachable!` there. It is now a usage error.
    #[test]
    fn empty_argv_is_a_usage_error() -> Result<(), String> {
        let got = parse_invocation(&[]);
        if got != Invocation::Usage {
            return Err(format!("empty argv: expected Usage, got {got:?}"));
        }
        Ok(())
    }

    #[test]
    fn command_lines_keep_their_meaning() -> Result<(), String> {
        let cases: [(&[&str], Invocation<'_>); 8] = [
            (&["p"], Invocation::Usage),
            (&["p", "--provenance"], Invocation::Provenance),
            (&["p", "--backward"], Invocation::Usage),
            (
                &["p", "f.cnf", "p.drat"],
                Invocation::Check {
                    cnf: Path::new("f.cnf"),
                    proof: Path::new("p.drat"),
                    mode: Mode::Forward,
                },
            ),
            (
                &["p", "f.cnf", "p.drat", "--backward"],
                Invocation::Check {
                    cnf: Path::new("f.cnf"),
                    proof: Path::new("p.drat"),
                    mode: Mode::Backward,
                },
            ),
            (&["p", "f.cnf", "p.drat", "--forward"], Invocation::Usage),
            (
                &["p", "f.cnf", "p.drat", "--backward", "x"],
                Invocation::Usage,
            ),
            (
                &["p", "--provenance", "x"],
                Invocation::Check {
                    cnf: Path::new("--provenance"),
                    proof: Path::new("x"),
                    mode: Mode::Forward,
                },
            ),
        ];
        for (words, want) in cases {
            let args = argv(words);
            let got = parse_invocation(&args);
            if got != want {
                return Err(format!("{words:?}: expected {want:?}, got {got:?}"));
            }
        }
        Ok(())
    }
}
