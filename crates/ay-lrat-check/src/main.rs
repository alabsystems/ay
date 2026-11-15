// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

/// What the command line asks for.
#[derive(Debug, Eq, PartialEq)]
enum Invocation<'a> {
    Provenance,
    Check { cnf: &'a Path, proof: &'a Path },
    Usage,
}

/// Classify the argument vector (program name first). An empty vector, which
/// `execve` permits, is a usage error rather than a panic; arguments are read
/// as `OsString`, so a non-UTF-8 path is a path rather than a panic in
/// `std::env::args`.
fn parse_invocation(args: &[OsString]) -> Invocation<'_> {
    match (args.get(1), args.get(2), args.get(3)) {
        (Some(flag), None, _) if flag == "--provenance" => Invocation::Provenance,
        (Some(cnf), Some(proof), None) => Invocation::Check {
            cnf: Path::new(cnf),
            proof: Path::new(proof),
        },
        _ => Invocation::Usage,
    }
}

fn usage(program: Option<&OsString>) {
    let program = program.map_or(Path::new("ay-lrat-check"), Path::new);
    eprintln!("usage: {} FORMULA.cnf PROOF.lrat", program.display());
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
        Invocation::Check { cnf, proof } => run(cnf, proof),
        Invocation::Usage => {
            usage(args.first());
            Ok(false)
        }
    };

    match result {
        Ok(true) => {
            println!("s VERIFIED");
            ExitCode::SUCCESS
        }
        Ok(false) => {
            println!("s NOT VERIFIED");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("c {error}");
            println!("s NOT VERIFIED");
            return ExitCode::from(1);
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

fn run(cnf_path: &Path, proof_path: &Path) -> Result<bool, String> {
    let cnf_data = fs::read(cnf_path)
        .map_err(|error| format!("cannot read {}: {error}", cnf_path.display()))?;
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(&cnf_data[..])
        .map_err(|error| format!("cannot parse {}: {error}", cnf_path.display()))?;
    if cnf.num_vars > ay_lrat_check::checker::MAX_DENSE_VARS {
        return Err(format!(
            "cannot check {}: variable count {} exceeds dense checker maximum {}",
            cnf_path.display(),
            cnf.num_vars,
            ay_lrat_check::checker::MAX_DENSE_VARS
        ));
    }

    let proof_data = fs::read(proof_path)
        .map_err(|error| format!("cannot read {}: {error}", proof_path.display()))?;
    let steps = if ay_lrat_check::lrat_parser::is_binary_lrat(&proof_data) {
        ay_lrat_check::lrat_parser::parse_binary_lrat(&proof_data).map_err(|error| {
            format!("cannot parse binary LRAT {}: {error}", proof_path.display())
        })?
    } else {
        let proof_text = std::str::from_utf8(&proof_data).map_err(|error| {
            format!("cannot decode text LRAT {}: {error}", proof_path.display())
        })?;
        ay_lrat_check::lrat_parser::parse_text_lrat(proof_text)
            .map_err(|error| format!("cannot parse text LRAT {}: {error}", proof_path.display()))?
    };

    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        if !checker.add_original(*id, clause) {
            eprintln!("c {}", checker.stats_summary());
            return Ok(false);
        }
    }

    let verified = checker.verify_proof(&steps);
    eprintln!("c {}", checker.stats_summary());
    Ok(verified)
}

#[cfg(test)]
mod tests {
    use super::{parse_invocation, Invocation};
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

    /// A non-UTF-8 path used to panic inside `std::env::args`; it is now a path.
    #[cfg(unix)]
    #[test]
    fn non_utf8_path_is_a_path() -> Result<(), String> {
        use std::os::unix::ffi::OsStringExt;
        let cnf = OsString::from_vec(vec![b'f', 0xff, b'.', b'c', b'n', b'f']);
        let args = vec![OsString::from("p"), cnf.clone(), OsString::from("p.lrat")];
        let want = Invocation::Check {
            cnf: Path::new(&cnf),
            proof: Path::new("p.lrat"),
        };
        let got = parse_invocation(&args);
        if got != want {
            return Err(format!("expected {want:?}, got {got:?}"));
        }
        Ok(())
    }

    #[test]
    fn command_lines_keep_their_meaning() -> Result<(), String> {
        let cases: [(&[&str], Invocation<'_>); 6] = [
            (&["p"], Invocation::Usage),
            (&["p", "--provenance"], Invocation::Provenance),
            (
                &["p", "f.cnf", "p.lrat"],
                Invocation::Check {
                    cnf: Path::new("f.cnf"),
                    proof: Path::new("p.lrat"),
                },
            ),
            (&["p", "f.cnf", "p.lrat", "x"], Invocation::Usage),
            (
                &["p", "--provenance", "x"],
                Invocation::Check {
                    cnf: Path::new("--provenance"),
                    proof: Path::new("x"),
                },
            ),
            (&["p", "--provenance", "x", "y"], Invocation::Usage),
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
