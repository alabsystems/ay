// Copyright 2026 Andrew Yates
// Standalone driver for the native PR/SR checker (verification harness).
// Usage: sr_check <cnf> <proof>

use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_drat_check::SrChecker;
use std::ffi::OsString;
use std::path::Path;
use std::process::ExitCode;

/// Exit status for a command-line error (unchanged from the original driver).
const EXIT_USAGE: u8 = 2;
/// Exit status when an input cannot be read or parsed. The original driver
/// panicked here, which exits with 101; scripts keep seeing that status.
const EXIT_INPUT_ERROR: u8 = 101;

/// The two input paths, or `None` when the command line has any other shape.
/// An empty argument vector (which `execve` permits) is a usage error.
fn input_paths(args: &[OsString]) -> Option<(&Path, &Path)> {
    match args {
        [_, cnf, proof] => Some((Path::new(cnf), Path::new(proof))),
        _ => None,
    }
}

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().collect();
    let Some((cnf_path, proof_path)) = input_paths(&args) else {
        let program = args
            .first()
            .map_or(Path::new("sr_check"), |program| Path::new(program));
        eprintln!("Usage: {} <cnf> <proof>", program.display());
        return ExitCode::from(EXIT_USAGE);
    };
    let cnf_bytes = match std::fs::read(cnf_path) {
        Ok(bytes) => bytes,
        Err(e) => return input_error("read cnf", &e),
    };
    let proof_bytes = match std::fs::read(proof_path) {
        Ok(bytes) => bytes,
        Err(e) => return input_error("read proof", &e),
    };
    let cnf = match parse_cnf(&cnf_bytes[..]) {
        Ok(cnf) => cnf,
        Err(e) => return input_error("parse cnf", &e),
    };
    let steps = match parse_drat(&proof_bytes) {
        Ok(steps) => steps,
        Err(e) => return input_error("parse proof", &e),
    };
    let mut chk = SrChecker::new(cnf.num_vars, true);
    match chk.verify(&cnf.clauses, &steps) {
        Ok(()) => {
            println!("s VERIFIED");
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("s NOT VERIFIED");
            eprintln!("c {e}");
            ExitCode::FAILURE
        }
    }
}

fn input_error(what: &str, error: &dyn std::fmt::Debug) -> ExitCode {
    eprintln!("{what}: {error:?}");
    ExitCode::from(EXIT_INPUT_ERROR)
}

#[cfg(test)]
mod tests {
    use super::input_paths;
    use std::ffi::OsString;
    use std::path::Path;

    fn argv(words: &[&str]) -> Vec<OsString> {
        words.iter().map(OsString::from).collect()
    }

    /// `execve` permits an empty argument vector; the usage path used to index
    /// `args[0]` and panic there. It is now a usage error.
    #[test]
    fn empty_argv_is_a_usage_error() -> Result<(), String> {
        let got = input_paths(&[]);
        if got.is_some() {
            return Err(format!("empty argv parsed as {got:?}"));
        }
        Ok(())
    }

    #[test]
    fn command_lines_keep_their_meaning() -> Result<(), String> {
        let cases: [(&[&str], Option<(&Path, &Path)>); 4] = [
            (&["p"], None),
            (&["p", "f.cnf"], None),
            (
                &["p", "f.cnf", "p.drat"],
                Some((Path::new("f.cnf"), Path::new("p.drat"))),
            ),
            (&["p", "f.cnf", "p.drat", "x"], None),
        ];
        for (words, want) in cases {
            let args = argv(words);
            let got = input_paths(&args);
            if got != want {
                return Err(format!("{words:?}: got {got:?}, want {want:?}"));
            }
        }
        Ok(())
    }
}
