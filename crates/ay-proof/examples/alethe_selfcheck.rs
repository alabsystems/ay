// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Offline driver for the Alethe document self-check.
//!
//! ```text
//! alethe_selfcheck [--dialect clean|pinned-carcara] PROOF.alethe PROBLEM.smt2
//! ```
//!
//! Prints one line — `ACCEPT <json>` or `REJECT <tag> <message>` — and exits
//! 0 / 1. Exists so the self-check can be differentially measured against
//! carcara over a whole benchmark corpus without running the solver, and so a
//! human can point it at any `.alethe` file AY has already written.
//!
//! `--dialect` names the checker the document is spelled for (`ay
//! --alethe-dialect`), which fixes the rule vocabulary the check accepts. The
//! default is `clean`, AY's default dialect, whose vocabulary adds
//! `dt_project`. A differential run against PINNED Carcara passes
//! `--dialect pinned-carcara`: pinned Carcara answers `unknown rule` for
//! `dt_project`, and so does the check in that vocabulary.
//!
//! The proof is streamed in 1 MiB chunks: the corpus contains a 687 MB
//! document and the point of the streaming exporter is that such a document is
//! never materialized.

use ay_proof::{AletheDialect, AletheDocumentChecker, ProblemScope};
use std::io::Read;

const USAGE: &str =
    "usage: alethe_selfcheck [--dialect clean|pinned-carcara] PROOF.alethe PROBLEM.smt2";

/// The checker the document is spelled for (`--dialect`), and the two
/// positional paths; `None` for any other command line.
fn parse_args(mut args: Vec<String>) -> Option<(AletheDialect, String, String)> {
    let mut dialect = AletheDialect::default();
    if let Some(at) = args.iter().position(|arg| arg == "--dialect") {
        dialect = match args.get(at + 1).map(String::as_str) {
            Some("clean") => AletheDialect::Clean,
            Some("pinned-carcara") => AletheDialect::PinnedCarcara,
            _ => return None,
        };
        args.drain(at..at + 2);
    }
    let [proof, problem]: [String; 2] = args.try_into().ok()?;
    Some((dialect, proof, problem))
}

fn main() {
    let Some((dialect, proof, problem)) = parse_args(std::env::args().skip(1).collect()) else {
        eprintln!("{USAGE}");
        std::process::exit(2);
    };
    let args = [proof, problem];
    let problem = match std::fs::read_to_string(&args[1]) {
        Ok(text) => text,
        Err(error) => {
            println!("ERROR problem-unreadable {error}");
            std::process::exit(2);
        }
    };
    let scope = ProblemScope::from_smtlib_source(&problem);
    let file = match std::fs::File::open(&args[0]) {
        Ok(file) => file,
        Err(error) => {
            println!("ERROR proof-unreadable {error}");
            std::process::exit(2);
        }
    };
    let mut reader = std::io::BufReader::with_capacity(1 << 20, file);
    let mut checker = AletheDocumentChecker::new(scope).with_dialect(dialect);
    let mut buf = vec![0u8; 1 << 20];
    loop {
        match reader.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => {
                if let Err(defect) = checker.push_bytes(&buf[..n]) {
                    println!("REJECT {} {defect}", defect.tag());
                    std::process::exit(1);
                }
            }
            Err(error) => {
                println!("ERROR proof-read-failed {error}");
                std::process::exit(2);
            }
        }
    }
    match checker.finish() {
        Ok(report) => {
            println!(
                "ACCEPT {{\"commands\":{},\"steps\":{},\"assumes\":{},\"anchors\":{},\"define_funs\":{},\"distinct_rules\":{}}}",
                report.commands,
                report.steps,
                report.assumes,
                report.anchors,
                report.define_funs,
                report.distinct_rules
            );
        }
        Err(defect) => {
            println!("REJECT {} {defect}", defect.tag());
            std::process::exit(1);
        }
    }
}
