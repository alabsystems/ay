// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Offline driver for the Alethe document self-check.
//!
//! ```text
//! alethe_selfcheck PROOF.alethe PROBLEM.smt2
//! ```
//!
//! Prints one line — `ACCEPT <json>` or `REJECT <tag> <message>` — and exits
//! 0 / 1. Exists so the self-check can be differentially measured against
//! carcara over a whole benchmark corpus without running the solver, and so a
//! human can point it at any `.alethe` file AY has already written.
//!
//! The proof is streamed in 1 MiB chunks: the corpus contains a 687 MB
//! document and the point of the streaming exporter is that such a document is
//! never materialized.

use ay_proof::{AletheDocumentChecker, ProblemScope};
use std::io::Read;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 2 {
        eprintln!("usage: alethe_selfcheck PROOF.alethe PROBLEM.smt2");
        std::process::exit(2);
    }
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
    let mut checker = AletheDocumentChecker::new(scope);
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
