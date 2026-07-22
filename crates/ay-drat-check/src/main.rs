// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use ay_drat_check::checker::{backward::BackwardChecker, DratChecker, Stats};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::Path;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Forward,
    Backward,
}

fn main() {
    let args = env::args_os().collect::<Vec<_>>();
    if matches!(args.as_slice(), [_, flag] if flag == "--provenance") {
        print_exact_provenance();
        return;
    }
    let result = match args.as_slice() {
        [_, cnf, proof] => run(Path::new(cnf), Path::new(proof), Mode::Forward),
        [_, cnf, proof, flag] if flag == "--backward" => {
            run(Path::new(cnf), Path::new(proof), Mode::Backward)
        }
        [program, ..] => {
            usage(program);
            Err("invalid command line".to_owned())
        }
        [] => unreachable!("argv always includes program name"),
    };

    match result {
        Ok(()) => {
            println!("s VERIFIED");
            std::process::exit(0);
        }
        Err(error) => {
            eprintln!("c {error}");
            println!("s NOT VERIFIED");
            std::process::exit(1);
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

fn usage(program: &OsString) {
    eprintln!(
        "usage: {} FORMULA.cnf PROOF.drat [--backward]",
        Path::new(program).display()
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
