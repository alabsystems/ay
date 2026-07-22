// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use std::env;
use std::fs;
use std::path::Path;

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if matches!(args.as_slice(), [_, flag] if flag == "--provenance") {
        print_exact_provenance();
        return;
    }
    let result = match args.as_slice() {
        [_, cnf, proof] => run(Path::new(cnf), Path::new(proof)),
        [program, ..] => {
            eprintln!("usage: {program} FORMULA.cnf PROOF.lrat");
            Ok(false)
        }
        [] => unreachable!("argv always includes program name"),
    };

    match result {
        Ok(true) => {
            println!("s VERIFIED");
            std::process::exit(0);
        }
        Ok(false) => {
            println!("s NOT VERIFIED");
            std::process::exit(1);
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
