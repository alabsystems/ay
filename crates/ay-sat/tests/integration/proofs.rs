// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common;
use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};
use ntest::timeout;

/// Test that DRAT proof is generated for simple UNSAT formula
#[test]
#[timeout(5_000)]
fn test_drat_proof_generation() {
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof =
        String::from_utf8(writer.into_vec().expect("proof writer flush")).expect("Valid UTF-8");

    assert!(
        proof.contains("0\n"),
        "Proof should contain empty clause: {proof}"
    );
}

/// Test that multiple UNSAT formulas generate valid proofs
#[test]
#[timeout(5_000)]
fn test_drat_proof_multiple_unsat() {
    let unsat_formulas = [
        "p cnf 1 2\n1 0\n-1 0\n",
        "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n",
        "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n",
    ];

    for (i, dimacs) in unsat_formulas.iter().enumerate() {
        let formula = parse_dimacs(dimacs).expect("Failed to parse");

        let proof_buffer: Vec<u8> = Vec::new();
        let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);

        for clause in formula.clauses {
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();
        assert!(result.is_unsat(), "Formula {i} should be UNSAT");

        let writer = solver
            .take_proof_writer()
            .expect("Proof writer should exist");
        let proof =
            String::from_utf8(writer.into_vec().expect("proof writer flush")).expect("Valid UTF-8");

        assert!(
            proof.ends_with("0\n"),
            "Formula {i} proof should end with empty clause: {proof}"
        );
    }
}

/// DRAT proof smoke test using synthetic UNSAT formulas.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(10_000))]
fn test_drat_smoke_synthetic() {
    let drat_trim_path = common::find_drat_trim();
    if drat_trim_path.is_none() {
        eprintln!("Note: drat-trim not found. Will only verify proof structure.");
        eprintln!("Install: cargo install drat-trim, or:");
        eprintln!(
            "  git clone https://github.com/marijnheule/drat-trim /tmp/drat-trim && cd /tmp/drat-trim && make && sudo cp drat-trim /usr/local/bin/"
        );
        assert!(
            std::env::var_os("CI").is_none(),
            "drat-trim is required in CI for exhaustive DRAT verification"
        );
    }

    let unsat_formulas = [
        ("x_and_not_x", "p cnf 1 2\n1 0\n-1 0\n"),
        ("y_and_not_y", "p cnf 2 2\n2 0\n-2 0\n"),
        ("unit_chain_2", "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n"),
        ("unit_chain_3", "p cnf 3 4\n1 2 3 0\n-1 0\n-2 0\n-3 0\n"),
        ("php_2_1", "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"),
        ("amo_conflict", "p cnf 3 4\n1 0\n2 0\n-1 -2 0\n3 0\n"),
        ("impl_chain", "p cnf 4 5\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n-4 0\n"),
        ("resolution_1", "p cnf 3 6\n1 2 0\n1 -2 0\n-1 3 0\n-1 -3 0\n2 3 0\n-2 -3 0\n"),
        ("double_impl", "p cnf 2 4\n1 0\n-1 2 0\n-2 0\n1 -2 0\n"),
        ("dual_conflict", "p cnf 2 4\n1 0\n-1 0\n2 0\n-2 0\n"),
        ("amo_zero", "p cnf 2 3\n-1 0\n-2 0\n1 2 0\n"),
        ("php_3_2", "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n"),
        ("chain_5", "p cnf 5 6\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n-4 5 0\n-5 0\n"),
        ("binary_unsat", "p cnf 3 6\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n1 3 0\n-3 0\n"),
        ("mixed_sizes", "p cnf 4 5\n1 2 3 4 0\n-1 0\n-2 0\n-3 0\n-4 0\n"),
    ];

    let mut structure_verified_count = 0;
    let mut external_verified_count = 0;
    let mut external_failures = Vec::new();

    for (name, dimacs) in &unsat_formulas {
        let formula = parse_dimacs(dimacs).expect("Failed to parse");

        let proof_buffer: Vec<u8> = Vec::new();
        let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);

        for clause in formula.clauses {
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();
        assert!(result.is_unsat(), "Formula '{name}' should be UNSAT");

        let writer = solver
            .take_proof_writer()
            .expect("Proof writer should exist");
        let proof = writer.into_vec().expect("proof writer flush");

        let proof_text = String::from_utf8_lossy(&proof);
        assert!(
            proof_text.ends_with("0\n"),
            "Formula '{name}' proof should end with empty clause"
        );
        structure_verified_count += 1;

        if let Some(ref drat_trim_bin) = drat_trim_path {
            let temp_dir = std::env::temp_dir();
            let cnf_path = temp_dir.join(format!("ay_test_{}_{}.cnf", name, std::process::id()));
            let proof_path = temp_dir.join(format!("ay_test_{}_{}.drat", name, std::process::id()));

            std::fs::write(&cnf_path, dimacs).expect("Write CNF");
            std::fs::write(&proof_path, &proof).expect("Write proof");

            let output = std::process::Command::new(drat_trim_bin)
                .arg(&cnf_path)
                .arg(&proof_path)
                .output()
                .expect("Execute drat-trim");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            let _ = std::fs::remove_file(&cnf_path);
            let _ = std::fs::remove_file(&proof_path);

            if output.status.success() {
                external_verified_count += 1;
            } else {
                external_failures.push(format!(
                    "{}: status={} stdout='{}' stderr='{}'",
                    name,
                    output
                        .status
                        .code()
                        .map_or_else(|| "signal".to_string(), |c| c.to_string()),
                    stdout.trim(),
                    stderr.trim()
                ));
            }
        }
    }

    let total = unsat_formulas.len();
    assert_eq!(
        structure_verified_count, total,
        "All UNSAT formulas must produce structurally complete proofs"
    );

    if drat_trim_path.is_some() {
        assert!(
            external_failures.is_empty(),
            "drat-trim failed for {} formula(s):\n{}",
            external_failures.len(),
            external_failures.join("\n")
        );
        assert_eq!(
            external_verified_count, total,
            "All UNSAT formulas must verify with drat-trim"
        );
    } else {
        eprintln!(
            "DRAT external verification skipped (drat-trim unavailable). Structure-verified {structure_verified_count}/{total} proofs."
        );
    }
}

/// DRAT proof verification using DIMACS benchmark corpus.
#[test]
#[timeout(60_000)]
fn test_drat_corpus_verification() {
    let Some(drat_trim_path) = common::find_drat_trim() else {
        eprintln!("Skipping: drat-trim not found");
        return;
    };

    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let workspace_root = std::path::Path::new(&manifest_dir)
        .parent()
        .and_then(|p| p.parent())
        .expect("cannot determine workspace root");
    let corpus_dir = workspace_root.join("benchmarks/sat/unsat");

    let mut corpus_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "cnf") {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    corpus_files.sort();

    assert!(
        !corpus_files.is_empty(),
        "No .cnf files found in {}. DRAT corpus verification requires at least one benchmark.",
        corpus_dir.display()
    );

    let mut structure_verified = 0;
    let mut external_verified = 0;
    let mut failures: Vec<String> = Vec::new();

    for cnf_path in &corpus_files {
        let name = cnf_path
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let dimacs_content = std::fs::read_to_string(cnf_path).expect("read corpus .cnf file");
        let formula = parse_dimacs(&dimacs_content)
            .unwrap_or_else(|e| panic!("Failed to parse {}: {}", cnf_path.display(), e));

        let proof_buffer: Vec<u8> = Vec::new();
        let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);
        for clause in formula.clauses {
            solver.add_clause(clause);
        }
        let result = solver.solve().into_inner();

        assert!(
            result.is_unsat(),
            "Corpus formula '{name}' should be UNSAT (got {result:?})"
        );

        let writer = solver
            .take_proof_writer()
            .expect("proof writer should exist");
        let proof = writer.into_vec().expect("proof writer flush");
        let proof_text = String::from_utf8_lossy(&proof);
        assert!(
            proof_text.ends_with("0\n"),
            "Corpus formula '{name}' proof should end with empty clause marker"
        );
        structure_verified += 1;

        let temp_dir = std::env::temp_dir();
        let proof_path = temp_dir.join(format!("ay_corpus_{}_{}.drat", name, std::process::id()));
        std::fs::write(&proof_path, &proof).expect("write proof");

        let output = std::process::Command::new(&drat_trim_path)
            .arg(cnf_path)
            .arg(&proof_path)
            .output()
            .expect("execute drat-trim");
        let _ = std::fs::remove_file(&proof_path);

        if output.status.success() {
            external_verified += 1;
        } else {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            failures.push(format!(
                "{}: status={} stdout='{}' stderr='{}'",
                name,
                output
                    .status
                    .code()
                    .map_or_else(|| "signal".to_string(), |c| c.to_string()),
                stdout.trim(),
                stderr.trim()
            ));
        }
    }

    let total = corpus_files.len();

    eprintln!(
        "DRAT corpus verification: {structure_verified}/{total} structure-verified, {external_verified}/{total} external-verified"
    );

    assert_eq!(
        structure_verified, total,
        "All corpus UNSAT formulas must produce structurally valid proofs"
    );

    assert!(
        failures.is_empty(),
        "drat-trim failed for {} corpus formula(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert_eq!(
        external_verified, total,
        "All corpus formulas must verify with drat-trim ({external_verified}/{total})"
    );
    eprintln!("DRAT corpus: ALL {total}/{total} benchmarks externally verified by drat-trim");
}

fn solve_and_verify_lrat(name: &str, dimacs: &str) -> Result<(), String> {
    let formula = parse_dimacs(dimacs).unwrap_or_else(|e| panic!("Failed to parse '{name}': {e}"));
    let n_clauses = formula.clauses.len() as u64;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), n_clauses);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "Formula '{name}' should be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8(proof_bytes).expect("LRAT proof should be UTF-8");

    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("Failed to re-parse '{name}' for LRAT: {e}"));
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(&proof_text)
        .map_err(|e| format!("{name}: LRAT parse error: {e}"))?;

    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        assert!(
            checker.add_original(*id, clause),
            "'{name}': add_original failed for clause {id}"
        );
    }
    if checker.verify_proof(&steps) {
        Ok(())
    } else {
        Err(format!(
            "{name}: LRAT verification FAILED\nproof (first 500 chars):\n{}",
            &proof_text[..proof_text.len().min(500)]
        ))
    }
}

/// Exhaustive LRAT proof verification using inline UNSAT formulas.
#[test]
#[timeout(30_000)]
fn test_exhaustive_lrat_verification() {
    let unsat_formulas = [
        ("x_and_not_x", "p cnf 1 2\n1 0\n-1 0\n"),
        ("y_and_not_y", "p cnf 2 2\n2 0\n-2 0\n"),
        ("unit_chain_2", "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n"),
        ("unit_chain_3", "p cnf 3 4\n1 2 3 0\n-1 0\n-2 0\n-3 0\n"),
        ("php_2_1", "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"),
        ("amo_conflict", "p cnf 3 4\n1 0\n2 0\n-1 -2 0\n3 0\n"),
        ("impl_chain", "p cnf 4 5\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n-4 0\n"),
        ("resolution_1", "p cnf 3 6\n1 2 0\n1 -2 0\n-1 3 0\n-1 -3 0\n2 3 0\n-2 -3 0\n"),
        ("double_impl", "p cnf 2 4\n1 0\n-1 2 0\n-2 0\n1 -2 0\n"),
        ("dual_conflict", "p cnf 2 4\n1 0\n-1 0\n2 0\n-2 0\n"),
        ("amo_zero", "p cnf 2 3\n-1 0\n-2 0\n1 2 0\n"),
        ("php_3_2", "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n"),
        ("chain_5", "p cnf 5 6\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n-4 5 0\n-5 0\n"),
        ("binary_unsat", "p cnf 3 6\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n1 3 0\n-3 0\n"),
        ("mixed_sizes", "p cnf 4 5\n1 2 3 4 0\n-1 0\n-2 0\n-3 0\n-4 0\n"),
    ];

    let mut failures: Vec<String> = Vec::new();
    for (name, dimacs) in &unsat_formulas {
        if let Err(e) = solve_and_verify_lrat(name, dimacs) {
            failures.push(e);
        }
    }
    let total = unsat_formulas.len();
    assert!(
        failures.is_empty(),
        "LRAT verification failed for {} of {total} formula(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    eprintln!("LRAT inline: ALL {total}/{total} verified by ay-lrat-check (in-process)");
}

/// LRAT proof verification using DIMACS benchmark corpus.
#[test]
#[timeout(60_000)]
fn test_lrat_corpus_verification() {
    let corpus_dir = common::workspace_root().join("benchmarks/sat/unsat");
    let mut corpus_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            path.extension()
                .is_some_and(|ext| ext == "cnf")
                .then_some(path)
        })
        .collect();
    corpus_files.sort();
    assert!(
        !corpus_files.is_empty(),
        "No .cnf files in {}. LRAT corpus verification requires benchmarks.",
        corpus_dir.display()
    );

    let mut failures: Vec<String> = Vec::new();
    for cnf_path in &corpus_files {
        let name = cnf_path.file_stem().unwrap_or_default().to_string_lossy();
        let dimacs = std::fs::read_to_string(cnf_path).expect("read corpus .cnf file");
        if let Err(e) = solve_and_verify_lrat(&name, &dimacs) {
            failures.push(e);
        }
    }
    let total = corpus_files.len();
    eprintln!(
        "LRAT corpus: {}/{total} verified by ay-lrat-check (in-process)",
        total - failures.len()
    );
    assert!(
        failures.is_empty(),
        "LRAT verification failed for {} of {total} corpus formula(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
}

/// Test that SAT formulas don't produce proofs (proof is only for UNSAT)
#[test]
#[timeout(1_000)]
fn test_no_proof_for_sat() {
    let dimacs = r"
p cnf 2 1
1 2 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {
            let writer = solver
                .take_proof_writer()
                .expect("Proof writer should exist");
            let proof = String::from_utf8(writer.into_vec().expect("proof writer flush"))
                .expect("Valid UTF-8");
            let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
            assert!(
                !has_empty_clause,
                "SAT formula should not have empty clause in proof: {proof:?}"
            );
        }
        _ => panic!("Formula should be SAT"),
    }
}
