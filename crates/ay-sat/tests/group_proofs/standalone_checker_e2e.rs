// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests: ay solver produces LRAT/DRAT proofs, standalone
//! ay-lrat-check verifies LRAT, and the ay-drat-check library verifies DRAT.
//!
//! These tests ensure the proof checker crates correctly validate proofs
//! produced by the ay SAT solver. They also cross-validate against the external
//! `lrat-check` binary (from drat-trim suite) when available.
//!
//! Reference: #5186, #5187

use super::common::{
    find_lrat_check, require_ay_lrat_check, BuiltWorkspaceBinary, PHP32_DIMACS, PHP43_DIMACS,
};
use ay_drat_check::ConcludeResult;
use ay_drat_check::{checker::DratChecker, cnf_parser::parse_cnf, drat_parser::parse_drat};
use ay_sat::{parse_dimacs, ProofOutput, Solver};
use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

// Every LRAT test can be the first caller in a fresh checkout. Its 600-second
// budget includes the one source-identified, isolated checker build; the proof
// generation/checking portion retains its ordinary short runtime in practice.

/// PHP(2,1): 2 pigeons, 1 hole — simplest UNSAT instance.
const PHP21_DIMACS: &str = "\
p cnf 2 3
1 0
2 0
-1 -2 0
";

fn temp_paths(prefix: &str) -> (PathBuf, PathBuf) {
    let seq = TEMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("ay_e2e_{prefix}_{pid}_{seq}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_e2e_{prefix}_{pid}_{seq}.proof"));
    (cnf, proof)
}

/// Solve a DIMACS formula with ay, produce LRAT proof, validate with ay-lrat-check.
fn solve_and_check_lrat(dimacs: &str, checker: &BuiltWorkspaceBinary, label: &str) {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");
    let proof_text = String::from_utf8(proof_bytes.clone()).expect("UTF-8 proof");
    assert!(!proof_text.is_empty(), "{label}: proof must not be empty");

    let (cnf_path, proof_path) = temp_paths(&format!("lrat_{label}"));
    std::fs::write(&cnf_path, dimacs).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write LRAT proof");

    let output = checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to run ay-lrat-check: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    assert!(
        output.status.success() && stdout.contains("s VERIFIED"),
        "ay-lrat-check FAILED on {label}\n\
         exit: {}\nstdout: {stdout}\nstderr: {stderr}\n\
         proof (first 500 chars): {}",
        output.status,
        &proof_text[..proof_text.len().min(500)]
    );
    eprintln!("ay-lrat-check VERIFIED ({label})");
}

/// Solve a DIMACS formula with ay, produce DRAT proof, validate with ay-drat-check.
fn solve_and_check_drat(dimacs: &str, label: &str) {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    let proof_writer = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");
    let proof_text = String::from_utf8(proof_bytes.clone()).expect("UTF-8 proof");
    assert!(!proof_text.is_empty(), "{label}: proof must not be empty");

    let cnf = parse_cnf(dimacs.as_bytes()).expect("parse checker CNF");
    let steps = parse_drat(&proof_bytes).expect("parse DRAT proof");
    let mut checker = DratChecker::new(cnf.num_vars, true);
    checker
        .verify(&cnf.clauses, &steps)
        .unwrap_or_else(|err| panic!("ay-drat-check FAILED on {label}: {err}"));
    assert!(
        matches!(checker.conclude_unsat(), ConcludeResult::Verified),
        "ay-drat-check FAILED to conclude UNSAT on {label}\n\
         proof (first 500 chars): {}",
        &proof_text[..proof_text.len().min(500)]
    );
    eprintln!("ay-drat-check VERIFIED ({label})");
}

// ============================================================================
// ay-lrat-check end-to-end tests
// ============================================================================

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_php21() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat(PHP21_DIMACS, checker, "php21");
}

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_php32() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat(PHP32_DIMACS, checker, "php32");
}

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_php43() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat(PHP43_DIMACS, checker, "php43");
}

// ============================================================================
// ay-drat-check end-to-end tests
// ============================================================================

#[test]
#[timeout(30_000)]
fn test_e2e_drat_php21() {
    solve_and_check_drat(PHP21_DIMACS, "php21");
}

#[test]
#[timeout(30_000)]
fn test_e2e_drat_php32() {
    solve_and_check_drat(PHP32_DIMACS, "php32");
}

#[test]
#[timeout(60_000)]
fn test_e2e_drat_php43() {
    solve_and_check_drat(PHP43_DIMACS, "php43");
}

// ============================================================================
// Cross-validation: ay-lrat-check vs external lrat-check on same proof
// ============================================================================

/// Generates an LRAT proof with ay, then validates it with BOTH ay-lrat-check
/// and the external lrat-check binary (from drat-trim suite). This ensures the
/// standalone checker produces the same results as the established reference.
#[test]
#[timeout(600_000)]
fn test_cross_validate_lrat_php32() {
    let ay_checker = require_ay_lrat_check();
    // External lrat-check from drat-trim suite may not be installed — skip
    // cross-validation (but not the ay-lrat-check part) if missing.
    let ext_checker = match find_lrat_check() {
        Some(p) => p,
        None => {
            eprintln!("external lrat-check not found, skipping cross-validation");
            return;
        }
    };

    let formula = parse_dimacs(PHP32_DIMACS).expect("parse");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("flush");

    let (cnf_path, proof_path) = temp_paths("cross_lrat_php32");
    std::fs::write(&cnf_path, PHP32_DIMACS).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write proof");

    // Validate with ay-lrat-check
    let ay_out = ay_checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("run ay-lrat-check");

    // Validate with external lrat-check
    let ext_out = Command::new(&ext_checker)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("run external lrat-check");

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    let ay_ok =
        ay_out.status.success() && String::from_utf8_lossy(&ay_out.stdout).contains("s VERIFIED");
    let ext_ok = ext_out.status.success();

    assert!(
        ay_ok,
        "ay-lrat-check failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&ay_out.stdout),
        String::from_utf8_lossy(&ay_out.stderr)
    );
    assert!(
        ext_ok,
        "external lrat-check failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&ext_out.stdout),
        String::from_utf8_lossy(&ext_out.stderr)
    );
    eprintln!(
        "Cross-validation passed: both ay-lrat-check and external lrat-check agree on PHP(3,2)"
    );
}

// ============================================================================
// CaDiCaL cross-validation: verify CaDiCaL-generated LRAT proofs with ay-lrat-check
// ============================================================================

/// Find CaDiCaL binary in reference/ directory.
///
/// Searches in workspace root first, then falls back to the main git repo root.
/// In worktree checkouts, the `reference/` directory may only exist in the main
/// repo, not in the worktree itself.
fn find_cadical() -> Option<PathBuf> {
    let ws = super::common::workspace_root();
    let candidate = ws.join("reference/cadical/build/cadical");
    if candidate.is_file() {
        return Some(candidate);
    }
    // In worktrees, try the main repo root (parent of `.git/worktrees/`).
    if let Ok(output) = Command::new("git")
        .arg("rev-parse")
        .arg("--git-common-dir")
        .current_dir(&ws)
        .output()
    {
        if output.status.success() {
            let git_common = String::from_utf8_lossy(&output.stdout).trim().to_owned();
            // `git_common` is typically `<repo>/.git`; its parent is the root.
            let main_root = Path::new(&git_common).parent()?;
            let candidate = main_root.join("reference/cadical/build/cadical");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

/// Generate an LRAT proof from CaDiCaL and verify it with ay-lrat-check.
///
/// Tests both binary and text LRAT formats from CaDiCaL against the
/// standalone checker, ensuring interoperability.
fn cadical_lrat_cross_validate(
    cnf_content: &str,
    checker: &BuiltWorkspaceBinary,
    cadical_path: &Path,
    label: &str,
    binary: bool,
) {
    let (cnf_path, proof_path) = temp_paths(&format!(
        "cadical_{label}_{}",
        if binary { "bin" } else { "txt" }
    ));
    std::fs::write(&cnf_path, cnf_content).expect("write CNF");

    // Generate LRAT proof with CaDiCaL
    let mut cadical_cmd = Command::new(cadical_path);
    cadical_cmd.arg("--lrat");
    if !binary {
        cadical_cmd.arg("--binary=false");
    }
    cadical_cmd.arg(&cnf_path).arg(&proof_path);

    let cadical_out = cadical_cmd
        .output()
        .unwrap_or_else(|e| panic!("failed to run CaDiCaL: {e}"));

    // CaDiCaL exit 20 = UNSAT
    assert_eq!(
        cadical_out.status.code(),
        Some(20),
        "CaDiCaL did not return UNSAT for {label}:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&cadical_out.stdout),
        String::from_utf8_lossy(&cadical_out.stderr)
    );

    let proof_size = std::fs::metadata(&proof_path).map(|m| m.len()).unwrap_or(0);
    assert!(proof_size > 0, "CaDiCaL produced empty proof for {label}");

    // Verify with ay-lrat-check
    let check_out = checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to run ay-lrat-check: {e}"));

    let stdout = String::from_utf8_lossy(&check_out.stdout);
    let stderr = String::from_utf8_lossy(&check_out.stderr);

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    assert!(
        check_out.status.success() && stdout.contains("s VERIFIED"),
        "ay-lrat-check FAILED on CaDiCaL proof for {label} ({})\n\
         exit: {}\nstdout: {stdout}\nstderr: {stderr}",
        if binary { "binary" } else { "text" },
        check_out.status,
    );
    eprintln!(
        "CaDiCaL cross-validation VERIFIED: {label} ({})",
        if binary { "binary" } else { "text" }
    );
}

/// Cross-validate: CaDiCaL binary LRAT → ay-lrat-check on PHP(4,3).
#[test]
#[timeout(600_000)]
fn test_cadical_lrat_binary_php43() {
    let checker = require_ay_lrat_check();
    let Some(cadical) = find_cadical() else {
        eprintln!("CaDiCaL binary not found at reference/cadical/build/cadical; skipping");
        return;
    };
    cadical_lrat_cross_validate(PHP43_DIMACS, checker, &cadical, "php43", true);
}

/// Cross-validate: CaDiCaL text LRAT → ay-lrat-check on PHP(4,3).
#[test]
#[timeout(600_000)]
fn test_cadical_lrat_text_php43() {
    let checker = require_ay_lrat_check();
    let Some(cadical) = find_cadical() else {
        eprintln!("CaDiCaL binary not found at reference/cadical/build/cadical; skipping");
        return;
    };
    cadical_lrat_cross_validate(PHP43_DIMACS, checker, &cadical, "php43", false);
}

/// Cross-validate: CaDiCaL binary LRAT → ay-lrat-check on PHP(3,2).
#[test]
#[timeout(600_000)]
fn test_cadical_lrat_binary_php32() {
    let checker = require_ay_lrat_check();
    let Some(cadical) = find_cadical() else {
        eprintln!("CaDiCaL binary not found at reference/cadical/build/cadical; skipping");
        return;
    };
    cadical_lrat_cross_validate(PHP32_DIMACS, checker, &cadical, "php32", true);
}

/// Cross-validate: CaDiCaL binary LRAT → ay-lrat-check on PHP(2,1).
#[test]
#[timeout(600_000)]
fn test_cadical_lrat_binary_php21() {
    let checker = require_ay_lrat_check();
    let Some(cadical) = find_cadical() else {
        eprintln!("CaDiCaL binary not found at reference/cadical/build/cadical; skipping");
        return;
    };
    cadical_lrat_cross_validate(PHP21_DIMACS, checker, &cadical, "php21", true);
}

/// Cross-validate: CaDiCaL binary LRAT on benchmark files from disk.
/// Tests diverse problem structures beyond PHP (Ramsey, mutilated chessboard).
#[test]
#[timeout(600_000)]
fn test_cadical_lrat_binary_benchmarks() {
    let checker = require_ay_lrat_check();
    let Some(cadical) = find_cadical() else {
        eprintln!("CaDiCaL binary not found at reference/cadical/build/cadical; skipping");
        return;
    };
    let benchmarks = [
        "ramsey_r3_3_6",
        "mutilated_chessboard_2x2",
        "at_most_1_of_5",
        "urquhart_3",
        "mutex_4proc",
    ];
    for name in &benchmarks {
        let cnf_path = super::common::workspace_root()
            .join("benchmarks/sat/unsat")
            .join(format!("{name}.cnf"));
        assert!(
            cnf_path.exists(),
            "Benchmark {name}.cnf not found at {}",
            cnf_path.display()
        );
        let cnf = std::fs::read_to_string(&cnf_path).expect("read CNF");
        cadical_lrat_cross_validate(&cnf, checker, &cadical, name, true);
    }
}

// ============================================================================
// ay-lrat-check binary LRAT end-to-end tests (#5334)
//
// Validates ay's binary LRAT output through the standalone ay-lrat-check
// checker. All previous e2e tests use text LRAT format exclusively.
// Binary LRAT (LEB128) is the standard format for SAT Competition proof
// verification; gaps here block competition participation.
// ============================================================================

/// Solve a DIMACS formula with ay, produce binary LRAT proof, validate
/// with ay-lrat-check. Disables all inprocessing to isolate binary format
/// encoding from proof chain issues (#5236).
fn solve_and_check_lrat_binary(dimacs: &str, checker: &BuiltWorkspaceBinary, label: &str) {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    let proof_writer = ProofOutput::lrat_binary(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");
    assert!(
        !proof_bytes.is_empty(),
        "{label}: binary LRAT proof must not be empty"
    );

    let (cnf_path, proof_path) = temp_paths(&format!("lrat_bin_{label}"));
    std::fs::write(&cnf_path, dimacs).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write binary LRAT proof");

    let output = checker
        .command()
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to run ay-lrat-check on binary LRAT: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    assert!(
        output.status.success() && stdout.contains("s VERIFIED"),
        "ay-lrat-check FAILED on binary LRAT {label}\n\
         exit: {}\nstdout: {stdout}\nstderr: {stderr}\n\
         proof size: {} bytes",
        output.status,
        proof_bytes.len()
    );
    eprintln!(
        "ay-lrat-check VERIFIED binary LRAT ({label}, {} bytes)",
        proof_bytes.len()
    );
}

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_binary_php21() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat_binary(PHP21_DIMACS, checker, "binary_php21");
}

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_binary_php32() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat_binary(PHP32_DIMACS, checker, "binary_php32");
}

#[test]
#[timeout(600_000)]
fn test_e2e_lrat_binary_php43() {
    let checker = require_ay_lrat_check();
    solve_and_check_lrat_binary(PHP43_DIMACS, checker, "binary_php43");
}

/// Binary vs text LRAT cross-validation via ay-lrat-check.
///
/// Both formats must verify on the same formula. A failure in one
/// format but not the other indicates a format-specific encoding bug.
#[test]
#[timeout(600_000)]
fn test_cross_validate_binary_vs_text_lrat_php32() {
    let checker = require_ay_lrat_check();
    // Text verification.
    solve_and_check_lrat(PHP32_DIMACS, checker, "cross_text_php32");
    // Binary verification.
    solve_and_check_lrat_binary(PHP32_DIMACS, checker, "cross_binary_php32");
    eprintln!("Cross-validation: both binary and text LRAT verified on PHP(3,2)");
}

// ============================================================================
// ay binary LRAT benchmark validation (#5334)
// ============================================================================

/// Solve a benchmark with ay LRAT, dump proof, validate with ay-lrat-check.
fn solve_benchmark_lrat(name: &str) {
    let cnf_path = super::common::workspace_root()
        .join("benchmarks/sat/unsat")
        .join(format!("{name}.cnf"));
    let dimacs =
        std::fs::read_to_string(&cnf_path).unwrap_or_else(|e| panic!("read {name}.cnf: {e}"));
    let formula = parse_dimacs(&dimacs).expect("parse DIMACS");
    let n_clauses = formula.clauses.len() as u64;
    let proof_writer = ProofOutput::lrat_text(Vec::new(), n_clauses);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{name} must be UNSAT");
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");
    let proof_text = String::from_utf8(proof_bytes.clone()).expect("UTF-8");

    let checker = require_ay_lrat_check();
    let (cnf_tmp, proof_tmp) = temp_paths(&format!("lrat_{name}_diag"));
    std::fs::write(&cnf_tmp, &dimacs).expect("write CNF");
    std::fs::write(&proof_tmp, &proof_bytes).expect("write LRAT");
    let output = checker
        .command()
        .arg(&cnf_tmp)
        .arg(&proof_tmp)
        .output()
        .expect("run ay-lrat-check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let _ = std::fs::remove_file(&cnf_tmp);
    let _ = std::fs::remove_file(&proof_tmp);
    assert!(
        output.status.success() && stdout.contains("s VERIFIED"),
        "ay-lrat-check FAILED on {name}:\nstdout: {stdout}\nstderr: {stderr}\nproof:\n{proof_text}"
    );
    eprintln!("ay-lrat-check VERIFIED ({name})");
}

// LRAT with full inprocessing: all 12 UNSAT benchmarks (#5194).
// These tests validate that inprocessing-derived proof hints are
// complete and correctly ordered for LRAT RUP verification.
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_at_most_1_of_5() {
    solve_benchmark_lrat("at_most_1_of_5");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_blocked_chain_8() {
    solve_benchmark_lrat("blocked_chain_8");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_graph_coloring_k3_4clique() {
    solve_benchmark_lrat("graph_coloring_k3_4clique");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_latin_square_2x2_conflict() {
    solve_benchmark_lrat("latin_square_2x2_conflict");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_mutex_4proc() {
    solve_benchmark_lrat("mutex_4proc");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_mutilated_chessboard_2x2() {
    solve_benchmark_lrat("mutilated_chessboard_2x2");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_parity_6() {
    solve_benchmark_lrat("parity_6");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_php_4_3() {
    solve_benchmark_lrat("php_4_3");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_php_5_4() {
    solve_benchmark_lrat("php_5_4");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_ramsey_r3_3_6() {
    solve_benchmark_lrat("ramsey_r3_3_6");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_tseitin_grid_3x3() {
    solve_benchmark_lrat("tseitin_grid_3x3");
}
#[test]
#[timeout(600_000)]
fn test_lrat_benchmark_urquhart3() {
    solve_benchmark_lrat("urquhart_3");
}
