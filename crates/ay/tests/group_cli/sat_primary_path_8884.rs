// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT primary-path CLI coverage for #8884.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn write_temp_cnf(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_sat_primary_path_{}_{}.cnf",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp CNF");
    (path.clone(), CleanupGuard(path))
}

fn unique_temp_path(name: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_sat_primary_path_{}_{}_{}.{}",
        name,
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn pigeonhole_cnf(pigeons: usize, holes: usize) -> String {
    let var = |pigeon: usize, hole: usize| -> usize { pigeon * holes + hole + 1 };
    let num_vars = pigeons * holes;
    let mut clauses = Vec::new();

    for pigeon in 0..pigeons {
        let mut clause = String::new();
        for hole in 0..holes {
            clause.push_str(&format!("{} ", var(pigeon, hole)));
        }
        clause.push('0');
        clauses.push(clause);

        for h1 in 0..holes {
            for h2 in (h1 + 1)..holes {
                clauses.push(format!("-{} -{} 0", var(pigeon, h1), var(pigeon, h2)));
            }
        }
    }

    for hole in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(format!("-{} -{} 0", var(p1, hole), var(p2, hole)));
            }
        }
    }

    format!(
        "p cnf {num_vars} {}\n{}\n",
        clauses.len(),
        clauses.join("\n")
    )
}

fn assert_single_satcomp_unknown_line(stdout: &str, context: &str) {
    let solution_lines = stdout
        .lines()
        .filter(|line| line.starts_with("s "))
        .collect::<Vec<_>>();
    assert_eq!(
        solution_lines,
        vec!["s UNKNOWN"],
        "{context}: expected exactly one SAT-COMP UNKNOWN line, stdout={stdout:?}"
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "unknown"),
        "{context}: lowercase SMT unknown must not be emitted under SAT-COMP wrapper env, stdout={stdout:?}"
    );
}

fn assert_satcomp_model_lines_are_wrapped(stdout: &str, num_vars: usize) {
    let model_lines = stdout
        .lines()
        .filter(|line| line.starts_with("v "))
        .collect::<Vec<_>>();
    assert!(
        !model_lines.is_empty(),
        "SAT output should include model value lines, stdout={stdout:?}"
    );

    let mut tokens = Vec::new();
    for line in model_lines {
        assert!(
            line.len() <= 4096,
            "SAT-COMP model line exceeds 4096 chars: len={}, line={line:?}",
            line.len()
        );
        for token in line.split_whitespace().skip(1) {
            tokens.push(
                token
                    .parse::<i32>()
                    .expect("SAT-COMP model token should be an integer"),
            );
        }
    }
    assert_eq!(
        tokens.last().copied(),
        Some(0),
        "SAT-COMP model should terminate with 0"
    );
    assert!(
        !tokens[..tokens.len() - 1].contains(&0),
        "SAT-COMP model should only contain the terminating 0 at the end"
    );

    let mut assignments = vec![None; num_vars + 1];
    for &lit in &tokens[..tokens.len() - 1] {
        let var = lit.unsigned_abs() as usize;
        assert!(
            (1..=num_vars).contains(&var),
            "model literal {lit} is out of range 1..={num_vars}"
        );
        let value = lit > 0;
        assert!(
            assignments[var]
                .replace(value)
                .is_none_or(|prev| prev == value),
            "model assigns variable {var} both ways"
        );
    }
    assert_eq!(
        assignments[1],
        Some(true),
        "model must satisfy the unit clause 1 0"
    );
}

#[test]
#[timeout(30_000)]
fn solve_help_shows_sat_primary_path_and_variant() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--help")
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve --help");

    assert!(
        output.status.success(),
        "help should exit successfully: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("SAT primary path"),
        "help should expose the SAT primary path: {stdout}"
    );
    assert!(
        stdout.contains("ay solve --sat-variant default FILE.cnf"),
        "help should show the recommended SAT command: {stdout}"
    );
    assert!(
        stdout.contains("--sat-variant <VARIANT>"),
        "help should expose --sat-variant without full help: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn satcomp_sat_model_lines_stay_under_4096_chars() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let num_vars = 2_000;
    let (input, _cleanup) = write_temp_cnf(&format!("p cnf {num_vars} 1\n1 0\n"));

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("default")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .env(
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-lrat-v1",
        )
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve with large SAT model");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(10),
        "large SAT canary should be SAT: stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "s SATISFIABLE"),
        "large SAT canary should print SATISFIABLE, stdout={stdout:?}"
    );
    assert_satcomp_model_lines_are_wrapped(&stdout, num_vars);
}

#[test]
#[timeout(60_000)]
fn satcomp_wrapper_dimacs_timeout_returns_unknown_exit_zero() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = pigeonhole_cnf(16, 15);
    let (input, _input_cleanup) = write_temp_cnf(&cnf);
    let (proof_path, _proof_cleanup) = unique_temp_path("timeout", "lrat");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--timeout")
        .arg("1")
        .arg("--sat-variant")
        .arg("default")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .env(
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-lrat-v1",
        )
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve with SAT-COMP wrapper timeout policy");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "SAT-COMP UNKNOWN timeout should exit 0: stdout={stdout}, stderr={stderr}"
    );
    assert_single_satcomp_unknown_line(&stdout, "SAT-COMP DIMACS timeout");
}

#[test]
#[timeout(60_000)]
fn non_satcomp_dimacs_timeout_keeps_timeout_exit_code() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = pigeonhole_cnf(16, 15);
    let (input, _input_cleanup) = write_temp_cnf(&cnf);

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--timeout")
        .arg("1")
        .arg("--sat-variant")
        .arg("default")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .env_remove("AY_INTERNAL_SATCOMP_WRAPPER")
        .env_remove("AY_SAT_COMPETITION_PROFILE")
        .env_remove("AY_SAT_PROFILE_ID")
        .env_remove("AY_COMPETITION_JIT_MODE")
        .env_remove("AY_SAT_TRACK")
        .env_remove("AY_SAT_AI_CLASS")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve with normal timeout policy");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(124),
        "non-SAT-COMP DIMACS timeout should keep exit 124: stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "s UNKNOWN"),
        "DIMACS timeout should still emit SAT-COMP UNKNOWN grammar, stdout={stdout:?}, stderr={stderr:?}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_run_emits_applied_sat_summary() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp_cnf("p cnf 2 1\n1 2 0\n");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("probe")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve");

    assert_eq!(
        output.status.code(),
        Some(10),
        "trivial CNF should be SAT: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "c --- SAT applied run ---",
        "c sat.policy: variant=probe",
        "c sat.policy_source: --sat-variant",
        "c sat.route_profile: standard",
        "c sat.route_fail_closed: no",
        "c sat.guidance_loaded: no",
        "c sat.proof_active: no",
        "c sat.proof_format: none",
        "c sat.proof_origin: none",
        "c sat.verify_proof: off",
    ] {
        assert!(
            stderr.contains(expected),
            "missing applied-run summary line {expected:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn satcomp_main_regular_summary_fails_closed_without_lrat_route() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp_cnf("p cnf 2 1\n1 2 0\n");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("default")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve under SAT-COMP Main/regular metadata");

    assert_eq!(
        output.status.code(),
        Some(10),
        "trivial CNF should be SAT: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "c sat.policy: variant=default",
        "c sat.policy_source: --sat-variant",
        "c sat.route_profile: standard",
        "c sat.route_fail_closed: yes",
        "c sat.proof_active: no",
        "c sat.proof_format: none",
    ] {
        assert!(
            stderr.contains(expected),
            "missing SAT-COMP fail-closed summary line {expected:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn satcomp_main_regular_summary_accepts_default_text_lrat_route() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp_cnf("p cnf 2 1\n1 2 0\n");
    let proof_path = std::env::temp_dir().join(format!(
        "ay_sat_primary_path_{}_official.lrat",
        std::process::id()
    ));
    let _proof_cleanup = CleanupGuard(proof_path.clone());

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("default")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve under official SAT-COMP Main/regular shape");

    assert_eq!(
        output.status.code(),
        Some(10),
        "trivial CNF should be SAT: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "c sat.policy: variant=default",
        "c sat.policy_source: --sat-variant",
        "c sat.route_profile: official-satcomp-main-lrat",
        "c sat.route_fail_closed: no",
        "c sat.proof_active: yes",
        "c sat.proof_format: lrat",
        "c sat.proof_origin: file",
    ] {
        assert!(
            stderr.contains(expected),
            "missing official SAT-COMP summary line {expected:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn satcomp_main_regular_proof_create_failure_returns_unknown_exit_zero() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _input_cleanup) = write_temp_cnf("p cnf 1 2\n1 0\n-1 0\n");
    let (proof_dir, _proof_cleanup) = unique_temp_path("proof-create-fail", "lrat");
    std::fs::create_dir(&proof_dir).expect("create proof path directory");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("default")
        .arg("--proof")
        .arg(&proof_dir)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve with unwritable proof path");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "official SAT-COMP proof setup failure should exit 0: stdout={stdout}, stderr={stderr}"
    );
    assert_single_satcomp_unknown_line(&stdout, "SAT-COMP proof setup failure");
    assert!(
        !stdout.lines().any(|line| line == "s UNSATISFIABLE"),
        "proof setup failure must not report UNSAT: stdout={stdout:?}"
    );
    assert!(
        stderr.contains("proof output unavailable"),
        "stderr should explain proof setup fail-closed path: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn satcomp_main_regular_streaming_proof_create_failure_returns_unknown_exit_zero() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _input_cleanup) = write_temp_cnf("p cnf 1 500001\n");
    let (proof_dir, _proof_cleanup) = unique_temp_path("streaming-proof-create-fail", "lrat");
    std::fs::create_dir(&proof_dir).expect("create proof path directory");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--sat-variant")
        .arg("default")
        .arg("--proof")
        .arg(&proof_dir)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay solve with streaming proof path failure");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "official SAT-COMP streaming proof setup failure should exit 0: stdout={stdout}, stderr={stderr}"
    );
    assert_single_satcomp_unknown_line(&stdout, "SAT-COMP streaming proof setup failure");
    assert!(
        !stdout.lines().any(|line| line == "s UNSATISFIABLE"),
        "streaming proof setup failure must not report UNSAT: stdout={stdout:?}"
    );
    assert!(
        stderr.contains("proof output unavailable"),
        "stderr should explain streaming proof setup fail-closed path: {stderr}"
    );
}
