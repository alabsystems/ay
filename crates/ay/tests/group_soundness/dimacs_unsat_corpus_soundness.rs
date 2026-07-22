// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn is_fail_closed_known_unsat_benchmark(path: &Path) -> bool {
    if path
        .file_name()
        .is_some_and(|name| name == "tseitin_cycle_10.cnf")
    {
        return false;
    }
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
    !contents
        .lines()
        .take_while(|line| !line.starts_with("p cnf"))
        .any(|line| line.contains("expected UNSAT"))
}

fn unsat_corpus_paths() -> Vec<PathBuf> {
    let corpus_dir = workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_paths: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", corpus_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .filter(|path| is_fail_closed_known_unsat_benchmark(path))
        .collect();
    cnf_paths.sort();
    assert!(
        !cnf_paths.is_empty(),
        "expected at least one UNSAT benchmark in {}",
        corpus_dir.display()
    );
    cnf_paths
}

#[test]
#[timeout(120_000)]
fn test_cli_dimacs_unsat_corpus_soundness() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut failures = Vec::new();

    for path in unsat_corpus_paths() {
        let output = Command::new(ay_path)
            .arg(&path)
            .output()
            .unwrap_or_else(|e| panic!("failed to run ay on {}: {e}", path.display()));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let saw_unsat_line = stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE");

        if output.status.code() != Some(20) || !saw_unsat_line {
            failures.push(format!(
                "{}: expected exit=20 and 's UNSATISFIABLE', got exit={:?}\nstdout:\n{}\nstderr:\n{}",
                path.display(),
                output.status.code(),
                stdout,
                stderr
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "CLI UNSAT corpus soundness regressions:\n{}",
        failures.join("\n\n")
    );
}
