// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay tutorial` integration tests (#8692).
//!
//! Covers the tutorial hub, role-based documentation tracks, feature atlas,
//! and the educational `ay tutorial solve <file>` path:
//!
//! * Help and the hub make every tutorial track discoverable without entering
//!   an interactive prompt.
//! * The feature atlas names every public solver family and companion tool.
//! * Engineer and expert tracks render both their complete course and a
//!   selected chapter without prompting.
//! * SAT input → "SATISFIABLE" banner, model block, and a
//!   per-assertion back-substitution section that prints each rule with
//!   model values plugged in and confirms it evaluates to True.
//! * UNSAT input → "UNSATISFIABLE" banner and a plain-English hint
//!   listing the contradicting rules.
//! * `ay tutorial` (no args) → prints the welcome banner without error.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_tutorial_solve_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

fn run_ay(args: &[&str]) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path)
        .args(args)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay")
}

fn run_ay_with_stdin(args: &[&str], input: &str) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path)
        .args(args)
        .output_timeout_with_stdin(input.as_bytes(), DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay with stdin")
}

fn help_lists_command(help: &str, command: &str) -> bool {
    help.lines()
        .any(|line| line.trim_start().starts_with(&format!("{command} ")))
}

fn successful_stdout(args: &[&str]) -> String {
    let output = run_ay(args);
    assert!(
        output.status.success(),
        "ay {} failed: stderr={}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("ay stdout should be UTF-8")
}

fn assert_contains_all(haystack: &str, expected: &[&str], context: &str) {
    let lowercase = haystack.to_ascii_lowercase();
    for needle in expected {
        assert!(
            lowercase.contains(&needle.to_ascii_lowercase()),
            "expected {context} to contain {needle:?}, got:\n{haystack}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn test_public_help_shows_tutorial_without_internal_commands() {
    let output = run_ay(&["--help"]);
    assert!(output.status.success(), "ay --help failed");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(help_lists_command(&stdout, "tutorial"), "{stdout}");
    assert!(help_lists_command(&stdout, "diagnose"), "{stdout}");

    for command in [
        "bench",
        "corpus",
        "tool",
        "z3-audit",
        "scripts",
        "competition-jit",
        "gate",
        "consumer-smoke",
        "launch-gate",
        "release",
        "launch-packet",
        "submission",
        "verifier-audit",
        "bisect",
    ] {
        assert!(!help_lists_command(&stdout, command), "{stdout}");
    }
}

#[test]
#[timeout(30_000)]
fn test_tutorial_help_discovers_tracks_atlas_and_sudoku_lab() {
    let help = successful_stdout(&["tutorial", "--help"]);
    for command in [
        "basics",
        "features",
        "engineers",
        "experts",
        "play",
        "solve",
    ] {
        assert!(
            help_lists_command(&help, command),
            "tutorial help should list {command:?}:\n{help}"
        );
    }
    assert_contains_all(&help, &["--interactive", "--challenge"], "tutorial help");

    // Check the stable selectable names through help only. In particular, do
    // not start `basics --interactive` or `play sudoku`, which intentionally
    // read from stdin.
    let features_help = successful_stdout(&["tutorial", "features", "--help"]);
    assert_contains_all(
        &features_help,
        &[
            "solving",
            "proofs",
            "optimization",
            "exploration",
            "integration",
            "tooling",
        ],
        "feature-atlas help",
    );

    let engineers_help = successful_stdout(&["tutorial", "engineers", "--help"]);
    assert_contains_all(
        &engineers_help,
        &["build", "automation", "rust", "migration", "production"],
        "engineer-track help",
    );

    let experts_help = successful_stdout(&["tutorial", "experts", "--help"]);
    assert_contains_all(
        &experts_help,
        &[
            "proofs",
            "incremental",
            "optimization",
            "theories",
            "research",
        ],
        "expert-track help",
    );

    let play_help = successful_stdout(&["tutorial", "play", "--help"]);
    assert!(
        help_lists_command(&play_help, "sudoku"),
        "tutorial play help should list sudoku:\n{play_help}"
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_hub_links_every_learning_track() {
    let stdout = successful_stdout(&["tutorial"]);
    assert_contains_all(
        &stdout,
        &[
            "AY tutorial",
            "ay tutorial basics",
            "ay tutorial engineers",
            "ay tutorial experts",
            "ay tutorial features",
            "ay tutorial play sudoku",
            "ay tutorial solve",
            "ay tutorial --challenge",
        ],
        "tutorial hub",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_sudoku_lab_checks_proves_a_hint_and_validates_a_solution() {
    let output = run_ay_with_stdin(
        &["tutorial", "play", "sudoku"],
        "check\nhint\nsolve\nquit\n",
    );
    assert!(
        output.status.success(),
        "Sudoku lab failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("Sudoku stdout should be UTF-8");
    assert_contains_all(
        &stdout,
        &[
            "AY Sudoku Lab",
            "SAT: every current move extends",
            "Forced hint",
            "proved every alternative impossible",
            "independently validated completion",
        ],
        "scripted Sudoku lab",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_feature_atlas_covers_every_major_public_surface() {
    let stdout = successful_stdout(&["tutorial", "features"]);
    assert_contains_all(
        &stdout,
        &[
            "AY Feature Atlas",
            "Solving",
            "Proofs",
            "Optimization",
            "Exploration",
            "Integration",
            "Tooling",
            // Primary solving modes routed through `ay solve`.
            "ay solve",
            "SMT-LIB",
            "DIMACS",
            "CHC",
            // Every dedicated public solver family.
            "ay flatzinc",
            "ay pb",
            "ay maxsat",
            "ay qbf",
            "ay lp",
            // Proofs, exploration, and developer tooling.
            "ay check",
            "ay allsat",
            "ay model-count",
            "ay simplify",
            "ay bench",
            "ay corpus",
            "ay diagnose",
            // The major embedding and migration surfaces.
            "Z3",
            "Rust",
            "Python",
        ],
        "complete feature atlas",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_feature_atlas_can_select_proofs_section() {
    let stdout = successful_stdout(&["tutorial", "features", "proofs"]);
    assert_contains_all(
        &stdout,
        &[
            "AY Feature Atlas",
            "Alethe",
            "DRAT",
            "LRAT",
            "VeriPB",
            "ay check",
            "--self-check",
        ],
        "feature-atlas proofs section",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_engineers_full_course_is_practical_and_noninteractive() {
    let stdout = successful_stdout(&["tutorial", "engineers"]);
    assert_contains_all(
        &stdout,
        &[
            "AY for Engineers",
            "cargo build",
            "--timeout",
            "--memory",
            "Cargo.toml",
            "--z3-mode",
            "--self-check",
        ],
        "complete engineer tutorial",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_engineer_build_chapter_contains_all_three_worked_applications() {
    let stdout = successful_stdout(&["tutorial", "engineers", "build"]);
    assert_contains_all(
        &stdout,
        &[
            "Sudoku",
            "LLM token router",
            "Minesweeper",
            "AY SearchSpec v1",
            "Expected LLM response",
            "model.int_grid",
            "model.minimize",
            "answer.require_solution()",
            "chat_local_load + code_local_load + batch_local_load <= 5",
            "status is `optimal`",
            "UNKNOWN means do not click",
            "Python",
            "TypeScript",
        ],
        "engineer build chapter",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_engineers_can_select_migration_chapter() {
    let stdout = successful_stdout(&["tutorial", "engineers", "migration"]);
    assert_contains_all(
        &stdout,
        &["AY for Engineers", "--z3-mode", "ayz3", "ay diagnose"],
        "engineer migration chapter",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_experts_full_course_shows_research_grade_features() {
    let stdout = successful_stdout(&["tutorial", "experts"]);
    assert_contains_all(
        &stdout,
        &[
            "AY for Experts",
            "Alethe",
            "check-sat-assuming",
            "get-unsat-core",
            "MaxSAT",
            "bit-vector",
            "ay bench",
        ],
        "complete expert tutorial",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_expert_course_uses_concrete_worked_examples() {
    let stdout = successful_stdout(&["tutorial", "experts"]);
    assert_contains_all(
        &stdout,
        &[
            "Worked example A",
            "carcara check",
            "ay check lrat",
            "get-objective-certificates",
            "get-unsat-core :farkas",
            "get-interpolant",
            "get-abduct",
            "original-clause CHC replay",
        ],
        "expert worked examples",
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_experts_can_select_incremental_chapter() {
    let stdout = successful_stdout(&["tutorial", "experts", "incremental"]);
    assert_contains_all(
        &stdout,
        &[
            "AY for Experts",
            "(push",
            "(pop",
            "check-sat-assuming",
            "get-unsat-core",
        ],
        "expert incremental chapter",
    );
}

#[test]
#[timeout(60_000)]
fn test_tutorial_solve_sat_shows_back_substitution() {
    // SAT input with two assertions. Tutorial output must:
    //   1. Identify the result as SATISFIABLE.
    //   2. Print a model block.
    //   3. For each rule, print the original body and the body with model
    //      values substituted, then confirm it evaluates to True.
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (> x y))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
(get-model)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&["tutorial", "solve", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay tutorial solve failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stdout.contains("Result: SATISFIABLE"),
        "expected SATISFIABLE banner, got: {stdout}"
    );
    assert!(
        stdout.contains("Model (variable assignments)"),
        "expected model block, got: {stdout}"
    );
    assert!(
        stdout.contains("Checking the model against each rule"),
        "expected back-substitution header, got: {stdout}"
    );
    // The first rule includes `(+ x y)` — after substitution it must contain
    // a `(+` with numeric values, not the literal symbols.
    assert!(
        stdout.contains("Rule 1: (= (+ x y) 10)"),
        "expected original Rule 1 text, got: {stdout}"
    );
    assert!(
        stdout.contains("with model: (= (+ "),
        "expected substituted rule 1, got: {stdout}"
    );
    // Every rule must be confirmed to evaluate to True.
    let true_count = stdout.matches("evaluates to True").count();
    assert!(
        true_count >= 4,
        "expected at least 4 'evaluates to True' confirmations (one per rule), got {true_count}: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn test_tutorial_solve_unsat_explains_contradiction() {
    // UNSAT input: x > 10 AND x < 0. Tutorial mode must:
    //   1. Say UNSATISFIABLE in plain English.
    //   2. List the rules so the user can see the contradiction.
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 0))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&["tutorial", "solve", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay tutorial solve failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stdout.contains("Result: UNSATISFIABLE"),
        "expected UNSATISFIABLE banner, got: {stdout}"
    );
    assert!(
        stdout.contains("No answer exists"),
        "expected plain-English UNSAT line, got: {stdout}"
    );
    assert!(
        stdout.contains("The rules were:"),
        "expected rules listing for small UNSAT, got: {stdout}"
    );
    assert!(
        stdout.contains("(> x 10)") && stdout.contains("(< x 0)"),
        "expected both contradicting rules to be listed, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_welcome_runs_without_file() {
    // `ay tutorial` with no args prints the welcome banner + a quick example.
    let output = run_ay(&["tutorial"]);
    assert!(
        output.status.success(),
        "ay tutorial failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("AY tutorial"),
        "expected welcome banner, got: {stdout}"
    );
    assert!(
        stdout.contains("ay tutorial --interactive"),
        "expected tutorial hint, got: {stdout}"
    );
}
