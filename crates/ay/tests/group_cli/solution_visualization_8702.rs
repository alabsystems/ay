// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CLI integration tests for solution visualization (#8702).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_solution_visualization_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp input");
    (path.clone(), CleanupGuard(path))
}

fn run_ay(args: &[&str]) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path).args(args).output().expect("spawn ay")
}

#[test]
#[timeout(60_000)]
fn solve_visualize_ascii_renders_n_queens_without_explicit_get_model() {
    let smt = r#"; N-Queens fixed 4x4 solution
(set-logic QF_LIA)
(declare-const q1 Int)
(declare-const q2 Int)
(declare-const q3 Int)
(declare-const q4 Int)
(assert (= q1 2))
(assert (= q2 4))
(assert (= q3 1))
(assert (= q4 3))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt);

    let output = run_ay(&["solve", "--visualize", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay solve --visualize failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(stdout.contains("sat"), "expected SAT result, got: {stdout}");
    assert!(
        stdout.contains("; ay visualization: n-queens 4x4"),
        "expected n-queens visualization header, got: {stdout}"
    );
    assert!(
        stdout.contains("| . | Q | . | . |"),
        "expected first queen row, got: {stdout}"
    );
    assert!(
        stdout.contains("| . | . | . | Q |"),
        "expected second queen row, got: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn solve_visualize_svg_renders_sudoku_grid() {
    let smt = r#"; Mini Sudoku fixed solution
(set-logic QF_LIA)
(declare-const r1c1 Int)
(declare-const r1c2 Int)
(declare-const r2c1 Int)
(declare-const r2c2 Int)
(assert (= r1c1 1))
(assert (= r1c2 2))
(assert (= r2c1 2))
(assert (= r2c2 1))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt);

    let output = run_ay(&["solve", "--visualize", "svg", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay solve --visualize svg failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(stdout.contains("sat"), "expected SAT result, got: {stdout}");
    assert!(
        stdout.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""),
        "expected SVG output, got: {stdout}"
    );
    assert!(
        stdout.contains("data-ay-visualization=\"sudoku\""),
        "expected sudoku SVG marker, got: {stdout}"
    );
    assert!(
        stdout.contains(">1</text>"),
        "expected cell value text, got: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn tutorial_solve_auto_renders_recognized_sudoku_model() {
    let smt = r#"; Mini Sudoku fixed solution
(set-logic QF_LIA)
(declare-const r1c1 Int)
(declare-const r1c2 Int)
(declare-const r2c1 Int)
(declare-const r2c2 Int)
(assert (= r1c1 1))
(assert (= r1c2 2))
(assert (= r2c1 2))
(assert (= r2c2 1))
(check-sat)
(get-model)
"#;
    let (input_path, _cleanup) = write_temp(smt);

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
        stdout.contains("; ay visualization: sudoku 2x2"),
        "expected automatic sudoku visualization, got: {stdout}"
    );
    assert!(
        stdout.contains("| 1 | 2 |"),
        "expected first sudoku row, got: {stdout}"
    );
}
