// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::OnceLock;
use std::time::Instant;

use ay_dpll::api::{Logic, SolveResult, Solver, Sort, Term};
use ay_test_support::{build_ay_cli, BuiltWorkspaceBinary};

const ROUND_TRIPS: usize = 10;

fn make_smtlib_script_with_sum(target_sum: i64) -> String {
    format!(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (assert (> x 0))\n\
         (assert (< x 100))\n\
         (assert (> y 0))\n\
         (assert (< y 100))\n\
         (assert (= (+ x y) {target_sum}))\n\
         (check-sat)\n\
         (get-value (x y))\n"
    )
}

fn setup_base_solver() -> (Solver, Term, Term) {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let hundred = solver.int_const(100);
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.lt(x, hundred);
    solver.assert_term(c2);
    let c3 = solver.gt(y, zero);
    solver.assert_term(c3);
    let c4 = solver.lt(y, hundred);
    solver.assert_term(c4);
    (solver, x, y)
}

fn solve_native_incremental(solver: &mut Solver, x: Term, y: Term, target_sum: i64) -> SolveResult {
    solver.push();
    let target = solver.int_const(target_sum);
    let sum = solver.add(x, y);
    let eq = solver.eq(sum, target);
    solver.assert_term(eq);
    let result = solver.check_sat();
    solver.pop();
    result.result().clone()
}

fn solve_parse_execute(script: &str) -> String {
    let commands = ay_frontend::parse(script).expect("parse should succeed");
    let mut executor = ay_dpll::Executor::new();
    let mut output = String::new();
    for cmd in &commands {
        if let Some(out) = executor.execute(cmd).expect("execute should succeed") {
            output.push_str(&out);
            output.push('\n');
        }
    }
    output
}

fn solve_subprocess(ay_binary: &BuiltWorkspaceBinary, script: &str) -> String {
    let mut child = ay_binary
        .command()
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| {
            panic!(
                "failed to spawn exact-source {}: {error}",
                ay_binary.artifact_display()
            )
        });
    child
        .stdin
        .as_mut()
        .expect("AY subprocess stdin")
        .write_all(script.as_bytes())
        .expect("write AY subprocess input");
    drop(child.stdin.take());
    let output = child.wait_with_output().expect("wait for AY subprocess");
    assert!(
        output.status.success(),
        "exact-source AY subprocess failed with status {}:\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("AY subprocess stdout should be UTF-8")
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("AY workspace root")
        .canonicalize()
        .expect("AY workspace root should be canonicalizable")
}

fn exact_ay_binary() -> &'static BuiltWorkspaceBinary {
    static AY_BINARY: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    AY_BINARY.get_or_init(|| build_ay_cli(&workspace_root()))
}

fn target_sum_for_trip(i: usize) -> i64 {
    (i * 7 % 197) as i64 + 2
}

fn bench_native_roundtrips() -> std::time::Duration {
    let (mut solver, x, y) = setup_base_solver();
    let _ = solve_native_incremental(&mut solver, x, y, 42); // warmup
    let start = Instant::now();
    for i in 1..=ROUND_TRIPS {
        let _ = solve_native_incremental(&mut solver, x, y, target_sum_for_trip(i));
    }
    start.elapsed()
}

fn bench_parse_execute_roundtrips() -> std::time::Duration {
    let script = make_smtlib_script_with_sum(42);
    solve_parse_execute(&script); // warmup
    let start = Instant::now();
    for i in 1..=ROUND_TRIPS {
        let script = make_smtlib_script_with_sum(target_sum_for_trip(i));
        solve_parse_execute(&script);
    }
    start.elapsed()
}

fn bench_subprocess_roundtrips(ay_path: &BuiltWorkspaceBinary) -> std::time::Duration {
    let script = make_smtlib_script_with_sum(42);
    solve_subprocess(ay_path, &script); // warmup
    let start = Instant::now();
    for i in 1..=ROUND_TRIPS {
        let script = make_smtlib_script_with_sum(target_sum_for_trip(i));
        solve_subprocess(ay_path, &script);
    }
    start.elapsed()
}

// --- Correctness tests ---

#[test]
fn test_native_api_correctness() {
    let (mut solver, x, y) = setup_base_solver();
    let forty_two = solver.int_const(42);
    let sum = solver.add(x, y);
    let c5 = solver.eq(sum, forty_two);
    solver.assert_term(c5);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat, "native API should find SAT");
    let verified_model = solver.model().expect("model should exist");
    let model = verified_model.model();
    let xv = model.int_val_i64("x").expect("model should have x");
    let yv = model.int_val_i64("y").expect("model should have y");
    assert!(xv > 0 && xv < 100, "x={xv} should be in (0,100)");
    assert!(yv > 0 && yv < 100, "y={yv} should be in (0,100)");
    assert_eq!(xv + yv, 42, "x+y should equal 42");
}

#[test]
fn test_native_incremental_correctness() {
    let (mut solver, x, y) = setup_base_solver();
    // x>0 and y>0 (ints) means x>=1, y>=1. x<100, y<100 means x<=99, y<=99.
    // So x+y range is [2, 198].
    assert_eq!(
        solve_native_incremental(&mut solver, x, y, 42),
        SolveResult::Sat
    );
    assert_eq!(
        solve_native_incremental(&mut solver, x, y, 2),
        SolveResult::Sat
    );
    assert_eq!(
        solve_native_incremental(&mut solver, x, y, 198),
        SolveResult::Sat
    );
    // x+y=1 impossible: x>=1, y>=1 so x+y>=2
    assert!(solve_native_incremental(&mut solver, x, y, 1).is_unsat());
    // x+y=199 impossible: x<=99, y<=99 so x+y<=198
    assert!(solve_native_incremental(&mut solver, x, y, 199).is_unsat());
}

#[test]
fn test_parse_execute_correctness() {
    let output = solve_parse_execute(&make_smtlib_script_with_sum(42));
    assert!(
        output.starts_with("sat"),
        "should return SAT, got: {output}"
    );
}

/// Normal package tests must exercise the real CLI lane without relying on
/// `AY_PATH`, `PATH`, or Cargo's integration-test-only binary environment.
#[test]
fn test_exact_source_subprocess_correctness() {
    let output = solve_subprocess(exact_ay_binary(), &make_smtlib_script_with_sum(42));
    assert!(
        output.starts_with("sat\n"),
        "exact-source CLI should return SAT, got: {output}"
    );
    assert!(
        output.contains("((x ") && output.contains("(y "),
        "exact-source CLI should return requested values, got: {output}"
    );
}

// --- Latency benchmarks ---

#[test]
fn bench_native_api_10_roundtrips() {
    let elapsed = bench_native_roundtrips();
    let per_trip = elapsed / ROUND_TRIPS as u32;
    eprintln!("=== NATIVE API: {ROUND_TRIPS} trips in {elapsed:?} ({per_trip:?}/trip) ===");
}

#[test]
fn bench_parse_execute_10_roundtrips() {
    let elapsed = bench_parse_execute_roundtrips();
    let per_trip = elapsed / ROUND_TRIPS as u32;
    eprintln!("=== PARSE+EXEC: {ROUND_TRIPS} trips in {elapsed:?} ({per_trip:?}/trip) ===");
}

#[test]
fn bench_subprocess_10_roundtrips() {
    let elapsed = bench_subprocess_roundtrips(exact_ay_binary());
    let per_trip = elapsed / ROUND_TRIPS as u32;
    eprintln!("=== SUBPROCESS: {ROUND_TRIPS} trips in {elapsed:?} ({per_trip:?}/trip) ===");
}

#[test]
fn bench_comparison_summary() {
    let native_elapsed = bench_native_roundtrips();
    let parse_exec_elapsed = bench_parse_execute_roundtrips();
    let subprocess_elapsed = bench_subprocess_roundtrips(exact_ay_binary());

    eprintln!("\n========== BENCHMARK SUMMARY ({ROUND_TRIPS} round trips) ==========");
    eprintln!(
        "  Native API (incremental): {:>10?}  ({:?}/trip)",
        native_elapsed,
        native_elapsed / ROUND_TRIPS as u32
    );
    eprintln!(
        "  Parse+Execute (fresh):    {:>10?}  ({:?}/trip)",
        parse_exec_elapsed,
        parse_exec_elapsed / ROUND_TRIPS as u32
    );
    eprintln!(
        "  Subprocess (one-shot):    {:>10?}  ({:?}/trip)",
        subprocess_elapsed,
        subprocess_elapsed / ROUND_TRIPS as u32
    );
    let native_speedup = subprocess_elapsed.as_nanos() as f64 / native_elapsed.as_nanos() as f64;
    let parse_speedup = subprocess_elapsed.as_nanos() as f64 / parse_exec_elapsed.as_nanos() as f64;
    eprintln!("  Native vs Subprocess speedup:        {native_speedup:.1}x");
    eprintln!("  Parse+Execute vs Subprocess speedup: {parse_speedup:.1}x");
    eprintln!("===========================================================\n");
}
