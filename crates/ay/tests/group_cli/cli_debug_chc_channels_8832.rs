// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for #8832: `--debug prop`, `--debug chc-smt`, `--debug algebraic`
//! were parsed into `DebugConfig` but never consulted by the runtime gates.
//! Post-fix the CLI path is the binary's source of truth and the channels
//! produce the expected tracing output.
//!
//! Acceptance criteria (from the issue):
//!   - [x] `--debug prop` emits `[PROP ...]` lines on stderr
//!   - [x] `--debug chc-smt` emits `[CHC-SMT ...]` lines on stderr
//!   - [x] `--debug algebraic` is accepted and routed through the same path
//!
use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;

/// A public CHC benchmark that exercises `propagate_equalities` (prop channel)
/// and the CHC SMT theory loop (chc-smt channel) reliably.
const BENCHMARK_REL_PATH: &str = "../../benchmarks/smt/model_checker_consumer_dt_simple.smt2";

fn benchmark_path() -> PathBuf {
    // `CARGO_MANIFEST_DIR` for integration tests resolves to `crates/ay`.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.join(BENCHMARK_REL_PATH)
}

fn ay_exe() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

#[test]
#[timeout(60_000)]
fn test_debug_prop_cli_emits_trace() {
    let input = benchmark_path();
    assert!(
        input.exists(),
        "benchmark missing, cannot verify #8832 fix: {}",
        input.display()
    );

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg("--debug")
        .arg("prop")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let prop_lines = stderr.lines().filter(|l| l.contains("[PROP")).count();
    assert!(
        prop_lines > 0,
        "--debug prop should emit [PROP ...] lines on stderr (got {prop_lines}). \
         Pre-fix (#8832) this was 0 because the gate only read AY_DEBUG_PROP. \
         stderr tail: {}",
        stderr.lines().rev().take(5).collect::<Vec<_>>().join(" | ")
    );
}

#[test]
#[timeout(60_000)]
fn test_debug_chc_smt_cli_emits_trace() {
    let input = benchmark_path();
    assert!(input.exists(), "benchmark missing: {}", input.display());

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg("--debug")
        .arg("chc-smt")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let chc_smt_lines = stderr.lines().filter(|l| l.contains("[CHC-SMT")).count();
    assert!(
        chc_smt_lines > 0,
        "--debug chc-smt should emit [CHC-SMT ...] lines on stderr (got {chc_smt_lines}). \
         Pre-fix (#8832) this was 0 because the gate only read AY_DEBUG_CHC_SMT."
    );
}

#[test]
#[timeout(60_000)]
fn test_debug_algebraic_cli_accepted() {
    // The `algebraic` channel only fires inside PDR on benchmarks that reach
    // `verify_implication_algebraically`. It's not universally triggered, so
    // the CLI-contract assertion is just that `--debug algebraic` parses,
    // routes through `DebugConfig::from_channels` (enabled -> true), and
    // terminates cleanly — no silent ignore, no panic. The wire-up is
    // verified structurally by the unit test `debug_channel_active` path;
    // here we verify the CLI boundary.
    let input = benchmark_path();
    assert!(input.exists(), "benchmark missing: {}", input.display());

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg("--debug")
        .arg("algebraic")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "--debug algebraic should parse and run cleanly, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("error: unexpected argument"),
        "--debug algebraic should be a valid channel, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_debug_combined_cli_channels() {
    // Combined `--debug prop,chc-smt` must enable BOTH gates in one invocation.
    let input = benchmark_path();
    assert!(input.exists(), "benchmark missing: {}", input.display());

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg("--debug")
        .arg("prop,chc-smt")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let prop_lines = stderr.lines().filter(|l| l.contains("[PROP")).count();
    let chc_smt_lines = stderr.lines().filter(|l| l.contains("[CHC-SMT")).count();
    assert!(
        prop_lines > 0 && chc_smt_lines > 0,
        "--debug prop,chc-smt should enable both channels \
         (prop={prop_lines}, chc-smt={chc_smt_lines})"
    );
}

#[test]
#[timeout(60_000)]
fn test_debug_prop_env_var_is_ignored_by_cli_binary() {
    let input = std::env::temp_dir().join(format!(
        "ay_debug_prop_env_ignored_{}.smt2",
        std::process::id()
    ));
    std::fs::write(
        &input,
        "(set-logic HORN)\n\
         (declare-fun Inv (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
         (assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))\n\
         (assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n\
         (check-sat)\n",
    )
    .expect("write temp CHC benchmark");

    let output = Command::new(ay_exe())
        .env("AY_DEBUG_PROP", "1")
        .arg("--chc")
        .arg(&input)
        .output()
        .expect("spawn ay");
    let _ = std::fs::remove_file(&input);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let prop_lines = stderr.lines().filter(|l| l.contains("[PROP")).count();
    assert_eq!(
        prop_lines,
        0,
        "AY_DEBUG_PROP should not affect the ay binary without --debug prop; stderr tail: {}",
        stderr.lines().rev().take(5).collect::<Vec<_>>().join(" | ")
    );
}
