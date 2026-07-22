// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the CLI-owned runtime observability / debug flags (#8726).
//!
//! The `ay` binary documents and honors these controls through CLI flags.

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

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_cli_runtime_flags_{}_{}.{}",
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

fn assert_success(output: &std::process::Output, context: &str) {
    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "{context}, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_no_deprecation(output: &std::process::Output, context: &str) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("deprecated"), "{context}, got: {stderr}");
}

/// Trivially satisfiable DIMACS CNF.
const TRIVIAL_SAT_CNF: &str = "p cnf 2 1\n1 2 0\n";

/// Trivially satisfiable SMT-LIB instance for theory-side flag parsing.
const TRIVIAL_LIA_SMT: &str =
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 0))\n(check-sat)\n";

/// Non-trivial pure-BV instance for the certificate-export flag.
const TRIVIAL_BV_SMT: &str = "(set-logic QF_BV)\n\
(declare-const x (_ BitVec 8))\n\
(assert (= x #x00))\n\
(check-sat)\n";

#[test]
#[timeout(60_000)]
fn test_debug_lia_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_LIA_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--debug")
        .arg("lia")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --debug lia");
    assert_no_deprecation(&output, "CLI --debug should not emit deprecation warnings");
}

#[test]
#[timeout(60_000)]
fn test_dump_conflicts_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--dump-conflicts")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --dump-conflicts");
    assert_no_deprecation(&output, "CLI --dump-conflicts should not warn");
}

#[test]
#[timeout(60_000)]
fn test_trace_ext_conflict_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--trace-ext-conflict")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --trace-ext-conflict");
    assert_no_deprecation(&output, "CLI --trace-ext-conflict should not warn");
}

#[test]
#[timeout(60_000)]
fn test_iuc_cli_flags_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_LIA_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--iuc-trace")
        .arg("--strict-iuc-farkas")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with IUC flags");
    assert_no_deprecation(&output, "CLI IUC flags should not warn");
}

#[test]
#[timeout(60_000)]
fn test_bve_cli_flags_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--bve-limit")
        .arg("1000000")
        .arg("--bve-max-rounds")
        .arg("5")
        .arg("--bve-trace")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with BVE tuning flags");
    assert_no_deprecation(&output, "CLI BVE tuning flags should not warn");
}

#[test]
#[timeout(60_000)]
fn test_observability_file_flags_parse_without_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_BV_SMT, "smt2");
    let (decision_log, _d1) = temp_path("log");
    let (dump_bv_cnf, _d2) = temp_path("cnf");
    let (diagnostic_file, _d3) = temp_path("jsonl");
    let (dpll_diagnostic_file, _d4) = temp_path("jsonl");
    let (dpll_trace_file, _d5) = temp_path("jsonl");
    let (kind_dump_dir, _d6) = temp_path("dir");

    let output = Command::new(ay_path)
        .arg("--decision-log")
        .arg(&decision_log)
        .arg("--dump-bv-cnf")
        .arg(&dump_bv_cnf)
        .arg("--diagnostic-file")
        .arg(&diagnostic_file)
        .arg("--dpll-diagnostic-file")
        .arg(&dpll_diagnostic_file)
        .arg("--dpll-trace-file")
        .arg(&dpll_trace_file)
        .arg("--kind-dump-dir")
        .arg(&kind_dump_dir)
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with observability file flags");
    assert_no_deprecation(&output, "CLI observability file flags should not warn");
    assert!(
        dump_bv_cnf.exists(),
        "--dump-bv-cnf must produce its requested certificate artifact"
    );
}

#[test]
#[timeout(60_000)]
fn test_clause_provenance_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--clause-provenance")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --clause-provenance");
    assert_no_deprecation(&output, "CLI --clause-provenance should not warn");
}

#[test]
#[timeout(60_000)]
fn test_dpll_diagnostic_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_LIA_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--dpll-diagnostic")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --dpll-diagnostic");
    assert_no_deprecation(&output, "CLI --dpll-diagnostic should not warn");
}

#[test]
#[timeout(60_000)]
fn test_sat_variant_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--sat-variant")
        .arg("default")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --sat-variant");
    assert_no_deprecation(&output, "CLI --sat-variant should not warn");
}

#[test]
#[timeout(60_000)]
fn test_log_and_memory_cli_flags_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--log")
        .arg("--memory")
        .arg("4096")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --log/--memory");
    assert_no_deprecation(&output, "CLI --log/--memory should not warn");
}

#[test]
#[timeout(60_000)]
fn test_debug_transred_clause_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--debug-transred-clause")
        .arg("42")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --debug-transred-clause");
    assert_no_deprecation(&output, "CLI --debug-transred-clause should not warn");
}

#[test]
#[timeout(60_000)]
fn test_multiple_new_flags_compose() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--dump-conflicts")
        .arg("--trace-ext-conflict")
        .arg("--bve-trace")
        .arg("--dump-auflia-assertions")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with composed CLI runtime flags");
    assert_no_deprecation(&output, "pure CLI composition should not warn");
}

#[test]
#[timeout(60_000)]
fn test_debug_channel_new_cli_flags_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--debug")
        .arg("array-axiom-site,auflia-fix,row2-components,regex,euf-fallback")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with composed --debug flags");
    assert_no_deprecation(&output, "CLI --debug channels should not warn");
}

#[test]
#[timeout(60_000)]
fn test_debug_pcr_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_LIA_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--debug")
        .arg("pcr")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --debug pcr");
    assert_no_deprecation(&output, "CLI --debug pcr should not warn");
}

#[test]
#[timeout(60_000)]
fn test_debug_auflia_fix_summary_cli_flag_no_warning() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_LIA_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--debug")
        .arg("auflia-fix-summary")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert_success(&output, "ay failed with --debug auflia-fix-summary");
    assert_no_deprecation(&output, "CLI --debug auflia-fix-summary should not warn");
}

#[test]
#[timeout(60_000)]
fn test_help_lists_new_8726_flags() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--help=full")
        .output()
        .expect("spawn ay");

    let help = String::from_utf8_lossy(&output.stdout);
    for flag in [
        "--dump-conflicts",
        "--trace-ext-conflict",
        "--iuc-trace",
        "--strict-iuc-farkas",
        "--decision-log",
        "--dump-bv-cnf",
        "--dpll-diagnostic-file",
        "--dpll-diagnostic",
        "--dpll-trace-file",
        "--kind-dump-dir",
        "--sat-variant",
        "--log",
        "--debug-transred-clause",
        "--memory",
    ] {
        assert!(
            help.contains(flag),
            "help output missing {flag}, got:\n{help}"
        );
    }
}
