// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for Z3-compatible CLI aliases handled by `ay`.

use ntest::timeout;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_z3_compat_args_{}_{}.{}",
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

fn write_dash_prefixed_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "-ay_z3_compat_args_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    std::fs::write(&path, contents).expect("write dash-prefixed temp input");
    (path.clone(), CleanupGuard(path))
}

fn trivial_sat_smt() -> &'static str {
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n"
}

fn trivial_safe_horn() -> &'static str {
    "(set-logic HORN)\n\
     (declare-rel Inv (Int))\n\
     (declare-var x Int)\n\
     (rule (Inv 0))\n\
     (rule (=> (and (Inv x) (< x 2)) (Inv (+ x 1))))\n\
     (query (and (Inv x) (> x 5)))\n"
}

fn trivial_safe_horn_check_sat() -> &'static str {
    "(set-logic HORN)\n\
     (declare-fun Inv (Int) Bool)\n\
     (assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
     (assert (forall ((x Int)) (=> (and (Inv x) (< x 10)) (Inv (+ x 1)))))\n\
     (assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n\
     (check-sat)\n"
}

fn trivial_sat_dimacs() -> &'static str {
    "p cnf 1 1\n1 0\n"
}

fn timeout_exerciser_smt() -> String {
    let mut smt = String::from("(set-logic QF_LIA)\n");
    for i in 0..5000 {
        smt.push_str(&format!("(declare-const x{i} Int)\n"));
        smt.push_str(&format!("(assert (>= x{i} 0))\n"));
        smt.push_str(&format!("(assert (<= x{i} 1000000))\n"));
    }
    smt.push_str("(check-sat)\n");
    smt
}

fn run_stdin(input: &str) -> std::process::Output {
    run_ay_stdin_with_args(&[], input, true)
}

fn run_ay_stdin_with_args(
    args: &[&str],
    input: &str,
    provenance_child: bool,
) -> std::process::Output {
    let mut command = Command::new(ay_binary());
    command
        .args(args)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if provenance_child {
        command.env("AY_INTERNAL_PROVENANCE_CHILD", "1");
    }
    let mut child = command.spawn().expect("spawn ay -in");

    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");

    child.wait_with_output().expect("wait for ay -in")
}

fn run_program_stdin(program: &str, input: &str, ay_child: bool) -> std::process::Output {
    let mut command = Command::new(program);
    command
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if ay_child {
        command.env("AY_INTERNAL_PROVENANCE_CHILD", "1");
    }
    let mut child = command.spawn().expect("spawn solver -in");

    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");

    child.wait_with_output().expect("wait for solver -in")
}

fn run_installed_z3(input: &str) -> Option<std::process::Output> {
    let z3 = "/opt/homebrew/bin/z3";
    if !Path::new(z3).is_file() {
        return None;
    }
    Some(run_program_stdin(z3, input, false))
}

#[test]
#[timeout(30_000)]
fn dash_version_alias_matches_long_version() {
    let expected = Command::new(ay_binary())
        .arg("--version")
        .output()
        .expect("spawn ay --version");
    let actual = Command::new(ay_binary())
        .arg("-version")
        .output()
        .expect("spawn ay -version");

    assert!(expected.status.success(), "--version should succeed");
    assert!(actual.status.success(), "-version should succeed");
    assert_eq!(actual.stdout, expected.stdout);
}

#[test]
#[timeout(30_000)]
fn question_mark_alias_prints_help() {
    let output = Command::new(ay_binary())
        .arg("-?")
        .output()
        .expect("spawn ay -?");

    assert!(
        output.status.success(),
        "-? should print help: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Usage:"), "expected help, got: {stdout}");
    assert!(stdout.contains("ay"), "expected ay help, got: {stdout}");
    assert!(
        stdout.contains("--                  End option parsing"),
        "expected Z3-style -- documentation, got: {stdout}"
    );
    assert!(
        stdout.contains("Unsupported Z3 options"),
        "expected unsupported Z3 option diagnostics in help, got: {stdout}"
    );
    assert!(
        stdout.contains("-tactics[:NAME]"),
        "expected unsupported Z3 catalog flags in help, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn file_colon_alias_solves_path() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg(format!("-file:{}", input.display()))
        .output()
        .expect("spawn ay -file:PATH");

    assert!(
        output.status.success(),
        "-file:PATH should solve: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn capital_t_timeout_alias_is_accepted() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-T:0")
        .arg(&input)
        .output()
        .expect("spawn ay -T:0");

    assert!(
        output.status.success(),
        "-T:0 should be accepted as no timeout: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn lowercase_t_timeout_alias_is_accepted() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-t:0")
        .arg(&input)
        .output()
        .expect("spawn ay -t:0");

    assert!(
        output.status.success(),
        "-t:0 should be accepted as no timeout: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn lowercase_t_timeout_alias_uses_watchdog() {
    let smt = timeout_exerciser_smt();
    let (input, _cleanup) = write_temp(&smt, "smt2");
    let output = Command::new(ay_binary())
        .arg("-t:1")
        .arg(&input)
        .output()
        .expect("spawn ay -t:1");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "-t:1 should route through the watchdog and print unknown; stdout={stdout:?}, stderr={stderr:?}, status={:?}",
        output.status
    );
    assert!(
        stderr.contains("timeout") || stderr.contains("reason-unknown"),
        "-t:1 should report the timeout reason on stderr; stdout={stdout:?}, stderr={stderr:?}, status={:?}",
        output.status
    );
}

#[test]
#[timeout(30_000)]
fn capital_t_timeout_alias_uses_watchdog() {
    let mut child = Command::new(ay_binary())
        .arg("-T:1")
        .arg("-in")
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -T:1");

    let _held_stdin = child.stdin.take().expect("child stdin");
    let status = child.wait().expect("wait for ay -T:1");

    let mut stdout = Vec::new();
    child
        .stdout
        .take()
        .expect("child stdout")
        .read_to_end(&mut stdout)
        .expect("read stdout");
    let mut stderr = Vec::new();
    child
        .stderr
        .take()
        .expect("child stderr")
        .read_to_end(&mut stderr)
        .expect("read stderr");

    let stdout = String::from_utf8_lossy(&stdout);
    let stderr = String::from_utf8_lossy(&stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "-T:1 should route through the watchdog and print unknown; stdout={stdout:?}, stderr={stderr:?}, status={status:?}"
    );
    assert!(
        stderr.contains("timeout") || stderr.contains("reason-unknown"),
        "-T:1 should report the timeout reason on stderr; stdout={stdout:?}, stderr={stderr:?}, status={status:?}"
    );
}

#[test]
#[timeout(30_000)]
fn memory_alias_is_accepted() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-memory:0")
        .arg(&input)
        .output()
        .expect("spawn ay -memory:0");

    assert!(
        output.status.success(),
        "-memory:0 should be accepted as unlimited memory: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn smt2_alias_is_accepted_as_noop() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-smt2")
        .arg(&input)
        .output()
        .expect("spawn ay -smt2");

    assert!(
        output.status.success(),
        "-smt2 should be accepted as an auto-detection no-op: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn double_dash_allows_dash_prefixed_input_file() {
    let (input, _cleanup) = write_dash_prefixed_temp(trivial_sat_smt(), "smt2");
    let filename = input.file_name().expect("temp input filename");
    let output = Command::new(ay_binary())
        .current_dir(input.parent().expect("temp input parent"))
        .arg("--")
        .arg(filename)
        .output()
        .expect("spawn ay -- -FILE");

    assert!(
        output.status.success(),
        "-- should allow dash-prefixed input files: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn dimacs_alias_is_accepted_as_auto_detected_mode() {
    let (input, _cleanup) = write_temp(trivial_sat_dimacs(), "txt");
    let output = Command::new(ay_binary())
        .arg("-dimacs")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .output()
        .expect("spawn ay -dimacs");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(10),
        "-dimacs should solve DIMACS input, stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.contains("s SATISFIABLE"),
        "expected DIMACS SAT output, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn warning_and_verbosity_aliases_are_accepted() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-nw")
        .arg("-v:2")
        .arg(&input)
        .output()
        .expect("spawn ay -nw -v:2");

    assert!(
        output.status.success(),
        "-nw and -v:level should be accepted: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn invalid_verbosity_alias_is_rejected_explicitly() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-v:abc")
        .arg(&input)
        .output()
        .expect("spawn ay -v:abc");

    assert!(
        !output.status.success(),
        "-v:abc should be rejected explicitly"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unsupported Z3 option '-v:abc'"),
        "expected explicit unsupported-option error: {stderr}"
    );
    assert!(
        stderr.contains("invalid verbosity level") && stderr.contains("unsigned integer"),
        "expected invalid verbosity diagnostic: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn parameter_listing_alias_prints_supported_z3_subset() {
    let output = Command::new(ay_binary())
        .arg("-p")
        .output()
        .expect("spawn ay -p");

    assert!(
        output.status.success(),
        "-p should print supported Z3-style params: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("Global parameters"),
        "expected global parameter header: {stdout}"
    );
    assert!(
        stdout.contains("timeout (unsigned int)"),
        "expected timeout parameter: {stdout}"
    );
    assert!(
        stdout.contains("[module] fp"),
        "expected fp module listing: {stdout}"
    );
    assert!(
        stdout.contains("engine (symbol)"),
        "expected fp.engine parameter: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "-p should not emit solve-session markers on stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn parameter_description_alias_prints_descriptions() {
    let output = Command::new(ay_binary())
        .arg("-pd")
        .output()
        .expect("spawn ay -pd");

    assert!(
        output.status.success(),
        "-pd should print supported Z3-style param descriptions: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("timeout in milliseconds"),
        "expected timeout description: {stdout}"
    );
    assert!(
        stdout.contains("print ay statistics when set to true"),
        "expected stats description: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn trace_param_description_alias_prints_compat_noop_contract() {
    let output = Command::new(ay_binary())
        .arg("-pp:trace_file_name")
        .output()
        .expect("spawn ay -pp:trace_file_name");

    assert!(
        output.status.success(),
        "-pp:trace_file_name should describe the supported trace-file compatibility param: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("trace_file_name") && stdout.contains("accepted as a compatibility no-op"),
        "expected trace_file_name no-op description: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn parameter_module_alias_prints_supported_module() {
    let output = Command::new(ay_binary())
        .arg("-pm:fp")
        .output()
        .expect("spawn ay -pm:fp");

    assert!(
        output.status.success(),
        "-pm:fp should print the supported fp compatibility subset: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("[module] fp"),
        "expected fp module header: {stdout}"
    );
    assert!(
        stdout.contains("engine (symbol)"),
        "expected fp.engine parameter: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn parameter_module_list_alias_prints_supported_modules() {
    let output = Command::new(ay_binary())
        .arg("-pm")
        .output()
        .expect("spawn ay -pm");

    assert!(
        output.status.success(),
        "-pm should print supported Z3-style compatibility modules: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    for module in [
        "[module] fp",
        "[module] nlsat",
        "[module] sat",
        "[module] smt",
    ] {
        assert!(
            stdout.contains(module),
            "expected supported module {module}: {stdout}"
        );
    }
    assert!(
        stderr.is_empty(),
        "-pm should not emit solve-session markers on stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn parameter_description_lookup_alias_prints_one_param() {
    let output = Command::new(ay_binary())
        .arg("-pp:timeout")
        .output()
        .expect("spawn ay -pp:timeout");

    assert!(
        output.status.success(),
        "-pp:timeout should print a supported parameter description: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("timeout"),
        "expected timeout parameter name: {stdout}"
    );
    assert!(
        stdout.contains("milliseconds"),
        "expected timeout parameter description: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn unsupported_z3_tactic_catalog_is_rejected_explicitly() {
    for flag in ["-tactics", "-tactics:ctx-solver-simplify"] {
        let output = Command::new(ay_binary())
            .arg(flag)
            .output()
            .unwrap_or_else(|error| panic!("spawn ay {flag}: {error}"));

        assert!(
            !output.status.success(),
            "{flag} should be rejected until ay exposes a real tactic catalog"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(&format!("unsupported Z3 option '{flag}'")),
            "expected explicit unsupported-option error for {flag}: {stderr}"
        );
        assert!(
            stderr.contains("tactic catalog"),
            "expected honest tactic catalog diagnostic for {flag}: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn unsupported_z3_help_surface_flags_are_rejected_explicitly() {
    for (flag, expected) in [
        ("-dl", "Datalog input is not supported"),
        ("-wcnf", "Weighted CNF DIMACS is not supported"),
        ("-lp", "Flag-style CPLEX LP parsing is not supported"),
        ("-log", "Z3 log input is not supported"),
        ("-probes", "ay does not implement Z3 probes"),
        ("-simplifiers", "does not expose Z3's simplifier catalog"),
        (
            "-simplifiers:ctx-simplify",
            "does not expose Z3's simplifier catalog",
        ),
        (
            "-pmmd:fp",
            "Markdown Z3 parameter listings are not supported",
        ),
        ("-pp", "option argument (-pp:name) is missing"),
    ] {
        let output = Command::new(ay_binary())
            .arg(flag)
            .output()
            .unwrap_or_else(|error| panic!("spawn ay {flag}: {error}"));

        assert!(
            !output.status.success(),
            "{flag} should be rejected explicitly"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(&format!("unsupported Z3 option '{flag}'")),
            "expected unsupported-option error for {flag}: {stderr}"
        );
        assert!(
            stderr.contains(expected),
            "expected diagnostic fragment {expected:?} for {flag}: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn unsupported_z3_input_mode_is_rejected_with_suggestion() {
    let (input, _cleanup) = write_temp("* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n", "opb");
    let output = Command::new(ay_binary())
        .arg("-opb")
        .arg(&input)
        .output()
        .expect("spawn ay -opb FILE");

    assert!(
        !output.status.success(),
        "-opb flag-style parsing should be rejected explicitly"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unsupported Z3 option '-opb'"),
        "expected explicit unsupported-option error: {stderr}"
    );
    assert!(
        stderr.contains("ay pb solve FILE"),
        "expected pb subcommand suggestion: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn stdin_alias_solves_piped_smt2() {
    let output = run_stdin(trivial_sat_smt());
    assert!(
        output.status.success(),
        "-in should solve piped SMT-LIB: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn smt_query_outputs_stay_on_stdout_without_stderr_noise() {
    let output = run_stdin(
        "(get-info :name)
(get-info :version)
(get-option :produce-models)
(set-option :produce-models true)
(get-option :produce-models)
(set-option :produce-unsat-cores true)
(get-option :produce-unsat-cores)
(exit)
",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "SMT query commands should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "metadata and option query output should not leak to stderr: {stderr}"
    );
    assert!(
        stdout.contains("(:name \"Z3\")"),
        "expected get-info :name on stdout: {stdout}"
    );
    assert!(
        stdout.contains("(:version \""),
        "expected get-info :version on stdout: {stdout}"
    );
    assert!(
        stdout.lines().filter(|line| *line == "true").count() >= 3,
        "expected bare true values for produce-models and produce-unsat-cores: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn smt_get_info_name_matches_installed_z3_transcript() {
    let script = "(get-info :name)\n";
    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "get-info :name should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert_eq!(stdout, "(:name \"Z3\")\n");
    assert!(
        stderr.is_empty(),
        "get-info :name should not emit stderr: {stderr}"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept get-info :name; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            output.stdout, z3.stdout,
            "ay stdout should match installed z3"
        );
        assert_eq!(
            output.stderr, z3.stderr,
            "ay stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_info_authors_matches_installed_z3_transcript() {
    let script = "(get-info :authors)\n";
    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "get-info :authors should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert_eq!(
        stdout,
        "(:authors \"Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger\")\n"
    );
    assert!(
        stderr.is_empty(),
        "get-info :authors should not emit stderr: {stderr}"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept get-info :authors; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            output.stdout, z3.stdout,
            "ay stdout should match installed z3"
        );
        assert_eq!(
            output.stderr, z3.stderr,
            "ay stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_info_version_keeps_ay_provenance_with_z3_record_shape() {
    let script = "(get-info :version)\n";
    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "get-info :version should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "get-info :version should not emit stderr: {stderr}"
    );
    assert!(
        stdout.starts_with("(:version \"build.version="),
        "get-info :version should preserve ay build provenance: {stdout}"
    );
    for fragment in [
        " build.increment=",
        " build.commit=",
        " build.datetime_utc=",
        " build.stamp=",
    ] {
        assert!(
            stdout.contains(fragment),
            "get-info :version should include {fragment:?}: {stdout}"
        );
    }
    assert!(
        stdout.ends_with("\")\n"),
        "get-info :version should remain an SMT-LIB version record: {stdout}"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept get-info :version; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert!(
            z3_stderr.is_empty(),
            "installed z3 should not emit stderr for get-info :version: {z3_stderr}"
        );
        assert!(
            z3_stdout.starts_with("(:version \"") && z3_stdout.ends_with("\")\n"),
            "installed z3 should emit an SMT-LIB version record: {z3_stdout}"
        );
        assert_ne!(
            output.stdout, z3.stdout,
            "ay intentionally keeps build provenance instead of spoofing the installed z3 version"
        );
    }
}

#[test]
#[timeout(30_000)]
fn z3_mode_get_info_version_suppresses_ay_build_provenance() {
    let output = run_ay_stdin_with_args(&["--z3-mode"], "(get-info :version)\n", true);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--z3-mode get-info :version should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "--z3-mode get-info :version should not emit stderr: {stderr}"
    );
    assert!(
        stdout.starts_with("(:version \"") && stdout.ends_with("\")\n"),
        "--z3-mode should keep the Z3 version record shape: {stdout}"
    );
    assert!(
        !stdout.contains("build.version=")
            && !stdout.contains("build.commit=")
            && !stdout.contains("build.stamp="),
        "--z3-mode should suppress AY build provenance in transcripts: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn z3_mode_skips_default_solve_session_provenance_wrapper() {
    let (input, _cleanup) = write_temp("(get-info :version)\n", "smt2");

    let default_output = Command::new(ay_binary())
        .env_remove("CARGO_TARGET_TMPDIR")
        .env_remove("AY_INTERNAL_PROVENANCE_CHILD")
        .arg(&input)
        .output()
        .expect("spawn ay FILE");
    let default_stderr = String::from_utf8_lossy(&default_output.stderr);
    assert!(
        default_output.status.success(),
        "default file solve should succeed: {default_stderr}"
    );
    assert!(
        default_stderr.contains("ay.session.start") && default_stderr.contains("ay.session.end"),
        "default AY file solve should keep session provenance markers: {default_stderr}"
    );

    let z3_mode_output = Command::new(ay_binary())
        .env_remove("CARGO_TARGET_TMPDIR")
        .env_remove("AY_INTERNAL_PROVENANCE_CHILD")
        .arg("--z3-mode")
        .arg(&input)
        .output()
        .expect("spawn ay --z3-mode FILE");
    let stdout = String::from_utf8_lossy(&z3_mode_output.stdout);
    let stderr = String::from_utf8_lossy(&z3_mode_output.stderr);
    assert!(
        z3_mode_output.status.success(),
        "--z3-mode file solve should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "--z3-mode should not emit solve-session provenance markers: {stderr}"
    );
    assert!(
        !stdout.contains("build.version="),
        "--z3-mode should keep the transcript clean on stdout too: {stdout}"
    );
}

#[cfg(unix)]
#[test]
#[timeout(30_000)]
fn argv0_z3_symlink_enables_z3_mode_without_explicit_flag() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let z3_link = temp.path().join("z3");
    std::os::unix::fs::symlink(ay_binary(), &z3_link).expect("create z3 symlink");

    let mut child = Command::new(&z3_link)
        .env_remove("CARGO_TARGET_TMPDIR")
        .env_remove("AY_INTERNAL_PROVENANCE_CHILD")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn argv0 z3 symlink -in");

    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(b"(get-info :version)\n")
        .expect("write SMT-LIB input");

    let output = child.wait_with_output().expect("wait for argv0 z3");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "argv0 z3 symlink should solve in Z3 mode; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "argv0 z3 symlink should suppress AY provenance: {stderr}"
    );
    assert!(
        stdout.starts_with("(:version \"") && stdout.ends_with("\")\n"),
        "argv0 z3 symlink should keep a Z3-shaped version record: {stdout}"
    );
    assert!(
        !stdout.contains("build.version=")
            && !stdout.contains("build.commit=")
            && !stdout.contains("build.stamp="),
        "argv0 z3 symlink should not expose AY build provenance: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn z3_mode_file_invocation_accepts_common_model_stats_flags_without_provenance() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .env_remove("CARGO_TARGET_TMPDIR")
        .env_remove("AY_INTERNAL_PROVENANCE_CHILD")
        .arg("--z3-mode")
        .arg("-smt2")
        .arg("-model")
        .arg("-st")
        .arg(format!("-file:{}", input.display()))
        .output()
        .expect("spawn ay --z3-mode -smt2 -model -st -file:PATH");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--z3-mode common file invocation should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    // --z3-mode emits get-model as a bare `( <define-fun>* )` (z3 4.15.4 /
    // SMT-LIB 2.6), not the legacy `(model …)` head (see d0201aa2). Assert the
    // z3-parity form, not the pre-parity one.
    assert!(
        stdout.contains("(\n  (define-fun x () Int"),
        "expected z3-mode bare model output: {stdout}"
    );
    assert!(
        stderr.contains("(:statistics") && stderr.contains(":num-assertions"),
        "-st should keep the explicit statistics channel available: {stderr}"
    );
    assert!(
        !stderr.contains("ay.session.") && !stdout.contains("build.version="),
        "--z3-mode should suppress default ay provenance while preserving requested output; stdout={stdout}, stderr={stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn chc_spacer_compat_params_accept_horn_cli_path() {
    let (input, _cleanup) = write_temp(trivial_safe_horn(), "smt2");
    let output = Command::new(ay_binary())
        .arg("fp.engine=spacer")
        .arg("fp.spacer.random_seed=7")
        .arg(format!("-file:{}", input.display()))
        .output()
        .expect("spawn ay fp.engine=spacer fp.spacer.random_seed=7 -file:PATH");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "CHC compatibility params should accept a HORN file invocation; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "unsat"),
        "expected SAFE HORN query result, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
#[ignore = "0.1.x: HORN (get-model) currently fails closed to `unknown` (the \
theory-search model falsifies an assertion, so the soundness gate rejects it) \
instead of emitting the Spacer-shaped invariant from the CHC certificate. This \
is SOUND — never a wrong model — but incomplete. Tracked in LIMITATIONS.md; the \
CHC invariant->get-model rendering is the fix."]
fn horn_get_model_in_z3_mode_emits_spacer_model_not_ay_certificate() {
    let input = format!("{}(get-model)\n", trivial_safe_horn_check_sat());
    let output = run_ay_stdin_with_args(&["--z3-mode"], &input, true);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "HORN get-model should succeed in --z3-mode; stdout={stdout}, stderr={stderr}"
    );
    assert_eq!(
        stdout.lines().next(),
        Some("sat"),
        "expected SAT result before HORN model: {stdout}"
    );
    assert!(
        stdout.contains("(\n  (define-fun Inv"),
        "expected Spacer-shaped HORN model, got: {stdout}"
    );
    assert!(
        !stdout.contains("AY CHC Certificate"),
        "--z3-mode explicit get-model should not emit the ay certificate on stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "--z3-mode HORN get-model should keep stderr clean: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn z3_model_flag_appends_horn_get_model_request() {
    let (input, _cleanup) = write_temp(trivial_safe_horn_check_sat(), "smt2");
    let output = Command::new(ay_binary())
        .arg("--z3-mode")
        .arg("-model")
        .arg(format!("-file:{}", input.display()))
        .output()
        .expect("spawn ay --z3-mode -model -file:HORN");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "HORN -model should succeed in --z3-mode; stdout={stdout}, stderr={stderr}"
    );
    assert_eq!(
        stdout.lines().next(),
        Some("sat"),
        "expected SAT result before HORN model: {stdout}"
    );
    assert!(
        stdout.contains("(\n  (define-fun Inv"),
        "expected -model to request a Spacer-shaped HORN model, got: {stdout}"
    );
    assert!(
        !stdout.contains("AY CHC Certificate"),
        "--z3-mode -model should not emit the ay certificate on stdout: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn smt_low_risk_info_queries_use_documented_ay_transcript() {
    let output = run_stdin(
        "(get-info :authors)
(get-info :error-behavior)
(get-info :reason-unknown)
(exit)
",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "low-risk get-info queries should not be CLI failures; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "low-risk get-info query output should not leak to stderr: {stderr}"
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines,
        vec![
            "(:authors \"Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger\")",
            "(:error-behavior continued-execution)",
            "(:reason-unknown \"state of the most recent check-sat command is not known\")",
        ],
        "unexpected get-info transcript: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn smt_status_rlimit_and_parameters_match_z3_low_risk_transcript() {
    let script = "(get-info :status)
(get-info :rlimit)
(get-info :parameters)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "status/rlimit/parameters query should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "status/rlimit/parameters query should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "(:status unknown)\n(:rlimit 1)\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept the comparison script; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stdout, z3_stdout, "ay transcript should match installed z3");
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
    }
}

#[test]
#[timeout(30_000)]
fn smt_status_tracks_set_info_and_print_success_like_z3() {
    let script = "(set-option :print-success true)
(set-info :status sat)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "set-info status transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "set-info status transcript should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "success\nsuccess\n(:status sat)\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept the set-info comparison script; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stdout, z3_stdout, "ay transcript should match installed z3");
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
    }
}

#[test]
#[timeout(30_000)]
fn smt_invalid_status_symbol_is_recoverable_but_nonzero() {
    let script = "(set-option :print-success true)
(set-info :status foo)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "invalid status attribute should make final CLI status non-zero; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "invalid status attribute should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\n(error \"line 2 column 18: invalid ':status' attribute\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the invalid status attribute but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            4,
            "installed z3 should emit success, error, status, success; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[0], "success");
        assert!(
            z3_lines[1].contains("invalid ':status' attribute"),
            "installed z3 should identify invalid :status; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[2], "(:status unknown)");
        assert_eq!(z3_lines[3], "success");
    }
}

#[test]
#[timeout(30_000)]
fn smt_pop_underflow_is_recoverable_but_nonzero_like_z3() {
    let script = "(set-option :print-success true)
(pop)
(push)
(pop 2)
(pop)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "invalid pop should make final CLI status non-zero; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "invalid pop should not emit stderr or panic text: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\n(error \"line 2 column 4: invalid pop command, argument is greater than the current stack depth\")\nsuccess\n(error \"line 4 column 6: invalid pop command, argument is greater than the current stack depth\")\nsuccess\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject invalid pops but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            7,
            "installed z3 should emit success, errors, later success, status, exit success; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[0], "success");
        assert!(
            z3_lines[1].contains("invalid pop command"),
            "installed z3 should identify invalid base pop; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[2], "success");
        assert!(
            z3_lines[3].contains("invalid pop command"),
            "installed z3 should identify over-deep pop; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[4], "success");
        assert_eq!(z3_lines[5], "(:status unknown)");
        assert_eq!(z3_lines[6], "success");
    }
}

#[test]
#[timeout(30_000)]
fn smt_reset_assertions_keeps_visible_scopes_like_z3() {
    let script = "(set-option :print-success true)
(push)
(assert false)
(reset-assertions)
(push)
(assert false)
(pop)
(pop)
(check-sat)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "reset-assertions should preserve Z3-visible scopes and keep later pops valid; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "reset-assertions scoped-pop transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsat\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept the reset-assertions scoped-pop script; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stdout, z3_stdout, "ay transcript should match installed z3");
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
    }
}

#[test]
#[timeout(30_000)]
fn smt_reset_clears_visible_scopes_like_z3() {
    let script = "(set-option :print-success true)
(push)
(assert false)
(reset)
(pop)
(check-sat)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "reset should clear Z3-visible scopes, so later pop is recoverable but non-zero; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "reset invalid-pop transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\n(error \"line 5 column 4: invalid pop command, argument is greater than the current stack depth\")\nsat\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject pop after reset but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            7,
            "installed z3 should emit success, reset, pop error, sat, exit success; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[0], "success");
        assert_eq!(z3_lines[1], "success");
        assert_eq!(z3_lines[2], "success");
        assert_eq!(z3_lines[3], "success");
        assert!(
            z3_lines[4].contains("invalid pop command"),
            "installed z3 should identify pop after reset as invalid; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[5], "sat");
        assert_eq!(z3_lines[6], "success");
    }
}

#[test]
#[timeout(30_000)]
fn smt_incremental_push_pop_repeated_checks_reuse_model_like_z3() {
    let script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
(push)
(assert (< x 0))
(check-sat)
(pop)
(check-sat)
(get-value (x))
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "incremental push/pop transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "incremental push/pop transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\nsat\nsuccess\nsuccess\nunsat\nsuccess\nsat\n((x 1))\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept incremental push/pop transcript; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay incremental push/pop stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay incremental push/pop stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_check_sat_assuming_unsat_assumptions_match_z3() {
    let script = "(set-option :print-success true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const p Bool)
(assert (=> p (< x 0)))
(assert (> x 0))
(check-sat-assuming (p))
(get-unsat-assumptions)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "check-sat-assuming unsat-assumptions transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "check-sat-assuming unsat-assumptions transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nunsat\n(p)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept check-sat-assuming unsat-assumptions transcript; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay check-sat-assuming stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay check-sat-assuming stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_undefined_symbol_errors_are_recoverable_stdout_results() {
    let reset_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const x Int)
(reset)
(assert (= x 1))
(check-sat)
(exit)
";

    // DELIBERATE DIVERGENCE FROM Z3 (#match-soundness, a152df2ff1 "fail-closed on
    // dropped assertions (wrong-SAT)"). `(assert (= x 1))` names `x`, which
    // `(reset)` erased, so the command errors and is DISCARDED. z3 then answers
    // `sat` about the surviving (empty) assertion set — standard-compliant, since
    // an erroring command has no effect. AY instead fails closed to `unknown`:
    // the assertion set it holds is a strict SUBSET of the problem the user
    // wrote, and a dropped constraint can only flip UNSAT into SAT, so answering
    // definitively on the remainder risks reporting `sat` for an unsatisfiable
    // problem. Error recovery itself is at parity — same `(error ...)` text,
    // same exit code, same continue-after-error semantics; only the verdict on a
    // knowingly-incomplete problem is (soundly) weaker. This test pins that
    // choice; it previously pinned the pre-fix behavior and silently rotted.
    let reset_output = run_stdin(reset_script);
    let reset_stdout = String::from_utf8_lossy(&reset_output.stdout);
    let reset_stderr = String::from_utf8_lossy(&reset_output.stderr);
    assert_eq!(
        reset_output.status.code(),
        Some(1),
        "undefined symbol after reset should make final CLI status non-zero; stdout={reset_stdout}, stderr={reset_stderr}"
    );
    assert_eq!(
        reset_stdout,
        "success\nsuccess\nsuccess\nsuccess\n(error \"line 5 column 11: unknown constant x\")\nunknown\nsuccess\n"
    );
    // The `unknown` is explained, not silent: AY says WHY on stderr, so a human
    // is never left guessing. `--z3-mode` suppresses it for byte-exact
    // transcript comparison against z3.
    assert!(
        reset_stderr.contains("a problem-contributing command was discarded"),
        "AY must explain the fail-closed unknown on stderr: {reset_stderr}"
    );

    if let Some(z3) = run_installed_z3(reset_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the undefined symbol but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        let ay_lines: Vec<&str> = reset_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            7,
            "installed z3 should emit success, unknown-constant error, sat, exit success; stdout={z3_stdout}"
        );
        assert_eq!(
            ay_lines.len(),
            z3_lines.len(),
            "ay must emit one response per command exactly as z3 does; ay={reset_stdout}, z3={z3_stdout}"
        );
        // Everything except the verdict line is byte-identical to z3: the
        // `success` acks, the error text, and the post-error recovery.
        for i in [0usize, 1, 2, 3, 6] {
            assert_eq!(
                ay_lines[i], z3_lines[i],
                "line {i} must match installed z3; ay={reset_stdout}, z3={z3_stdout}"
            );
        }
        assert_eq!(
            ay_lines[4], z3_lines[4],
            "the error line must match installed z3 byte-for-byte"
        );
        assert!(
            z3_lines[4].contains("unknown constant x"),
            "installed z3 should identify unknown constant x; stdout={z3_stdout}"
        );
        // The one intended difference: z3 answers on the remainder, AY refuses.
        assert_eq!(z3_lines[5], "sat");
        assert_eq!(ay_lines[5], "unknown");
        assert!(
            z3_stderr.is_empty(),
            "installed z3 emits nothing on stderr here; ay adds only the reason diagnostic"
        );
    }

    let assuming_script = "(set-option :print-success true)
(set-logic QF_LIA)
(check-sat-assuming (p))
(get-info :status)
(exit)
";

    let assuming_output = run_stdin(assuming_script);
    let assuming_stdout = String::from_utf8_lossy(&assuming_output.stdout);
    let assuming_stderr = String::from_utf8_lossy(&assuming_output.stderr);
    assert_eq!(
        assuming_output.status.code(),
        Some(1),
        "undefined check-sat-assuming literal should make final CLI status non-zero; stdout={assuming_stdout}, stderr={assuming_stderr}"
    );
    // AY answers the failed decision query with a synthesized fail-closed
    // `unknown` (every check-sat emits a verdict) and explains it with a
    // single reason diagnostic on stderr; the error text itself matches z3.
    assert_eq!(
        assuming_stderr,
        "(:reason-unknown (incomplete decision-execution-error))\n",
        "undefined check-sat-assuming literal should emit exactly the reason diagnostic: {assuming_stderr}"
    );
    assert_eq!(
        assuming_stdout,
        "success\nsuccess\n(error \"line 3 column 21: unknown constant p\")\nunknown\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(assuming_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the undefined assumption but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        // DELIBERATE DIVERGENCE FROM Z3 (same #match-soundness rationale as
        // the reset script above): AY answers the failed decision query with
        // a synthesized fail-closed `unknown` and explains it with a single
        // reason diagnostic on stderr; z3 emits neither. Every other line is
        // byte-identical to z3.
        assert!(
            z3_stderr.is_empty(),
            "installed z3 emits nothing on stderr here; ay adds only the reason diagnostic: {z3_stderr}"
        );
        let ay_lines: Vec<&str> = assuming_stdout.lines().collect();
        let z3_stdout_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            ay_lines.len(),
            z3_stdout_lines.len() + 1,
            "ay adds exactly the synthesized unknown; ay={assuming_stdout}, z3={z3_stdout}"
        );
        assert_eq!(ay_lines[3], "unknown", "ay={assuming_stdout}");
        for (i, z3_line) in z3_stdout_lines.iter().enumerate() {
            let ay_index = if i < 3 { i } else { i + 1 };
            assert_eq!(
                &ay_lines[ay_index], z3_line,
                "line {i} must match installed z3 outside the synthesized unknown; ay={assuming_stdout}, z3={z3_stdout}"
            );
        }
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            5,
            "installed z3 should emit success, unknown-constant error, status, exit success; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[0], "success");
        assert_eq!(z3_lines[1], "success");
        assert!(
            z3_lines[2].contains("unknown constant p"),
            "installed z3 should identify unknown constant p; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[3], "(:status unknown)");
        assert_eq!(z3_lines[4], "success");
    }

    let function_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= (f y true) 2))
(get-info :status)
(exit)
";

    let function_output = run_stdin(function_script);
    let function_stdout = String::from_utf8_lossy(&function_output.stdout);
    let function_stderr = String::from_utf8_lossy(&function_output.stderr);
    assert_eq!(
        function_output.status.code(),
        Some(1),
        "undefined function application should make final CLI status non-zero; stdout={function_stdout}, stderr={function_stderr}"
    );
    assert!(
        function_stderr.is_empty(),
        "undefined function application should not emit stderr: {function_stderr}"
    );
    assert_eq!(
        function_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 20: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(function_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the undefined function application but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            function_stderr, z3_stderr,
            "ay stderr should match installed z3"
        );
        assert_eq!(
            function_stdout, z3_stdout,
            "ay undefined-function transcript should match installed z3"
        );
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            6,
            "installed z3 should emit success, unknown-function error, status, exit success; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[0], "success");
        assert_eq!(z3_lines[1], "success");
        assert_eq!(z3_lines[2], "success");
        assert!(
            z3_lines[3].contains("unknown constant f (Int Bool) "),
            "installed z3 should include argument sorts for undefined f; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[4], "(:status unknown)");
        assert_eq!(z3_lines[5], "success");
    }
}

#[test]
#[timeout(30_000)]
fn smt_nested_undefined_function_diagnostics_include_arg_sorts() {
    let nested_assert_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= (f (+ y 1) true) 2))
(get-info :status)
(exit)
";

    let nested_assert_output = run_stdin(nested_assert_script);
    let nested_assert_stdout = String::from_utf8_lossy(&nested_assert_output.stdout);
    let nested_assert_stderr = String::from_utf8_lossy(&nested_assert_output.stderr);
    assert_eq!(
        nested_assert_output.status.code(),
        Some(1),
        "nested undefined function should make final CLI status non-zero; stdout={nested_assert_stdout}, stderr={nested_assert_stderr}"
    );
    assert!(
        nested_assert_stderr.is_empty(),
        "nested undefined function should not emit stderr: {nested_assert_stderr}"
    );
    assert_eq!(
        nested_assert_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 26: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(nested_assert_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the nested undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            nested_assert_stderr, z3_stderr,
            "ay nested undefined-function stderr should match installed z3"
        );
        assert_eq!(
            nested_assert_stdout, z3_stdout,
            "ay nested undefined-function stdout should match installed z3"
        );
    }

    let get_value_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(get-value ((f (+ y 1) true)))
(get-info :status)
(exit)
";

    let get_value_output = run_stdin(get_value_script);
    let get_value_stdout = String::from_utf8_lossy(&get_value_output.stdout);
    let get_value_stderr = String::from_utf8_lossy(&get_value_output.stderr);
    assert_eq!(
        get_value_output.status.code(),
        Some(1),
        "nested get-value undefined function should make final CLI status non-zero; stdout={get_value_stdout}, stderr={get_value_stderr}"
    );
    assert!(
        get_value_stderr.is_empty(),
        "nested get-value undefined function should not emit stderr: {get_value_stderr}"
    );
    assert_eq!(
        get_value_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 27: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(get_value_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the nested get-value undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            get_value_stderr, z3_stderr,
            "ay nested get-value stderr should match installed z3"
        );
        assert_eq!(
            get_value_stdout, z3_stdout,
            "ay nested get-value stdout should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_let_bound_undefined_function_diagnostics_include_arg_sorts() {
    let nested_assert_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= (let ((a (+ y 1))) (f a true)) 2))
(get-info :status)
(exit)
";

    let nested_assert_output = run_stdin(nested_assert_script);
    let nested_assert_stdout = String::from_utf8_lossy(&nested_assert_output.stdout);
    let nested_assert_stderr = String::from_utf8_lossy(&nested_assert_output.stderr);
    assert_eq!(
        nested_assert_output.status.code(),
        Some(1),
        "let-bound undefined function should make final CLI status non-zero; stdout={nested_assert_stdout}, stderr={nested_assert_stderr}"
    );
    assert!(
        nested_assert_stderr.is_empty(),
        "let-bound undefined function should not emit stderr: {nested_assert_stderr}"
    );
    assert_eq!(
        nested_assert_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 39: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(nested_assert_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the let-bound undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            nested_assert_stderr, z3_stderr,
            "ay let-bound undefined-function stderr should match installed z3"
        );
        assert_eq!(
            nested_assert_stdout, z3_stdout,
            "ay let-bound undefined-function stdout should match installed z3"
        );
    }

    let get_value_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(get-value ((let ((a (+ y 1))) (f a true))))
(get-info :status)
(exit)
";

    let get_value_output = run_stdin(get_value_script);
    let get_value_stdout = String::from_utf8_lossy(&get_value_output.stdout);
    let get_value_stderr = String::from_utf8_lossy(&get_value_output.stderr);
    assert_eq!(
        get_value_output.status.code(),
        Some(1),
        "let-bound get-value undefined function should make final CLI status non-zero; stdout={get_value_stdout}, stderr={get_value_stderr}"
    );
    assert!(
        get_value_stderr.is_empty(),
        "let-bound get-value undefined function should not emit stderr: {get_value_stderr}"
    );
    assert_eq!(
        get_value_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 40: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(get_value_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the let-bound get-value undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            get_value_stderr, z3_stderr,
            "ay let-bound get-value stderr should match installed z3"
        );
        assert_eq!(
            get_value_stdout, z3_stdout,
            "ay let-bound get-value stdout should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_quantified_undefined_function_diagnostics_include_bound_arg_sorts() {
    let forall_script = "(set-option :print-success true)
(assert (forall ((q Int)) (= (f q true) 0)))
(get-info :status)
(exit)
";

    let forall_output = run_stdin(forall_script);
    let forall_stdout = String::from_utf8_lossy(&forall_output.stdout);
    let forall_stderr = String::from_utf8_lossy(&forall_output.stderr);
    assert_eq!(
        forall_output.status.code(),
        Some(1),
        "forall undefined function should make final CLI status non-zero; stdout={forall_stdout}, stderr={forall_stderr}"
    );
    assert!(
        forall_stderr.is_empty(),
        "forall undefined function should not emit stderr: {forall_stderr}"
    );
    assert_eq!(
        forall_stdout,
        "success\n(error \"line 2 column 38: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(forall_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the forall undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            forall_stderr, z3_stderr,
            "ay forall undefined-function stderr should match installed z3"
        );
        assert_eq!(
            forall_stdout, z3_stdout,
            "ay forall undefined-function stdout should match installed z3"
        );
    }

    let exists_script = "(set-option :print-success true)
(assert (exists ((q Int)) (= (f q true) 0)))
(get-info :status)
(exit)
";

    let exists_output = run_stdin(exists_script);
    let exists_stdout = String::from_utf8_lossy(&exists_output.stdout);
    let exists_stderr = String::from_utf8_lossy(&exists_output.stderr);
    assert_eq!(
        exists_output.status.code(),
        Some(1),
        "exists undefined function should make final CLI status non-zero; stdout={exists_stdout}, stderr={exists_stderr}"
    );
    assert!(
        exists_stderr.is_empty(),
        "exists undefined function should not emit stderr: {exists_stderr}"
    );
    assert_eq!(
        exists_stdout,
        "success\n(error \"line 2 column 38: unknown constant f (Int Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(exists_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the exists undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            exists_stderr, z3_stderr,
            "ay exists undefined-function stderr should match installed z3"
        );
        assert_eq!(
            exists_stdout, z3_stdout,
            "ay exists undefined-function stdout should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_array_select_store_undefined_function_diagnostics_include_arg_sorts() {
    let select_script = "(set-option :print-success true)
(declare-const a (Array Int Bool))
(assert (= (f (select a 0) 1) 2))
(get-info :status)
(exit)
";

    let select_output = run_stdin(select_script);
    let select_stdout = String::from_utf8_lossy(&select_output.stdout);
    let select_stderr = String::from_utf8_lossy(&select_output.stderr);
    assert_eq!(
        select_output.status.code(),
        Some(1),
        "select undefined function should make final CLI status non-zero; stdout={select_stdout}, stderr={select_stderr}"
    );
    assert!(
        select_stderr.is_empty(),
        "select undefined function should not emit stderr: {select_stderr}"
    );
    assert_eq!(
        select_stdout,
        "success\nsuccess\n(error \"line 3 column 28: unknown constant f (Bool Int) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(select_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the select undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            select_stderr, z3_stderr,
            "ay select undefined-function stderr should match installed z3"
        );
        assert_eq!(
            select_stdout, z3_stdout,
            "ay select undefined-function stdout should match installed z3"
        );
    }

    let store_script = "(set-option :print-success true)
(declare-const a (Array Int Bool))
(assert (= (f (store a 0 true) false) 2))
(get-info :status)
(exit)
";

    let store_output = run_stdin(store_script);
    let store_stdout = String::from_utf8_lossy(&store_output.stdout);
    let store_stderr = String::from_utf8_lossy(&store_output.stderr);
    assert_eq!(
        store_output.status.code(),
        Some(1),
        "store undefined function should make final CLI status non-zero; stdout={store_stdout}, stderr={store_stderr}"
    );
    assert!(
        store_stderr.is_empty(),
        "store undefined function should not emit stderr: {store_stderr}"
    );
    assert_eq!(
        store_stdout,
        "success\nsuccess\n(error \"line 3 column 36: unknown constant f ((Array Int Bool) Bool) \")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(store_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject the store undefined function but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            store_stderr, z3_stderr,
            "ay store undefined-function stderr should match installed z3"
        );
        assert_eq!(
            store_stdout, z3_stdout,
            "ay store undefined-function stdout should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_rlimit_after_simple_sat_matches_installed_z3() {
    let script = "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(get-info :rlimit)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "simple SAT rlimit transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "simple SAT rlimit transcript should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "sat\n(:rlimit 34)\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept the rlimit comparison script; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(stdout, z3_stdout, "ay transcript should match installed z3");
        assert_eq!(stderr, z3_stderr, "ay stderr should match installed z3");
    }
}

#[test]
#[timeout(30_000)]
fn smt_assertion_stack_levels_track_visible_scopes_like_z3() {
    let script = "(set-option :print-success true)
(get-info :assertion-stack-levels)
(push 2)
(get-info :assertion-stack-levels)
(pop)
(get-info :assertion-stack-levels)
(reset)
(get-info :assertion-stack-levels)
(push)
(reset-assertions)
(get-info :assertion-stack-levels)
(pop)
(get-info :assertion-stack-levels)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "assertion-stack-levels transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "assertion-stack-levels transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\n(:assertion-stack-levels 0)\nsuccess\n(:assertion-stack-levels 2)\nsuccess\n(:assertion-stack-levels 1)\nsuccess\n(:assertion-stack-levels 0)\nsuccess\nsuccess\n(:assertion-stack-levels 1)\nsuccess\n(:assertion-stack-levels 0)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept assertion-stack-levels transcript; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay assertion-stack-levels transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay assertion-stack-levels stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_low_risk_option_queries_use_documented_ay_transcript() {
    let output = run_stdin(
        "(get-option :timeout)
(get-option :print-success)
(set-option :print-success true)
(get-option :print-success)
(set-option :timeout 17)
(get-option :timeout)
(exit)
",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "low-risk get-option queries should not be CLI failures; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "low-risk get-option query output should not leak to stderr: {stderr}"
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines,
        vec![
            "4294967295",
            "false",
            "success",
            "true",
            "success",
            "17",
            "success",
        ],
        "unexpected get-option transcript: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn smt_proof_and_assignment_option_queries_use_z3_bare_values() {
    let script = "(get-option :produce-proofs)
(set-option :produce-proofs true)
(get-option :produce-proofs)
(get-option :produce-assignments)
(set-option :produce-assignments true)
(get-option :produce-assignments)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "proof/assignment option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "proof/assignment option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "false\ntrue\nfalse\ntrue\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept proof/assignment option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay proof/assignment option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay proof/assignment option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_unsat_assumptions_option_query_uses_z3_bare_values() {
    let script = "(get-option :produce-unsat-assumptions)
(set-option :produce-unsat-assumptions true)
(get-option :produce-unsat-assumptions)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unsat-assumptions option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "unsat-assumptions option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "false\ntrue\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept unsat-assumptions option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay unsat-assumptions option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay unsat-assumptions option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_global_decls_option_query_uses_z3_bare_values() {
    let script = "(get-option :global-declarations)
(get-option :global-decls)
(set-option :global-decls true)
(get-option :global-declarations)
(get-option :global-decls)
(set-option :global-declarations false)
(get-option :global-declarations)
(get-option :global-decls)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "global-decls option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "global-decls option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "false\nfalse\ntrue\ntrue\nfalse\nfalse\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept global-decls option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay global-decls option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay global-decls option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_global_decls_alias_reaches_frontend_scope_semantics() {
    let script = "(set-option :global-decls true)
(push 1)
(declare-const x Int)
(pop 1)
(assert (= x 0))
(check-sat)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "global-decls alias should reach frontend scoping semantics; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "global-decls alias scoping script should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "sat\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept global-decls scoping script; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay global-decls scoping stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay global-decls scoping stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_auto_config_option_query_uses_z3_bare_values() {
    let script = "(get-option :auto-config)
(set-option :auto-config false)
(get-option :auto-config)
(set-option :auto-config true)
(get-option :auto-config)
(set-option :print-success true)
(set-option :auto-config false)
(get-option :auto-config)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "auto-config option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "auto-config option queries should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "true\nfalse\ntrue\nsuccess\nsuccess\nfalse\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept auto-config option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay auto-config option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay auto-config option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_pp_decimal_option_query_uses_z3_bare_values() {
    let script = "(get-option :pp.decimal)
(set-option :pp.decimal false)
(get-option :pp.decimal)
(set-option :pp.decimal true)
(get-option :pp.decimal)
(set-option :print-success true)
(set-option :pp.decimal false)
(get-option :pp.decimal)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "pp.decimal option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "pp.decimal option queries should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "false\nfalse\ntrue\nsuccess\nsuccess\nfalse\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept pp.decimal option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay pp.decimal option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay pp.decimal option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_pp_decimal_precision_option_query_uses_z3_bare_values() {
    let script = "(get-option :pp.decimal-precision)
(set-option :pp.decimal-precision 4)
(get-option :pp.decimal-precision)
(set-option :pp.decimal-precision 10)
(get-option :pp.decimal-precision)
(set-option :print-success true)
(set-option :pp.decimal-precision 7)
(get-option :pp.decimal-precision)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "pp.decimal-precision option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "pp.decimal-precision option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "10\n4\n10\nsuccess\nsuccess\n7\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept pp.decimal-precision option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay pp.decimal-precision option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay pp.decimal-precision option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_pp_max_depth_option_query_uses_z3_bare_values() {
    let script = "(get-option :pp.max-depth)
(set-option :pp.max-depth 3)
(get-option :pp.max-depth)
(set-option :print-success true)
(set-option :pp.max-depth 7)
(get-option :pp.max-depth)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "pp.max-depth option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "pp.max-depth option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "5\n3\nsuccess\nsuccess\n7\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept pp.max-depth option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay pp.max-depth option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay pp.max-depth option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_pp_max_ribbon_option_query_uses_z3_bare_values() {
    let script = "(get-option :pp.max-ribbon)
(set-option :pp.max-ribbon 40)
(get-option :pp.max-ribbon)
(set-option :print-success true)
(set-option :pp.max-ribbon 12)
(get-option :pp.max-ribbon)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "pp.max-ribbon option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "pp.max-ribbon option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "80\n40\nsuccess\nsuccess\n12\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept pp.max-ribbon option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay pp.max-ribbon option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay pp.max-ribbon option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_model_and_extra_pp_option_queries_use_z3_bare_values() {
    let script = "(get-option :model.v2)
(set-option :model.v2 true)
(get-option :model.v2)
(get-option :model.compact)
(set-option :model.compact false)
(get-option :model.compact)
(get-option :model.partial)
(set-option :model.partial true)
(get-option :model.partial)
(get-option :model.completion)
(set-option :model.completion true)
(get-option :model.completion)
(get-option :pp.single-line)
(set-option :pp.single-line true)
(get-option :pp.single-line)
(get-option :pp.bv-literals)
(set-option :pp.bv-literals false)
(get-option :pp.bv-literals)
(set-option :print-success true)
(set-option :model.v2 false)
(set-option :model.compact true)
(set-option :model.partial false)
(set-option :model.completion false)
(set-option :pp.single-line false)
(set-option :pp.bv-literals true)
(get-option :model.v2)
(get-option :model.compact)
(get-option :model.partial)
(get-option :model.completion)
(get-option :pp.single-line)
(get-option :pp.bv-literals)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "model/extra pp option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "model/extra pp option queries should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "false\ntrue\ntrue\nfalse\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\ntrue\nfalse\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nfalse\ntrue\nfalse\nfalse\nfalse\ntrue\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept model/extra pp option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay model/extra pp option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay model/extra pp option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_random_seed_option_query_uses_z3_bare_values() {
    let script = "(get-option :random-seed)
(set-option :random-seed 7)
(get-option :random-seed)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "random-seed option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "random-seed option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "0\n7\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept random-seed option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay random-seed option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay random-seed option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_output_channel_options_follow_z3_transcript() {
    let cases = [
        (
            "default channel queries",
            "(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(exit)
",
            "stdout\nstderr\n",
            "",
        ),
        (
            "print-success channel settings",
            "(set-option :print-success true)
(set-option :regular-output-channel \"stdout\")
(set-option :diagnostic-output-channel \"stderr\")
(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(exit)
",
            "success\nsuccess\nsuccess\nstdout\nstderr\nsuccess\n",
            "",
        ),
        (
            "regular output routed to stderr",
            "(set-option :regular-output-channel \"stderr\")
(get-option :regular-output-channel)
(exit)
",
            "",
            "stderr\n",
        ),
        (
            "diagnostic output routed to stdout",
            "(set-option :diagnostic-output-channel \"stdout\")
(get-option :diagnostic-output-channel)
(get-option :ay-no-such-option)
(exit)
",
            "stdout\nunsupported\n; :ay-no-such-option line: 3 position: 0\n",
            "",
        ),
    ];

    for (label, script, expected_stdout, expected_stderr) in cases {
        let output = run_stdin(script);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "{label} should succeed; stdout={stdout}, stderr={stderr}"
        );
        assert_eq!(
            stdout, expected_stdout,
            "unexpected stdout for {label}: {stdout}"
        );
        assert_eq!(
            stderr, expected_stderr,
            "unexpected stderr for {label}: {stderr}"
        );

        if let Some(z3) = run_installed_z3(script) {
            let z3_stdout = String::from_utf8_lossy(&z3.stdout);
            let z3_stderr = String::from_utf8_lossy(&z3.stderr);
            assert!(
                z3.status.success(),
                "installed z3 should accept {label}; stdout={z3_stdout}, stderr={z3_stderr}"
            );
            assert_eq!(stdout, z3_stdout, "ay stdout should match z3 for {label}");
            assert_eq!(stderr, z3_stderr, "ay stderr should match z3 for {label}");
        }
    }
}

#[test]
#[timeout(30_000)]
fn smt_verbosity_option_query_uses_z3_bare_values() {
    let script = "(get-option :verbosity)
(set-option :verbosity 2)
(get-option :verbosity)
(set-option :print-success true)
(set-option :verbosity 0)
(get-option :verbosity)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "verbosity option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "verbosity option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "0\n2\nsuccess\nsuccess\n0\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept verbosity option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay verbosity option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay verbosity option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_rlimit_option_query_uses_z3_bare_values() {
    let script = "(get-option :rlimit)
(set-option :rlimit 7)
(get-option :rlimit)
(set-option :rlimit 0)
(get-option :rlimit)
(set-option :print-success true)
(set-option :rlimit 5)
(get-option :rlimit)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "rlimit option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "rlimit option queries should not emit stderr: {stderr}"
    );
    assert_eq!(stdout, "0\n7\n0\nsuccess\nsuccess\n5\nsuccess\n");

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept rlimit option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay rlimit option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay rlimit option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_legacy_boolean_option_queries_use_z3_bare_values() {
    let script = "(get-option :model_validate)
(set-option :model_validate true)
(get-option :model_validate)
(get-option :unsat_core)
(set-option :unsat_core true)
(get-option :unsat_core)
(get-option :type-check)
(set-option :type-check false)
(get-option :type-check)
(get-option :well-sorted-check)
(set-option :well-sorted-check true)
(get-option :well-sorted-check)
(get-option :debug-ref-count)
(set-option :debug-ref-count true)
(get-option :debug-ref-count)
(get-option :trace)
(set-option :trace true)
(get-option :trace)
(get-option :dump-models)
(set-option :dump-models true)
(get-option :dump-models)
(get-option :stats)
(set-option :stats true)
(get-option :stats)
(get-option :ctrl-c)
(set-option :ctrl-c false)
(get-option :ctrl-c)
(set-option :print-success true)
(set-option :model_validate false)
(set-option :unsat_core false)
(set-option :type-check true)
(set-option :well-sorted-check false)
(set-option :debug-ref-count false)
(set-option :trace false)
(set-option :dump-models false)
(set-option :stats false)
(set-option :ctrl-c true)
(get-option :model_validate)
(get-option :unsat_core)
(get-option :type-check)
(get-option :well-sorted-check)
(get-option :debug-ref-count)
(get-option :trace)
(get-option :dump-models)
(get-option :stats)
(get-option :ctrl-c)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "legacy boolean option queries should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "legacy boolean option queries should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "false\ntrue\nfalse\ntrue\ntrue\nfalse\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\ntrue\nfalse\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nsuccess\nfalse\nfalse\ntrue\nfalse\nfalse\nfalse\nfalse\nfalse\ntrue\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept legacy boolean option queries; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay legacy boolean option transcript should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay legacy boolean option stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_assertions_requires_interactive_mode_like_z3() {
    let disabled_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(get-option :interactive-mode)
(get-assertions)
(get-info :status)
(exit)
";

    let disabled_output = run_stdin(disabled_script);
    let disabled_stdout = String::from_utf8_lossy(&disabled_output.stdout);
    let disabled_stderr = String::from_utf8_lossy(&disabled_output.stderr);
    assert_eq!(
        disabled_output.status.code(),
        Some(1),
        "disabled get-assertions should be recoverable but make the final CLI status nonzero; stdout={disabled_stdout}, stderr={disabled_stderr}"
    );
    assert!(
        disabled_stderr.is_empty(),
        "disabled get-assertions should not emit stderr: {disabled_stderr}"
    );
    assert_eq!(
        disabled_stdout,
        "success\nsuccess\nsuccess\nsuccess\nfalse\n(error \"line 6 column 15: command is only available in interactive mode, use command (set-option :interactive-mode true)\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(disabled_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject non-interactive get-assertions but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            disabled_stdout, z3_stdout,
            "ay disabled get-assertions stdout should match installed z3"
        );
        assert_eq!(
            disabled_stderr, z3_stderr,
            "ay disabled get-assertions stderr should match installed z3"
        );
    }

    let enabled_script = "(set-option :print-success true)
(set-option :interactive-mode true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(get-option :interactive-mode)
(get-assertions)
(exit)
";

    let enabled_output = run_stdin(enabled_script);
    let enabled_stdout = String::from_utf8_lossy(&enabled_output.stdout);
    let enabled_stderr = String::from_utf8_lossy(&enabled_output.stderr);
    assert!(
        enabled_output.status.success(),
        "interactive get-assertions should succeed; stdout={enabled_stdout}, stderr={enabled_stderr}"
    );
    assert!(
        enabled_stderr.is_empty(),
        "interactive get-assertions should not emit stderr: {enabled_stderr}"
    );
    assert_eq!(
        enabled_stdout,
        "success\nsuccess\nsuccess\nsuccess\nsuccess\ntrue\n((= x 1))\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(enabled_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept interactive get-assertions; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            enabled_stdout, z3_stdout,
            "ay interactive get-assertions stdout should match installed z3"
        );
        assert_eq!(
            enabled_stderr, z3_stderr,
            "ay interactive get-assertions stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_proof_requires_produce_proofs_like_z3() {
    let script = "(set-option :print-success true)
(set-logic QF_LIA)
(assert false)
(check-sat)
(get-proof)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "disabled get-proof should be recoverable but make the final CLI status nonzero; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "disabled get-proof should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nunsat\n(error \"line 5 column 10: proof construction is not enabled, use command (set-option :produce-proofs true)\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject disabled get-proof but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay disabled get-proof stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay disabled get-proof stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_unsat_assumptions_requires_option_like_z3() {
    let script = "(set-option :print-success true)
(set-logic QF_UF)
(declare-const p Bool)
(assert false)
(check-sat)
(get-unsat-assumptions)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "disabled get-unsat-assumptions should be recoverable but make the final CLI status nonzero; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "disabled get-unsat-assumptions should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\nunsat\n(error \"line 6 column 22: unsat assumptions construction is not enabled, use command (set-option :produce-unsat-assumptions true)\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject disabled get-unsat-assumptions but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay disabled get-unsat-assumptions stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay disabled get-unsat-assumptions stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_enabled_get_unsat_assumptions_matches_z3_empty_and_unavailable_cases() {
    let unsat_script = "(set-option :print-success true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(assert false)
(check-sat)
(get-unsat-assumptions)
(get-info :status)
(exit)
";

    let unsat_output = run_stdin(unsat_script);
    let unsat_stdout = String::from_utf8_lossy(&unsat_output.stdout);
    let unsat_stderr = String::from_utf8_lossy(&unsat_output.stderr);
    assert!(
        unsat_output.status.success(),
        "enabled get-unsat-assumptions after plain UNSAT should succeed; stdout={unsat_stdout}, stderr={unsat_stderr}"
    );
    assert!(
        unsat_stderr.is_empty(),
        "enabled get-unsat-assumptions after plain UNSAT should not emit stderr: {unsat_stderr}"
    );
    assert_eq!(
        unsat_stdout,
        "success\nsuccess\nsuccess\nsuccess\nunsat\n()\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(unsat_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should return an empty unsat-assumptions list; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            unsat_stdout, z3_stdout,
            "ay enabled get-unsat-assumptions stdout should match installed z3 for plain UNSAT"
        );
        assert_eq!(
            unsat_stderr, z3_stderr,
            "ay enabled get-unsat-assumptions stderr should match installed z3 for plain UNSAT"
        );
    }

    let sat_script = "(set-option :print-success true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-const p Bool)
(check-sat)
(get-unsat-assumptions)
(get-info :status)
(exit)
";

    let sat_output = run_stdin(sat_script);
    let sat_stdout = String::from_utf8_lossy(&sat_output.stdout);
    let sat_stderr = String::from_utf8_lossy(&sat_output.stderr);
    assert_eq!(
        sat_output.status.code(),
        Some(1),
        "enabled get-unsat-assumptions after SAT should be recoverable but make the final CLI status nonzero; stdout={sat_stdout}, stderr={sat_stderr}"
    );
    assert!(
        sat_stderr.is_empty(),
        "enabled get-unsat-assumptions after SAT should not emit stderr: {sat_stderr}"
    );
    assert_eq!(
        sat_stdout,
        "success\nsuccess\nsuccess\nsuccess\nsat\n(error \"line 6 column 22: unsat assumptions is not available\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(sat_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject unavailable unsat assumptions after SAT; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            sat_stdout, z3_stdout,
            "ay enabled get-unsat-assumptions stdout should match installed z3 after SAT"
        );
        assert_eq!(
            sat_stderr, z3_stderr,
            "ay enabled get-unsat-assumptions stderr should match installed z3 after SAT"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_get_assignment_uses_z3_default_collection_contract() {
    let script = "(set-option :print-success true)
(set-logic QF_UF)
(declare-const p Bool)
(assert (! p :named a))
(check-sat)
(get-option :produce-assignments)
(get-assignment)
(get-option :produce-assignments)
(get-info :status)
(exit)
";

    let output = run_stdin(script);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "default get-assignment transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "default get-assignment transcript should not emit stderr: {stderr}"
    );
    assert_eq!(
        stdout,
        "success\nsuccess\nsuccess\nsuccess\nsat\nfalse\n((a true))\nfalse\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should accept default get-assignment; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            stdout, z3_stdout,
            "ay default get-assignment stdout should match installed z3"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay default get-assignment stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_print_success_emits_z3_style_acknowledgements() {
    let output = run_stdin(
        "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "print-success transcript should succeed; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.is_empty(),
        "supported print-success commands should not emit stderr: {stderr}"
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines,
        vec!["success", "success", "success", "success", "sat", "success"],
        "unexpected print-success transcript: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn smt_unknown_info_and_option_queries_are_z3_style_unsupported() {
    let output = run_stdin(
        "(get-info :ay-no-such-info)
(get-info :authors)
(get-option :ay-no-such-option)
(get-option :print-success)
(exit)
",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unknown query commands should remain SMT-LIB responses; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.contains(":ay-no-such-info") && stderr.contains(":ay-no-such-option"),
        "unknown query commands should emit Z3-style stderr comments: {stderr}"
    );
    assert_eq!(
        stderr,
        "; :ay-no-such-info line: 1 position: 1\n; :ay-no-such-option line: 3 position: 0\n"
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines,
        vec![
            "unsupported",
            "; Suppported get-info parameters:",
            "; (get-info :reason-unknown)",
            "; (get-info :status)",
            "; (get-info :version)",
            "; (get-info :authors)",
            "; (get-info :error-behavior)",
            "; (get-info :parameters)",
            "; (get-info :rlimit)",
            "; (get-info :assertion-stack-levels)",
            "(:authors \"Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger\")",
            "unsupported",
            "false",
        ],
        "unexpected unknown-query transcript: {stdout}"
    );

    if let Some(z3) = run_installed_z3(
        "(get-info :ay-no-such-info)
(get-info :authors)
(get-option :ay-no-such-option)
(get-option :print-success)
(exit)
",
    ) {
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert!(
            z3.status.success(),
            "installed z3 should keep unsupported queries recoverable; stderr={z3_stderr}"
        );
        assert_eq!(
            stderr, z3_stderr,
            "ay unsupported-query stderr should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn smt_model_and_unsat_core_contracts_are_stdout_only() {
    let model_output = run_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 7))
(check-sat)
(get-model)
(exit)
",
    );
    let model_stdout = String::from_utf8_lossy(&model_output.stdout);
    let model_stderr = String::from_utf8_lossy(&model_output.stderr);
    assert!(
        model_output.status.success(),
        "get-model script should succeed; stdout={model_stdout}, stderr={model_stderr}"
    );
    assert!(
        model_stderr.is_empty(),
        "get-model output should stay on stdout without stderr noise: {model_stderr}"
    );
    assert!(
        model_stdout.lines().any(|line| line == "sat"),
        "expected sat before model: {model_stdout}"
    );
    assert!(
        model_stdout.contains("(model") && model_stdout.contains("define-fun x () Int 7"),
        "expected concrete model for x on stdout: {model_stdout}"
    );

    let core_output = run_stdin(
        "(set-option :produce-unsat-cores true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 10) :named a1))
(assert (! (< x 5) :named a2))
(check-sat)
(get-unsat-core)
(exit)
",
    );
    let core_stdout = String::from_utf8_lossy(&core_output.stdout);
    let core_stderr = String::from_utf8_lossy(&core_output.stderr);
    assert!(
        core_output.status.success(),
        "get-unsat-core script should succeed; stdout={core_stdout}, stderr={core_stderr}"
    );
    assert!(
        core_stderr.is_empty(),
        "get-unsat-core output should stay on stdout without stderr noise: {core_stderr}"
    );
    assert!(
        core_stdout.lines().any(|line| line == "unsat"),
        "expected unsat before core: {core_stdout}"
    );
    assert!(
        core_stdout
            .lines()
            .any(|line| line == "(a1 a2)" || line == "(a2 a1)"),
        "expected named unsat core on stdout: {core_stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn disabled_model_and_unsat_core_errors_follow_z3_recoverable_contract() {
    let model_script = "(set-option :print-success true)
(set-option :produce-models false)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 7))
(check-sat)
(get-model)
(get-info :status)
(exit)
";
    let model_output = run_stdin(model_script);
    let model_stdout = String::from_utf8_lossy(&model_output.stdout);
    let model_stderr = String::from_utf8_lossy(&model_output.stderr);
    assert_eq!(
        model_output.status.code(),
        Some(1),
        "disabled get-model should make final CLI status non-zero; stdout={model_stdout}, stderr={model_stderr}"
    );
    assert!(
        model_stderr.is_empty(),
        "disabled get-model response should not use stderr: {model_stderr}"
    );
    assert_eq!(
        model_stdout,
        "success\nsuccess\nsuccess\nsuccess\nsuccess\nsat\n(error \"line 7 column 10: model is not available\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(model_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject disabled get-model but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            model_stderr, z3_stderr,
            "ay stderr should match installed z3"
        );
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            9,
            "installed z3 should emit success acknowledgements around the recoverable get-model error; stdout={z3_stdout}"
        );
        let model_lines: Vec<&str> = model_stdout.lines().collect();
        assert_eq!(&z3_lines[0..6], &model_lines[0..6]);
        assert!(
            z3_lines[6].contains("model is not available"),
            "installed z3 should identify unavailable model; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[7], "(:status unknown)");
        assert_eq!(z3_lines[8], "success");
    }

    let core_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 10) :named a1))
(assert (! (< x 5) :named a2))
(check-sat)
(get-unsat-core)
(get-info :status)
(exit)
";
    let core_output = run_stdin(core_script);
    let core_stdout = String::from_utf8_lossy(&core_output.stdout);
    let core_stderr = String::from_utf8_lossy(&core_output.stderr);
    assert_eq!(
        core_output.status.code(),
        Some(1),
        "disabled get-unsat-core should make final CLI status non-zero; stdout={core_stdout}, stderr={core_stderr}"
    );
    assert!(
        core_stderr.is_empty(),
        "disabled get-unsat-core response should not use stderr: {core_stderr}"
    );
    assert_eq!(
        core_stdout,
        "success\nsuccess\nsuccess\nsuccess\nsuccess\nunsat\n(error \"line 7 column 15: unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(core_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject disabled get-unsat-core but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            core_stderr, z3_stderr,
            "ay stderr should match installed z3"
        );
        let z3_lines: Vec<&str> = z3_stdout.lines().collect();
        assert_eq!(
            z3_lines.len(),
            9,
            "installed z3 should emit success acknowledgements around the recoverable get-unsat-core error; stdout={z3_stdout}"
        );
        let core_lines: Vec<&str> = core_stdout.lines().collect();
        assert_eq!(&z3_lines[0..6], &core_lines[0..6]);
        assert!(
            z3_lines[6].contains("unsat core construction is not enabled"),
            "installed z3 should identify disabled unsat-core construction; stdout={z3_stdout}"
        );
        assert_eq!(z3_lines[7], "(:status unknown)");
        assert_eq!(z3_lines[8], "success");
    }
}

#[test]
#[timeout(30_000)]
fn unavailable_get_value_model_errors_follow_z3_recoverable_contract() {
    let before_check_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(get-value (y))
(get-info :status)
(exit)
";
    let before_check_output = run_stdin(before_check_script);
    let before_check_stdout = String::from_utf8_lossy(&before_check_output.stdout);
    let before_check_stderr = String::from_utf8_lossy(&before_check_output.stderr);
    assert_eq!(
        before_check_output.status.code(),
        Some(1),
        "get-value before check-sat should make final CLI status non-zero; stdout={before_check_stdout}, stderr={before_check_stderr}"
    );
    assert!(
        before_check_stderr.is_empty(),
        "get-value before check-sat should not emit stderr: {before_check_stderr}"
    );
    assert_eq!(
        before_check_stdout,
        "success\nsuccess\nsuccess\n(error \"line 4 column 14: model is not available\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(before_check_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject get-value before check-sat but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            before_check_stderr, z3_stderr,
            "ay get-value-before-check stderr should match installed z3"
        );
        assert_eq!(
            before_check_stdout, z3_stdout,
            "ay get-value-before-check stdout should match installed z3"
        );
    }

    let after_unsat_script = "(set-option :print-success true)
(set-logic QF_LIA)
(declare-const y Int)
(assert false)
(check-sat)
(get-value (y))
(get-info :status)
(exit)
";
    let after_unsat_output = run_stdin(after_unsat_script);
    let after_unsat_stdout = String::from_utf8_lossy(&after_unsat_output.stdout);
    let after_unsat_stderr = String::from_utf8_lossy(&after_unsat_output.stderr);
    assert_eq!(
        after_unsat_output.status.code(),
        Some(1),
        "get-value after unsat should make final CLI status non-zero; stdout={after_unsat_stdout}, stderr={after_unsat_stderr}"
    );
    assert!(
        after_unsat_stderr.is_empty(),
        "get-value after unsat should not emit stderr: {after_unsat_stderr}"
    );
    assert_eq!(
        after_unsat_stdout,
        "success\nsuccess\nsuccess\nsuccess\nunsat\n(error \"line 6 column 14: model is not available\")\n(:status unknown)\nsuccess\n"
    );

    if let Some(z3) = run_installed_z3(after_unsat_script) {
        let z3_stdout = String::from_utf8_lossy(&z3.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3.stderr);
        assert_eq!(
            z3.status.code(),
            Some(1),
            "installed z3 should reject get-value after unsat but continue; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert_eq!(
            after_unsat_stderr, z3_stderr,
            "ay get-value-after-unsat stderr should match installed z3"
        );
        assert_eq!(
            after_unsat_stdout, z3_stdout,
            "ay get-value-after-unsat stdout should match installed z3"
        );
    }
}

#[test]
#[timeout(30_000)]
fn stats_alias_prints_existing_stats_output() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-st")
        .arg(&input)
        .output()
        .expect("spawn ay -st");

    assert!(
        output.status.success(),
        "-st should solve and print stats: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(
        stderr.contains("ay.mode:"),
        "expected canonical stats output: {stderr}"
    );
    assert!(
        stderr.contains(":num-assertions"),
        "expected SMT-LIB stats output: {stderr}"
    );
    for key in [":time", ":memory", ":max-memory", ":rlimit-count"] {
        assert!(
            stderr.contains(key),
            "expected Z3-style resource stats key {key} in -st output: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn model_alias_prints_existing_smt_model_output() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("-model")
        .arg(&input)
        .output()
        .expect("spawn ay -model");

    assert!(
        output.status.success(),
        "-model should solve and print a model: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(stdout.contains("(model"), "expected model output: {stdout}");
    assert!(
        stdout.contains("define-fun x () Int"),
        "expected x binding in model: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn z3_model_flag_ignores_comments_and_strings_when_injecting_model_request() {
    for prefix in [
        "; (get-model)\n",
        "; (exit)\n",
        "(set-info :source \"(get-model)\")\n",
        "(set-info :source \"(exit)\")\n",
    ] {
        let input = format!(
            "(set-logic QF_LIA)\n{prefix}(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n"
        );
        let output = run_ay_stdin_with_args(&["--z3-mode", "-model"], &input, true);

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "--z3-mode -model should ignore inert command text in {prefix:?}; stdout={stdout}, stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|line| line == "sat"),
            "expected sat before model for {prefix:?}, got: {stdout}"
        );
        // --z3-mode emits the bare `( <define-fun>* )` model form (d0201aa2),
        // not the legacy `(model …)` head.
        assert!(
            stdout.contains("(\n  (define-fun") && stdout.contains("define-fun x () Int"),
            "expected model for {prefix:?}, got: {stdout}"
        );
        assert!(
            stderr.is_empty(),
            "--z3-mode -model should keep stderr clean for {prefix:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn z3_model_flag_ignores_nested_symbols_named_like_commands() {
    for function_name in ["get-model", "exit"] {
        let input = format!(
            "(set-logic ALL)\n\
             (declare-fun {function_name} (Int) Int)\n\
             (declare-const x Int)\n\
             (assert (= ({function_name} 1) 7))\n\
             (assert (= x 3))\n\
             (check-sat)\n"
        );
        let output = run_ay_stdin_with_args(&["--z3-mode", "-model"], &input, true);

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "--z3-mode -model should ignore nested {function_name:?} applications; stdout={stdout}, stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|line| line == "sat"),
            "expected sat before model for nested {function_name:?}, got: {stdout}"
        );
        // --z3-mode emits the bare `( <define-fun>* )` model form (d0201aa2),
        // not the legacy `(model …)` head.
        assert!(
            stdout.contains("(\n  (define-fun") && stdout.contains("define-fun x () Int"),
            "expected model for nested {function_name:?}, got: {stdout}"
        );
        assert!(
            stderr.is_empty(),
            "--z3-mode -model should keep stderr clean for nested {function_name:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn dump_models_param_prints_existing_smt_model_output() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("dump_models=true")
        .arg(&input)
        .output()
        .expect("spawn ay dump_models=true");

    assert!(
        output.status.success(),
        "dump_models=true should solve and print a model: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(stdout.contains("(model"), "expected model output: {stdout}");
    assert!(
        stdout.contains("define-fun x () Int"),
        "expected x binding in model: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn hyphen_and_dotted_key_value_aliases_match_installed_z3_acceptance() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let alias_args = [
        "type-check=true",
        "well-sorted-check=true",
        "debug-ref-count=false",
        "dump-models=true",
        "model.v2=true",
        "model.compact=true",
        "pp.single-line=true",
        "pp.bv-literals=true",
        "pp.fixed-indent=true",
    ];

    let output = Command::new(ay_binary())
        .args(alias_args)
        .arg(&input)
        .output()
        .expect("spawn ay with hyphen/dotted Z3 key=value aliases");

    assert!(
        output.status.success(),
        "hyphen/dotted Z3 key=value aliases should be accepted: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(
        stdout.contains("(model"),
        "dump-models=true should print a model: {stdout}"
    );

    let z3 = "/opt/homebrew/bin/z3";
    if Path::new(z3).is_file() {
        let z3_output = Command::new(z3)
            .args(alias_args)
            .arg(&input)
            .output()
            .expect("spawn installed z3 with hyphen/dotted key=value aliases");
        let z3_stdout = String::from_utf8_lossy(&z3_output.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3_output.stderr);
        assert!(
            z3_output.status.success(),
            "installed z3 should accept the alias slice; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert!(
            z3_stdout.lines().any(|line| line == "sat"),
            "installed z3 should solve after alias params: {z3_stdout}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn allowlisted_fp_engine_param_is_accepted() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("fp.engine=spacer")
        .arg(&input)
        .output()
        .expect("spawn ay fp.engine=spacer");

    assert!(
        output.status.success(),
        "allowlisted fp.engine=spacer should be accepted: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn common_z3_key_value_params_are_accepted_or_translated() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("timeout=0")
        .arg("memory_max_size=0")
        .arg("stats=true")
        .arg("auto_config=false")
        .arg("ctrl_c=false")
        .arg("model_validate=true")
        .arg("proof=true")
        .arg("unsat_core=true")
        .arg("smt.random_seed=7")
        .arg(&input)
        .output()
        .expect("spawn ay with common Z3 key=value params");

    assert!(
        output.status.success(),
        "common Z3 params should be accepted: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(
        stderr.contains("ay.mode:"),
        "stats=true should enable canonical stats output: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn representative_z3_key_value_noop_params_are_accepted() {
    let args = [
        "model=true",
        "smtlib2_compliant=true",
        "warning=false",
        "verbose=2",
        "random_seed=11",
        "rlimit=97",
        "model.partial=true",
        "model.completion=true",
        "pp.decimal=true",
        "pp.decimal_precision=12",
        "pp.max-depth=7",
        "pp.max-ribbon=80",
        "sat.random_seed=13",
        "nlsat.seed=17",
        "type_check=true",
        "well_sorted_check=false",
        "stats=false",
        "dump_models=false",
    ];
    let output = run_ay_stdin_with_args(&args, trivial_sat_smt(), true);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "representative Z3 key=value params should be accepted; stdout={stdout}, stderr={stderr}"
    );
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(
        !stdout.contains("(model"),
        "dump_models=false and model=true no-op should not print a model: {stdout}"
    );
    assert!(
        !stderr.contains("ay.mode:") && !stderr.contains("(:statistics"),
        "stats=false should not enable statistics output: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn trace_key_value_params_are_accepted_as_noops() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let (trace_path, _trace_cleanup) = temp_path("log");
    let output = Command::new(ay_binary())
        .arg("trace=true")
        .arg("trace=false")
        .arg(format!("trace_file_name={}", trace_path.display()))
        .arg(&input)
        .output()
        .expect("spawn ay trace=true trace=false trace_file_name=PATH");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "trace key-value params should be accepted as Z3 compatibility no-ops; stdout={stdout}, stderr={stderr}"
    );
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");
    assert!(
        !trace_path.exists(),
        "ay should accept Z3 trace params without emitting a Z3 trace file at {}",
        trace_path.display()
    );

    let z3 = "/opt/homebrew/bin/z3";
    if Path::new(z3).is_file() {
        let (z3_trace_path, _z3_trace_cleanup) = temp_path("log");
        let z3_output = Command::new(z3)
            .arg("trace=true")
            .arg(format!("trace_file_name={}", z3_trace_path.display()))
            .arg(&input)
            .output()
            .expect("spawn installed z3 trace=true trace_file_name=PATH");
        let z3_stdout = String::from_utf8_lossy(&z3_output.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3_output.stderr);
        assert!(
            z3_output.status.success(),
            "installed z3 should accept trace params; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert!(
            z3_stdout.lines().any(|line| line == "sat"),
            "installed z3 should solve the input after trace params: {z3_stdout}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn ctrl_c_hyphen_key_value_param_matches_installed_z3_acceptance() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("ctrl-c=false")
        .arg(&input)
        .output()
        .expect("spawn ay ctrl-c=false");

    assert!(
        output.status.success(),
        "ctrl-c=false should be accepted as a Z3 compatibility no-op: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "sat"), "got: {stdout}");

    let z3 = "/opt/homebrew/bin/z3";
    if Path::new(z3).is_file() {
        let z3_output = Command::new(z3)
            .arg("ctrl-c=false")
            .arg(&input)
            .output()
            .expect("spawn installed z3 ctrl-c=false");
        let z3_stdout = String::from_utf8_lossy(&z3_output.stdout);
        let z3_stderr = String::from_utf8_lossy(&z3_output.stderr);
        assert!(
            z3_output.status.success(),
            "installed z3 should accept ctrl-c=false; stdout={z3_stdout}, stderr={z3_stderr}"
        );
        assert!(
            z3_stdout.lines().any(|line| line == "sat"),
            "installed z3 should solve the input after ctrl-c=false: {z3_stdout}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn unsupported_key_value_param_is_rejected() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("smt.this_parameter_does_not_exist=7")
        .arg(&input)
        .output()
        .expect("spawn ay unsupported key=value");

    assert!(
        !output.status.success(),
        "unsupported key=value param should fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unsupported Z3 parameter 'smt.this_parameter_does_not_exist=7'"),
        "expected explicit unsupported-param error, got: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn real_z3_tuning_params_are_accepted_and_solve() {
    // Real libz3 module parameters AY does not implement must be ACCEPTED so the
    // run proceeds (z3 solves), not rejected with a fatal error and no verdict.
    // Why3/Dafny/Boogie pass these on every invocation, so rejecting them broke
    // drop-in use. See `crates/ay/src/z3_params.rs`.
    for param in [
        "smt.mbqi=false",
        "smt.arith.solver=2",
        "pp.bv_literals=false", // underscore spelling; z3 normalizes - and _
        "sat.threads=4",
        "smt.relevancy=0",
        "smt.qi.eager_threshold=100",
    ] {
        let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
        let output = Command::new(ay_binary())
            .arg(param)
            .arg(&input)
            .output()
            .unwrap_or_else(|e| panic!("spawn ay {param}: {e}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "ay must accept real z3 param {param} and solve; stdout={stdout}, stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|l| l == "sat"),
            "ay must emit a verdict for {param}, got stdout={stdout}"
        );
        // The dropped knob is announced, never silent.
        assert!(
            stderr.contains("accepted but NOT honored"),
            "ay must announce the ignored knob {param} on stderr, got {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn dash_in_streams_verdict_before_stdin_closes() {
    // z3's `-in` answers each `(check-sat)` as it arrives, WITHOUT waiting for
    // EOF, so a coprocess driver (Why3/Dafny/Boogie/IDE) that keeps stdin open
    // and reads the reply before sending the next command works. AY used to read
    // stdin to EOF first, so those drivers deadlocked. This test holds stdin OPEN
    // and requires the first verdict to arrive anyway.
    let mut child = Command::new(ay_binary())
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ay -in");

    let mut stdin = child.stdin.take().expect("child stdin");
    let mut stdout = child.stdout.take().expect("child stdout");

    // Drive two rounds on the SAME still-open stream, on a worker thread, so the
    // test times out rather than hanging if streaming regresses. Reading the
    // first verdict BEFORE writing the second is exactly the coprocess pattern:
    // if `-in` waited for EOF, the first read would block forever here.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let read_line = |stdout: &mut std::process::ChildStdout| -> String {
            let mut got = Vec::new();
            let mut buf = [0u8; 64];
            while !got.contains(&b'\n') {
                match stdout.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => got.extend_from_slice(&buf[..n]),
                    Err(_) => break,
                }
            }
            String::from_utf8_lossy(&got).trim().to_string()
        };
        let _ = stdin.write_all(
            b"(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        );
        let _ = stdin.flush();
        let first = read_line(&mut stdout);
        // Only after seeing the first reply do we send the next command.
        let _ = stdin.write_all(b"(assert (< x 0))\n(check-sat)\n");
        let _ = stdin.flush();
        let second = read_line(&mut stdout);
        let _ = tx.send((first, second));
        // Closing stdin lets the child exit.
        drop(stdin);
    });

    let (first, second) = rx
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("ay -in must stream verdicts on an open stream (it deadlocked on read-to-EOF)");
    assert_eq!(first, "sat", "first streamed verdict wrong; got {first:?}");
    assert_eq!(
        second, "unsat",
        "second streamed verdict wrong; got {second:?}"
    );
    let _ = child.wait();
}

#[test]
#[timeout(30_000)]
fn ignored_z3_param_note_is_suppressed_under_z3_mode() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg("--z3-mode")
        .arg("smt.mbqi=false")
        .arg(&input)
        .output()
        .expect("spawn ay --z3-mode smt.mbqi=false");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "z3-mode run must succeed: {stderr}"
    );
    assert_eq!(
        stdout, "sat\n",
        "z3-mode stdout must be exactly the verdict"
    );
    assert!(
        stderr.is_empty(),
        "z3-mode must suppress the ignored-knob note for a clean transcript: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn bogus_param_in_real_module_still_rejected_like_z3() {
    // z3 rejects an unknown NAME in a known module (`smt.bogus_knob`) and an
    // unknown MODULE (`bogusmodule.x`). AY must too — accept-and-ignore is only
    // for real knobs, so a typo still fails loudly on both engines.
    for param in ["smt.bogus_knob=1", "bogusmodule.x=1"] {
        let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
        let output = Command::new(ay_binary())
            .arg(param)
            .arg(&input)
            .output()
            .unwrap_or_else(|e| panic!("spawn ay {param}: {e}"));
        assert!(
            !output.status.success(),
            "a name z3 itself rejects must stay a hard error on ay: {param}"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(&format!("unsupported Z3 parameter '{param}'")),
            "expected explicit rejection of {param}, got: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn help_with_file_path_routes_to_solve_help() {
    let (input, _cleanup) = write_temp(trivial_sat_smt(), "smt2");
    let output = Command::new(ay_binary())
        .arg(&input)
        .arg("-?")
        .output()
        .expect("spawn ay FILE -?");

    assert!(
        output.status.success(),
        "FILE -? should print solve help: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Usage: ay solve"),
        "expected solve help, got: {stdout}"
    );
    assert!(
        stdout.contains("Input file"),
        "expected solve args in help, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn piped_in_continues_after_parse_error() {
    // Regression (Phase 1 CLI drop-in): piped `-in` must recover per-command
    // like z3 (continued-execution), not abort the whole stream on the first
    // bad command. Previously the whole-buffer parse exited on `(foobar bad)`
    // and silently dropped the later `check-sat`/`get-value`.
    let script = "(set-logic QF_LIA)\n\
                  (declare-const x Int)\n\
                  (assert (> x 0))\n\
                  (foobar bad)\n\
                  (check-sat)\n\
                  (get-value (x))\n";
    for args in [&["--z3-mode"][..], &[][..]] {
        let output = run_ay_stdin_with_args(args, script, true);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let combined = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        assert!(
            combined.contains("error"),
            "expected an error for the bad command (args={args:?}): {combined}"
        );
        assert!(
            stdout.contains("sat"),
            "check-sat after a parse error must still run (args={args:?}): {stdout}"
        );
        assert!(
            stdout.contains("(x "),
            "get-value after a parse error must still run (args={args:?}): {stdout}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn unknown_set_logic_is_ignored_and_continues() {
    // Regression (Phase 1 CLI drop-in, P3-logics): a genuinely unrecognized
    // `(set-logic X)` — one z3's structural recognizer would also reject — is
    // IGNORED exactly as z3 does: stdout prints `unsupported`, a
    // `; ignoring unsupported logic <TOK> ...` diagnostic goes to stderr,
    // solving CONTINUES with ALL semantics, and the exit code is 0 (an ignored
    // logic does NOT taint the exit, unlike other recoverable errors). No
    // `(error ...)` line.
    let output = run_ay_stdin_with_args(
        &["--z3-mode"],
        "(set-logic NOPE)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        true,
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("unsupported") && stdout.contains("sat"),
        "unknown logic must print `unsupported` then solve: stdout={stdout} stderr={stderr}"
    );
    assert!(
        !stdout.contains("(error"),
        "an ignored logic must not emit an (error ...) line: {stdout}"
    );
    assert!(
        stderr.contains("; ignoring unsupported logic NOPE"),
        "ignored-logic diagnostic must name the token on stderr: {stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "an ignored logic must not taint the exit code (z3 exits 0)"
    );

    // A z3-RECOGNIZED-but-unmapped token (QF_UFLIRA) is silently accepted and
    // solves with the correct verdict, exit 0 — no `unsupported`, no error.
    let accepted = run_ay_stdin_with_args(
        &["--z3-mode"],
        "(set-logic QF_UFLIRA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        true,
    );
    let accepted_stdout = String::from_utf8_lossy(&accepted.stdout);
    assert!(
        accepted_stdout.contains("sat")
            && !accepted_stdout.contains("(error")
            && !accepted_stdout.contains("unsupported"),
        "a z3-recognized unmapped logic must be silently accepted: {accepted_stdout}"
    );
    assert_eq!(accepted.status.code(), Some(0));

    // A valid mapped logic is still accepted with no error.
    let ok = run_ay_stdin_with_args(
        &["--z3-mode"],
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        true,
    );
    let ok_stdout = String::from_utf8_lossy(&ok.stdout);
    assert!(
        ok_stdout.contains("sat") && !ok_stdout.contains("(error"),
        "valid logic must still be accepted without error: {ok_stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn z3_mode_get_info_version_is_consistent_z3_version() {
    // Regression (Phase 1 CLI drop-in): under explicit `--z3-mode` (full Z3
    // impersonation, documented to match the cached Z3 4.15.4 baseline), the
    // identity triple must be internally consistent — `:name "Z3"` pairs with a
    // real Z3 version, not AY's 0.11.0. Plain `-in` keeps AY provenance (see
    // smt_get_info_version_keeps_ay_provenance_with_z3_record_shape).
    let output = run_ay_stdin_with_args(&["--z3-mode"], "(get-info :version)\n", true);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout, "(:version \"4.15.4\")\n", "got: {stdout}");
}
