// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::io::{BufRead, Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_smt2(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_cli_error_fatal_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).unwrap();
    (path.clone(), CleanupGuard(path))
}

fn assert_recoverable_unknown_constant_transcript(stdout: &str, stderr: &str) {
    assert!(
        stdout.contains("(error \"line 2 column 12: unknown constant x\")"),
        "Expected Z3-style recoverable unknown-constant error on stdout, got: {stdout}"
    );
    assert!(
        stdout.contains("\nsat\n") || stdout.ends_with("\nsat"),
        "Expected transcript to continue through check-sat, got: {stdout}"
    );
    assert!(
        !stderr.contains("(error"),
        "Recoverable SMT-LIB errors should stay on stdout, got stderr: {stderr}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_undefined_get_value_is_recoverable_in_file_mode() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(get-value (x))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdout: {stdout:?}");
    eprintln!("AY stderr: {stderr:?}");
    eprintln!("AY exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    assert_recoverable_unknown_constant_transcript(&stdout, &stderr);
}

#[test]
#[timeout(60000)]
fn test_cli_undefined_get_value_is_recoverable_on_piped_stdin() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(get-value (x))
(check-sat)
"#;

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdin stdout: {stdout:?}");
    eprintln!("AY stdin stderr: {stderr:?}");
    eprintln!("AY stdin exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    assert_recoverable_unknown_constant_transcript(&stdout, &stderr);
}

#[test]
#[timeout(30000)]
fn test_cli_timeout_after_recoverable_error_reports_diagnostic() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("solve")
        .arg("--timeout")
        .arg("1000")
        .arg("--incremental")
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    let mut stdin = child.stdin.take().expect("child stdin");
    let stdout_pipe = child.stdout.take().expect("child stdout");
    let mut stdout_reader = std::io::BufReader::new(stdout_pipe);

    stdin
        .write_all(b"(set-logic QF_LIA)\n(assert x)\n")
        .expect("write recoverable-error prefix");
    stdin.flush().expect("flush recoverable-error prefix");

    let mut stdout = String::new();
    stdout_reader
        .read_line(&mut stdout)
        .expect("read recoverable error");
    assert!(
        stdout.contains("unknown constant x"),
        "Expected recoverable SMT-LIB error before timeout, got stdout prefix: {stdout:?}"
    );

    std::thread::sleep(Duration::from_millis(1100));
    stdin
        .write_all(b"(check-sat)\n")
        .expect("wake incremental reader after timeout");
    stdin.flush().expect("flush timeout wake command");
    drop(stdin);

    let status = child.wait().expect("wait on ay timeout child");
    stdout_reader
        .read_to_string(&mut stdout)
        .expect("read remaining stdout");

    let mut stderr = String::new();
    child
        .stderr
        .take()
        .expect("child stderr")
        .read_to_string(&mut stderr)
        .expect("read stderr");

    assert_eq!(
        status.code(),
        Some(124),
        "Expected timeout exit after recoverable error; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.contains("timeout occurred after 1 recoverable SMT-LIB error"),
        "Expected timeout diagnostic to mention prior recoverable SMT-LIB error; stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.contains("(:reason-unknown \"timeout\")"),
        "Expected standard timeout reason to remain present; stdout={stdout}, stderr={stderr}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_file_continues_after_unknown_command() {
    // Per-command error recovery (continued-execution) for FILE input: an
    // unknown command between two valid (check-sat) commands must print an
    // (error "...") and still run BOTH check-sats. Mirrors z3's behavior and
    // the advertised (:error-behavior continued-execution).
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "(declare-const x Int)(assert (> x 0))(check-sat)(bogus-command)(assert (< x 5))(check-sat)\n";

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdout: {stdout:?}");
    eprintln!("AY stderr: {stderr:?}");
    eprintln!("AY exit: {:?}", output.status);

    // The transcript on stdout is exactly: sat, (error ...), sat.
    let lines: Vec<&str> = stdout.lines().filter(|l| !l.trim().is_empty()).collect();
    assert_eq!(
        lines.len(),
        3,
        "Expected exactly sat / error / sat on stdout, got: {stdout:?}"
    );
    assert_eq!(lines[0], "sat", "first command must be sat: {stdout:?}");
    assert!(
        lines[1].starts_with("(error ") && lines[1].contains("bogus-command"),
        "second line must be the recoverable (error ...): {stdout:?}"
    );
    assert_eq!(lines[2], "sat", "third command must be sat: {stdout:?}");
    // Recoverable SMT-LIB errors stay on stdout.
    assert!(
        !stderr.contains("(error"),
        "recoverable errors must not duplicate on stderr: {stderr}"
    );
    // An error occurred, so the process exits non-zero.
    assert!(
        !output.status.success(),
        "Expected non-zero exit after a recoverable error, got {:?}",
        output.status
    );
}

#[test]
#[timeout(60000)]
fn test_cli_file_continues_after_malformed_sexp() {
    // A malformed (stray close paren) top-level form mid-file must not abort
    // the commands that precede or follow it.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "(declare-const x Int)(assert (> x 0))(check-sat))(assert (< x 5))(check-sat)\n";

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);

    eprintln!("AY stdout: {stdout:?}");
    eprintln!("AY exit: {:?}", output.status);

    let sat_count = stdout.lines().filter(|l| l.trim() == "sat").count();
    assert_eq!(
        sat_count, 2,
        "both check-sats must run despite the malformed form: {stdout:?}"
    );
    assert!(
        stdout.contains("(error "),
        "malformed form must yield an (error ...): {stdout:?}"
    );
    assert!(
        !output.status.success(),
        "Expected non-zero exit after a recoverable error, got {:?}",
        output.status
    );
}

#[test]
#[timeout(60000)]
fn test_cli_accepts_quantified_bv_logic() {
    // BV logic (quantified bitvectors) is routed to QF_BV solver since 8d790229a.
    // This formula is a tautology (bvadd commutativity), so sat is correct.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic BV)
(declare-fun x () (_ BitVec 8))
(assert (forall ((y (_ BitVec 8))) (= (bvadd x y) (bvadd y x))))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );
    let result = stdout.trim();
    assert!(
        result == "sat" || result == "unknown",
        "Expected sat or unknown for quantified BV tautology, got: {result}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_reports_bvadd_arity_error() {
    // A `bvadd` arity error is a problem-contributing elaboration failure (the
    // `assert` is dropped). It must FAIL CLOSED, not abort to an empty verdict:
    // the error is reported on STDOUT (z3-style `(error ...)`) and the pending
    // check-sat still emits a verdict — `unknown` — because a dropped constraint
    // can only turn UNSAT into SAT (#every-check-sat-emits-a-verdict). The
    // process still exits non-zero (a recoverable SMT-LIB error occurred). This
    // supersedes the earlier stderr-and-abort-to-empty-stdout behavior, aligning
    // arity errors with the undefined-symbol / sort-mismatch recoverable path.
    // (z3 itself accepts 1-arg bvadd as identity and answers `sat`; AY is
    // stricter but degrades gracefully to `unknown` rather than a wrong `sat`.)
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x) #x01))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    // The recoverable (error ...) is on STDOUT (not stderr), followed by a
    // check-sat verdict of `unknown`.
    assert!(
        stdout.contains("(error ") && stdout.contains("bvadd requires at least 2 arguments"),
        "Expected the bvadd arity (error ...) on stdout, got: {stdout}"
    );
    assert!(
        stdout.contains("\nunknown") || stdout.trim() == "unknown" || stdout.contains("unknown"),
        "Expected check-sat to fail closed to unknown, got: {stdout}"
    );
    assert!(
        !stderr.contains("(error"),
        "Recoverable SMT-LIB errors should stay on stdout, got stderr: {stderr}"
    );
}
