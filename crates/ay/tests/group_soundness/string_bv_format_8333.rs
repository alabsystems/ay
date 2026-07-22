// String+BV format-string routing regression (#8333).
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Format-string vulnerability queries combine string predicates over the
// candidate format with BV address constraints over the write target. Until a
// real combination layer exists, the solver must return unknown instead of
// routing to QF_BV and dropping string constraints.

use ntest::timeout;
use std::io::Write;
use std::process::Command;

const FORMAT_STRING_BV_REPRO: &str = r#"(set-logic ALL)
(declare-const fmt String)
(declare-const fmt_addr (_ BitVec 64))
(declare-const ret_addr (_ BitVec 64))
(declare-const write_target (_ BitVec 64))

; Vulnerability condition: a %n conversion writes through a stack-derived target.
(assert (str.contains fmt "%n"))
(assert (= write_target ret_addr))

; Concrete candidate has no %n conversion, so the string side is contradictory.
(assert (= fmt "%08x.%08x"))

; BV address constraints force the formula through String+BV auto-detection.
(assert (= fmt_addr #x0000000000402000))
(assert (= ret_addr #x00007fffffffe018))
(assert (bvuge write_target #x00007fffffffe000))
(assert (bvule write_target #x00007ffffffff000))
(check-sat)
"#;

struct AYRun {
    answer: String,
    stdout: String,
    stderr: String,
}

fn answer_line(stdout: &str) -> String {
    stdout
        .lines()
        .map(str::trim)
        .find(|line| {
            !line.is_empty()
                && !line.starts_with("c ")
                && matches!(*line, "sat" | "unsat" | "unknown")
        })
        .unwrap_or("")
        .to_string()
}

fn run_ay_on_smt(smt: &str, timeout_ms: u64) -> AYRun {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut tmp = tempfile::NamedTempFile::new().expect("tempfile");
    tmp.write_all(smt.as_bytes()).expect("write smt");
    tmp.flush().expect("flush");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg(format!("-t:{timeout_ms}"))
        .arg(tmp.path())
        .output()
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(
        output.status.success(),
        "ay exited with {:?} for #8333 repro\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );

    AYRun {
        answer: answer_line(&stdout),
        stdout,
        stderr,
    }
}

#[test]
#[timeout(30_000)]
fn string_bv_format_query_must_not_drop_string_constraints() {
    let run = run_ay_on_smt(FORMAT_STRING_BV_REPRO, 5_000);
    assert!(
        matches!(run.answer.as_str(), "unsat" | "unknown"),
        "String+BV format query must not answer sat by dropping string constraints (#8333).\n\
         stdout:\n{}\nstderr:\n{}",
        run.stdout,
        run.stderr
    );
}
