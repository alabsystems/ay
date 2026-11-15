// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A RAW character in the surrogate carrier block `U+10D800..=U+10DFFF` must
//! never be read as the surrogate it carries (2026-09-28 fp-strings verifier,
//! `witness/rawcarrier_*`). AY stores surrogate `s` in the `char`
//! `s + 0x10_0000`; a raw U+10D800 in a literal was stored as-is and so WAS
//! `\u{d800}`: `(= "R" "\u{d800}")` answered `sat`, `(not (= "R" (str.from_code
//! 55296)))` `unsat`, where z3 (and AY's own code-point reading of a raw
//! character, 0x10D800) says the opposite. The literal is now refused, its
//! command discarded, and `check-sat` answers `unknown` in both postures.

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
        "ay_surrogate_carrier_raw_input_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

/// `(stdout, the last sat/unsat/unknown line)` of `script` in the default
/// posture or, with `z3_mode`, in `--z3-mode`.
fn run(script: &str, z3_mode: bool) -> (String, String) {
    let (input, _cleanup) = write_temp(script);
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    if z3_mode {
        command.arg("--z3-mode");
    }
    let output = command.arg("-T:20").arg(&input).output().expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let verdict = stdout
        .lines()
        .rev()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .trim()
        .to_string();
    (stdout, verdict)
}

/// The verifier's five wrong answers (R = raw U+10D800, R' = raw U+10D801),
/// each with z3 5.1.0's verdict, which AY must never contradict.
const RAW_CARRIER_WITNESSES: [(&str, &str); 5] = [
    ("(assert (= \"\u{10D800}\" \"\\u{d800}\"))", "unsat"),
    (
        "(declare-const n Int) (assert (= n (str.to_code \"\u{10D800}\"))) (assert (= n 55296))",
        "unsat",
    ),
    (
        "(assert (str.in_re \"\u{10D801}\" (re.range \"\\u{d800}\" \"\\u{dfff}\")))",
        "unsat",
    ),
    (
        "(declare-const x String) (declare-const y String) \
         (assert (= (str.++ x \"\u{10D801}\") (str.++ \"\\u{d801}\" y))) \
         (assert (= (str.len x) 0))",
        "unsat",
    ),
    (
        "(assert (not (= \"\u{10D800}\" (str.from_code 55296))))",
        "sat",
    ),
];

#[test]
#[timeout(240_000)]
fn a_raw_carrier_block_character_is_refused_not_read_as_a_surrogate() {
    for (body, z3_verdict) in RAW_CARRIER_WITNESSES {
        let script = format!("(set-logic QF_SLIA)\n{body}\n(check-sat)\n");
        for z3_mode in [false, true] {
            let (stdout, verdict) = run(&script, z3_mode);
            assert!(
                stdout.contains("reserves to carry the surrogate code point U+D80"),
                "z3_mode={z3_mode}: the raw carrier must be refused\n{script}\n{stdout}"
            );
            assert_eq!(
                verdict, "unknown",
                "z3_mode={z3_mode}: z3 says {z3_verdict}; a verdict here reads the raw \
                 character as a surrogate\n{script}\n{stdout}"
            );
        }
    }
}

/// Controls: the surrogate ESCAPE is still one SMT-LIB character, and a raw
/// character just outside the carrier block is still accepted as-is.
#[test]
#[timeout(240_000)]
fn surrogate_escapes_and_neighbouring_raw_characters_still_decide() {
    let cases = [
        ("(assert (= (str.to_code \"\\u{d800}\") 55296))", "sat"),
        (
            "(assert (not (= \"\\u{d800}\" (str.from_code 55296))))",
            "unsat",
        ),
        ("(assert (= \"\u{10D7FF}\" \"\\u{d7ff}\"))", "unsat"),
        ("(assert (= \"\u{10E000}\" \"\\u{e000}\"))", "unsat"),
    ];
    for (body, expected) in cases {
        let script = format!("(set-logic QF_SLIA)\n{body}\n(check-sat)\n");
        for z3_mode in [false, true] {
            let (stdout, verdict) = run(&script, z3_mode);
            assert!(
                !stdout.contains("(error"),
                "z3_mode={z3_mode}: nothing here is refused\n{script}\n{stdout}"
            );
            assert_eq!(verdict, expected, "z3_mode={z3_mode}\n{script}\n{stdout}");
        }
    }
}
