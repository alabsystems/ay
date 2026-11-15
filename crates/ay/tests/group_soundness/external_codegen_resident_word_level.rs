// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! external-codegen's resident route decides a word-level x86-64 body theorem the way
//! its one-shot route does.
//!
//! external-codegen asks a resident `ay --incremental` first, one window per query
//! (`<body>(echo "==TCG_SRV_n==")(reset)`, verdict only), and replays a
//! resident `unsat` through the one-shot `-smt2 F --strict-proofs` route for
//! its proof. A stdin session retains no parsed proof surface
//! (`configure_unproved_smt_executor`) but still certifies its `unsat`, and
//! the raw ground closure, which refutes these theorems word by word, read its
//! roots from that surface alone. It found none, so the session handed the
//! whole root to the bit-level members. Measured on AY main b1b0b9de0 (build
//! 12713) with external-codegen's census query for `u64::wrapping_mul`: the one-shot
//! route certified in 0.1 s, the resident route answered `unknown` with
//! `(:reason-unknown timeout)` at the query's own 30 s, where build 10530 had
//! answered resident in 3.1 s. Two of external-codegen's newly failing census roots
//! and seven of its uncertified bodies came from that difference.
//!
//! Each window is the bridge's exact bytes, its `(set-option :timeout 30000)`
//! included: the verdict this test pins is the one the bridge receives under
//! that deadline. The closure decides each of these in well under a second,
//! so the deadline is not what separates a pass from a failure here. The
//! session runs every query in one process, as the bridge does, so a window
//! after `(reset)` is covered too, and a satisfiable twin must stay `sat`.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// external-codegen's census query for `u64::wrapping_mul` (byte-identical for
/// `usize::wrapping_mul`): the 64-bit `bvmul` against its `imul` lowering.
const U64_WRAPPING_MUL: &str = "(set-option :timeout 30000)
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const p0 (_ BitVec 64))
(declare-const p1 (_ BitVec 64))
(declare-const s0 (_ BitVec 64))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(declare-const m3 (_ BitVec 64))
(assert (and (= p0 e_rdi) (and (= p1 e_rsi) (and (= s0 (bvmul p0 p1)) (and (= m0 e_rdi) (and (= m1 e_rsi) (and (= m2 (bvmul m0 m1)) (and (= m3 m2) (not (= s0 m3))))))))))
(check-sat)
(exit)
";

/// The satisfiable twin: the machine side squares its first argument, so the
/// claim fails whenever `e_rdi * e_rsi != e_rdi * e_rdi` (`e_rdi = 1`,
/// `e_rsi = 0`). No word-level rule may refute it.
const U64_WRONG_MUL: &str = "(set-option :timeout 30000)
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const p0 (_ BitVec 64))
(declare-const p1 (_ BitVec 64))
(declare-const s0 (_ BitVec 64))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(declare-const m3 (_ BitVec 64))
(assert (and (= p0 e_rdi) (and (= p1 e_rsi) (and (= s0 (bvmul p0 p1)) (and (= m0 e_rdi) (and (= m1 e_rsi) (and (= m2 (bvmul m0 m0)) (and (= m3 m2) (not (= s0 m3))))))))))
(check-sat)
(exit)
";

/// The bridge's harness deadline is 30 s per window; twelve windows fit here
/// with room for a loaded host.
const SESSION_TIMEOUT: Duration = Duration::from_mins(10);

/// The `word-level-closure` rows of the consumer-certificate corpus: external-codegen
/// x86-64 body theorems that the one-shot route certifies through the raw
/// ground closure.
fn word_level_closure_fixtures() -> Vec<(String, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/external_codegen_consumer_certificates");
    let manifest = std::fs::read_to_string(dir.join("MANIFEST.tsv")).expect("read MANIFEST.tsv");
    let fixtures: Vec<(String, String)> = manifest
        .lines()
        .filter(|line| !line.starts_with('#'))
        .filter_map(|line| {
            let mut columns = line.split('\t');
            let id = columns.next()?;
            (columns.next()? == "word-level-closure").then(|| {
                let script = std::fs::read_to_string(dir.join(format!("{id}.smt2")))
                    .unwrap_or_else(|e| panic!("read {id}.smt2: {e}"));
                (id.to_string(), script)
            })
        })
        .collect();
    assert_eq!(fixtures.len(), 10, "the corpus has ten word-level rows");
    fixtures
}

/// One resident session with external-codegen's framing; one verdict list per window,
/// plus stderr.
fn session(scripts: &[&str]) -> (Vec<Vec<String>>, String) {
    let mut input = String::new();
    for (k, script) in scripts.iter().enumerate() {
        let body = script
            .trim_end()
            .strip_suffix("(exit)")
            .expect("a bridge query ends in (exit)");
        input.push_str(body);
        input.push_str(&format!("\n(echo \"==TCG_SRV_{k}==\")\n(reset)\n"));
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--incremental")
        .output_timeout_with_stdin(input.as_bytes(), SESSION_TIMEOUT)
        .expect("run ay --incremental");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mut windows = Vec::new();
    let mut current = Vec::new();
    for line in stdout.lines().map(str::trim) {
        if line == format!("==TCG_SRV_{}==", windows.len()) {
            windows.push(std::mem::take(&mut current));
        } else if matches!(line, "sat" | "unsat" | "unknown") || line.contains(":reason-unknown") {
            current.push(line.to_string());
        }
    }
    assert_eq!(
        windows.len(),
        scripts.len(),
        "session ended early\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    (windows, stderr)
}

#[test]
#[timeout(900_000)]
fn word_level_body_theorems_are_unsat_on_the_resident_route() {
    let fixtures = word_level_closure_fixtures();
    let mut names = vec!["u64::wrapping_mul".to_string()];
    let mut scripts = vec![U64_WRAPPING_MUL];
    for (id, script) in &fixtures {
        names.push(id.clone());
        scripts.push(script);
    }
    names.push("u64 wrong product (sat twin)".to_string());
    scripts.push(U64_WRONG_MUL);
    let (windows, stderr) = session(&scripts);
    assert!(
        !stderr.contains("panicked"),
        "the session panicked\nstderr:\n{stderr}"
    );
    let last = windows.len() - 1;
    let wrong: Vec<String> = windows
        .iter()
        .enumerate()
        .filter(|(k, window)| {
            let expected = if *k == last { "sat" } else { "unsat" };
            window.as_slice() != [expected]
        })
        .map(|(k, window)| format!("{}: {window:?}", names[k]))
        .collect();
    assert!(
        wrong.is_empty(),
        "resident windows that did not answer as the one-shot route does:\n{}\nstderr:\n{stderr}",
        wrong.join("\n")
    );
}
