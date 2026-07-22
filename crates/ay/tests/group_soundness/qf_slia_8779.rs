// QF_SLIA false-SAT on ground str.in_re violation regression (#8779).
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// #8779: AY returned `sat` on QF_SLIA benchmarks where the model assigned
// `atkPtn = ""` while the assertion `(str.in_re atkPtn (str.to_re "vbscript:"))`
// was satisfied by the SAT layer. The model validator's `#7460` fallback
// was too coarse — it treated every `Bool(false)` on a string-flagged
// assertion as a model-extraction gap, even when the evaluation was
// structurally ground (no gap possible). The fix adds a definitive-ground
// check so ground str.in_re / str.contains / str.prefixof / str.suffixof
// violations are reported as Violated.

use ntest::timeout;
use std::io::Write;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

const NARROW7_SMT: &str = r#"(set-logic QF_SLIA)
(declare-fun sigmaStar_safe_48 () String)
(declare-fun b_sigmaStar_safe_48 () Bool)
(declare-fun literal_8 () String)
(declare-fun b_literal_8 () Bool)
(declare-fun literal_13 () String)
(declare-fun b_literal_13 () Bool)
(declare-fun x_1 () String)
(declare-fun b_x_1 () Bool)
(declare-fun x_2 () String)
(declare-fun b_x_2 () Bool)
(declare-fun x_9 () String)
(declare-fun b_x_9 () Bool)
(declare-fun x_14 () String)
(declare-fun b_x_14 () Bool)
(declare-fun sink () String)
(declare-fun atkPtn () String)
(declare-fun atk_sigmaStar_1 () String)
(declare-fun atk_sigmaStar_2 () String)
(declare-fun atk_sink () String)
(assert (and b_sigmaStar_safe_48 (str.in_re sigmaStar_safe_48 (re.* (re.range "0" "9")))))
(assert (and b_literal_8 (= literal_8 "\x20\x20\x20\x20")))
(assert (and b_literal_13 (= literal_13 "abcd")))
(assert (str.in_re atkPtn (str.to_re "vbscript:")))
(assert (= atk_sink (str.++ atk_sigmaStar_1 (str.++ atkPtn atk_sigmaStar_2))))
(assert (= b_x_1 (and (= x_1 sigmaStar_safe_48) b_sigmaStar_safe_48)))
(assert (= b_x_2 (and (= x_2 x_1) b_x_1)))
(assert (= b_x_9 (and (= x_9 (str.++ literal_8 x_2)) b_literal_8 b_x_2)))
(assert (= b_x_14 (and (= x_14 (str.++ x_9 literal_13)) b_x_9 b_literal_13)))
(assert (and (= sink x_14) (= sink atk_sink) b_x_14))
(assert (> 50 (+ (str.len x_2) (str.len sink))))
(check-sat)
"#;

struct AYRun {
    first_line: String,
    stdout: String,
    stderr: String,
}

fn result_line(stdout: &str) -> String {
    stdout.trim().lines().next().unwrap_or("").to_string()
}

fn assert_clean_not_sat(run: &AYRun, context: &str) {
    assert!(
        matches!(run.first_line.as_str(), "unsat" | "unknown"),
        "Soundness regression (#8779): AY must return `unsat` or `unknown` on {context}, \
         not {:?}.\nstdout:\n{}\nstderr:\n{}",
        run.first_line,
        run.stdout,
        run.stderr
    );
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
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(
        output.status.success(),
        "ay exited with {:?} for inline #8779 repro\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    AYRun {
        first_line: result_line(&stdout),
        stdout,
        stderr,
    }
}

/// #8779: Narrow reproducer must not answer `sat`.
#[test]
#[timeout(60_000)]
fn qf_slia_8779_narrow_repro_not_sat() {
    let run = run_ay_on_smt(NARROW7_SMT, 15_000);
    assert_clean_not_sat(&run, "the narrow QF_SLIA repro");
}

/// #8779: Full lan_replace_all2 benchmark must not answer `sat`.
#[test]
#[timeout(120_000)]
fn qf_slia_8779_lan_replace_all2_not_sat() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smtlib-2025/non-incremental/QF_SLIA/20230403-webapp/lan-rep-all/lan_replace_all2.smt2",
        env!("CARGO_MANIFEST_DIR")
    );
    if !Path::new(&benchmark_path).is_file() {
        eprintln!("SKIP: optional #8779 benchmark not found: {benchmark_path}");
        return;
    }
    let output = Command::new(ay_path)
        .arg("solve")
        .arg("-t:30000")
        .arg(&benchmark_path)
        .output_timeout(Duration::from_secs(115))
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(
        output.status.success(),
        "ay exited with {:?} for {benchmark_path}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    let run = AYRun {
        first_line: result_line(&stdout),
        stdout,
        stderr,
    };
    assert_clean_not_sat(&run, "lan_replace_all2.smt2");
}

/// #8779: The frontend rewrite for `(str.in_re x (str.to_re s)) --> (= x s)`
/// must not leave ay with a false-SAT on the Tseitin pattern used by
/// QF_SLIA pipeline corpora. Pattern: `(= b_var (and (= var (str.++ ...))
/// ...))` together with an equality chain that forces the concatenation to
/// a value inconsistent with a later `= var literal` constraint. Z3 says
/// UNSAT; ay must not say SAT.
const TSEITIN_STR_PATTERN_SMT: &str = r#"(set-logic QF_SLIA)
(declare-fun lit () String)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun b_lit () Bool)
(declare-fun b_x () Bool)
(declare-fun b_y () Bool)
(assert (= b_lit (= lit "abcd")))
(assert (= b_x (and (= x (str.++ a b)) b_lit)))
(assert (= b_y (and (= y x) b_x)))
(assert b_y)
(assert (= y lit))
(assert (= a "zz"))
(assert (= b "zz"))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn qf_slia_8779_tseitin_str_concat_equality_not_sat() {
    // y = x = a ++ b = "zzzz" contradicts y = lit = "abcd".
    let run = run_ay_on_smt(TSEITIN_STR_PATTERN_SMT, 15_000);
    assert_clean_not_sat(&run, "the Tseitin-wrapped string-concat equality repro");
}

/// #8779: Symmetric case — the ground `str.in_re(x, (str.to_re s))` lifting
/// must drive `x = s`. If the rewrite is dropped, this returns `sat` with
/// `x = ""`.
const IN_RE_LIFT_SMT: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.in_re x (str.to_re "hello")))
(assert (not (= x "hello")))
(check-sat)
"#;

#[test]
#[timeout(30_000)]
fn qf_slia_8779_str_in_re_to_re_lifting_not_sat() {
    let run = run_ay_on_smt(IN_RE_LIFT_SMT, 10_000);
    assert_clean_not_sat(&run, "the str.in_re/str.to_re lifting repro");
}
