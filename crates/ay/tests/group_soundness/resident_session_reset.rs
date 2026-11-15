// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! After `(reset)` a resident `ay --incremental` session answers the next query
//! exactly as a fresh process does, in array logics too.
//!
//! `(reset)` replaced the frontend's term store but kept most of the
//! executor's own state, including `TermId`s into the discarded store. Measured
//! on 36a5da9d7 with external-codegen's framing (`<body>(echo ..)(reset)`), each pair
//! below answered its second query `sat` in a fresh process and `unknown` after
//! the first query; the first two pairs panicked on the way:
//!
//! * storecomm then `sat_nested_function`: `index out of bounds: the len is 7
//!   but the index is 247` in `ay-core/src/term/mod.rs` (the first query's
//!   rejected array assertion, dereferenced by the second query's read-pin
//!   repair);
//! * `store_select_same_idx_sat` then `interface_eq_basic`: `index out of
//!   bounds: the len is 1 but the index is 1` in
//!   `ay-dpll/src/executor/model/output_format.rs`;
//! * the other three: a bare `unknown`, no panic.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// `(first, second)`: benchmark paths relative to the repository root. Every
/// second query is `sat`.
const PAIRS: [(&str, &str); 5] = [
    (
        "crates/ay-dpll/tests/group_auflia/data/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
        "benchmarks/smt/QF_UFLIA/sat_nested_function.smt2",
    ),
    (
        "benchmarks/smt/QF_ALIA/store_select_same_idx_sat.smt2",
        "benchmarks/smt/QF_AUFLIA/interface_eq_basic.smt2",
    ),
    (
        "benchmarks/conformance/QF_ABV/sat_store_select.smt2",
        "benchmarks/smt/QF_ALIA/multi_store_distinct_sat.smt2",
    ),
    (
        "benchmarks/smt/QF_AX/ext_two_indices.smt2",
        "benchmarks/smt/QF_ABV/model_checker_consumer_pattern_mul_store.smt2",
    ),
    (
        "benchmarks/smt/regression/soundness_fuzz_round3/r3_rank3_qf_alia_false_UNSAT.smt2",
        "benchmarks/smt/regression/soundness_fuzz_round3/r3_rank4_qf_ax__nested_arrays__array_index__array_index_elem___false_UNSAT.smt2",
    ),
];

const SESSION_TIMEOUT: Duration = Duration::from_mins(3);

fn body(relative: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.replace("(exit)", "")
}

/// One resident session with external-codegen's framing; one verdict list per window,
/// plus stderr.
fn session(bodies: &[String]) -> (Vec<Vec<String>>, String) {
    let mut script = String::new();
    for (k, body) in bodies.iter().enumerate() {
        script.push_str(body);
        script.push_str(&format!("\n(echo \"==reset-window-{k}==\")\n(reset)\n"));
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--incremental")
        .output_timeout_with_stdin(script.as_bytes(), SESSION_TIMEOUT)
        .expect("run ay --incremental");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mut windows = Vec::new();
    let mut current = Vec::new();
    for line in stdout.lines().map(str::trim) {
        if line == format!("==reset-window-{}==", windows.len()) {
            windows.push(std::mem::take(&mut current));
        } else if matches!(line, "sat" | "unsat" | "unknown") {
            current.push(line.to_string());
        }
    }
    assert_eq!(
        windows.len(),
        bodies.len(),
        "session ended early\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    (windows, stderr)
}

#[test]
#[timeout(900_000)]
fn a_query_after_reset_answers_as_in_a_fresh_process() {
    for (first, second) in PAIRS {
        let (fresh, fresh_err) = session(&[body(second)]);
        assert_eq!(
            fresh[0],
            ["sat"],
            "{second} alone in a fresh session\nstderr:\n{fresh_err}"
        );
        let (windows, stderr) = session(&[body(first), body(second)]);
        assert_eq!(
            windows[0],
            ["sat"],
            "{first} first in the session\nstderr:\n{stderr}"
        );
        assert_eq!(
            windows[1], fresh[0],
            "{second} after {first} and (reset) must answer as in a fresh session\nstderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("panicked"),
            "{first} then {second}: the session panicked\nstderr:\n{stderr}"
        );
    }
}

/// A resource option one window's SCRIPT sets does not bound a later window.
///
/// SMT-LIB `(reset)` returns options to their initial values, and the initial
/// values are the host's (here: none). Measured on the round-4 head and on its
/// merge with origin/main: after a window that set `(set-option :timeout 1)`,
/// `system_03` answered `unknown (timeout)` after `(reset)`, where a fresh
/// session answers `unsat`. The same window also set `:rlimit` and
/// `:max-memory`, so all three script-set limits are covered.
#[test]
#[timeout(300_000)]
fn a_script_set_limit_does_not_survive_reset() {
    let query = body("benchmarks/smt/QF_LIA/system_03.smt2");
    let (fresh, fresh_err) = session(std::slice::from_ref(&query));
    assert_eq!(
        fresh[0],
        ["unsat"],
        "system_03 alone in a fresh session\nstderr:\n{fresh_err}"
    );
    let limiting_window = "(set-option :timeout 1)\n(set-option :rlimit 1)\n(set-option :max-memory 1)\n(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n".to_string();
    let (windows, stderr) = session(&[limiting_window, query]);
    assert_eq!(
        windows[1], fresh[0],
        "system_03 after a window that set :timeout/:rlimit/:max-memory and (reset) must answer as in a fresh session\nstderr:\n{stderr}"
    );
}
