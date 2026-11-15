// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Tests for array frame condition (Issues #70, #85)
//!
//! These tests verify that AY correctly implements the array theory axiom:
//! ROW2: select(store(A, i, v), j) = select(A, j) when i ≠ j
//!
//! A frame condition violation means AY cannot prove that unmodified
//! array indices retain their values.
//!
//! Test files are in crates/ay-frontend/tests/ for historical reasons.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run AY with given SMT-LIB input and return stdout
fn run_ay(input: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");

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
    String::from_utf8_lossy(&output.stdout).to_string()
}

/// Run AY on a file in ay-frontend/tests directory
fn run_ay_file(filename: &str) -> String {
    // Files are in ay-frontend/tests/ directory
    let workspace_root = env!("CARGO_MANIFEST_DIR")
        .strip_suffix("/crates/ay")
        .unwrap_or(env!("CARGO_MANIFEST_DIR"));
    let path = format!("{workspace_root}/crates/ay-frontend/tests/{filename}");
    let input =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    run_ay(&input)
}

/// Flat ROW2 test: single-level array frame condition
///
/// Tests: select(store(A, i, v), j) = select(A, j) when i ≠ j
/// Expected: unsat (frame condition holds)
#[test]
#[timeout(60000)]
fn frame_condition_flat() {
    let output = run_ay_file("frame_condition_flat.smt2");
    assert!(
        output.trim() == "unsat",
        "Expected 'unsat', got: {}",
        output.trim()
    );
}

/// ROW2 with syntactically distinct indices (Issue #70 - FIXED)
///
/// Same as flat but with i=0, j=1 explicitly bound.
/// Fixed in Worker iter 158 via:
/// - Syntactic constant distinctness in known_distinct
/// - Equality following via find_store_through_eq
/// - Extended ROW2 via check_row2_extended
///
/// Expected: unsat
#[test]
#[timeout(60000)]
fn frame_condition_debug() {
    let output = run_ay_file("frame_condition_debug.smt2");
    // Fixed in issue #70 - must return unsat
    assert!(
        output.trim() == "unsat",
        "REGRESSION: frame_condition_debug returned '{}', expected 'unsat' (Issue #70)",
        output.trim()
    );
}

/// Run AY on a file in ay-frontend/tests with `(get-info :all-statistics)`
/// appended, so a withheld verdict can be attributed to the gate that
/// withheld it.
fn run_ay_file_with_statistics(filename: &str) -> String {
    let workspace_root = env!("CARGO_MANIFEST_DIR")
        .strip_suffix("/crates/ay")
        .unwrap_or(env!("CARGO_MANIFEST_DIR"));
    let path = format!("{workspace_root}/crates/ay-frontend/tests/{filename}");
    let input =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    run_ay(&format!("{input}\n(get-info :all-statistics)\n"))
}

/// The `check-sat` verdict: the first non-empty stdout line.
fn check_sat_verdict(output: &str) -> &str {
    output
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or("")
}

/// The nested-array UNSAT contract since `53e9ac3c0` ("fix(arrays):
/// quarantine uncertified nested-array unsat", 2026-07-22).
///
/// A nested-array refutation publishes only on a checked authority
/// (`Executor::quarantine_unverified_nested_array_unsat`); anything else is
/// withheld as `unknown` with `:unknown.phase "array-combination-quarantine"`.
/// `6a0a66457` recorded that completeness cost as deliberate in LIMITATIONS.md
/// ("Do not widen the predicate to recover verdicts; give the ladder another
/// checked authority instead").
///
/// The Issue #85 bug these files were written for was a WRONG `sat`, so `sat`
/// always fails. `unsat` passes (the day the proof lane certifies these files
/// this test needs no change), and `unknown` passes ONLY when the quarantine
/// is what withheld it: any other lost verdict still fails here.
fn assert_frame_condition_unsat_or_quarantined(filename: &str) {
    let output = run_ay_file_with_statistics(filename);
    let verdict = check_sat_verdict(&output);
    assert_ne!(
        verdict, "sat",
        "SOUNDNESS BUG (Issue #85): {filename} returned 'sat' for an unsat nested-array frame \
         condition (z3: unsat).\nstdout:\n{output}"
    );
    match verdict {
        "unsat" => {}
        "unknown" => assert!(
            output.contains(":unknown.phase")
                && output.contains("\"array-combination-quarantine\""),
            "{filename}: `unknown` is acceptable only as the nested-array UNSAT quarantine \
             (53e9ac3c0); a different cause lost this verdict.\nstdout:\n{output}"
        ),
        other => {
            panic!("{filename}: expected unsat or quarantined unknown, got {other:?}\n{output}")
        }
    }
}

/// 3D nested array frame condition (Issue #85 - FIXED)
///
/// Tests: Heap[0][obj1][field1] = 99 should not affect Heap[0][obj1][field2]
/// The problem is unsat (the frame condition holds; z3 agrees).
///
/// Fixed in Worker iter 159 via:
/// - normalize_select: Recursively follows nested selects through stores
/// - get_effective_array: Applies ROW1 to simplify select(store(a,i,v),i) = v
/// - follow_stores_to_base: Applies ROW2 to skip stores at distinct indices
/// - check_nested_select_conflicts: Detects when two selects normalize to same (base, index)
///
/// Why this file may answer `unknown`: the proof lane cannot yet certify a
/// NESTED read through the defined post-state heap. `(= Heap_post (store Heap
/// s X))` with `(select (select Heap_post s) j)` alone reproduces the gap,
/// while the same read one level deep, and the whole obligation with the
/// store written inline, certify. With no checked authority the nested-array
/// quarantine withholds the refutation. Its certificate already stopped
/// passing AY's own self-certification with the 2026-07-21 self-check leak
/// fixes (`ae07a5c9e`, `d4dd3fe46`; `--self-check` answers `unknown` from
/// then on); `53e9ac3c0` extended that refusal to every posture.
/// [`frame_condition_3d_nested_inline_is_unsat`] pins that the #85 ROW
/// reasoning itself still refutes, and certifies, the same obligation.
#[test]
#[timeout(60000)]
fn frame_condition_3d_nested() {
    assert_frame_condition_unsat_or_quarantined("3d_nested_frame_condition.smt2");
}

/// Positive control for [`frame_condition_3d_nested`]: the SAME 3D frame
/// obligation with the post-state heap written inline instead of through a
/// defined `Heap_post` constant. No definition is substituted, so the proof
/// lane certifies the nested read-over-write refutation and the quarantine
/// publishes it: this must stay `unsat`. A regression in the #85 ROW
/// machinery (a wrong `sat`, or a lost refutation) fails here.
#[test]
#[timeout(60000)]
fn frame_condition_3d_nested_inline_is_unsat() {
    let output = run_ay(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun Heap () (Array Int (Array Int (Array Int Int))))\n\
         (declare-const obj1 Int)\n\
         (declare-const field1 Int)\n\
         (declare-const field2 Int)\n\
         (assert (not (= field1 field2)))\n\
         (assert (not (= (select (select (select Heap 0) obj1) field2)\n\
                         (select (select (select (store Heap 0 (store (select Heap 0) obj1\n\
                                   (store (select (select Heap 0) obj1) field1 99))) 0) obj1) field2))))\n\
         (check-sat)\n",
    );
    assert_eq!(
        check_sat_verdict(&output),
        "unsat",
        "Issue #85: the inline 3D nested frame condition must stay a certified unsat.\n\
         stdout:\n{output}"
    );
}

/// Method delegation frame condition (Issue #85 - FIXED)
///
/// Tests: modifying self.inner should not affect self.other_field
/// Uses 2D nested array encoding for heap: Heap: object -> (field_id -> value)
///
/// Fixed by the same changes that fixed #85 (3D nested case):
/// - normalize_select: Recursively follows nested selects through stores
/// - get_effective_array: Applies ROW1 to simplify select(store(a,i,v),i) = v
/// - follow_stores_to_base: Applies ROW2 to skip stores at distinct indices
///
/// The problem is unsat. Like [`frame_condition_3d_nested`], its refutation
/// rests on the substituted `Heap_post` definition, so it may be withheld by
/// the nested-array quarantine; [`method_delegation_inline_is_unsat`] is its
/// positive control.
#[test]
#[timeout(60000)]
fn method_delegation_simple() {
    assert_frame_condition_unsat_or_quarantined("method_delegation_simple.smt2");
}

/// Positive control for [`method_delegation_simple`]: the same frame
/// obligation with the post-state heap written inline. Must stay `unsat`.
#[test]
#[timeout(60000)]
fn method_delegation_inline_is_unsat() {
    let output = run_ay(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun Heap () (Array Int (Array Int Int)))\n\
         (declare-const self_ref Int)\n\
         (declare-const inner_field Int)\n\
         (declare-const other_field Int)\n\
         (declare-const inner_post Int)\n\
         (assert (distinct inner_field other_field))\n\
         (assert (not (= (select (select Heap self_ref) other_field)\n\
                         (select (select (store Heap self_ref\n\
                                   (store (select Heap self_ref) inner_field inner_post))\n\
                                 self_ref) other_field))))\n\
         (check-sat)\n",
    );
    assert_eq!(
        check_sat_verdict(&output),
        "unsat",
        "Issue #85: the inline method-delegation frame condition must stay a certified unsat.\n\
         stdout:\n{output}"
    );
}

// Note: method_delegation_encoding.smt2 is malformed (uses Int sort in QF_UF logic)
// Z3 rejects it: "Invalid function declaration: unknown sort 'Int'"
// We verify AY doesn't crash on it.

#[test]
#[timeout(60000)]
fn method_delegation_encoding_is_malformed() {
    // This file uses Int sort in QF_UF logic which is incorrect
    let output = run_ay_file("method_delegation_encoding.smt2");
    // Accept any result - just don't crash
    assert!(
        output.starts_with("sat")
            || output.starts_with("unsat")
            || output.starts_with("unknown")
            || output.contains("error"),
        "AY produced unexpected output (possible crash): {output}"
    );
}
