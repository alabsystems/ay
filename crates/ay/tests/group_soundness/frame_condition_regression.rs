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

/// 3D nested array frame condition (Issue #85 - FIXED)
///
/// Tests: Heap[0][obj1][field1] = 99 should not affect Heap[0][obj1][field2]
/// Expected: unsat (frame condition holds)
///
/// Fixed in Worker iter 159 via:
/// - normalize_select: Recursively follows nested selects through stores
/// - get_effective_array: Applies ROW1 to simplify select(store(a,i,v),i) = v
/// - follow_stores_to_base: Applies ROW2 to skip stores at distinct indices
/// - check_nested_select_conflicts: Detects when two selects normalize to same (base, index)
#[test]
#[timeout(60000)]
fn frame_condition_3d_nested() {
    let output = run_ay_file("3d_nested_frame_condition.smt2");
    // Issue #85: AY returns sat (WRONG), Z3 returns unsat (CORRECT)
    // This test documents the EXPECTED behavior after fix
    assert!(
        output.trim() == "unsat",
        "SOUNDNESS BUG (Issue #85): 3d_nested_frame_condition returned '{}', expected 'unsat'. \
         AY is returning wrong results for 3D nested array frame conditions.",
        output.trim()
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
/// Expected: unsat
#[test]
#[timeout(60000)]
fn method_delegation_simple() {
    let output = run_ay_file("method_delegation_simple.smt2");
    assert!(
        output.trim() == "unsat",
        "REGRESSION: method_delegation_simple returned '{}', expected 'unsat' (Issue #85)",
        output.trim()
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
