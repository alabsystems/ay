// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests: ay solves a SAT problem, exports the LRAT proof certificate
//! as a kernel-checked Lean4 file, and (when `lean` is on PATH) invokes the
//! Lean4 kernel to verify the emitted proof. Part of #8697 Phase 2.
//!
//! The tests in `ay_sat::lean_export` exercise the emitter on hand-crafted
//! LRAT steps. These tests close the loop by driving the full pipeline:
//!   DIMACS input -> Solver -> ProofCertificate -> write_lean4_kernel -> lean kernel
//!
//! Default `cargo test` always runs the emission path (writing the Lean source
//! and sanity-checking its structure). Kernel invocation is behind the
//! `lean-integration` feature so the default test suite does not require a
//! Lean4 toolchain.

#![allow(clippy::print_stderr)]

#[cfg(feature = "lean-integration")]
use std::sync::atomic::{AtomicU64, Ordering};

use ay_sat::{parse_dimacs, ProofOutput, Solver};

#[cfg(feature = "lean-integration")]
static LEAN_TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

/// PHP(2,1): 2 pigeons, 1 hole — simplest non-trivial UNSAT instance.
const PHP21_DIMACS: &str = "\
p cnf 2 3
1 0
2 0
-1 -2 0
";

/// (x) AND (NOT x) — smallest possible UNSAT instance.
const TRIVIAL_UNSAT_DIMACS: &str = "\
p cnf 1 2
1 0
-1 0
";

/// Solve the formula, extract the streaming ProofCertificate, and emit a
/// kernel-checked Lean4 proof into a `Vec<u8>`. Returns the emitted source
/// text (valid UTF-8). Panics if solving doesn't yield UNSAT, or if the proof
/// certificate is not attached to the result.
fn solve_and_emit_lean4_kernel(dimacs: &str, label: &str) -> String {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    // Enable LRAT backward reconstruction so a ProofCertificate is attached.
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    // Collect clauses into DIMACS (clause_id, Vec<i32>) for the emitter BEFORE
    // handing them to the solver — the solver consumes them.
    let mut originals: Vec<(u64, Vec<i32>)> = Vec::with_capacity(formula.clauses.len());
    for (idx, clause) in formula.clauses.iter().enumerate() {
        let dimacs_lits: Vec<i32> = clause.iter().map(|lit| lit.to_dimacs()).collect();
        // Clause IDs start at 1 in the LRAT convention; match that.
        originals.push((idx as u64 + 1, dimacs_lits));
    }

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT");

    let cert = result
        .proof_certificate()
        .unwrap_or_else(|| panic!("{label}: no ProofCertificate on UNSAT result"));

    let mut buf: Vec<u8> = Vec::new();
    cert.write_lean4_kernel(&originals, &mut buf)
        .unwrap_or_else(|e| panic!("{label}: write_lean4_kernel failed: {e}"));

    String::from_utf8(buf).unwrap_or_else(|e| panic!("{label}: emitter produced non-UTF8: {e}"))
}

/// Structural sanity checks on the emitted Lean4 source. These run on every
/// `cargo test` invocation and do NOT require `lean` on PATH.
fn assert_structural(source: &str, label: &str) {
    for needle in [
        "namespace AY.LratProof",
        "def lratCheck",
        "def rupStep",
        "def originalClauses",
        "def proofSteps",
        "theorem proof_valid",
        "native_decide",
        "end AY.LratProof",
    ] {
        assert!(
            source.contains(needle),
            "{label}: emitted Lean4 missing marker {needle:?}. Source (first 600 chars):\n{}",
            &source[..source.len().min(600)]
        );
    }

    // Delimiter balance — catches emitter truncation / escape bugs.
    let open_brackets = source.chars().filter(|&c| c == '[').count();
    let close_brackets = source.chars().filter(|&c| c == ']').count();
    assert_eq!(
        open_brackets, close_brackets,
        "{label}: bracket imbalance {open_brackets}/{close_brackets}"
    );

    let open_braces = source.chars().filter(|&c| c == '{').count();
    let close_braces = source.chars().filter(|&c| c == '}').count();
    assert_eq!(
        open_braces, close_braces,
        "{label}: brace imbalance {open_braces}/{close_braces}"
    );

    let open_parens = source.chars().filter(|&c| c == '(').count();
    let close_parens = source.chars().filter(|&c| c == ')').count();
    assert_eq!(
        open_parens, close_parens,
        "{label}: paren imbalance {open_parens}/{close_parens}"
    );
}

/// When `lean-integration` is enabled, shell out to `lean` and fail the test
/// if the kernel rejects the emitted proof. Requires `lean` on PATH.
#[cfg(feature = "lean-integration")]
fn assert_lean_kernel_accepts(source: &str, label: &str) {
    use std::io::Write as _;
    use std::process::Command;

    let seq = LEAN_TEMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let tmp = std::env::temp_dir().join(format!("ay_lean_e2e_{label}_{pid}_{seq}.lean"));
    {
        let mut f =
            std::fs::File::create(&tmp).unwrap_or_else(|e| panic!("{label}: create {tmp:?}: {e}"));
        f.write_all(source.as_bytes())
            .unwrap_or_else(|e| panic!("{label}: write {tmp:?}: {e}"));
    }

    let out = Command::new("lean")
        .arg(&tmp)
        .output()
        .unwrap_or_else(|e| panic!("{label}: failed to spawn `lean`: {e}"));

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);

    // Clean up before asserting so failures don't leak temp files.
    let _ = std::fs::remove_file(&tmp);

    assert!(
        out.status.success(),
        "{label}: Lean kernel REJECTED ay-emitted proof.\n\
         exit={}\nstdout:\n{stdout}\nstderr:\n{stderr}\n\
         Source (first 800 chars):\n{}",
        out.status,
        &source[..source.len().min(800)]
    );
    eprintln!("lean kernel VERIFIED ay-emitted proof ({label})");
}

#[cfg(not(feature = "lean-integration"))]
#[allow(dead_code)]
fn assert_lean_kernel_accepts(_source: &str, _label: &str) {
    // No-op when the feature is off. Structural check already ran.
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn test_lean4_kernel_e2e_trivial_unsat_emits_well_formed() {
    let src = solve_and_emit_lean4_kernel(TRIVIAL_UNSAT_DIMACS, "trivial");
    assert_structural(&src, "trivial");
    assert_lean_kernel_accepts(&src, "trivial");
}

#[test]
fn test_lean4_kernel_e2e_php21_emits_well_formed() {
    let src = solve_and_emit_lean4_kernel(PHP21_DIMACS, "php21");
    assert_structural(&src, "php21");
    assert_lean_kernel_accepts(&src, "php21");
}

#[test]
fn test_lean4_kernel_e2e_emits_deterministic() {
    // Same input twice must produce byte-identical Lean source (determinism is
    // a requirement for reproducible proof artifacts).
    let src1 = solve_and_emit_lean4_kernel(TRIVIAL_UNSAT_DIMACS, "det_a");
    let src2 = solve_and_emit_lean4_kernel(TRIVIAL_UNSAT_DIMACS, "det_b");
    assert_eq!(
        src1, src2,
        "lean4 kernel emitter must be deterministic for a fixed input"
    );
}
