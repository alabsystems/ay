// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for #8698 — delayed-bvmul circuit clauses must persist
//! across re-check iterations.
//!
//! Root cause (discovered 2026-04-18 while investigating z3_7526):
//! The BV executor re-check loop at
//! `crates/ay-dpll/src/executor/theories/bv/mod.rs` creates a fresh SAT solver
//! every iteration (to dodge a stale-BCP soundness bug from #8480). Before
//! this fix, each fresh solver received `all_clauses` plus only the CURRENT
//! iteration's new clauses. Circuit clauses for delayed ops that were built
//! in earlier iterations silently disappeared. Once a circuit was gone, the
//! SAT solver could return a model that violated that circuit but whose op
//! was flagged `circuit_built=true`, so the re-check loop skipped it and
//! declared the model consistent. The outer model-validation pipeline then
//! rejected the model and degraded SAT to Unknown (#8373 Violated path),
//! producing `model-validation-failures 1` with `:reason-unknown incomplete`.
//!
//! Fix: accumulate every cheap-axiom and circuit clause across all
//! iterations into a single vector that is replayed into every fresh solver.
//!
//! The canonical failing benchmark is
//! `benchmarks/smt/z3-perf-cliffs/z3_7526.smt2` (32-bit) and its 16-bit
//! minimization below. Both are algebraic tautologies whose negation is
//! UNSAT; before the fix ay returned Unknown.

#![allow(clippy::panic)]

use ntest::timeout;

/// Narrow-bound variant: the bvult bounds are what makes z3_7526 tractable
/// (each operand < 2^8 so the true product fits in 16 bits). Kept as a
/// regression guard for the bounded case the original issue targets.
#[test]
#[timeout(60_000)]
fn test_bvmul_overflow_identity_16bit_bounded_unsat_8698() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (bvult x (_ bv256 16)))
        (assert (bvult y (_ bv256 16)))
        (assert (not (= (bvmul x y)
                        ((_ extract 15 0)
                         (bvmul ((_ zero_extend 16) x)
                                ((_ zero_extend 16) y))))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "bounded bvmul overflow identity at width 16 must be UNSAT (#8698)"
    );
}
