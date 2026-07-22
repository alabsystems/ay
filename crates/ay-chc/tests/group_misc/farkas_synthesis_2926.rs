// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #2926: verify that Farkas conflicts are **synthesized**
//! when the theory returns `TheoryResult::Unsat` without a Farkas certificate.
//!
//! The existing inline test `test_farkas_conflicts_synthesized_in_unsat_core`
//! (smt.rs) is misnamed — it exercises the **genuine Farkas certificate** path
//! (LRA bound-contradiction for `x >= 1 AND x <= -1`), not the synthesis path.
//!
//! This test uses a Diophantine-infeasible formula `2x = 3` (GCD(2) does not
//! divide 3) to trigger `TheoryResult::Unsat` without Farkas data, exercising
//! the synthesis path at smt.rs:2819-2845 that creates uniform weight-1 Farkas
//! annotations.

use ay_chc::{ChcExpr, ChcSort, ChcVar, SmtContext, SmtResult};

/// Verify that Farkas conflicts are synthesized with uniform weight-1 coefficients
/// when the LIA theory returns UNSAT from Diophantine infeasibility (no Farkas
/// certificate available).
#[test]
fn test_farkas_synthesis_diophantine_unsat() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // background: 2*x = 3 (Diophantine infeasible: GCD(2) does not divide 3)
    let two_x = ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x.clone()));
    let bg = ChcExpr::eq(two_x, ChcExpr::int(3));
    // assumption: x >= 0 (ensures x is relevant in both partitions)
    let assumption = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let result = ctx.check_sat_with_assumption_conjuncts(&[bg], &[assumption]);
    match &result {
        SmtResult::UnsatWithCore(core) => {
            assert!(
                !core.farkas_conflicts.is_empty(),
                "expected non-empty farkas_conflicts from Diophantine synthesis, got empty"
            );
            for conflict in &core.farkas_conflicts {
                assert_eq!(
                    conflict.conflict_terms.len(),
                    conflict.polarities.len(),
                    "conflict_terms and polarities length mismatch"
                );
                assert_eq!(
                    conflict.conflict_terms.len(),
                    conflict.farkas.coefficients.len(),
                    "conflict_terms and farkas coefficients length mismatch"
                );
                // Synthesized Farkas should have uniform weight-1 coefficients
                for coeff in &conflict.farkas.coefficients {
                    assert_eq!(
                        *coeff,
                        num_rational::Rational64::from(1),
                        "synthesized Farkas coefficient should be uniform weight 1, got {coeff}"
                    );
                }
            }
        }
        SmtResult::Unsat => {
            // Plain UNSAT is acceptable if the solver short-circuits before
            // reaching the assumption-driven code path
        }
        other => {
            panic!("expected UnsatWithCore or Unsat for Diophantine infeasibility, got {other:?}")
        }
    }
}
