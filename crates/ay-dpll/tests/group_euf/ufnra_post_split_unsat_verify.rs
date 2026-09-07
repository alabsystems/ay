// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #post-split-verify-lane: the UF+NRA / UF+NIA lanes must PUBLISH a
//! post-expression-split propositional UNSAT they can re-derive, not discard it.
//!
//! `solve_uf_nra` and `solve_uf_nia` invoked the eager split-loop macro with
//! neither UNSAT opt-in, so the #6812 stale-learned-clause guard escalated
//! every propositional UNSAT reached after an expression split
//! (`Eager UFNRA UNSAT after expression splits … verify_attempted=false`,
//! pipeline_incremental_split_eager_macros.rs). The lanes derived the
//! refutation and then answered `unknown`; their UF+LIA sibling
//! (`solve_uf_lia`) and `solve_euf` had carried
//! `verify_unsat_after_splits: true` all along.
//!
//! Both lanes now opt in with their OWN `PostSplitVerifyLane`, so the UNSAT is
//! re-derived on a FRESH, isolated solve of the ORIGINAL assertions and
//! published only on an explicit fresh `Unsat`; `Sat`, `Unknown` and verifier
//! failure all still escalate to `unknown`.

use crate::common::{run_executor_file_with_timeout, workspace_path, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

/// The QF_UFNRA `FFT` family is the measured population for this defect: 7 of
/// its 10 files reached the escalation site twice per run and published
/// `unknown` where z3 4.16.0 answers `unsat` in 0.02 s. `smtlib.630867` is one
/// of them, and its refutation is the linear trichotomy plus EUF congruence —
/// the file's only product is `(* 2.0 f6)`, so the verification re-derives it
/// easily. `unknown` here means the lane went back to discarding the answer.
#[test]
#[timeout(60_000)]
fn test_ufnra_post_split_unsat_is_verified_and_published() -> Result<()> {
    let benchmark = workspace_path("benchmarks/smt/QF_UFNRA/FFT/smtlib.630867.smt2");
    let outcome = run_executor_file_with_timeout(&benchmark, 30)?;
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#post-split-verify-lane: the verified post-split UNSAT must be published, got {outcome:?}"
    );
    Ok(())
}

/// Soundness companion: the opt-in must not manufacture an UNSAT. This UF+NRA
/// formula is satisfiable (`g` is uninterpreted and `a`, `b` may differ), and
/// the disequality forces the very expression splits the guard watches, so the
/// verify-before-accept path is exercised on a SAT instance. It must never
/// publish `unsat`.
#[test]
#[timeout(30_000)]
fn test_ufnra_post_split_verify_never_manufactures_unsat() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (>= (* a a) 1.0))
(assert (<= (* a a) 4.0))
(assert (>= (* b b) 1.0))
(assert (<= (* b b) 4.0))
(assert (not (= a b)))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown");
    assert_ne!(
        result, "unsat",
        "#post-split-verify-lane: verify-before-accept must never publish a wrong unsat"
    );
}
