// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! AY-SMT-2 (2026-11-19) end-to-end fences.
//!
//! 1. QF_UFLIA `0 <= f(1) <= 0`, `f(1) != 0`. EUF forwards the disequality to
//!    LIA as a SHARED pair; the finite-domain lane used to return the witness
//!    `f(1) = 0` without looking at it, so the fail-closed conflict verifier's
//!    combiner called the genuine conflict satisfiable and the CLI's default
//!    mode answered `unknown` (with `--z3-mode` the same build answered
//!    `unsat` through another route).
//! 2. AUFLIA 498486a2 (SMT-COMP; z3 and cvc5 answer `unsat`). Besides the
//!    shape above, its quantifier rounds handed the model gate a candidate
//!    whose arithmetic model put two UF arguments on the same value
//!    (`x2 = sk!x12 = 6`) while the applications kept different values; the
//!    AUFLIA lane never split on that coincidence, model reunification moved
//!    `x2`, and the strict gate degraded the round to `unknown`.
//!
//! `sat` is an outright soundness bug on both.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

#[test]
#[ntest::timeout(60_000)]
fn uf_constant_argument_shared_disequality_is_unsat() -> Result<()> {
    let smt = "(set-logic QF_UFLIA)(declare-fun f (Int) Int)\
               (assert (<= 0 (f 1)))(assert (<= (f 1) 0))(assert (not (= 0 (f 1))))\
               (check-sat)";
    let outcome = run_executor_smt_with_timeout(smt, 20)?;
    assert_eq!(outcome, SolverOutcome::Unsat);
    Ok(())
}

#[test]
#[ntest::timeout(120_000)]
fn auflia_498486a2_uf_argument_coincidence_is_never_sat() -> Result<()> {
    // The instance is unsat (z3 and cvc5). The first run of this test with a
    // compiler (20 November 2026) got Unknown: the shared-interface changes
    // stop the false Sat candidate, they do not yet refute the instance, so
    // AY-SMT-2 stays open for it. What holds, and is asserted, is that the
    // answer is never Sat.
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/ay_smt_2/auflia_498486a2.smt2");
    let smt = std::fs::read_to_string(&path)?;
    let outcome = run_executor_smt_with_timeout(&smt, 60)?;
    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "SOUNDNESS BUG: sat on {} (z3 and cvc5: unsat)",
        path.display()
    );
    Ok(())
}
