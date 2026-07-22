// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! QF_AX swap `_np_sf_` false-SAT soundness fences (#qf-ax-swap-sf-false-sat).
//!
//! The 2026-07 division-scale bench found 8 wrong-SATs on the
//! Armando/Bonacina/Ranise/Schulz swap `_sf_` family (`:status unsat`,
//! z3: unsat, AY: sat). The `_sf_` shape names each chain link
//! (`(= a_k (store a_{k-1} i v))`) and pins element constants through
//! separate select equations (`(= e_j (select a_m i))`). Three holes combined:
//!  1. `verify_array_propagation` never `register_atom`ed the propagation's
//!     literals, so the fresh verifier saw no array structure, vacuously
//!     answered Sat for VALID read-over-store propagations, and BUG(#6242)
//!     dropped them — silencing the level-0 extensionality refutation;
//!  2. the same verifier rejected valid propagations on `NeedModelEqualities`
//!     for case-split requests IRRELEVANT to the entailment (now resolved by
//!     bounded both-polarity splits);
//!  3. the wrong candidate models pinned the SAME free-base read
//!     (`select(a1, i)`) to two DIFFERENT concrete element values through two
//!     asserted select equations — an inconsistency no single-assertion ground
//!     evaluation could see (now refuted fail-closed by
//!     `conflicting_free_base_read_pins_violated`).
//!
//! These fences pin NOT-SAT on the full 8-file repro set in
//! `benchmarks/smt/regression/soundness_qf_ax/`. `unknown` is sound (the lazy
//! ArraySolver is incomplete on this family); `sat` is the soundness bug
//! returning.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// Per-file solver budget. The wrong SAT manifested in milliseconds, so a
/// short budget still catches a regression; a slow honest `unknown`/timeout
/// passes the fence.
const SOLVE_TIMEOUT_SECS: u64 = 15;

#[test]
#[ntest::timeout(300_000)]
fn test_qf_ax_swap_sf_repro_corpus_never_sat() -> Result<()> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/soundness_qf_ax");
    let mut checked = 0usize;
    for entry in std::fs::read_dir(&dir)? {
        let path = entry?.path();
        if path.extension().is_none_or(|ext| ext != "smt2") {
            continue;
        }
        let smt = std::fs::read_to_string(&path)?;
        let outcome = run_executor_smt_with_timeout(&smt, SOLVE_TIMEOUT_SECS)?;
        assert_ne!(
            outcome,
            SolverOutcome::Sat,
            "SOUNDNESS BUG: false SAT on QF_AX swap `_sf_` repro {} \
             (#qf-ax-swap-sf-false-sat; declared status: unsat)",
            path.display()
        );
        checked += 1;
    }
    assert!(
        checked >= 8,
        "expected the 8-file soundness_qf_ax repro corpus, found {checked} files in {}",
        dir.display()
    );
    Ok(())
}
