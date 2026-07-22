// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UFLIA combiner-level finite-domain rescue completeness fence
//! (#uflia-fd-rescue, main b74e7c84a9; retriggered by the hybrid rewiring).
//!
//! On a UFLIA armed re-solve (after the independent gate refutes the
//! first-pass model for a UF function-graph violation), the combiner tries a
//! bounded finite-domain model of the current assignment with UF congruence
//! Ackermannized in, and — on success — installs it as LIA's
//! `direct_enum_witness` so the fall-through `Sat` materializes that
//! congruence-consistent model, re-validated by the same independent gate.
//!
//! `hash_sat_04_06` (mathsat Hash SAT family) is genuinely satisfiable
//! (`:status sat`). HISTORY of this fence: while the hybrid arm router and
//! the congruence-repair arming were unwired (the 2026-07-17 descendant
//! merge), the armed re-solve never ran, the first-pass invalid model was
//! quarantined by the gate, and this fence pinned the sound fail-closed
//! `unknown`. With the router rewired (#detour-snapshot-extend campaign:
//! `solve_uf_lia` marks `uflia_congruence_lane`, every arm forwards
//! `arm_uflia_congruence_repair` into the combiner, and `check_sat_guarded`'s
//! retry-once consumer re-solves on a gate rejection), the repair pass
//! case-splits the coincident argument values and the re-solve produces a
//! model the SAME independent gate ACCEPTS — the expected outcome is `sat`
//! again, through the unchanged single SAT-emission chokepoint (a stderr
//! invalid-model banner from the refuted FIRST pass is expected and correct).
//!
//! `unsat` remains an outright soundness bug at any time.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

const SOLVE_TIMEOUT_SECS: u64 = 15;

#[test]
#[ntest::timeout(60_000)]
fn test_uflia_fd_rescue_hash_sat_04_06_recovers_validated_sat() -> Result<()> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/uflia_fd_rescue/hash_sat_04_06_fd_rescue.smt2");
    let smt = std::fs::read_to_string(&path)?;
    let outcome = run_executor_smt_with_timeout(&smt, SOLVE_TIMEOUT_SECS)?;
    // Soundness: a genuinely-SAT file (`:status sat`) must never be refuted.
    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG: wrong UNSAT on genuinely-SAT hash_sat_04_06 \
         (#uflia-fd-rescue; declared status: sat) — {}",
        path.display()
    );
    // With the congruence-repair retry seam rewired, the armed re-solve must
    // recover a gate-VALIDATED sat (the +12 Hash SAT family behavior). A
    // fail-closed `unknown` here means the retry seam regressed (the lane
    // marker, the combiner arming, or the retry-once consumer) — exactly the
    // silent unwiring this fence exists to catch.
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "hash_sat_04_06 must recover a gate-validated sat via the armed \
         congruence-repair re-solve; got {outcome:?}. See #uflia-fd-rescue \
         and #uflia-cong-repair-arm."
    );
    Ok(())
}
