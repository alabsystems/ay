// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`SequentialReplayer`].
//!
//! Covers:
//! - Trivial UNSAT DRAT replays cleanly.
//! - Non-UNSAT DRAT (no empty clause) reports `verified = false`.
//! - Corrupted DRAT bytes fail at parse.
//! - Manual multi-step DRAT trace (derive `a` then `-a` then empty) replays
//!   cleanly — this is the PHP(3,2)-style proof shape without needing the
//!   ay binary, so it stays pure-unit. The end-to-end ay-binary replay +
//!   wall-clock comparison lives in
//!   `crates/ay/tests/group_cli/replay_php32_8796.rs` where
//!   `CARGO_BIN_EXE_ay` is available.

use super::*;

/// Trivial UNSAT: `(x)` AND `(-x)`. A valid DRAT proof just contains the
/// empty clause — both units are already in the original formula, so BCP
/// immediately conflicts.
const UNSAT_CNF: &[u8] = b"p cnf 1 2\n1 0\n-1 0\n";
const UNSAT_DRAT: &[u8] = b"0\n";

/// Multi-step UNSAT: (a OR b), (a OR -b), (-a OR b), (-a OR -b). Derives
/// `a`, then `-a`, then the empty clause — the same step shape ay produces
/// on small pigeonhole instances.
const MULTI_CNF: &[u8] = b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
/// DRAT: add unit `1` (RUP from 1,2 resolution-shadow), then unit `-1`
/// (RUP from 3,4), then the empty clause (RUP from units).
const MULTI_DRAT: &[u8] = b"1 0\n-1 0\n0\n";

#[test]
fn trivial_unsat_drat_verifies() {
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: UNSAT_CNF,
            proof: UNSAT_DRAT,
        })
        .expect("valid DRAT should parse");
    assert_eq!(plan.num_vars, 1);
    assert_eq!(plan.originals.len(), 2);
    assert_eq!(plan.add_step_count(), 1);

    let outcome = replayer.replay(&plan).expect("replay");
    assert!(
        outcome.is_verified(),
        "expected verified, got {outcome} (reason={:?})",
        outcome.failure_reason
    );
    assert_eq!(outcome.add_steps_verified, 1);
}

#[test]
fn corrupted_drat_fails_to_load() {
    // Non-numeric tokens are rejected by the text DRAT parser.
    let bad_proof = b"banana\n";
    let replayer = SequentialReplayer::new();
    let err = replayer
        .load(&DratReplayInput {
            cnf: UNSAT_CNF,
            proof: bad_proof,
        })
        .expect_err("corrupted DRAT must not load");
    matches!(err, DratReplayError::Drat(_));
}

#[test]
fn degenerate_cnf_is_rejected() {
    let empty_cnf = b"p cnf 0 0\n";
    let replayer = SequentialReplayer::new();
    let err = replayer
        .load(&DratReplayInput {
            cnf: empty_cnf,
            proof: UNSAT_DRAT,
        })
        .expect_err("must reject zero-clause CNF");
    assert!(matches!(err, DratReplayError::DegenerateCnf { .. }));
}

#[test]
fn non_conflicting_drat_reports_unverified() {
    // (x OR y) — satisfiable. A DRAT proof claiming the empty clause without
    // any derivation steps is not a valid refutation.
    let sat_cnf = b"p cnf 2 1\n1 2 0\n";
    // An empty proof: no steps at all. The checker will not derive the empty
    // clause (since the formula is SAT), so conclude_unsat should fail.
    let empty_proof = b"";
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: sat_cnf,
            proof: empty_proof,
        })
        .expect("load");
    let outcome = replayer.replay(&plan).expect("replay");
    assert!(
        !outcome.is_verified(),
        "SAT formula with empty proof must NOT verify, got {outcome}"
    );
    assert!(outcome.failure_reason.is_some());
}

#[test]
fn deterministic_replay_same_output_twice() {
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: UNSAT_CNF,
            proof: UNSAT_DRAT,
        })
        .expect("load");
    let o1 = replayer.replay(&plan).expect("replay #1");
    let o2 = replayer.replay(&plan).expect("replay #2");
    assert_eq!(o1.verified, o2.verified);
    assert_eq!(o1.add_steps_verified, o2.add_steps_verified);
    assert_eq!(o1.stats.additions, o2.stats.additions);
    assert_eq!(o1.stats.original, o2.stats.original);
}

#[test]
fn multi_step_drat_verifies() {
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: MULTI_CNF,
            proof: MULTI_DRAT,
        })
        .expect("load multi-step DRAT");
    assert_eq!(plan.num_vars, 2);
    assert_eq!(plan.originals.len(), 4);
    assert_eq!(plan.add_step_count(), 3);

    let outcome = replayer.replay(&plan).expect("replay");
    assert!(
        outcome.is_verified(),
        "multi-step DRAT must verify: {outcome} (reason={:?})",
        outcome.failure_reason
    );
    assert_eq!(outcome.add_steps_verified, 3);
    // conclude_unsat fires because the empty clause was derived: `stats.additions`
    // counts every derived-clause attempt, regardless of outcome.
    assert_eq!(outcome.stats.additions, 3);
}

#[test]
fn execution_profile_marks_conclusion_boundary() {
    let proof_with_tail = b"1 0\n-1 0\n0\nd 1 0\n";
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: MULTI_CNF,
            proof: proof_with_tail,
        })
        .expect("load DRAT with post-conclusion tail");

    assert_eq!(plan.execution_profile.concluding_empty_clause_step, Some(2));
    assert_eq!(plan.replay_step_limit(), 3);
    assert_eq!(plan.execution_profile.trailing_steps_skipped, 1);
}

#[test]
fn replay_skips_post_conclusion_steps() {
    let proof_with_tail = b"1 0\n-1 0\n0\nd 1 0\nd -1 0\n";
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput {
            cnf: MULTI_CNF,
            proof: proof_with_tail,
        })
        .expect("load DRAT with post-conclusion tail");

    let outcome = replayer.replay(&plan).expect("replay");

    assert!(
        outcome.is_verified(),
        "post-conclusion tail should not affect verification: {outcome:?}"
    );
    assert_eq!(outcome.steps_replayed, 3);
    assert_eq!(outcome.add_steps_verified, 3);
    assert_eq!(outcome.delete_steps_applied, 0);
    assert_eq!(outcome.trailing_steps_skipped, 2);
}
