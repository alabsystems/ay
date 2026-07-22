// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "replay-jit")]

//! Phase-2 `replay-jit` wire-up test (AUDIT-2 Y6, #8789).
//!
//! Feeds a trivial UNSAT DIMACS instance + its DRAT proof to BOTH the
//! native ay-drat-check checker and the new ay-replay
//! `SequentialReplayer`, and asserts that both verdicts agree. This is
//! the same observational cross-check the `ay check drat` subcommand
//! performs when compiled with `--features replay-jit`, but expressed
//! at the library level so the test stays fast and independent of the
//! binary.
//!
//! Enabling the feature flag OFF by default is the Phase-2 correctness
//! gate: we do NOT want ay-replay's DRAT path to influence the verdict
//! of `ay check drat` in production yet. We only want to observe that
//! it agrees with the authoritative checker across well-formed inputs.

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_replay::drat::{DratReplayInput, SequentialReplayer};

/// Trivially-UNSAT DIMACS: (x) AND (-x). The empty clause is derivable
/// by propagating both units.
const TRIVIAL_UNSAT_CNF: &[u8] = b"p cnf 1 2\n1 0\n-1 0\n";
/// A valid DRAT proof: derive the empty clause. RUP-implied because
/// both units are in the formula.
const TRIVIAL_UNSAT_DRAT: &[u8] = b"0\n";

/// Multi-step UNSAT matching the shape ay emits on small pigeonhole
/// instances: four binary clauses over two variables, proof derives
/// `1`, then `-1`, then the empty clause.
const MULTI_UNSAT_CNF: &[u8] = b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
const MULTI_UNSAT_DRAT: &[u8] = b"1 0\n-1 0\n0\n";

fn native_verify(cnf: &[u8], proof: &[u8]) -> bool {
    let cnf = parse_cnf(cnf).expect("valid CNF");
    let steps = parse_drat(proof).expect("valid DRAT");
    let mut checker = DratChecker::new(cnf.num_vars, /* check_rat = */ true);
    checker.verify(&cnf.clauses, &steps).is_ok()
}

fn replay_verify(cnf: &[u8], proof: &[u8]) -> bool {
    let replayer = SequentialReplayer::new();
    let plan = replayer
        .load(&DratReplayInput { cnf, proof })
        .expect("valid CNF + DRAT");
    let outcome = replayer.replay(&plan).expect("replay");
    outcome.is_verified()
}

#[test]
fn test_replay_wire_trivial_unsat_agrees() {
    let native = native_verify(TRIVIAL_UNSAT_CNF, TRIVIAL_UNSAT_DRAT);
    let replay = replay_verify(TRIVIAL_UNSAT_CNF, TRIVIAL_UNSAT_DRAT);
    assert!(native, "native checker must verify trivial UNSAT");
    assert!(replay, "ay-replay must verify trivial UNSAT");
    assert_eq!(
        native, replay,
        "native and replay verdicts MUST agree for trivial UNSAT"
    );
}

#[test]
fn test_replay_wire_multi_step_unsat_agrees() {
    let native = native_verify(MULTI_UNSAT_CNF, MULTI_UNSAT_DRAT);
    let replay = replay_verify(MULTI_UNSAT_CNF, MULTI_UNSAT_DRAT);
    assert!(native, "native checker must verify 2-var UNSAT");
    assert!(replay, "ay-replay must verify 2-var UNSAT");
    assert_eq!(
        native, replay,
        "native and replay verdicts MUST agree for 2-var UNSAT"
    );
}

/// Exercise the cross-check's rejection branch: a SAT formula paired
/// with an empty proof is rejected by both checkers (no empty clause
/// derivable). The Phase-2 wiring logs this as "agree=true,
/// native=false, replay=false" — i.e. both paths agree the proof
/// does NOT verify.
#[test]
fn test_replay_wire_sat_with_empty_proof_agrees_on_rejection() {
    // (x OR y) — satisfiable. An empty proof cannot derive the empty
    // clause, so neither checker verifies.
    let sat_cnf: &[u8] = b"p cnf 2 1\n1 2 0\n";
    let empty_proof: &[u8] = b"";
    let native = native_verify(sat_cnf, empty_proof);
    let replay = replay_verify(sat_cnf, empty_proof);
    assert!(
        !native,
        "native checker MUST reject SAT formula with empty proof"
    );
    assert!(
        !replay,
        "ay-replay MUST reject SAT formula with empty proof"
    );
    assert_eq!(native, replay, "native and replay MUST agree on rejection");
}
