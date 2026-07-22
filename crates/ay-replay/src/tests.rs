// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the deterministic LRAT replayer.
//!
//! Covers:
//! - Valid LRAT proof -> `Success`
//! - Corrupted LRAT bytes -> `ReplayError::Lrat` at load, or `InvalidProof`
//!   at replay when the LRAT parses but doesn't check out.
//! - Deterministic replay: same input yields the same outcome twice.

use super::*;

/// Trivial UNSAT CNF: (x) AND (-x). LRAT derives the empty clause from the
/// two originals (ids 1 and 2) at derived id 3.
const UNSAT_CNF: &[u8] = b"p cnf 1 2\n1 0\n-1 0\n";
const UNSAT_LRAT: &[u8] = b"3 0 1 2 0\n";

/// Slightly larger UNSAT: (a OR b), (a OR -b), (-a OR b), (-a OR -b).
/// ay/drat-trim style LRAT with intermediate derivations.
const UNSAT_CNF_2: &[u8] = b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
/// 5: a    from 1,2 (unit propagate)
/// 6: -a   from 3,4
/// 7: empty from 5,6
const UNSAT_LRAT_2: &[u8] = b"5 1 0 1 2 0\n6 -1 0 3 4 0\n7 0 5 6 0\n";

#[test]
fn valid_lrat_produces_success() {
    let mut replayer = DeterministicReplayer::new();
    let plan = replayer
        .load_lrat(&ReplayInput {
            cnf: UNSAT_CNF,
            proof: UNSAT_LRAT,
        })
        .expect("valid LRAT should parse");
    assert_eq!(plan.num_vars, 1);
    assert_eq!(plan.originals.len(), 2);
    assert_eq!(plan.add_step_count(), 1);

    let outcome = replayer.replay(&plan);
    assert!(outcome.is_success(), "expected Success, got {outcome}");
    if let ReplayOutcome::Success { trace } = outcome {
        assert_eq!(trace.steps_replayed, 1);
        assert_eq!(trace.checker_stats.originals, 2);
        assert!(trace.checker_stats.derived >= 1);
        assert_eq!(trace.checker_stats.failures, 0);
    }
}

#[test]
fn valid_multi_step_lrat_produces_success() {
    let mut replayer = DeterministicReplayer::new();
    let plan = replayer
        .load_lrat(&ReplayInput {
            cnf: UNSAT_CNF_2,
            proof: UNSAT_LRAT_2,
        })
        .expect("multi-step LRAT should parse");
    assert_eq!(plan.num_vars, 2);
    assert_eq!(plan.originals.len(), 4);
    assert_eq!(plan.add_step_count(), 3);

    let outcome = replayer.replay(&plan);
    assert!(outcome.is_success(), "expected Success, got {outcome}");
}

#[test]
fn corrupted_lrat_fails_to_load() {
    // Not a number, not a comment, not 'd' -> text LRAT parser rejects.
    let bad_proof = b"banana\n";
    let mut replayer = DeterministicReplayer::new();
    let err = replayer
        .load_lrat(&ReplayInput {
            cnf: UNSAT_CNF,
            proof: bad_proof,
        })
        .expect_err("corrupted LRAT must not load");
    matches_lrat_err(&err);
}

#[test]
fn parseable_but_unsound_lrat_reports_invalid_proof() {
    // LRAT parses cleanly but the hints don't actually yield a conflict:
    // derive the empty clause claiming hint `1` (the unit `x`) is enough,
    // which does NOT falsify to empty without hint `2` (-x).
    let bogus_lrat = b"3 0 1 0\n";
    let mut replayer = DeterministicReplayer::new();
    let plan = replayer
        .load_lrat(&ReplayInput {
            cnf: UNSAT_CNF,
            proof: bogus_lrat,
        })
        .expect("bogus LRAT still parses");
    let outcome = replayer.replay(&plan);
    match outcome {
        ReplayOutcome::InvalidProof(_) => {}
        other => panic!("expected InvalidProof, got {other}"),
    }
}

#[test]
fn deterministic_replay_same_output_twice() {
    let mut replayer = DeterministicReplayer::new();
    let plan = replayer
        .load_lrat(&ReplayInput {
            cnf: UNSAT_CNF_2,
            proof: UNSAT_LRAT_2,
        })
        .expect("valid LRAT");

    let first = replayer.replay(&plan);
    let second = replayer.replay(&plan);
    assert!(first.is_success());
    assert!(second.is_success());

    // Compare trace contents by reformatting -- Stats is not PartialEq in the
    // public API so we check field-by-field.
    if let (ReplayOutcome::Success { trace: t1 }, ReplayOutcome::Success { trace: t2 }) =
        (&first, &second)
    {
        assert_eq!(t1.steps_replayed, t2.steps_replayed);
        assert_eq!(t1.checker_stats.originals, t2.checker_stats.originals);
        assert_eq!(t1.checker_stats.derived, t2.checker_stats.derived);
        assert_eq!(t1.checker_stats.rup_ok, t2.checker_stats.rup_ok);
        assert_eq!(t1.checker_stats.failures, t2.checker_stats.failures);
    }
}

#[test]
fn deterministic_across_replayer_instances() {
    let input = ReplayInput {
        cnf: UNSAT_CNF_2,
        proof: UNSAT_LRAT_2,
    };
    let mut r1 = DeterministicReplayer::new();
    let mut r2 = DeterministicReplayer::new();
    let p1 = r1.load_lrat(&input).expect("valid");
    let p2 = r2.load_lrat(&input).expect("valid");
    let o1 = r1.replay(&p1);
    let o2 = r2.replay(&p2);
    assert_eq!(o1.is_success(), o2.is_success());
}

#[test]
fn free_function_load_plan_matches_trait() {
    let input = ReplayInput {
        cnf: UNSAT_CNF,
        proof: UNSAT_LRAT,
    };
    let via_free = load_plan(&input).expect("free fn");
    let mut via_trait = DeterministicReplayer::new();
    let via_trait_plan = via_trait.load_lrat(&input).expect("trait");
    assert_eq!(via_free.num_vars, via_trait_plan.num_vars);
    assert_eq!(via_free.step_count(), via_trait_plan.step_count());
    assert_eq!(via_free.binary, via_trait_plan.binary);
}

#[test]
fn degenerate_cnf_is_rejected() {
    let empty_cnf = b"p cnf 0 0\n";
    let err = load_plan(&ReplayInput {
        cnf: empty_cnf,
        proof: UNSAT_LRAT,
    })
    .expect_err("must reject zero-clause CNF");
    assert!(matches!(err, ReplayError::DegenerateCnf { .. }));
}

#[track_caller]
fn matches_lrat_err(err: &ReplayError) {
    match err {
        ReplayError::Lrat(_) => {}
        other => panic!("expected ReplayError::Lrat, got {other:?}"),
    }
}
