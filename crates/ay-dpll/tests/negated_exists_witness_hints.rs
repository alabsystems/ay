// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Negated-existential obligations whose refuting witness is NOT an authored
//! subterm must still certify `unsat` in the embedder posture
//! (#negated-exists-cegqi-witness-hints).
//!
//! Embedder posture (deductive-checks, `encoder/mod.rs` `with_logic` + `with_limits`):
//! unsat cores ON, proofs OFF, a 30 s command deadline; every fixture is a
//! query deductive-checks's regression harnesses raised and z3 answers `unsat` on
//! (`C_quantifiers`, `C_quantifiers_recommends`, `C_seqs`). Before the fix
//! each came back `unknown` in well under a second: CEGQI found the witness
//! (`301`, or the positive existential's Skolem constant), the inner solve
//! was UNSAT, and mandatory authored-scope certification declined because the
//! negated-exists lane's only witness source was the authored ground scan,
//! which never descends under a binder — and on the named-core route the lane
//! was not consulted at all.

use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, SolveResult, Solver};
use ntest::timeout;

const EMBEDDER_WALL: Duration = Duration::from_secs(30);

fn embedder_solver(named_cores: bool) -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver constructs");
    solver.set_produce_unsat_cores(named_cores);
    solver.set_timeout(Some(EMBEDDER_WALL));
    solver
}

fn assert_certified_unsat(name: &str, named_cores: bool, input: &str) {
    let mut solver = embedder_solver(named_cores);
    solver.parse_smtlib2(input).expect("fixture parses");
    let started = Instant::now();
    let details = solver.check_sat_with_details();
    let elapsed = started.elapsed();
    let verdict = details
        .result
        .accept_for_consumer()
        .unwrap_or_else(|error| panic!("{name}: consumer acceptance failed: {error:?}"))
        .clone();
    assert!(
        matches!(verdict, SolveResult::Unsat(_)),
        "{name}: expected the certified unsat, got {verdict:?} (reason {:?}) after {elapsed:?}",
        details.unknown_reason
    );
    assert_eq!(details.unknown_reason, None, "{name}");
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{name}: the published unsat must carry the strict certification: {:?}",
        details.verification
    );
    if !cfg!(debug_assertions) {
        assert!(
            elapsed < EMBEDDER_WALL,
            "{name}: verdict must arrive inside the command deadline, took {elapsed:?}"
        );
    }
    if named_cores {
        let core = solver
            .try_get_unsat_core()
            .unwrap_or_else(|error| panic!("{name}: core must be readable: {error:?}"));
        assert!(!core.is_empty(), "{name}: the named core must not be empty");
    }
}

/// `C_quantifiers` `assertion_1`: `(not (exists i. 0 <= i < 2^32 ∧ 300 < i))`
/// beside a BV ground fact — no authored `Int` term outside the body.
#[test]
#[timeout(300_000)]
fn quantifiers_not_exists_certifies_unsat_on_the_named_core_route() {
    assert_certified_unsat(
        "quantifiers_not_exists",
        true,
        include_str!("fixtures/deductive_checks_quantifiers_not_exists_named_core.smt2"),
    );
}

/// `C_quantifiers_recommends` `assertion_1`: identical modulo `:named`.
#[test]
#[timeout(300_000)]
fn quantifiers_recommends_not_exists_certifies_unsat_on_the_named_core_route() {
    assert_certified_unsat(
        "quantifiers_recommends_not_exists",
        true,
        include_str!("fixtures/deductive_checks_quantifiers_recommends_not_exists_named_core.smt2"),
    );
}

/// `C_seqs` `assertion_0` (both arch widths): `seq_contains` asserted and
/// denied over a BV-indexed array; the witness is the positive existential's
/// Skolem constant.
#[test]
#[timeout(300_000)]
fn seqs_contains_both_sides_certifies_unsat_on_the_named_core_route() {
    assert_certified_unsat(
        "seqs_contains_both_sides",
        true,
        include_str!("fixtures/deductive_checks_seqs_contains_both_sides_named_core.smt2"),
    );
}

/// `C_seqs` `test1_seq_to_set_contains_matches_source_contains_variable`:
/// the needle is a declared constant, so the consequence-replay probe must
/// not substitute it away (`proof_probe_skips_varsubst`).
#[test]
#[timeout(300_000)]
fn seqs_contains_symbolic_needle_certifies_unsat_on_the_named_core_route() {
    assert_certified_unsat(
        "seqs_contains_symbolic_needle",
        true,
        include_str!("fixtures/deductive_checks_seqs_contains_needle_named_core.smt2"),
    );
}

/// The same shapes on the plain `check-sat` route, minimized.
#[test]
#[timeout(300_000)]
fn minimized_shapes_certify_unsat_on_the_plain_route() {
    assert_certified_unsat(
        "q_two_lo",
        false,
        "(set-logic ALL)\n(assert (not (exists ((i Int)) (and (<= 0 i) (< 300 i)))))\n",
    );
    assert_certified_unsat(
        "s_pure",
        false,
        "(set-logic ALL)\n(declare-const n Int)\n\
         (assert (exists ((i Int)) (and (<= 0 i) (< i n))))\n\
         (assert (not (exists ((j Int)) (and (<= 0 j) (< j n)))))\n",
    );
    assert_certified_unsat(
        "n_needle_int",
        false,
        "(set-logic ALL)\n(declare-const needle Int)\n(declare-const n Int)\n\
         (declare-const s (Array Int Int))\n\
         (assert (exists ((i Int)) (and (<= 0 i) (< i n) (= needle (select s i)))))\n\
         (assert (not (exists ((j Int)) (and (<= 0 j) (< j n) (= needle (select s j))))))\n",
    );
    assert_certified_unsat(
        "s_bv_idx",
        false,
        "(set-logic ALL)\n(declare-const n Int)\n\
         (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))\n\
         (assert (exists ((i Int)) (and (<= 0 i) (< i n) (= #x00000005 (select s ((_ int2bv 64) i))))))\n\
         (assert (not (exists ((j Int)) (and (<= 0 j) (< j n) (= #x00000005 (select s ((_ int2bv 64) j)))))))\n",
    );
}

/// Control: a wrong witness is not a refutation — the satisfiable sibling
/// (`i <= 300` is witnessed by 0) stays `sat`.
#[test]
#[timeout(300_000)]
fn the_satisfiable_sibling_stays_sat() {
    let mut solver = embedder_solver(true);
    solver
        .parse_smtlib2(
            "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n\
             (assert (! (not (exists ((i Int)) (and (<= 0 i) (< i 4294967296) (< 300 i) (< i 200)))) :named dn0))\n",
        )
        .expect("fixture parses");
    let details = solver.check_sat_with_details();
    let verdict = details
        .result
        .accept_for_consumer()
        .expect("consumer acceptance")
        .clone();
    assert!(
        matches!(verdict, SolveResult::Sat),
        "no i satisfies 300 < i < 200: the negated existential is true, got {verdict:?} ({:?})",
        details.unknown_reason
    );
}
