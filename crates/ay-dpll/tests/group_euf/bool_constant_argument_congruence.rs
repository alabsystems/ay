// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A Bool constant as an uninterpreted-function argument, `(B false)`, next
//! to the same function applied to a Bool term whose value the search fixes,
//! `(B p)`. EUF merges each assigned Bool term into the class of its value so
//! the two applications become congruent, but it left the constants out of
//! those classes: the model then held two different values of `B` at `false`,
//! the model gate rejected it, and a satisfiable ground query ended `unknown`.
//! The constants now join their value's class structurally, in the solver and
//! in the fresh solver that re-checks each conflict alike, in a solve that
//! publishes without a proof (`--z3-mode`). The proof-carrying postures keep
//! them apart: a refutation resting on the merge yields an EUF lemma their
//! proof checker rejects, so there the satisfiable fixtures may stay
//! `unknown`.
//! Verus boxes Booleans this way, `(B true)` in a datatype field next to
//! `(B (> (%I b) 10))` from a definition (Verus fix queue, row D).
//!
//! Ground truth for every fixture was checked with z3 4.12.5.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::time::Duration;

fn verdict(smt: &str, proof_shed: bool) -> String {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    if proof_shed {
        // The CLI's `--z3-mode` posture.
        exec.set_competition_mode(true);
    }
    exec.set_timeout(Some(Duration::from_secs(20)));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    lines
        .iter()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "none".to_string())
}

const PREAMBLE: &str = "(declare-sort P 0)
(declare-fun B (Bool) P)
(declare-fun g (P) P)
(declare-fun i (P) Int)
(declare-const p Bool)
";

/// **SAT** (z3: sat): `p` is false, so `(B p)` is `(B false)` and `g` maps
/// `(B false)` to it.
const FALSE_ARGUMENT: &str = "(assert (= p (< 10 (i (B false)))))
(assert (= (i (B false)) 0))
(assert (= (g (B false)) (B p)))
(check-sat)";

/// **SAT** (z3: sat): the same with `true`.
const TRUE_ARGUMENT: &str = "(assert (= p (< 10 (i (B true)))))
(assert (= (i (B true)) 11))
(assert (= (g (B true)) (B p)))
(check-sat)";

/// **SAT** (z3: sat), found by differential fuzzing: a conflict whose
/// explanation merges `p` into the class of the constant `true` must be
/// re-provable by the fresh solver that checks it, which gets no literal for
/// the constant.
const CONFLICT_THROUGH_A_CONSTANT: &str = "(declare-const q Bool)
(assert (or (= (g (B false)) (B q)) (not (= (B q) (B true)))))
(assert (not (= (g (B true)) (B p))))
(check-sat)";

/// **UNSAT** (z3: unsat): `p` is false, so `(B p)` and `(B false)` are equal.
const FALSE_ARGUMENT_DENIED: &str = "(assert (= p (< 10 (i (B false)))))
(assert (= (i (B false)) 0))
(assert (not (= (B p) (B false))))
(check-sat)";

/// **UNSAT** (z3: unsat): the same with `true`.
const TRUE_ARGUMENT_DENIED: &str = "(assert (= p (< 10 (i (B true)))))
(assert (= (i (B true)) 11))
(assert (not (= (B p) (B true))))
(check-sat)";

#[test]
#[timeout(120_000)]
fn a_bool_constant_argument_is_congruent_with_a_term_of_its_value() {
    for (name, body) in [
        ("false", FALSE_ARGUMENT),
        ("true", TRUE_ARGUMENT),
        ("conflict through a constant", CONFLICT_THROUGH_A_CONSTANT),
    ] {
        let smt = format!("{PREAMBLE}{body}");
        let got = verdict(&smt, true);
        assert_eq!(
            got, "sat",
            "{name}: the query is satisfiable and its model is congruent"
        );
        let got = verdict(&smt, false);
        assert!(
            got != "unsat",
            "WRONG ANSWER ({name}, default posture): the query is SATISFIABLE; got {got:?}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn a_bool_constant_argument_never_hides_a_refutation() {
    for (name, body) in [
        ("false", FALSE_ARGUMENT_DENIED),
        ("true", TRUE_ARGUMENT_DENIED),
    ] {
        let smt = format!("{PREAMBLE}{body}");
        for proof_shed in [false, true] {
            let got = verdict(&smt, proof_shed);
            assert!(
                got != "sat",
                "WRONG ANSWER ({name}, proof shed: {proof_shed}): the query is UNSATISFIABLE; got {got:?}"
            );
        }
    }
}

/// **UNSAT** (z3: unsat), from differential fuzzing (gen_boolargs seed 155):
/// `b0` is true through `b2`, so `(h b0)` is `(h true)`. The default posture
/// refutes it; with Bool constants seeded, its refutation rested on an EUF
/// lemma the proof checker rejects, and it answered `unknown`.
const CONSTANT_THROUGH_AN_EQUALITY: &str = "(declare-fun h (Bool) Int)
(declare-const b0 Bool)
(declare-const b2 Bool)
(assert (= b0 b2))
(assert b2)
(assert (not (= (h b0) (h true))))
(check-sat)";

/// **SAT** (z3: sat): `CONSTANT_THROUGH_AN_EQUALITY` with `b2` false.
const CONSTANT_THROUGH_AN_EQUALITY_SAT: &str = "(declare-fun h (Bool) Int)
(declare-const b0 Bool)
(declare-const b2 Bool)
(assert (= b0 b2))
(assert (not b2))
(assert (not (= (h b0) (h true))))
(check-sat)";

#[test]
#[timeout(120_000)]
fn a_bool_constant_argument_is_refuted_in_both_postures() {
    for proof_shed in [false, true] {
        let got = verdict(CONSTANT_THROUGH_AN_EQUALITY, proof_shed);
        assert_eq!(got, "unsat", "proof shed: {proof_shed}");
        let got = verdict(CONSTANT_THROUGH_AN_EQUALITY_SAT, proof_shed);
        assert!(
            got != "unsat",
            "WRONG ANSWER (proof shed: {proof_shed}): the query is SATISFIABLE; got {got:?}"
        );
    }
}
