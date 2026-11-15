// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LRA `check-sat-assuming` refutations over disequality / `ite` / `or`
//! bearing queries publish `unsat` once independently certified.
//!
//! The fragile-construct gate used to turn EVERY such assumption UNSAT into
//! `unknown`: `(assert (=> p (= z x))) (assert (not (= z x)))
//! (check-sat-assuming (p))` answered `unknown` (z3: `unsat`). The gate now
//! demands a checked certificate from a disposable non-incremental probe and
//! publishes on it (`check_sat_assuming/fragile_lra_gate.rs`); the forged-
//! verdict fail-closed pins live beside the gate as unit tests.
//!
//! Every expected verdict below is z3 4.16.0's, pinned in the proof-shedding
//! posture (`--competition` / `--z3-mode`) and the default posture. Every
//! printed `get-unsat-assumptions` core was checked by z3 to be unsat with
//! the asserted formulas.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn outputs(smt: &str, competition: bool) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    let mut out = Vec::new();
    for command in &commands {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
        {
            let line = line.trim().to_owned();
            if !line.is_empty() {
                out.push(line);
            }
        }
    }
    out
}

fn assert_outputs(smt: &str, expected: &[&str]) {
    let expected: Vec<String> = expected.iter().map(|s| (*s).to_owned()).collect();
    assert_eq!(outputs(smt, true), expected, "competition posture\n{smt}");
    assert_eq!(outputs(smt, false), expected, "default posture\n{smt}");
}

const HEADER: &str = "(set-option :produce-unsat-assumptions true)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const p Bool)
(declare-const q Bool)
";

/// The reported case: one disequality, one implication, one assumption.
#[test]
#[timeout(60_000)]
fn disequality_refuted_under_assumption_is_unsat() {
    let smt = format!(
        "{HEADER}(assert (=> p (= z x)))
(assert (not (= z x)))
(check-sat-assuming (p))
(get-unsat-assumptions)
(check-sat)
"
    );
    assert_outputs(&smt, &["unsat", "(p)", "sat"]);
}

/// `distinct` over three terms, refuted by an assumed equality chain, with
/// an irrelevant second assumption left out of the core.
#[test]
#[timeout(60_000)]
fn distinct_refuted_by_assumed_equalities_is_unsat() {
    let smt = format!(
        "{HEADER}(assert (distinct x y z))
(assert (= p (= x y)))
(check-sat-assuming (q p))
(get-unsat-assumptions)
(check-sat-assuming (q))
"
    );
    assert_outputs(&smt, &["unsat", "(p)", "sat"]);
}

/// Boolean `ite` + `or` structure inside push/pop in an incremental session;
/// the refutation under the assumption must not leak into the later checks.
#[test]
#[timeout(60_000)]
fn ite_refutation_inside_a_scope_is_unsat_and_scoped() {
    let smt = format!(
        "{HEADER}(push 1)
(assert (ite q (< y x) (> y (+ x 1.0))))
(assert (or (> x 0.0) (> z 0.0)))
(assert (>= y x))
(check-sat-assuming (q))
(get-unsat-assumptions)
(check-sat)
(pop 1)
(check-sat-assuming (q))
"
    );
    assert_outputs(&smt, &["unsat", "(q)", "sat", "sat"]);
}

/// Still fail-closed: this refutation (z3: `unsat`) rests on a term-level
/// `ite` lifted under an arithmetic equality plus a disequality split, and
/// neither preprocessing clause carries proof authority today. Its only
/// certificate is `DischargedTrust` (a fresh run of the same engine
/// re-deriving `unsat`), which the gate refuses, so it stays `unknown` in both
/// postures. When those clauses gain exact proof authority this pin should
/// move to `unsat` -- never to `sat`.
#[test]
#[timeout(60_000)]
fn trust_discharge_only_refutation_stays_unknown() {
    let smt = format!(
        "{HEADER}(push 1)
(assert (or (< x 0.0) (= y (ite q x (+ x 1.0)))))
(assert (> x 0.0))
(assert (not (= y x)))
(check-sat-assuming (q))
(check-sat)
(pop 1)
(check-sat-assuming (q))
"
    );
    let verdicts = |competition: bool| -> Vec<String> {
        outputs(&smt, competition)
            .into_iter()
            .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .collect()
    };
    assert_eq!(
        verdicts(true),
        ["unknown", "sat", "sat"],
        "competition posture"
    );
    assert_eq!(
        verdicts(false),
        ["unknown", "sat", "sat"],
        "default posture"
    );
}
