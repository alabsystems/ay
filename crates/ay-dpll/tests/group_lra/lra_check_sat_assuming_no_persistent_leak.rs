// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: incremental QF_LRA answered a false `unsat` after a
//! `check-sat-assuming`, and every later check in the same scope stayed
//! `unsat`. Found by the push/pop + ite differential fuzz against z3
//! (2026-09-26).
//!
//! Root cause: when the direct assumption route returns Unknown (a
//! disequality is enough), `solve_scoped_assumptions` merges the assumption
//! literals into `ctx.assertions` and runs the plain dispatch. In incremental
//! mode that dispatch reaches the session-persistent SAT lanes
//! (`#lra-inc-engine`, persist-SAT, lazy push/pop), which encode every root
//! and add its activation unit at the current scope depth. Restoring
//! `ctx.assertions` afterwards did not retract the unit, so the assumption
//! stayed a hard constraint until the enclosing scope was popped, and at
//! depth 0 for the rest of the session. The scoped sub-solve now runs on
//! an isolated incremental-state window (`solve_scoped_window`).
//!
//! Each test pins z3's exact verdicts in both the proof-shedding posture
//! (`--competition` / `--z3-mode`, where the wrong `unsat` shipped) and the
//! default proof-carrying posture (where strict certification turned it into
//! `unknown`).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn verdicts(smt: &str, competition: bool) -> Vec<String> {
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
            if matches!(line.as_str(), "sat" | "unsat" | "unknown") {
                out.push(line);
            }
        }
    }
    out
}

fn assert_verdicts(smt: &str, expected: &[&str]) {
    let expected: Vec<String> = expected.iter().map(|s| (*s).to_owned()).collect();
    assert_eq!(verdicts(smt, true), expected, "competition posture\n{smt}");
    assert_eq!(verdicts(smt, false), expected, "default posture\n{smt}");
}

const HEADER: &str = "(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const p Bool)
(declare-const q Bool)
";

/// The minimal reproducer: one disequality, one pushed scope, one
/// assumption on an otherwise unconstrained Bool. The leaked `p` made
/// `(assert (not p))` contradictory.
#[test]
#[timeout(30_000)]
fn assumption_does_not_survive_its_query_in_a_pushed_scope() {
    let smt = format!(
        "{HEADER}(assert (not (= z x)))
(push 1)
(check-sat-assuming (p))
(assert (not p))
(check-sat)
"
    );
    assert_verdicts(&smt, &["sat", "sat"]);
}

/// At scope depth 0 in incremental mode the leaked activation was a global
/// unit: permanent for the rest of the session.
#[test]
#[timeout(30_000)]
fn assumption_does_not_become_a_global_unit_at_depth_zero() {
    let smt = format!(
        "{HEADER}(push 1)
(pop 1)
(assert (not (= z x)))
(check-sat-assuming (p))
(assert (not p))
(check-sat)
(push 1)
(assert q)
(check-sat)
(pop 1)
"
    );
    assert_verdicts(&smt, &["sat", "sat", "sat"]);
}

/// The shrunk fuzz case (`wrong_303_39`): the assumption is a Bool that
/// selects an `ite` branch, and later assertions force it the other way.
#[test]
#[timeout(30_000)]
fn ite_selector_assumption_does_not_pin_later_checks() {
    let smt = format!(
        "{HEADER}(assert (not (= z (ite q x (ite (= y 0.0) y x)))))
(push 1)
(check-sat-assuming (q))
(assert p)
(assert (= q (not p)))
(check-sat)
"
    );
    assert_verdicts(&smt, &["sat", "sat"]);
}

/// Negated and multiple assumptions, followed by an assumption query that
/// contradicts the first one. z3: sat sat sat.
#[test]
#[timeout(30_000)]
fn later_assumption_queries_see_only_their_own_literals() {
    let smt = format!(
        "{HEADER}(assert (not (= z x)))
(push 1)
(check-sat-assuming ((not p) q))
(assert p)
(assert (not q))
(check-sat)
(check-sat-assuming (p))
"
    );
    assert_verdicts(&smt, &["sat", "sat", "sat"]);
}
