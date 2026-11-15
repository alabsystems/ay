// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A QSAT route `sat` the SAT emission's gate refuses (`qsat_route/
//! refused_sat.rs`), on a closed alternation under a demanded certificate
//! (`:produce-proofs`).
//!
//! `∀q ∃r. r > q` is true (take `r = q + 1`), so `sat`. The game decides it
//! `sat`, but the gate's strategy route cannot confirm it with a strict proof
//! (its ground refutation of `¬(q < q + 1)` has none), and the route's
//! handed-off `sat` used to end the query `unknown`, with the legacy lanes
//! that decide it stood down. `∀q ∃r. r > q ∧ r < q` is false (no `r` is on
//! both sides of `q`), so `unsat`: the control, so that answering `sat` for
//! every closed alternation cannot pass.
//!
//! The control does NOT reach the re-solve: the route publishes that `unsat`
//! itself (`qsat.publish` `unsat-expansion`); only a game `sat` the gate
//! refuses enters `qsat_refused_sat_resolve`, and no natural `unsat` formula
//! produces one. The verdicts alone therefore cannot show that the `sat` test
//! still exercises that path: a route that stopped handing this `sat` to the
//! emission would leave the public verdict and the game's verdict as they are
//! (the legacy lanes answer `sat`) and the re-solve untested. So the `sat`
//! test also pins what the path records: the gate refused the route's `sat`
//! (`qsat.publish` `sat-gate-refused`), the query was solved exactly once
//! more (`qsat.refused_sat_resolves` 1), and the answer is a `sat` the
//! independent model gate confirmed (`model_check_gate.result`
//! `confirmed-sat`; the re-solve resets the statistics, so that is its own
//! emission's result).

use std::time::Duration;

use crate::Executor;
use ay_frontend::parse;

/// Wall cap per test query; generous so load cannot flip a verdict.
const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

/// What one closed alternation's solve reported.
struct ClosedAlternation {
    /// The public verdict.
    verdict: String,
    /// The game's verdict (`qsat.verdict`).
    engine: Option<String>,
    /// What the route published (`qsat.publish`).
    publish: Option<String>,
    /// Re-solves after a refused route `sat` (`qsat.refused_sat_resolves`).
    resolves: Option<u64>,
    /// The independent model gate's result (`model_check_gate.result`).
    gate: Option<String>,
}

/// The closed `∀q:Int. ∃r:Int. body` under `logic` with `:produce-proofs`.
fn solve_closed_alternation(logic: &str, body: &str) -> ClosedAlternation {
    let smt = format!(
        "(set-option :produce-proofs true)(set-logic {logic})\
         (assert (forall ((q Int)) (exists ((r Int)) {body})))(check-sat)"
    );
    let commands = parse(&smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    let verdict = outputs
        .iter()
        .rev()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_default();
    ClosedAlternation {
        verdict,
        engine: text("qsat.verdict"),
        publish: text("qsat.publish"),
        resolves: stats.get_int("qsat.refused_sat_resolves"),
        gate: text("model_check_gate.result"),
    }
}

/// The game decides the closed alternation, and the answer is its verdict;
/// `check` then holds the solve to the path it must have taken.
fn assert_closed_alternation_under_proofs(
    body: &str,
    expected: &str,
    check: fn(&str, &ClosedAlternation),
) {
    for logic in ["LIA", "ALL"] {
        let solve = solve_closed_alternation(logic, body);
        let publish = &solve.publish;
        assert_eq!(
            solve.engine.as_deref(),
            Some(expected),
            "{logic} {body}: the game decides it (publish={publish:?})"
        );
        assert_eq!(
            solve.verdict, expected,
            "{logic} {body}: verdict (publish={publish:?})"
        );
        check(logic, &solve);
    }
}

#[test]
fn closed_alternation_under_produce_proofs_is_sat() {
    assert_closed_alternation_under_proofs("(> r q)", "sat", |logic, solve| {
        assert_eq!(
            solve.publish.as_deref(),
            Some("sat-gate-refused"),
            "{logic}: the gate refused the route's `sat`"
        );
        assert_eq!(
            solve.resolves,
            Some(1),
            "{logic}: the refused `sat` was solved once more"
        );
        assert_eq!(
            solve.gate.as_deref(),
            Some("confirmed-sat"),
            "{logic}: the re-solve's `sat` passed the model gate (publish={:?})",
            solve.publish
        );
    });
}

#[test]
fn false_closed_alternation_under_produce_proofs_is_unsat() {
    assert_closed_alternation_under_proofs("(and (> r q) (< r q))", "unsat", |logic, solve| {
        assert_eq!(
            solve.resolves, None,
            "{logic}: a route `unsat` never enters the refused-sat re-solve (publish={:?})",
            solve.publish
        );
    });
}
