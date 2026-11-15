// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A query must leave the session's proof configuration exactly as it found
//! it, so a resident session decides every query as a fresh process does.
//!
//! Parsed-assertion retention selects the certification funnel's lanes. When a
//! `check-sat` switched it on (the public-solve boundary), or a lane borrowed it
//! and did not hand it back (the quantified trace retry, the non-string
//! sequence corroboration), the same query certified through different lanes
//! depending on what the session had solved before, and where those lanes
//! disagree the verdict flipped between `unsat` and
//! `unknown (incomplete self-check-rejected)`.

use super::Executor;
use ay_frontend::parse;

/// The session configuration of the `ay --incremental` CLI for a session that
/// emits no proof artifact: retention off, budgeted best-effort reconstruction.
const CLI_STDIN_BUDGET: u64 = 1_000_000;

fn cli_stdin_session(competition: bool) -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.set_retain_parsed_assertions(false);
    exec.set_proof_reconstruction_step_budget(Some(CLI_STDIN_BUDGET));
    exec
}

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).expect("parse");
    exec.execute_all(&commands).expect("execute")
}

/// `benchmarks/smt/QF_LIA/system_03.smt2`: `unsat` as the first query of an
/// `ay --incremental` session, `unknown (incomplete self-check-rejected)` after
/// any earlier `check-sat` while the public-solve boundary re-armed retention.
const SYSTEM_03: &str = r"
    (set-logic QF_LIA)
    (declare-fun v0 () Int)
    (declare-fun v1 () Int)
    (declare-fun v2 () Int)
    (declare-fun v3 () Int)
    (assert (<= (+ (* -4 v0) (* -2 v1) (* -4 v2) (* 3 v3)) 47))
    (assert (= (+ (* 4 v0) (* 4 v1) (* 4 v2) (* -2 v3)) 49))
    (assert (<= (+ (* 1 v0) (* 2 v1) (* 2 v2) (* -1 v3)) 25))
    (assert (= (+ (* -1 v0) (* 4 v1) (* 4 v2) (* -5 v3)) 28))
    (assert (= (+ (* -4 v0) (* -2 v1) (* 5 v2) (* -2 v3)) -17))
    (assert (>= (+ (* -4 v0) (* -3 v1) (* -2 v2) (* -3 v3)) 20))
    (check-sat)
";

/// A public solve never changes retention, in either posture: the query after
/// `(reset)` retains exactly what the first query retained.
#[test]
fn a_public_solve_leaves_the_session_proof_configuration_unchanged() {
    const QUERY: &str = "(set-logic QF_UF) (declare-const p Bool) (assert p) (check-sat)";
    for competition in [false, true] {
        let mut exec = cli_stdin_session(competition);
        let configured = exec.session_proof_configuration();
        run(&mut exec, QUERY);
        let first_retained = exec.context().assertions_parsed().len();
        assert_eq!(
            exec.session_proof_configuration(),
            configured,
            "competition={competition}: the first check-sat changed the session configuration"
        );
        run(&mut exec, "(reset)");
        run(&mut exec, QUERY);
        assert_eq!(
            exec.context().assertions_parsed().len(),
            first_retained,
            "competition={competition}: the second query retained differently from the first"
        );
        assert_eq!(exec.session_proof_configuration(), configured);
    }
}

/// The measured verdict flip: the same query, first in the session and after
/// an earlier (empty) `check-sat`.
#[test]
fn system_03_verdict_does_not_depend_on_an_earlier_check_sat() {
    let mut first = cli_stdin_session(false);
    let first_outputs = run(&mut first, SYSTEM_03);
    assert_eq!(first_outputs, ["unsat"], "first query of the session");

    let mut later = cli_stdin_session(false);
    let later_outputs = run(&mut later, &format!("(check-sat) (reset) {SYSTEM_03}"));
    assert_eq!(
        later_outputs,
        ["sat", "unsat"],
        "after an earlier check-sat the same query must still be unsat"
    );
}

/// `(set-option :produce-proofs true)` is script state: after `(reset)` the
/// next query is decided with the host's configuration.
#[test]
fn a_reset_script_proof_option_does_not_reach_the_next_query() {
    let mut fresh = cli_stdin_session(false);
    run(
        &mut fresh,
        "(set-logic QF_UF) (declare-const p Bool) (assert p)",
    );

    let mut reused = cli_stdin_session(false);
    run(&mut reused, "(set-option :produce-proofs true) (reset)");
    run(
        &mut reused,
        "(set-logic QF_UF) (declare-const p Bool) (assert p)",
    );
    assert_eq!(
        reused.context().assertions_parsed().len(),
        fresh.context().assertions_parsed().len()
    );
    assert_eq!(
        reused.context().retains_parsed_assertions(),
        fresh.context().retains_parsed_assertions()
    );

    let mut after = cli_stdin_session(false);
    let outputs = run(
        &mut after,
        &format!("(set-option :produce-proofs true) (reset) {SYSTEM_03}"),
    );
    assert_eq!(outputs, ["unsat"]);
}

/// The quantified trace retry (competition mode) borrows retention and a
/// reconstruction budget for its one query and hands both back.
#[test]
fn quantified_trace_retry_hands_back_the_borrowed_configuration() {
    const SCRIPT: &str = r"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun a () Real)
        (assert (< 0.0 a))
        (assert (not (< 0.0 (f a))))
        (assert (forall ((x Real)) (=> (< 0.0 x) (< 0.0 (f x)))))
        (check-sat)
    ";
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let configured = exec.session_proof_configuration();
    // `competition_mode_publishes_an_instantiation_driven_quantified_unsat`
    // pins that this `unsat` exists only through the retry.
    assert_eq!(run(&mut exec, SCRIPT), ["unsat"]);
    assert_eq!(
        exec.session_proof_configuration(),
        configured,
        "the retry must restore retention and budget"
    );
    let outputs = run(&mut exec, &format!("(reset) {SCRIPT}"));
    assert_eq!(
        outputs,
        ["unsat"],
        "the retried query must decide the same way again"
    );
    assert_eq!(exec.session_proof_configuration(), configured);
}

/// The non-string sequence corroboration re-solves with proofs forced on and
/// must hand back the session's own retention and budget, whichever they were.
#[test]
fn nonstring_sequence_corroboration_hands_back_the_borrowed_configuration() {
    const SCRIPT: &str = r"
        (set-logic ALL)
        (declare-const s (Seq Int))
        (declare-const x Int)
        (assert (= (seq.len s) x))
        (assert (> x 5))
        (assert (< x 3))
        (check-sat)
    ";
    for retain in [true, false] {
        let mut exec = Executor::new();
        exec.set_retain_parsed_assertions(retain);
        exec.set_proof_reconstruction_step_budget(Some(CLI_STDIN_BUDGET));
        let configured = exec.session_proof_configuration();
        assert_eq!(run(&mut exec, SCRIPT), ["unsat"], "retain={retain}");
        assert_eq!(
            exec.session_proof_configuration(),
            configured,
            "retain={retain}: the corroboration must restore retention and budget"
        );
    }
}
