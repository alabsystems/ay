// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the lane's affine route (#qmv-affine-route), in the
//! CLI's default posture (the best-effort proof sidecar) unless a test says
//! otherwise. A publishing assertion also reads `eq_qe.affine_roots` and
//! `eq_qe.gate`, so a `sat` the legacy path reached cannot pass for the
//! route's.

use std::time::Duration;

use ay_frontend::parse;

use crate::Executor;

const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

/// The CLI's default reconstruction budget is irrelevant here; any budget
/// puts the executor in the default (proof-carrying, best-effort) posture.
const PROOF_STEP_BUDGET: u64 = 1_000_000;

struct RouteRun {
    verdicts: Vec<String>,
    affine_roots: Option<u64>,
    gate: Option<String>,
    /// `model_check_gate.quantified`: what the published `sat` rests on.
    quantified_authority: Option<String>,
}

fn run_default_posture(smt: &str) -> RouteRun {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_best_effort_produce_proofs(PROOF_STEP_BUDGET);
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    RouteRun {
        verdicts: outputs
            .iter()
            .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .collect(),
        affine_roots: stats.get_int("eq_qe.affine_roots"),
        gate: stats.get_string("eq_qe.gate").map(str::to_string),
        quantified_authority: stats
            .get_string("model_check_gate.quantified")
            .map(str::to_string),
    }
}

fn assert_route_published_sat(name: &str, smt: &str) {
    let run = run_default_posture(smt);
    assert_eq!(run.verdicts, ["sat"], "{name}");
    assert_eq!(
        run.affine_roots,
        Some(1),
        "{name}: the affine route must see the root"
    );
    assert_eq!(
        run.gate.as_deref(),
        Some("confirmed"),
        "{name}: the quantified model gate must confirm the authored root"
    );
}

/// t1: `∀v. c·v − v = 0` holds exactly at `c = 1`. Base (default posture)
/// answered `unknown (incomplete)` after ~12 s in the NIA ground solve of the
/// CEGQI counterexample lemma; `--z3-mode` and z3 answer `sat`.
const T1: &str = "(set-logic ALL)(declare-fun c () Int)\
    (assert (forall ((v Int)) (= (+ (* c v) (* (- 1) v)) 0)))(check-sat)";

/// t6: `∀v. 0·v = c·v` holds exactly at `c = 0`.
const T6: &str = "(set-logic ALL)(declare-fun c () Int)\
    (assert (forall ((v Int)) (= (* 0 v) (* c v))))(check-sat)";

/// t2: the coefficient is an array read, `∀v. A[a]·v − v = 0`.
const T2: &str = "(set-logic ALL)(declare-fun A () (Array Int Int))(declare-fun a () Int)\
    (assert (forall ((v Int)) (= (+ (* (select A a) v) (* (- 1) v)) 0)))(check-sat)";

/// The differential gate's `w1_51` shape: a vacuous `∃w` over the universal,
/// an array-read coefficient, and a ground UF sibling.
const W1_51: &str = "(set-logic ALL)(declare-fun A () (Array Int Int))(declare-fun a () Int)\
    (declare-fun f (Int) Int)\
    (assert (exists ((w Int)) (forall ((v Int)) (= (+ (* (select A a) v) (* (- 1) v)) 0))))\
    (assert (= (f a) 0))(check-sat)";

#[test]
fn affine_universal_over_a_free_constant_is_published_sat() {
    assert_route_published_sat("t1", T1);
    assert_route_published_sat("t6", T6);
}

#[test]
fn affine_universal_over_an_array_read_is_published_sat() {
    assert_route_published_sat("t2", T2);
    assert_route_published_sat("w1_51", W1_51);
}

/// t5 (linear body) and t7 (the constant pinned by a sibling) were already
/// `sat` in the default posture; whichever route answers, they stay `sat`.
#[test]
fn linear_and_pinned_universals_stay_sat() {
    let t5 = "(set-logic ALL)(declare-fun c () Int)\
        (assert (forall ((v Int)) (> (+ v c) v)))(check-sat)";
    let t7 = "(set-logic ALL)(declare-fun c () Int)(assert (= c 1))\
        (assert (forall ((v Int)) (= (* c v) v)))(check-sat)";
    for (name, smt) in [("t5", t5), ("t7", t7)] {
        assert_eq!(run_default_posture(smt).verdicts, ["sat"], "{name}");
    }
}

/// t1 with `c = 2` pinned is UNSAT (`v = 1` gives `1 = 0`). The route's ground
/// probe refutes the eliminated problem and declines, and the route never
/// answers `unsat` itself: whatever the legacy path answers, it is not `sat`.
#[test]
fn affine_universal_contradicting_its_pin_is_never_sat() {
    let smt = "(set-logic ALL)(declare-fun c () Int)(assert (= c 2))\
        (assert (forall ((v Int)) (= (+ (* c v) (* (- 1) v)) 0)))(check-sat)";
    let run = run_default_posture(smt);
    assert_ne!(run.verdicts, ["sat"]);
    assert_ne!(run.gate.as_deref(), Some("confirmed"));
    // An infeasible rest (`∀v. c·v = v + 1`: `c = 1 ∧ −1 = 0`) is refuted the
    // same way.
    let infeasible = "(set-logic ALL)(declare-fun c () Int)\
        (assert (forall ((v Int)) (= (* c v) (+ v 1))))(check-sat)";
    let run = run_default_posture(infeasible);
    assert_ne!(run.verdicts, ["sat"]);
    assert_ne!(run.gate.as_deref(), Some("confirmed"));
}

/// A body that stays nonlinear in its binder is not affine: the elimination
/// keeps the quantifier and the route declines before recognition. `v = 0`
/// falsifies it, so the query is UNSAT; nothing may publish `sat`.
#[test]
fn body_nonlinear_in_its_binder_is_refused_by_the_route() {
    let smt = "(set-logic ALL)(declare-fun c () Int)\
        (assert (forall ((v Int)) (>= (* c v v) 1)))(check-sat)";
    let run = run_default_posture(smt);
    assert_eq!(run.affine_roots, None);
    assert_eq!(run.gate, None);
    assert_ne!(run.verdicts, ["sat"]);
}

/// The raw posture applies the same elimination in place, so the route stays
/// out of it and the legacy path answers.
#[test]
fn raw_posture_does_not_take_the_route() {
    let commands = parse(T1).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).expect("execute");
    assert!(outputs.iter().any(|line| line == "sat"), "{outputs:?}");
    assert_eq!(exec.statistics().get_int("eq_qe.affine_roots"), None);
}

/// `∀v. v·w = 0 ∨ 2v + h(s) = 1` eliminates to `w = 0`, dropping `h` and the
/// uninterpreted-sort constant `s`: the in-place model would print no value
/// for either, so the route declines rather than publish a partial model.
#[test]
fn elimination_that_drops_a_function_is_declined() {
    let smt = "(set-logic ALL)(declare-sort S 0)(declare-fun h (S) Int)\
        (declare-fun w () Int)(declare-const s S)\
        (assert (forall ((v Int)) (or (= (* v w) 0) (= (+ (* 2 v) (h s)) 1))))\
        (check-sat)";
    let run = run_default_posture(smt);
    assert_eq!(
        run.affine_roots, None,
        "the route must not recognize the root"
    );
    assert_eq!(run.gate, None);
}

/// The 2026-10-01 verifier's crash repro. The model sets both coefficients
/// `(f 1)` and `(f 0)` to 0; the emission's quantified model check refutes the
/// negated substituted body, whose proof rebuild parses `(* 0 v)` in LRA.
/// `scale_rat(0)` kept the entry `(v, 0)` and `is_expression_forced_to_value`
/// divided by it: a num-bigint divide-by-zero panic, answered `unknown
/// (internal solver error)`. Base and z3 answer `sat`.
const ZERO_COEFFICIENT_PANIC: &str = "(declare-fun f (Int) Int)\
    (assert (forall ((v Int)) (or (= (* (f 1) v) (* (f 0) v)) (= v 3))))(check-sat)";

#[test]
fn zero_model_coefficients_do_not_crash_the_model_check() {
    let run = run_default_posture(ZERO_COEFFICIENT_PANIC);
    assert_eq!(run.verdicts, ["sat"], "{:?}", run.verdicts);
}

/// The session variant: the panic answered `unknown` and the session then
/// dropped every later problem-contributing command, so ALL later check-sats
/// answered `unknown`. z3 and base answer sat, sat, unsat.
#[test]
fn zero_model_coefficients_do_not_poison_the_session() {
    let smt = "(declare-fun f (Int) Int)(declare-fun c () Int)\
        (push 1)\
        (assert (forall ((v Int)) (or (= (* (f 1) v) (* (f 0) v)) (= v 3))))\
        (check-sat)\
        (pop 1)\
        (assert (> c 0))(check-sat)\
        (assert (< c 0))(check-sat)";
    let run = run_default_posture(smt);
    assert_eq!(run.verdicts, ["sat", "sat", "unsat"], "{:?}", run.verdicts);
}

/// What a route `sat` rests on is recorded, not assumed. t1's nested
/// refutations are admitted as checked, so the model check's grant carries it.
/// With an `abs`, `mod` or `ite` coefficient the nested proof is a single
/// trust step that only a fresh executor re-decides: that refutation decides
/// nothing (on fcdf5b51e it published this `sat` behind a model-check grant,
/// recorded `deferred-discharged-trust-full-domain`), so no grant is
/// installed and the publication gate confirms the authored conjunct against
/// the emitted model itself.
#[test]
fn recorded_authority_names_the_admission_class() {
    let t1 = run_default_posture(T1);
    assert_eq!(t1.verdicts, ["sat"]);
    assert_eq!(
        t1.quantified_authority.as_deref(),
        Some("deferred-certified-bv-full-domain"),
        "t1"
    );
    for (name, coefficient) in [
        ("abs", "(abs c)"),
        ("mod", "(mod c 3)"),
        ("ite", "(ite (> c 0) c (- c))"),
    ] {
        let smt = format!(
            "(set-logic ALL)(declare-fun c () Int)\
             (assert (forall ((v Int)) (= (* {coefficient} v) v)))(assert (< c 0))(check-sat)"
        );
        let run = run_default_posture(&smt);
        assert_eq!(run.verdicts, ["sat"], "{name}");
        assert_eq!(
            run.quantified_authority.as_deref(),
            Some("confirmed"),
            "{name}: a trust-step refutation mints no grant; the gate's own \
             evaluation is what this sat rests on"
        );
    }
}
