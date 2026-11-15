// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdicts the QSAT route (claude/qsat-mbp 0807e08285) lost, from the
//! 2026-09-30 verification campaign, pinned corpus-free. z3 5.1.0 agrees
//! with every expected verdict here, and each was also checked by hand.
//!
//! * BUDGET — one undecided kernel query used the route's whole share (4/5 of
//!   the deadline), so the legacy path that decides the file in under a
//!   second ran out of time. A kernel query is now capped at a third of
//!   the share (on a long deadline, the share less 4 s), and the game
//!   declines on it.
//! * APPLIED — the route stood the deep-QE retry and the nested-CEGQI lane
//!   down as soon as it recognized the problem, even when its own verdict was
//!   never published; under `--z3-mode` that lost an `unsat` the retry
//!   decides in 0.05 s.
//! * EVIDENCE — under a demanded certificate (`--proof FILE`,
//!   `--strict-proofs`) a QSAT unsat whose document does not render (or, under
//!   strict, carries a `hole` or a foreign `assume`) pre-empted the legacy
//!   certificate: `--strict-proofs` answered `unknown`, and `--proof FILE`
//!   exited 1 with no verdict.
//! * PURIFY — `div`/`mod` of an arithmetic `ite` kept the `ite` in the
//!   purification's definition atoms, so MBP declined (`mbp-parse`).
//! * GATE-DIV — an Int strategy that uses `div` could not be confirmed by the
//!   gate's checked ground refutation, and the early probe spent the arm's
//!   envelope, starving the routes that confirm the formula without one.
//! * CONFIRM — a kernel probe refuted a satisfiable level-0 query; the game's
//!   `unsat` survived only because publication refused it. A decisive kernel
//!   UNSAT is now confirmed by an independent solve.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// The CLI default: the best-effort proof sidecar.
    Default,
    /// `--z3-mode`: the internal proof cycle is shed.
    Z3Mode,
    /// `--proof FILE`: a certificate is demanded.
    Proof,
    /// `--strict-proofs`.
    Strict,
}

struct Outcome {
    verdict: String,
    engine: Option<String>,
    kernel_ms: Option<u64>,
    /// The problem-scoped Alethe export after an `unsat`: `Some(true)` when
    /// it rendered.
    rendered: Option<bool>,
}

fn solve(smt: &str, posture: Posture, budget: Duration) -> Outcome {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(budget));
    match posture {
        Posture::Default => exec.set_best_effort_produce_proofs(1_000_000),
        Posture::Z3Mode => exec.set_competition_mode(true),
        Posture::Proof => exec.set_produce_proofs(true),
        Posture::Strict => {
            exec.set_produce_proofs(true);
            exec.set_strict_grant_evidence_required(true);
        }
    }
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));
    let verdict = outputs
        .iter()
        .rev()
        .map(|l| l.trim())
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
        .to_string();
    let rendered = (verdict == "unsat").then(|| {
        matches!(
            exec.try_export_last_proof_alethe_for_problem_scope(),
            Some(Ok(_))
        )
    });
    let stats = exec.statistics();
    Outcome {
        verdict,
        engine: stats.get_string("qsat.verdict").map(str::to_string),
        kernel_ms: stats.get_int("qsat.kernel_ms"),
        rendered,
    }
}

const BUDGET_MODQ4: &str = "(set-logic LIA)
(assert (forall ((y Int)) (exists ((x Int)) (and (= (mod (+ x y) 3) 0) (> x 0) (< x 3)))))
(check-sat)";

const BUDGET_D02: &str = "(set-logic LIA)
(assert (forall ((x Int)) (exists ((y Int)) (or (= (mod x 3) 0) (= x (+ (* 3 y) 1))))))
(check-sat)";

const BUDGET_PARITY2: &str = "(set-logic LIA)
(assert (forall ((x Int)) (exists ((y Int)) (or (= x (* 3 y)) (= x (+ (* 3 y) 1))))))
(check-sat)";

/// BUDGET: the kernel stalls on a trivially unsat ground query of each of
/// these (a pre-existing ground-lane gap); the route must give up after its
/// per-query cap and leave the legacy path the rest of a 5 s deadline. On
/// 0807e08285 the kernel spent ~4,000 ms of the 5,000 and the answer was
/// `unknown` or late.
#[test]
fn qsat_undecided_kernel_query_leaves_the_legacy_path_its_time() {
    for (name, smt) in [
        ("modq4", BUDGET_MODQ4),
        ("d02", BUDGET_D02),
        ("parity2", BUDGET_PARITY2),
    ] {
        for posture in [Posture::Default, Posture::Z3Mode] {
            let out = solve(smt, posture, Duration::from_secs(5));
            assert_ne!(out.verdict, "sat", "WRONG VERDICT ({name}, {posture:?})");
            if let Some(ms) = out.kernel_ms {
                assert!(
                    ms <= 2_500,
                    "{name} ({posture:?}): the kernel spent {ms} ms of a 5 s deadline \
                     (engine {:?}); one query is capped at a third of the route's share",
                    out.engine
                );
            }
        }
        let out = solve(smt, Posture::Default, Duration::from_secs(10));
        assert_eq!(
            out.verdict, "unsat",
            "{name}: the legacy path decides it (engine {:?})",
            out.engine
        );
    }
}

const APPLIED_Z3MODE: &str = "(set-logic LIA)
(declare-fun p () Bool)
(assert (= p (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y (+ x 2)))))))
(assert (not p))
(check-sat)";

const APPLIED_Z3MODE_REAL: &str = "(set-logic LRA)
(declare-fun p () Bool)
(assert (= p (forall ((x Real)) (exists ((y Real)) (and (> y x) (< y (+ x 2.0)))))))
(assert (not p))
(check-sat)";

/// APPLIED: the game decides `unsat` but no publication route carries this
/// shape; the deep-QE retry must still run (0807e08285: `unknown` 4/4).
#[test]
fn qsat_unpublished_game_unsat_keeps_the_legacy_lanes() {
    for (name, smt) in [("int", APPLIED_Z3MODE), ("real", APPLIED_Z3MODE_REAL)] {
        let out = solve(smt, Posture::Z3Mode, Duration::from_secs(10));
        assert_eq!(out.verdict, "unsat", "{name}: engine {:?}", out.engine);
    }
}

const EVIDENCE_D4: &str = "(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (exists ((y Int)) (and (> y a) (< y b))))
(assert (forall ((x Int)) (or (<= x a) (>= x b))))
(check-sat)";

const EVIDENCE_R7: &str = "(set-logic LRA)
(declare-fun a () Real)
(assert (forall ((y Real)) (and (and (= (+ (* 2.0 y) 3.0) (+ (- y) (- a) (- 3.0))) (= (- y) (+ (* 3.0 y) a))) (<= (- y) a))))
(assert (forall ((x Real)) (< (+ x 4.0) (+ (* 2.0 x) (* 3.0 a) (- 2.0)))))
(assert (or (forall ((x Real)) (<= (+ a x) (+ (- x) (- a) 0.0))) (< (+ a 2.0) a)))
(assert (< (+ (* 3.0 a) (- 1.0)) (* 3.0 a)))
(assert (> (+ (- a) 0.0) a))
(check-sat)";

const EVIDENCE_V146: &str = "(set-logic LRA)
(assert (forall ((x1 Real) (x2 Real)) (=> (and (<= (- 3.0) x2) (<= x2 3.0)) (< (* 3.0 x1) x2))))
(assert (forall ((x3 Real)) (=> (and (<= (- 3.0) x3) (<= x3 -1.0)) (<= (ite (>= (ite (= 0.0 (- (/ 1.0 3.0))) 0.0 x3) (* (- 1.0) x3)) (* (- 1.0) x3) x3) x3))))
(assert (exists ((x4 Real)) (and (and (<= (- 3.0) x4) (<= x4 1.0)) (< (* 2.0 x4) (* 3.0 x4)))))
(check-sat)";

const EVIDENCE_NE1: &str = "(set-logic LIA)
(assert (not (exists ((x Int)) (< x 13))))
(check-sat)";

const EVIDENCE_AL2: &str = "(set-logic LRA)
(assert (exists ((x Real)) (forall ((y Real)) (< y x))))
(check-sat)";

/// EVIDENCE: under a demanded certificate an `unsat` always comes with a
/// document the exporter renders (the CLI turns a refused render under
/// `--proof FILE` into exit 1 with no verdict), and the verdicts the legacy
/// path certifies are not lost to a QSAT proof that falls short.
#[test]
fn qsat_demanded_certificate_falls_back_to_the_legacy_certificate() {
    for (name, smt) in [
        ("d4", EVIDENCE_D4),
        ("r7_036", EVIDENCE_R7),
        ("v146", EVIDENCE_V146),
        ("ne1", EVIDENCE_NE1),
        ("al2", EVIDENCE_AL2),
    ] {
        for posture in [Posture::Proof, Posture::Strict] {
            let out = solve(smt, posture, Duration::from_secs(10));
            assert_ne!(out.verdict, "sat", "WRONG VERDICT ({name}, {posture:?})");
            assert_ne!(
                out.rendered,
                Some(false),
                "{name} ({posture:?}): an unsat under a demanded certificate must render"
            );
        }
    }
    // The legacy path certifies these three; strict must not lose them.
    for (name, smt) in [
        ("d4", EVIDENCE_D4),
        ("r7_036", EVIDENCE_R7),
        ("v146", EVIDENCE_V146),
    ] {
        let out = solve(smt, Posture::Strict, Duration::from_secs(10));
        assert_eq!(
            out.verdict, "unsat",
            "{name}: strict verdict (engine {:?})",
            out.engine
        );
    }
}

/// PURIFY: `(mod (ite c a b) k)` and `(div (ite c a b) k)` are played, not
/// declined (0807e08285: `mbp-parse` on both, `unknown` everywhere).
#[test]
fn qsat_div_mod_of_an_ite_is_played() {
    let unsat = "(set-logic LIA)
        (assert (exists ((j Int)) (forall ((i Int)) (= (mod (ite (> i 0) i j) 2) 0))))
        (check-sat)";
    let abs = "(set-logic LIA)
        (assert (exists ((j Int)) (forall ((i Int)) (= (mod (+ (abs i) j) 2) 0))))
        (check-sat)";
    let sat = "(set-logic LIA)
        (assert (exists ((j Int)) (forall ((i Int)) (=> (> i 5) (> (div (ite (> i 10) i j) 2) 2)))))
        (check-sat)";
    for (name, smt, expected) in [
        ("mod-ite", unsat, "unsat"),
        ("mod-abs", abs, "unsat"),
        ("div-ite", sat, "sat"),
    ] {
        for posture in [Posture::Default, Posture::Z3Mode] {
            let out = solve(smt, posture, Duration::from_secs(10));
            assert_eq!(
                out.engine.as_deref(),
                Some(expected),
                "{name} ({posture:?}): the game plays it (public {})",
                out.verdict
            );
            let opposite = if expected == "sat" { "unsat" } else { "sat" };
            assert_ne!(out.verdict, opposite, "WRONG VERDICT ({name}, {posture:?})");
        }
    }
    let out = solve(sat, Posture::Default, Duration::from_secs(10));
    assert_eq!(
        out.verdict, "sat",
        "div-ite: the strategy is confirmed (j = 6 works)"
    );
}

/// GATE-DIV: `∀x ∃y. 2y = 2x` is valid (y = x). The strategy is a `div`
/// term; the gate must confirm it, or at least not starve the routes that
/// confirm the formula without one (0807e08285: `unknown` in both postures,
/// where the base binary answers `sat`).
#[test]
fn qsat_div_strategy_is_confirmed_by_the_gate() {
    for (name, k) in [("q1", 2), ("r1", 3)] {
        let smt = format!(
            "(set-logic LIA)(assert (forall ((x Int)) (exists ((y Int)) (= (* {k} y) (* {k} x)))))(check-sat)"
        );
        for posture in [Posture::Default, Posture::Z3Mode] {
            let out = solve(&smt, posture, Duration::from_secs(10));
            assert_eq!(
                out.verdict, "sat",
                "{name} ({posture:?}): engine {:?}",
                out.engine
            );
        }
    }
}

/// CONFIRM: `(distinct (to_real c) (+ (to_real c) 0.5))` holds for every
/// `c`, so the universal is valid. The kernel probe refuted the level-0
/// query on 0807e08285 (game `unsat`); the confirmation must refuse that.
#[test]
fn qsat_decisive_kernel_unsat_is_confirmed() {
    let smt = "(set-logic ALL)
        (declare-fun c () Int)
        (assert (forall ((y Int)) (or (distinct (to_real c) (+ (to_real c) 0.5)) (> y 0))))
        (check-sat)";
    for posture in [Posture::Default, Posture::Z3Mode] {
        let out = solve(smt, posture, Duration::from_secs(10));
        assert_ne!(
            out.engine.as_deref(),
            Some("unsat"),
            "{posture:?}: the game's verdict is wrong"
        );
        assert_eq!(
            out.verdict, "sat",
            "{posture:?}: the legacy path decides it"
        );
    }
}

/// CONFIRM, the case the plain lane also "confirmed" under the other
/// formulation: `p` is forced true and the alternation is valid (y = x + 1),
/// so the file is satisfiable; the full pipeline cannot decide the level-0
/// query, and the game must not end on the plain lane's word.
#[test]
fn qsat_decisive_kernel_unsat_needs_a_pipeline_refutation() {
    let smt = "(set-logic ALL)
        (declare-fun p () Bool)
        (declare-fun c () Int)
        (assert (= p (forall ((x Int)) (exists ((y Int))
            (and (> y x) (< y (+ x 2)) (distinct (to_real c) (+ (to_real c) 0.5)))))))
        (assert p)
        (check-sat)";
    for posture in [Posture::Default, Posture::Z3Mode] {
        let out = solve(smt, posture, Duration::from_secs(10));
        assert_ne!(
            out.engine.as_deref(),
            Some("unsat"),
            "{posture:?}: the game's verdict is wrong"
        );
        assert_ne!(out.verdict, "unsat", "WRONG VERDICT ({posture:?})");
    }
}
