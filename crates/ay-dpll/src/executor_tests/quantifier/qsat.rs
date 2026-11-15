// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QSAT route (roadmap component QS) end to end.
//!
//! The fixtures are the nested-CEGQI lane's (`qlra/`, which now runs them
//! under `--no-qsat`) plus integer ones. Every publishing assertion reads the
//! route's own `qsat.publish` statistic, so a verdict another path happened
//! to reach cannot satisfy a test that is about the route.

use std::time::Duration;

use crate::Executor;
use ay_frontend::parse;

/// Wall cap per test query; generous so load cannot flip a verdict.
const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

struct RouteRun {
    verdict: String,
    /// `qsat.verdict`: what the game decided (a hint until published).
    engine: Option<String>,
    /// `qsat.publish`: how the verdict was published, or why it was not.
    publish: Option<String>,
    /// `qsat.evidence`: the evidence gate's reading of a route `unsat`.
    evidence: Option<String>,
}

fn run(smt: &str) -> RouteRun {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    RouteRun {
        verdict: outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default(),
        engine: text("qsat.verdict"),
        publish: text("qsat.publish"),
        evidence: text("qsat.evidence"),
    }
}

/// The route decided `smt` as `expected` and published it itself.
fn assert_route(name: &str, smt: &str, expected: &str) {
    let run = run(smt);
    assert_eq!(
        run.verdict, expected,
        "{name}: verdict (engine={:?}, publish={:?})",
        run.engine, run.publish
    );
    let publish = run.publish.as_deref().unwrap_or("none");
    let by_route = if expected == "sat" {
        publish == "sat-gated"
    } else {
        matches!(
            publish,
            "unsat-replayed" | "unsat-expansion" | "unsat-firewall"
        )
    };
    assert!(
        by_route,
        "{name}: the route must be the publisher (publish={publish})"
    );
    if expected == "unsat" {
        // The default posture publishes a route `unsat` only with its
        // complete authored document (`qsat_route/evidence.rs`).
        assert_eq!(
            run.evidence.as_deref(),
            Some("document"),
            "{name}: evidence"
        );
    }
}

/// The game decided `smt` as `expected`; the public answer is never the
/// opposite one.
fn assert_engine(name: &str, smt: &str, expected: &str) {
    let run = run(smt);
    assert_eq!(
        run.engine.as_deref(),
        Some(expected),
        "{name}: engine verdict (publish={:?})",
        run.publish
    );
    let opposite = if expected == "sat" { "unsat" } else { "sat" };
    assert_ne!(run.verdict, opposite, "{name}: WRONG public verdict");
}

#[test]
fn depth_one_universals_are_refuted_with_strict_proofs() {
    for (name, smt) in [
        (
            "p3",
            "(set-logic LRA)(assert (forall ((x Real)) (< x 5)))(check-sat)",
        ),
        (
            "p7",
            "(set-logic LRA)(declare-const c Real)\
             (assert (forall ((x Real)) (and (> c 0) (< c 0) (> x 0))))(check-sat)",
        ),
        (
            "p8",
            "(set-logic LRA)(declare-const c Real)(assert (> c 0))\
             (assert (forall ((x Real)) (and (< c 0) (> x 0))))(check-sat)",
        ),
        (
            "a07u",
            "(set-logic LRA)(declare-const a Real)(declare-const b Real)(assert (< a b))\
             (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
        ),
        (
            "a31",
            "(set-logic LRA)(declare-const a Real)(declare-const b Real)\
             (assert (exists ((z Real)) (and (> z a) (< z b))))\
             (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
        ),
        (
            "a12",
            "(set-logic LRA)(declare-const c Real)\
             (assert (forall ((q Bool) (x Real)) (=> q (> x c))))(check-sat)",
        ),
        (
            "shadow-unsat",
            "(set-logic LRA)(declare-const x Real)(assert (= x 1))\
             (assert (forall ((x Real)) (< x 1)))(check-sat)",
        ),
        (
            "forall-a-b-eq",
            "(set-logic LRA)(assert (forall ((a Real) (b Real)) (= a b)))(check-sat)",
        ),
        (
            "int-strict",
            "(set-logic LIA)(assert (forall ((x Int)) (> x 0)))(check-sat)",
        ),
    ] {
        assert_route(name, smt, "unsat");
    }
}

#[test]
fn valid_universals_are_published_sat_through_the_gate() {
    for (name, smt) in [
        (
            "or-lt-ge",
            "(set-logic LRA)(declare-const c Real)\
             (assert (forall ((x Real)) (or (< x c) (>= x c))))(check-sat)",
        ),
        (
            "shift",
            "(set-logic LRA)(declare-const c Real)(assert (> c 0))\
             (assert (forall ((x Real)) (=> (> x 0) (> (+ x c) c))))(check-sat)",
        ),
        (
            "a07s",
            "(set-logic LRA)(declare-const a Real)(declare-const b Real)(assert (<= b a))\
             (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
        ),
        (
            "valid-iff",
            "(set-logic LRA)(declare-const c Real)\
             (assert (forall ((x Real)) (xor (> x c) (<= x c))))(check-sat)",
        ),
        (
            "shadow-sat",
            "(set-logic LRA)(declare-const x Real)(assert (= x 1))\
             (assert (forall ((x Real)) (or (< x 1) (>= x 1))))(check-sat)",
        ),
        (
            "int-gap",
            "(set-logic LIA)(declare-const c Int)\
             (assert (forall ((x Int)) (or (<= x c) (>= x (+ c 1)))))(check-sat)",
        ),
    ] {
        assert_route(name, smt, "sat");
    }
}

/// Alternations: the ∃ player's strategy certifies `sat` through the gate's
/// strategy route; the ∀ player's strategy expands to an `unsat` proof.
#[test]
fn alternations_are_decided_and_published() {
    for (name, smt, expected) in [
        (
            "e1",
            "(set-logic LIA)(declare-fun a () Int)\
             (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y (+ x a))))))\
             (assert (< a 2))(check-sat)",
            "unsat",
        ),
        (
            "n11",
            "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) \
             (and (> y x) (< y (+ x 1))))))(check-sat)",
            "sat",
        ),
        (
            "p10",
            "(set-logic LRA)(assert (forall ((a Real)) (exists ((x Real)) (<= (+ x a) 3))))\
             (check-sat)",
            "sat",
        ),
        (
            "m7",
            "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) (> y x))))(check-sat)",
            "sat",
        ),
    ] {
        assert_route(name, smt, expected);
    }
}

/// Instances of authored universals that the replay consumes in canonical
/// form, which no checked printer bridge relates yet: `(or (> 0 11.0) (<= 11.0
/// 10))` as `(< 11.0 0.0)` / `(<= 11.0 10.0)` (k7); the `=>` instance
/// `(=> (>= (+ y 1.0) 0) (<= (+ y 1.0) y))` projected by `or_pos` as the
/// canonical `(or ..)` (k10); the dual instance of a negated existential
/// whose `(= (+ ?X ?Y) ?Z)` is consumed reoriented and normalized, so no
/// `or_neg` over the printed surface reproduces its clause (NUM907=1). The
/// game decides `unsat`, the evidence gate refuses the document, and the route
/// does not publish it.
#[test]
fn universal_whose_instance_has_no_printed_bridge_is_not_published_by_the_route() {
    for (name, smt) in [
        (
            "k7",
            "(set-logic LRA)(assert (forall ((s Real)) (or (> 0 s) (<= s 10))))(check-sat)",
        ),
        (
            "k10",
            "(set-logic LRA)(declare-const y Real)\
             (assert (forall ((s Real)) (=> (>= s 0) (<= s y))))(check-sat)",
        ),
        (
            "NUM907=1",
            "(set-logic LRA)\
             (assert (not (exists ((?X Real) (?Y Real) (?Z Real)) \
               (= (= (+ ?X ?Y) ?Z) (and (= (- ?Z ?Y) ?X) (= (- ?Z ?X) ?Y))))))\
             (check-sat)",
        ),
    ] {
        let run = run(smt);
        assert_eq!(run.engine.as_deref(), Some("unsat"), "{name}");
        assert_eq!(run.publish.as_deref(), Some("unsat-unevidenced"), "{name}");
        assert_eq!(run.evidence.as_deref(), Some("render-refused"), "{name}");
        assert_ne!(run.verdict, "sat", "{name}");
    }
}

/// An ∃-first alternation's expansion Skolemizes a body that still binds the
/// ∀ variable, which the certified Skolem printer cannot spell: the game
/// decides `unsat`, the evidence gate refuses the document-less proof, and the
/// route publishes nothing (never `sat`).
#[test]
fn alternation_without_a_document_is_not_published_by_the_route() {
    let run =
        run("(set-logic LRA)(assert (exists ((y Real)) (forall ((x Real)) (> y x))))(check-sat)");
    assert_eq!(run.engine.as_deref(), Some("unsat"));
    assert_eq!(run.publish.as_deref(), Some("unsat-unevidenced"));
    assert_eq!(run.evidence.as_deref(), Some("render-refused"));
    assert_ne!(run.verdict, "sat");
}

/// Integer projection needs divisibility: `x = 2y` has no solution for odd
/// `x`, which a real relaxation would miss.
#[test]
fn integer_divisibility_is_not_relaxed() {
    assert_engine(
        "int-even",
        "(set-logic LIA)(assert (forall ((x Int)) (exists ((y Int)) (= x (* 2 y)))))(check-sat)",
        "unsat",
    );
    // The ∃ strategy is `y = x div 2` on each residue: the gate's checked
    // ground refutation over `div` is the open LIA proof gap, so only the
    // game's verdict is pinned.
    assert_engine(
        "int-parity",
        "(set-logic LIA)(assert (forall ((x Int)) (exists ((y Int)) \
         (or (= x (* 2 y)) (= x (+ (* 2 y) 1))))))(check-sat)",
        "sat",
    );
    assert_engine(
        "int-mod",
        "(set-logic LIA)(assert (forall ((x Int)) (exists ((y Int)) \
         (and (> y x) (= (mod y 3) 0)))))(check-sat)",
        "sat",
    );
}

macro_rules! exemplar {
    ($test:ident, $file:literal, $status:literal) => {
        #[test]
        fn $test() {
            assert_engine(
                $file,
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/fixtures/quantifier/qlra/",
                    $file
                )),
                $status,
            );
        }
    };
}

exemplar!(mjollnir3_155_unsat, "mjollnir3_formula_155.smt2", "unsat");
exemplar!(mjollnir3_202_sat, "mjollnir3_formula_202.smt2", "sat");
exemplar!(mjollnir2_219_unsat, "mjollnir2_formula_219.smt2", "unsat");
exemplar!(mjollnir4_252_unsat, "mjollnir4_formula_252.smt2", "unsat");
exemplar!(rndpre_3_3_sat, "RNDPRE_3_3.smt2", "sat");
exemplar!(rndpre_4_18_unsat, "RNDPRE_4_18.smt2", "unsat");
exemplar!(rnd_3_5_unsat, "RND_3_5.smt2", "unsat");
exemplar!(rnd_4_3_sat, "RND_4_3.smt2", "sat");

/// A universal under a disjunction is a game node, not a fact.
#[test]
fn universal_under_disjunction_is_never_misread() {
    let refuted = run("(set-logic LRA)(declare-const p Bool)\
         (assert (or p (forall ((x Real)) (> x 0))))(assert (not p))(check-sat)");
    assert_ne!(refuted.verdict, "sat", "the problem is unsat");
    let satisfied = run("(set-logic LRA)(declare-const p Bool)\
         (assert (or p (forall ((x Real)) (> x 0))))(check-sat)");
    assert_ne!(satisfied.verdict, "unsat", "p = true satisfies the problem");
}

/// A quantifier with an empty binder list has no engine variable to play
/// and no occurrence the publication replay can walk: the route declines the
/// shape (it used to panic in the expansion chain, `expansion.rs`, with an
/// index into the empty binder list) and the ordinary path answers.
#[test]
fn empty_binder_quantifier_is_declined_not_played() {
    for assertion in [
        "(assert (let ((a p)) (exists () a)))",
        "(assert (forall () p))",
        "(assert (exists () (and p (forall ((x Int)) (> (+ x 1) x)))))",
    ] {
        let smt =
            format!("(set-logic ALL)(declare-const p Bool){assertion}(assert (not p))(check-sat)");
        let commands = parse(&smt).expect("parse");
        let mut exec = Executor::new();
        exec.set_timeout(Some(QUERY_TIMEOUT));
        let outputs = exec.execute_all(&commands).expect("execute");
        let stats = exec.statistics();
        assert_eq!(
            stats.get_string("qsat.decline"),
            Some("shape-empty-binder"),
            "{assertion}"
        );
        assert_eq!(
            stats.get_string("qsat.verdict"),
            None,
            "{assertion}: no game"
        );
        assert!(
            !outputs.iter().any(|line| line == "sat"),
            "{assertion}: {outputs:?}"
        );
    }
}

/// The route decides plain `check-sat` over the authored scope only.
#[test]
fn assumption_and_incremental_queries_keep_the_route_inert() {
    const UNIVERSAL: &str = "(set-logic LRA)(declare-const c Real)(declare-const p Bool)\
         (assert (forall ((x Real)) (xor (> x c) (<= x c))))";
    assert_route("plain", &format!("{UNIVERSAL}(check-sat)"), "sat");
    let assuming = run(&format!("{UNIVERSAL}(check-sat-assuming (p))"));
    assert_eq!(
        assuming.engine, None,
        "check-sat-assuming must not reach the route"
    );
    assert_ne!(assuming.verdict, "unsat");
    let pushed = run(&format!("{UNIVERSAL}(push 1)(assert p)(check-sat)(pop 1)"));
    assert_eq!(
        pushed.engine, None,
        "an incremental session must not reach the route"
    );
    assert_ne!(pushed.verdict, "unsat");
}

#[test]
fn kill_switch_removes_the_route() {
    let _no_qsat = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let run = run("(set-logic LRA)(assert (forall ((x Real)) (< x 5)))(check-sat)");
    assert_eq!(
        run.engine, None,
        "--no-qsat must keep the route from running"
    );
    assert_ne!(run.verdict, "sat");
}

/// The replayed proof is installed outside the ordinary assembly, and still
/// prints the problem's own spelling at the `assume` and the `forall_inst`
/// (AY stores `(> x 0)` as `(< 0 x)` with a renamed binder).
#[test]
fn exported_unsat_proof_keeps_the_authored_surface() {
    let commands = parse(
        "(set-logic LIA)(set-option :produce-proofs true)\
         (assert (forall ((x Int)) (> x 0)))(check-sat)",
    )
    .expect("parse");
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    assert_eq!(exec.execute_all(&commands).expect("execute"), vec!["unsat"]);
    assert_eq!(
        exec.statistics().get_string("qsat.publish"),
        Some("unsat-replayed"),
        "the route must be the publisher"
    );
    let exported = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("certified UNSAT must retain an exportable proof")
        .expect("Alethe export must succeed");
    assert!(
        exported.contains("(assume t0 (forall ((x Int)) (> x 0)))"),
        "the assume must be the authored assertion: {exported}"
    );
    let forall_inst = exported
        .lines()
        .find(|line| line.contains(":rule forall_inst"))
        .expect("proof must contain the authored forall instantiation");
    assert!(
        forall_inst.contains("(> 0 0)"),
        "the instance must use the source quantifier's surface orientation: {forall_inst}"
    );
}

/// [`run`] under the CLI's `--z3-mode` posture (competition shedding, no
/// parsed-assertion retention), with the installed proof re-checked here.
fn run_z3(smt: &str) -> (RouteRun, bool) {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    let run = RouteRun {
        verdict: outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default(),
        engine: text("qsat.verdict"),
        publish: text("qsat.publish"),
        evidence: text("qsat.evidence"),
    };
    let strict = exec.test_installed_proof_is_strict_authored();
    (run, strict)
}

/// A top-level `exists` with several binders (depth 1) and a negated
/// multi-binder `forall` (the expansion chain's existential step) are
/// Skolemized one binder at a time: a `qnt_join` split, then a single-binder
/// `sko` step with its own registered witness, each re-derived by its strict
/// validator. Before, both shapes declined (`unsat-multi-binder-exists`,
/// `unsat-expansion-multi-binder`).
#[test]
fn multi_binder_existentials_are_skolemized_binder_by_binder() {
    for (name, smt, routes) in [
        (
            "a31-multi",
            "(set-logic LRA)(declare-const a Real)(declare-const b Real)\
             (assert (exists ((z Real) (w Real)) (and (> z a) (< z b) (= w z))))\
             (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
            &["unsat-replayed"][..],
        ),
        (
            "neg-forall-multi",
            "(set-logic LRA)\
             (assert (not (forall ((y Real) (z Real)) \
             (exists ((x Real)) (> x (+ y z))))))(check-sat)",
            &["unsat-replayed", "unsat-expansion"][..],
        ),
    ] {
        let (shed, strict) = run_z3(smt);
        assert_eq!(
            shed.verdict, "unsat",
            "{name}: verdict (engine={:?}, publish={:?})",
            shed.engine, shed.publish
        );
        let publish = shed.publish.as_deref().unwrap_or("none");
        assert!(
            routes.contains(&publish),
            "{name}: the route must be the publisher (publish={publish})"
        );
        assert!(
            strict,
            "{name}: the installed proof must re-check strict-complete"
        );

        // The default posture publishes a route `unsat` only with its
        // complete authored document; the Skolem printer does not render
        // this certificate, so the route must stand down there, never
        // publish without the document, and never answer `sat`.
        let default = run(smt);
        assert_ne!(default.verdict, "sat", "{name}: WRONG default verdict");
        let publish = default.publish.as_deref().unwrap_or("none");
        if matches!(publish, "unsat-replayed" | "unsat-expansion") {
            assert_eq!(default.evidence.as_deref(), Some("document"), "{name}");
        }
    }
}

/// A repeated binder name has no `qnt_join` split (its validator refuses
/// one), so the multi-binder Skolemization refuses up front and records
/// nothing.
#[test]
fn multi_binder_skolemization_refuses_a_repeated_binder_name() {
    let mut exec = Executor::new();
    let refused = exec.test_skolemize_binders_with_repeated_name();
    assert_eq!(refused, (Err("unsat-skolem-binder-names"), 0));
}
