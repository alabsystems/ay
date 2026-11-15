// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The QSAT route's `unsat` carries its document in the default posture.
//!
//! The route publishes an `unsat` only with the Alethe document a consumer
//! receives: rendered, no `hole`/`trust` step, every premise `assume` an
//! assertion of the input as written. Measured on the branch that introduced
//! the route (0807e0828), every fixture here published `unsat` WITHOUT such a
//! document: `(not (and ..))` and `=>` roots assumed AY's canonical `(or ..)`
//! (pinned carcara: "could not match term to any of the original problem
//! premises"), a negated existential and an alternation shipped no document at
//! all. Each now ships a complete authored document; a shape whose document
//! still cannot be built is handed back (`qsat.publish = unsat-unevidenced`),
//! never published by the route.

use ay_dpll::{normalize_premise_surface, Executor};
use ay_frontend::parse;
use ay_proof::AletheDocumentScan;
use std::time::Duration;

const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

/// Route publication labels.
const ROUTE_UNSAT: [&str; 3] = ["unsat-replayed", "unsat-expansion", "unsat-firewall"];

struct Run {
    exec: Executor,
    verdict: String,
    publish: Option<String>,
    evidence: Option<String>,
}

/// The default posture with the document retrievable afterwards (a library
/// caller reads `last_proof` only when it asked for proofs).
fn with_proofs(exec: &mut Executor) {
    exec.set_produce_proofs(true);
}

fn run(smt: &str, configure: impl FnOnce(&mut Executor)) -> Run {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    configure(&mut exec);
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    let (publish, evidence) = (text("qsat.publish"), text("qsat.evidence"));
    Run {
        verdict: outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default(),
        exec,
        publish,
        evidence,
    }
}

/// The published document is complete and assumes only authored premises.
fn assert_authored_document(name: &str, exec: &Executor) {
    let mut scan = AletheDocumentScan::default();
    match exec.try_export_last_proof_alethe_for_problem_scope_to(&mut scan) {
        Some(Ok(())) => {}
        other => panic!("{name}: the published unsat must render its document: {other:?}"),
    }
    assert_eq!(
        scan.unproved, 0,
        "{name}: the document carries an unproved step"
    );
    let authored = exec
        .authored_premise_surfaces()
        .unwrap_or_else(|| panic!("{name}: authored premises must be retained"));
    for assume in &scan.premise_assumes {
        assert!(
            authored.contains(&normalize_premise_surface(assume)),
            "{name}: `{assume}` is not an assertion of the input as written"
        );
    }
}

const NOT_AND: &str = "(set-logic LIA)(declare-fun p () Bool)(declare-fun q () Bool)\
    (assert (not (and (not p) (not q))))(assert (not p))(assert (not q))\
    (assert (forall ((x Int)) (> (+ x 1) x)))(check-sat)";
const IMPLIES: &str = "(set-logic LIA)(declare-fun p () Bool)(declare-fun q () Bool)\
    (assert (=> p q))(assert p)(assert (not q))\
    (assert (forall ((x Int)) (> (+ x 1) x)))(check-sat)";
const NOT_EXISTS: &str = "(set-logic LIA)(assert (not (exists ((x Int)) (< x 13))))(check-sat)";
const NOT_EXISTS_EQ: &str =
    "(set-logic LIA)(declare-fun a () Int)(assert (not (exists ((x Int)) (= x a))))(check-sat)";
const ALTERNATION: &str = "(set-logic LIA)(declare-fun a () Int)\
    (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y (+ x a))))))\
    (assert (< a 2))(check-sat)";

#[test]
fn route_unsat_ships_a_complete_authored_document() {
    for (name, smt) in [
        ("not-and", NOT_AND),
        ("implies", IMPLIES),
        ("not-exists", NOT_EXISTS),
        ("not-exists-eq", NOT_EXISTS_EQ),
        ("alternation", ALTERNATION),
    ] {
        let run = run(smt, with_proofs);
        assert_eq!(
            run.verdict, "unsat",
            "{name}: publish={:?} evidence={:?}",
            run.publish, run.evidence
        );
        let publish = run.publish.as_deref().unwrap_or("none");
        assert!(
            ROUTE_UNSAT.contains(&publish),
            "{name}: the route must publish (publish={publish})"
        );
        assert_eq!(run.evidence.as_deref(), Some("document"), "{name}");
        assert_authored_document(name, &run.exec);
    }
}

/// A negated existential prints the dual with the authored binder and a
/// checked derivation of `qnt_neg_exists`, never a `hole`.
#[test]
fn negated_existential_dual_is_derived_with_the_authored_binder() {
    let run = run(NOT_EXISTS, with_proofs);
    assert_eq!(run.verdict, "unsat");
    let document = run
        .exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("retained proof")
        .expect("rendered document");
    assert!(
        document.contains(":rule connective_def") && !document.contains(":rule hole"),
        "{document}"
    );
    assert!(
        document.contains("(forall ((x Int)) (not (< x 13)))"),
        "the dual must keep the authored binder: {document}"
    );
}

/// The authored `let` root has no checked bridge to its canonical body (the
/// printer can only `hole` it): the route hands the query back rather than
/// publish that document, and the verdict is never `sat`.
#[test]
fn route_never_publishes_an_unsat_whose_document_is_holey() {
    let smt = "(set-logic LIA)(declare-fun p () Bool)(declare-fun q () Bool)\
        (assert (let ((z (not p))) (not (and z (not q)))))(assert (not p))(assert (not q))\
        (assert (forall ((x Int)) (> (+ x 1) x)))(check-sat)";
    let run = run(smt, with_proofs);
    assert_ne!(run.verdict, "sat");
    let publish = run.publish.as_deref().unwrap_or("none");
    assert_eq!(publish, "unsat-unevidenced", "evidence={:?}", run.evidence);
    assert_eq!(run.evidence.as_deref(), Some("unproved-step"));
}

/// The shed posture (`--z3-mode`, `--no-proof`) produces no document by
/// request and keeps the internal strict admission.
#[test]
fn shed_posture_keeps_the_internal_strict_admission() {
    let run = run(NOT_EXISTS, |exec| {
        exec.set_competition_mode(true);
        exec.set_retain_parsed_assertions(false);
    });
    assert_eq!(run.verdict, "unsat");
    assert_eq!(run.evidence.as_deref(), Some("shed-posture"));
}

/// A twelve-level alternation (`2010-Monniaux-QE/mjollnir2/formula_199`)
/// whose game is decided `unsat` in ~0.1 s. Its expansion replay was refused
/// twice over: the replay's ground probe refuted the final instance only
/// through a sum-of-monomials-rewritten leaf (`t0: trust (cl false)`), and
/// once the probe ingested the instance as is, the stitched chain exhausted
/// the strict envelope on the `General` product of its `forall_inst`,
/// `sko_forall`/`sko_ex` and `equiv_pos2` steps (`work 333978893+31803193 of
/// 350000000`). The route now publishes it, in the shed posture, through the
/// same strict boundary.
#[test]
fn deep_alternation_publishes_through_the_expansion_replay() {
    let smt = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/quantifier/qlra/mjollnir2_formula_199.smt2"
    ));
    let run = run(smt, |exec| {
        exec.set_competition_mode(true);
        exec.set_retain_parsed_assertions(false);
    });
    assert_eq!(run.verdict, "unsat", "publish={:?}", run.publish);
    assert_eq!(run.publish.as_deref(), Some("unsat-expansion"));
    assert_eq!(run.evidence.as_deref(), Some("shed-posture"));
}
