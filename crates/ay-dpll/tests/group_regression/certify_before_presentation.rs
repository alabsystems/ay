// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! #certify-before-presentation: a declined authored-surface override plan
//! withholds the DOCUMENT, never a document an authored replacement builds.
//!
//! The plan declines on the binder shape veto for any root with a quantifier
//! in it, however small. It used to replace the whole proof with the one-line
//! `(cl)` trust poison, and on this shape the authored cascade then rebuilt a
//! complete authored document over the poisoned candidate (pinned carcara:
//! `valid`). Keeping the derivation for certification made the candidate
//! strictly publishable, which skipped the cascade and withheld that valid
//! document — measured on this fixture and on UF
//! `sledgehammer/TypeSafe/uf.1083624` before the cascade was told that a
//! withheld derivation is not a publishable presentation.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::AletheDocumentScan;
use std::time::Duration;

/// A quantified conjunct (the plan's binder veto) beside a ground linear
/// contradiction the derivation refutes on its own.
const BINDER_ROOT_BESIDE_GROUND_REFUTATION: &str = "\
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (and (forall ((x Int)) (>= (f x) 0)) (> a (+ b 1))))
(assert (> b a))
(check-sat)
";

#[test]
fn a_declined_surface_plan_keeps_the_cascades_authored_document() {
    let commands = parse(BINDER_ROOT_BESIDE_GROUND_REFUTATION).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("strict-proof"),
        "the refutation is strictly certified"
    );
    assert_eq!(
        exec.last_unsat_document_withheld_by(),
        None,
        "an authored replacement's document must not be withheld"
    );
    let mut scan = AletheDocumentScan::default();
    match exec.try_export_last_proof_alethe_for_problem_scope_to(&mut scan) {
        Some(Ok(())) => {}
        other => panic!("the authored document must render: {other:?}"),
    }
    assert_eq!(scan.unproved, 0, "the document carries an unproved step");
}
