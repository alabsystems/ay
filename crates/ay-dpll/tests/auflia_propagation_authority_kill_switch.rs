// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the AUFLIA fixpoint propagation provenance
//! (#ppp-l3, #quant-unit-authority).
//!
//! This file deliberately holds ONE test in its own binary: it mutates the
//! process environment, which must never race sibling tests in a shared
//! process.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;

/// The #ppp-l3 bool-eq-fold fixture. With the campaign kill switch OFF the
/// AUFLIA fixpoint drain must store nothing and the licensing augmentation
/// must decline, restoring the baseline: the verdict still publishes (the
/// independent rescue discharge is untouched) but the certificate leans on
/// trust. With the switch back ON the same input must certify strict and
/// trust-free. Deleting either the drain's kill-switch gate or the
/// augmentation's authority gate makes the OFF half fail.
#[test]
fn auflia_propagation_provenance_is_fully_covered_by_the_kill_switch() {
    let smt = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun f (Int) Int)
        (declare-const r Bool)
        (assert (= (f 0) 1))
        (assert (= r (<= (f 0) 2)))
        (assert (=> r (> (select a 1) 5)))
        (assert (< (select a 1) 3))
        (check-sat)
    "#;
    let commands = parse(smt).expect("fixture parses");

    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quant_unit_authority: true,
        ..Default::default()
    });
    let mut off_exec = Executor::new();
    let off_outputs = off_exec.execute_all(&commands).expect("off-mode executes");
    let off_strict_trust_free = off_exec.last_proof().is_some_and(|proof| {
        ay_proof::check_proof_strict(proof, off_exec.terms())
            .is_ok_and(|quality| quality.trust_count == 0)
    });
    drop(off_guard);
    assert!(
        !off_outputs.iter().any(|r| r == "sat"),
        "off-mode may only publish the baseline unsat/unknown; got {off_outputs:?}"
    );
    assert!(
        !off_strict_trust_free,
        "with the kill switch off no propagation record may be stored, \
         so the folded assume must fall back to the baseline trust demotion"
    );

    let mut on_exec = Executor::new();
    let on_outputs = on_exec.execute_all(&commands).expect("on-mode executes");
    assert_eq!(
        on_outputs,
        vec!["unsat"],
        "with the kill switch on (default) the fixture decides unsat"
    );
    let proof = on_exec.last_proof().expect("UNSAT publishes a proof");
    let quality = ay_proof::check_proof_strict(proof, on_exec.terms())
        .expect("the replayed propagation fold certifies strictly");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
}
