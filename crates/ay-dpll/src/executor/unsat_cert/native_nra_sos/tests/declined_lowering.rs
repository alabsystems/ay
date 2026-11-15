// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sealed native-bundle exception still admits a strict native SOS UNSAT
//! whose step the checked Alethe lowering declines to its honest `hole`.

#![cfg(test)]

use super::*;

/// The SOS clause literal is the raw negation of the authored root, so it
/// prints `(not (not (>= (* x x) 0.0)))`, which the pinned `la_generic`
/// cannot read: the lowering declines it and the step keeps its wire gap.
const DOUBLE_NEGATED_SQUARE: &str = "(declare-const x Real) (assert (not (>= (* x x) 0.0)))";

#[test]
fn a_sealed_bundle_the_lowering_declines_still_publishes_its_unsat() {
    let mut executor = load(DOUBLE_NEGATED_SQUARE);
    open(&mut executor, &[]);
    install(&mut executor, &[]);
    let proof = executor.last_proof.as_ref().unwrap();
    assert!(executor.proof_has_known_wire_gap(proof));
    assert!(!executor.unsat_proof_terminal_trust_detected());
    let text = ay_proof::try_export_alethe(proof, &executor.ctx.terms).unwrap();
    assert_eq!(text.matches(":rule hole").count(), 1, "{text}");
    assert!(
        text.contains("ay-nra-sos: native certificate retained"),
        "{text}"
    );
    assert!(!text.contains(":rule la_mult_"), "{text}");
    // Only the current sealed bundle admits the gap (`unsat_cert.rs`
    // `strict_native_bundle_verified`); nothing else here could.
    let certificate = executor.last_unsat_certificate.as_ref().unwrap();
    assert!(certificate.strict_native_bundle_verified(&executor));
    assert!(executor
        .decline_trust_bearing_unsat_under_strict_proofs(SolveResult::unsat())
        .is_unsat());
}
