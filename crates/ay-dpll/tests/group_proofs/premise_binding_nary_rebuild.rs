// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Publication-boundary coverage for finite-enum pigeonhole certificates.
//!
//! A direct binary disequality clique carries enough authored premise identity
//! to rebuild the finite-cardinality argument as a strict native proof: one
//! `DatatypeEnumPigeonhole` lemma, one `Assume` per edge, and one n-ary
//! resolution. The pinned external Alethe calculus has no datatype-
//! exhaustiveness rule, so its diagnostic rendering honestly keeps that lemma
//! as `hole`; the serializable native bundle remains the portable strict
//! certificate.
//! Evidence hidden in one n-ary `distinct` assertion deliberately does not take
//! that shortcut: the individual edge is not itself an authored premise, so
//! publication must remain fail-closed rather than cite invented assumptions.
//!
//! Both shapes are genuinely UNSAT. The distinction here is proof authority,
//! not solver semantics: direct roots publish `unsat`; unsupported premise
//! decomposition publishes `unknown` and revokes the artifact.

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn pigeonhole_script(places: usize) -> String {
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_DT)\n\
         (declare-datatype Unit ((u0) (u1) (u2)))\n",
    );
    for index in 0..places {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    for index in 0..places {
        script.push_str(&format!(
            "(assert (or (= p{index} u0) (= p{index} u1) (= p{index} u2)))\n"
        ));
    }
    script.push_str("(assert (distinct");
    for index in 0..places {
        script.push_str(&format!(" p{index}"));
    }
    script.push_str("))\n(check-sat)\n(get-proof)\n");
    script
}

/// Assert that a pigeonhole encoded as one n-ary `distinct` remains fail-closed.
fn assert_nary_distinct_pigeonhole_declines_publication(places: usize) {
    assert!(
        places > 3,
        "instance is only UNSAT when it overflows Unit's 3 constructors"
    );
    let script = pigeonhole_script(places);
    let commands = parse(&script).expect("parse datatype pigeonhole");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute datatype pigeonhole");
    assert_eq!(outputs.first().map(String::as_str), Some("unknown"));
    assert!(
        outputs
            .get(1)
            .is_some_and(|output| output.contains("proof is not available")),
        "get-proof must disclose revocation after fail-closed publication: {outputs:?}"
    );
    assert!(
        exec.last_proof().is_none(),
        "an unknown verdict must not expose the rejected proof artifact"
    );
}

fn direct_binary_pigeonhole_script(constructors: usize) -> String {
    let places = constructors + 1;
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n\
         (set-logic QF_DT)\n\
         (declare-datatype Unit (",
    );
    for index in 0..constructors {
        script.push_str(&format!("(u{index})"));
    }
    script.push_str("))\n");
    for index in 0..places {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    for left in 0..places {
        for right in (left + 1)..places {
            script.push_str(&format!("(assert (not (= p{left} p{right})))\n"));
        }
    }
    script.push_str("(check-sat)\n(get-proof)\n");
    script
}

/// Assert that direct authored edge premises produce the dedicated strict rule.
fn assert_direct_binary_pigeonhole_has_internal_strict_proof(constructors: usize) {
    assert!(constructors > 0);
    let commands = parse(&direct_binary_pigeonhole_script(constructors))
        .expect("parse direct finite-enum pigeonhole");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute direct finite-enum pigeonhole");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));

    let proof = exec
        .last_proof()
        .expect("strictly certified UNSAT must retain its proof");
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
                ..
            }
        )
    }));
    assert!(
        proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::Step {
                rule: ay_core::AletheRule::Trust | ay_core::AletheRule::Hole,
                ..
            } | ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "the direct pigeonhole proof must contain no trust-family step: {proof:?}"
    );
    let alethe = outputs.get(1).expect("get-proof output");
    assert!(
        alethe.contains(":rule hole"),
        "the unsupported external calculus gap must stay explicit:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule dt_enum_pigeonhole"),
        "get-proof must not invent an unknown wire rule:\n{alethe}"
    );
}

#[test]
#[timeout(30_000)]
fn test_nary_distinct_datatype_pigeonhole_declines_strict_publication() {
    assert_nary_distinct_pigeonhole_declines_publication(6);
}

#[test]
#[timeout(60_000)]
fn test_large_nary_distinct_datatype_pigeonhole_declines_strict_publication() {
    assert_nary_distinct_pigeonhole_declines_publication(24);
}

#[test]
#[timeout(30_000)]
fn test_direct_binary_datatype_pigeonhole_publishes_internal_strict_proof() {
    assert_direct_binary_pigeonhole_has_internal_strict_proof(3);
}

#[test]
#[timeout(60_000)]
fn test_larger_direct_binary_datatype_pigeonhole_publishes_internal_strict_proof() {
    // 33 values over 32 constructors exercise a 528-edge n-ary resolution.
    assert_direct_binary_pigeonhole_has_internal_strict_proof(32);
}
