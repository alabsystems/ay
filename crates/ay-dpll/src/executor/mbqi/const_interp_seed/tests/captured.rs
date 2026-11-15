// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn bv(exec: &Executor, term: TermId) -> (BigInt, u32) {
    let model = exec.last_model.as_ref().expect("accepted whole model");
    let evaluated = exec.evaluate_term(model, term);
    let EvalValue::BitVec { value, width } = evaluated else {
        panic!("exact scalar model value for {term:?}: {evaluated:?}");
    };
    (value, width)
}

#[test]
fn captured_full4_seed_requires_validated_sat_and_complete_fresh_witness() {
    // No fixture model is injected here. This intentionally stays strong if
    // preprocessing has removed an original observation: missing data is an
    // unresolved capability, not permission to relax SAT/model validation.
    let mut exec = prepared(true);
    let authored = exec.ctx.assertions.clone();
    let outcome = exec.execute(&ay_frontend::Command::CheckSat).unwrap();
    assert_eq!(
        outcome.as_deref(),
        Some("sat"),
        "full4 needs native validated SAT; origin={:?}, reason={:?}; {}",
        exec.unknown_origin(),
        exec.unknown_reason(),
        observation_diagnostic(&exec, &authored)
    );
    assert!(exec.was_model_validated());
    assert!(exec.last_proof().is_none());
    let length = term(&mut exec, "length");
    let index = term(&mut exec, "__gpc1");
    let fill = term(&mut exec, "fill");
    let x = term(&mut exec, "x");
    let original_point = term(&mut exec, "(f true x)");
    let fresh_point = term(&mut exec, "(f false #xff)");
    let original_cell = term(&mut exec, "(select a __gpc1)");
    let fresh_cell = term(&mut exec, "(select a #xffffffffffffffff)");
    assert_eq!(bv(&exec, length), (BigInt::from(65), 64));
    let (index_value, width) = bv(&exec, index);
    assert_eq!(width, 64);
    assert!(index_value >= BigInt::from(32) && index_value < BigInt::from(65));
    assert_eq!(bv(&exec, x).1, 8);
    let value = bv(&exec, fill);
    assert_eq!(value.1, 8);
    for observed in [original_point, fresh_point, original_cell, fresh_cell] {
        assert_eq!(
            bv(&exec, observed),
            value,
            "one complete constant interpretation, not selected-point pins"
        );
    }
    let text = exec.model();
    for name in HEADS {
        assert!(
            text.contains(&format!("(define-fun {name} ")),
            "complete declared witness lacks {name}: {text}"
        );
    }
    assert_eq!(
        authored.len(),
        4,
        "all four original assertions were retained for certification"
    );
    let read = exec.values(&[
        ("fresh-uf".to_string(), fresh_point),
        ("fresh-cell".to_string(), fresh_cell),
    ]);
    assert!(
        !read.starts_with("(error"),
        "fresh public reads agree with the installed witness: {read}"
    );
}

#[test]
fn captured_original_disagreement_and_qf_mutation_keep_their_verdicts() {
    let mut original = prepared(false);
    assert_eq!(
        original
            .execute(&ay_frontend::Command::CheckSat)
            .unwrap()
            .as_deref(),
        Some("unsat")
    );
    let proof = original.last_proof().expect("original strict refutation");
    assert!(original
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let mut qf = Executor::new();
    qf.set_verification_level(crate::VerificationLevel::ProofChecked);
    qf.set_timeout(Some(Duration::from_secs(15)));
    qf.set_term_memory_limit(Some(128 * 1024 * 1024));
    qf.execute_all(&ay_frontend::parse(&source(true, false)).unwrap())
        .unwrap();
    assert_eq!(
        qf.execute(&ay_frontend::Command::CheckSat)
            .unwrap()
            .as_deref(),
        Some("sat")
    );
    assert!(qf.was_model_validated());
}
