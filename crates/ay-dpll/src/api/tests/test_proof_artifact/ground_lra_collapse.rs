// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `test_proof_artifact.rs` to preserve the existing test
// fully qualified names.

/// A ground false QF_LRA assertion is folded to the Boolean constant `false`
/// before the ordinary LRA conflict path sees it. The proof exporter must
/// recover the exact authored arithmetic literal and certify its complement;
/// a placeholder `hole` is not an acceptable proof of a concrete inequality.
#[cfg(test)]
fn assert_ground_qf_lra_collapse_is_strict(script: &str, expect_farkas: bool) {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLra);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(script)
        .expect("ground QF_LRA fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "ground arithmetic assertion is false, got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("ground QF_LRA refutation must export an artifact");
    assert!(
        matches!(
            &artifact.strict_verdict,
            StrictProofVerdict::Verified(quality) if quality.is_complete()
        ),
        "ground QF_LRA proof must be complete and strictly checked: {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        !artifact.alethe.contains(":rule hole") && !artifact.alethe.contains(":rule trust"),
        "ground QF_LRA proof must not carry an admitted step:\n{}",
        artifact.alethe,
    );
    let scope = ay_proof::ProblemScope::from_smtlib_source(script);
    let wire_report = ay_proof::check_alethe_document(&artifact.alethe, &scope)
        .expect("rendered ground QF_LRA proof must pass the Alethe document checker");
    assert!(
        wire_report.steps > 0 && wire_report.assumes == 1,
        "Alethe document check must consume the nonempty refutation: {wire_report:?}",
    );
    assert_eq!(
        artifact.farkas_certificates.len(),
        usize::from(expect_farkas),
        "the comparison lane uses one printable Farkas row; a ground equality uses evaluate",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("ground QF_LRA proof must remain offline-recheckable");
    re_check_bundle_strict(&bundle).expect("independent strict bundle replay must accept");

    let mut mutated = bundle;
    if expect_farkas {
        // Non-vacuity: corrupt the one-row Farkas witness. The same checker
        // that accepted the producer artifact must reject a zero coefficient.
        let certificate = mutated.steps.iter_mut().find_map(|step| match step {
            ProofStep::TheoryLemma {
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                ..
            } => Some(farkas),
            _ => None,
        });
        let certificate = certificate.expect("refutation must contain one Farkas row");
        *certificate = FarkasAnnotation::from_ints(&[0]);
    } else {
        // A one-row Farkas certificate cannot express the disequality that is
        // the complement of a true equality. Corrupt the checked `evaluate`
        // rule instead, proving that this alternative certificate is not an
        // unchecked replacement for the old hole.
        let rule = mutated.steps.iter_mut().find_map(|step| match step {
            ProofStep::Step {
                rule: rule @ AletheRule::Evaluate,
                ..
            } => Some(rule),
            _ => None,
        });
        let rule = rule.expect("ground equality refutation must contain evaluate");
        *rule = AletheRule::Hole;
    }
    assert!(
        re_check_bundle_strict(&mutated).is_err(),
        "strict replay must reject the corrupted ground-arithmetic certificate",
    );
}

#[test]
fn ground_qf_lra_comparison_collapse_is_strict_verified() {
    assert_ground_qf_lra_collapse_is_strict("(assert (not (< 0.0 1.0)))", true);
}

#[test]
fn ground_qf_lra_addition_equality_collapse_is_strict_verified() {
    assert_ground_qf_lra_collapse_is_strict("(assert (not (= (+ 2.0 3.0) 5.0)))", false);
}

#[test]
fn ground_qf_lra_collapse_operator_and_polarity_matrix_is_strict_verified() {
    for script in [
        "(assert (< 1.0 0.0))",
        "(assert (= 2.0 3.0))",
        "(assert (not (<= 0.0 1.0)))",
        "(assert (not (> 1.0 0.0)))",
        "(assert (not (>= 1.0 0.0)))",
    ] {
        assert_ground_qf_lra_collapse_is_strict(script, true);
    }
}

#[test]
fn ground_qf_lra_collapse_near_misses_remain_satisfiable() {
    for script in [
        "(assert (not (< 1.0 0.0)))",
        "(assert (not (= (+ 2.0 3.0) 6.0)))",
        "(assert (< 0.0 1.0))",
        "(assert (= 2.0 2.0))",
        "(assert (not (<= 1.0 0.0)))",
        "(assert (not (> 0.0 1.0)))",
        "(assert (not (>= 0.0 1.0)))",
    ] {
        #[allow(deprecated)]
        let mut solver = Solver::new(Logic::QfLra);
        solver.set_produce_proofs(true);
        solver
            .parse_smtlib2(script)
            .expect("ground QF_LRA near-miss must parse");
        let verdict = solver.check_sat();
        assert!(
            verdict.is_sat(),
            "satisfiable arithmetic near-miss must not gain a refutation: \
             {script}: {verdict:?} / {:?}",
            solver.unknown_reason(),
        );
    }
}

/// SAT result returns None for the proof artifact.
#[test]
fn artifact_sat_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None after SAT result"
    );
}
