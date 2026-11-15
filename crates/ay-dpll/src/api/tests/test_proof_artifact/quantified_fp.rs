// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn universal(body: &str) -> String {
    let fp = "(fp ((_ extract 63 63) q) ((_ extract 62 52) q) ((_ extract 51 0) q))";
    format!(
        "(assert (forall ((q (_ BitVec 64))) {}))",
        body.replace("BITS", fp)
    )
}

#[test]
fn bvfp_universal_has_an_offline_checked_native_artifact() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2("(set-logic BVFP)").unwrap();
    solver.parse_smtlib2(&universal("(fp.isNaN BITS)")).unwrap();
    assert!(
        solver.check_sat().is_unsat(),
        "reason={:?}, checker={:?}, retained proof={:?}",
        solver.unknown_reason(),
        solver.executor.proof_check_result(),
        solver.executor.retained_internal_proof_for_test()
    );
    assert_fp_ground_eval_refutation_is_plainly_checked(&solver);
    assert!(solver
        .last_proof()
        .unwrap()
        .steps
        .iter()
        .any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )));
    let artifact = solver.export_last_unsat_artifact().unwrap();
    assert!(artifact.carcara_surface.unsupported_reason().is_some());
}

#[test]
fn bvfp_non_nan_universal_is_refuted_at_a_nan_pattern() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2("(set-logic BVFP)").unwrap();
    solver
        .parse_smtlib2(&universal("(not (fp.isNaN BITS))"))
        .unwrap();
    assert!(
        solver.check_sat().is_unsat(),
        "{:?}",
        solver.unknown_reason()
    );
    assert_fp_ground_eval_refutation_is_plainly_checked(&solver);
}

#[test]
fn bvfp_external_style_self_check_still_refuses_the_unsupported_surface() {
    // Native strict replay and the external-style self-check contract are
    // distinct. This producer must not relax the latter's surface gate.
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.executor.set_self_check(true);
    solver.parse_smtlib2("(set-logic BVFP)").unwrap();
    solver.parse_smtlib2(&universal("(fp.isNaN BITS)")).unwrap();
    assert!(solver.check_sat().is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::SelfCheckRejected)
    );
    assert!(solver.export_last_unsat_bundle().is_none());
}

#[test]
fn bvfp_tautology_cannot_reuse_a_popped_refutation() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2("(set-logic BVFP)").unwrap();
    solver.push();
    solver.parse_smtlib2(&universal("(fp.isNaN BITS)")).unwrap();
    assert!(solver.check_sat().is_unsat());
    assert!(solver.export_last_unsat_bundle().is_some());
    solver.pop();
    solver
        .parse_smtlib2(&universal("(or (fp.isNaN BITS) (not (fp.isNaN BITS)))"))
        .unwrap();
    assert!(!solver.check_sat().is_unsat());
    assert!(solver.last_proof().is_none());
    assert!(solver.export_last_unsat_bundle().is_none());
}
