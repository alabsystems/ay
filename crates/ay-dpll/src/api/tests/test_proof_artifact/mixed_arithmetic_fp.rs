// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const FALSE_FORALL: &str = "(forall ((q Real)) (and (> (+ q q) q) (fp.isNaN (_ NaN 11 53))))";
const TRUE_FORALL: &str = "(forall ((q Real)) (or (= q q) (fp.isNaN (_ NaN 11 53))))";

fn fixture() -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2("(set-logic FPLRA)").unwrap();
    solver
}

fn assert_complete_native_fp_refutation(solver: &mut Solver) {
    assert!(
        solver.check_sat().is_unsat(),
        "reason={:?}, checker={:?}, retained proof={:?}",
        solver.unknown_reason(),
        solver.executor.proof_check_result(),
        solver.executor.retained_internal_proof_for_test()
    );
    assert_eq!(solver.unknown_reason(), None);
    assert_fp_ground_eval_refutation_is_plainly_checked(solver);
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
}

#[test]
fn fplra_zero_instance_has_an_offline_checked_native_artifact() {
    let mut solver = fixture();
    solver
        .parse_smtlib2(&format!("(assert {FALSE_FORALL})"))
        .unwrap();
    assert_complete_native_fp_refutation(&mut solver);
}

#[test]
fn fplra_mixed_arithmetic_binders_have_typed_zero_instances() {
    let mut solver = fixture();
    solver
        .parse_smtlib2(
            "(assert (forall ((i Int) (q Real))
               (and (> (+ i i) i) (> (+ q q) q) (fp.isNaN (_ NaN 11 53)))))",
        )
        .unwrap();
    assert_complete_native_fp_refutation(&mut solver);
}

#[test]
fn fplra_rounded_fp_instance_has_an_offline_checked_native_artifact() {
    let mut solver = fixture();
    solver
        .parse_smtlib2(
            "(assert (forall ((q Real))
               (and (> (+ q q) q)
                    (fp.isNaN (fp.add RNE (_ NaN 11 53) (_ NaN 11 53))))))",
        )
        .unwrap();
    assert_complete_native_fp_refutation(&mut solver);
}

#[test]
fn fplra_conjunctive_universal_is_derived_from_its_authored_root() {
    let mut solver = fixture();
    solver
        .parse_smtlib2(&format!(
            "(declare-const enabled Bool)(assert (and enabled {FALSE_FORALL}))"
        ))
        .unwrap();
    assert_complete_native_fp_refutation(&mut solver);
    assert!(solver
        .last_proof()
        .unwrap()
        .steps
        .iter()
        .any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )));
}

#[test]
fn fplra_false_universal_in_disjunction_cannot_be_assumed() {
    let mut solver = fixture();
    solver
        .parse_smtlib2(&format!(
            "(declare-const enabled Bool)\
             (assert (or enabled {FALSE_FORALL}))(assert enabled)"
        ))
        .unwrap();
    assert!(!solver.check_sat().is_unsat());
    assert!(solver.export_last_unsat_bundle().is_none());
}

#[test]
fn fplra_popped_refutation_cannot_authorize_a_tautology() {
    let mut solver = fixture();
    solver.push();
    solver
        .parse_smtlib2(&format!("(assert {FALSE_FORALL})"))
        .unwrap();
    assert_complete_native_fp_refutation(&mut solver);
    solver.pop();
    solver
        .parse_smtlib2(&format!("(assert {TRUE_FORALL})"))
        .unwrap();
    assert!(!solver.check_sat().is_unsat());
    assert!(solver.last_proof().is_none());
    assert!(solver.export_last_unsat_bundle().is_none());
}

#[test]
fn fplra_external_style_self_check_keeps_its_surface_refusal() {
    let mut solver = fixture();
    solver.executor.set_self_check(true);
    solver
        .parse_smtlib2(&format!("(assert {FALSE_FORALL})"))
        .unwrap();
    assert!(solver.check_sat().is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(UnknownReason::SelfCheckRejected)
    );
    assert!(solver.export_last_unsat_bundle().is_none());
}
