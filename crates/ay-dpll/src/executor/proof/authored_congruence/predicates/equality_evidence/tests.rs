// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native regressions composing checked NaN equality with UF congruence.
//! Serialized bundles independently replay the symbolic equality derivation.

use super::super::tests::{conditional_source, parsed, reachable_steps, scope};
use super::*;
use crate::api::{Logic, Solver};
use ay_core::time::Instant;
use ay_core::ProofStep;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

fn source(eb: u32, sb: u32, reverse: bool, support: &str) -> String {
    let (left, right) = if reverse { ("y", "x") } else { ("x", "y") };
    format!(
        "(set-logic ALL) (declare-fun g ((_ FloatingPoint {eb} {sb})) Bool)
        (declare-const x (_ FloatingPoint {eb} {sb}))
        (declare-const y (_ FloatingPoint {eb} {sb}))
        (declare-const z (_ FloatingPoint {eb} {sb}))
        (assert (g {left})) (assert (not (g {right}))) {support}"
    )
}

const BOTH: &str = "(assert (fp.isNaN x)) (assert (fp.isNaN y))";

fn attempt(executor: &mut Executor, budget: usize, checks: usize) -> (Outcome, Proof, Attempt) {
    let (roots, equalities) = scope(executor);
    let mut proof = Proof::new();
    proof.add_assume(roots[0], None);
    let before = proof.steps.clone();
    let mut allowance = Attempt {
        work: budget,
        checks,
    };
    let outcome = executor.try_authored_predicate_with_attempt(
        &mut proof,
        &roots,
        &equalities,
        &mut allowance,
    );
    if outcome != Outcome::Committed {
        assert_eq!(proof.steps, before);
    }
    (outcome, proof, allowance)
}

fn assert_bundle(bundle: &ay_proof::SerializableProofBundle, assumptions: usize) {
    let encoded = serde_json::to_vec(bundle).unwrap();
    let restored: ay_proof::SerializableProofBundle = serde_json::from_slice(&encoded).unwrap();
    assert!(ay_proof::re_check_bundle_strict(&restored)
        .unwrap()
        .quality
        .is_complete());
    let proof = Proof::from_steps(restored.steps.clone());
    let reachable = reachable_steps(&proof);
    let mut roots: Vec<_> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(i, step)| match step {
            ProofStep::Assume(root) if reachable[i] => Some(*root),
            _ => None,
        })
        .collect();
    roots.sort_unstable();
    roots.dedup();
    assert_eq!(roots.len(), assumptions);
    assert!(roots
        .iter()
        .all(|root| restored.obligation_assertions.contains(root)));
    let equality = proof
        .steps
        .iter()
        .enumerate()
        .find_map(|(i, step)| match step {
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::FpClassification { .. },
                ..
            } if reachable[i] => Some(*clause.last().unwrap()),
            _ => None,
        })
        .expect("reachable checked NaN theorem");
    assert!(!restored.obligation_assertions.contains(&equality));
    assert!(!proof.steps.iter().any(|step| matches!(step,
        ProofStep::Assume(root) if *root == equality
    )));
    let index = proof
        .steps
        .iter()
        .enumerate()
        .find_map(|(i, step)| match step {
            ProofStep::Resolution { clause, .. } if reachable[i] && clause == &[equality] => {
                Some(i)
            }
            _ => None,
        })
        .expect("reachable derived equality unit");
    let mut forged = restored;
    forged.steps[index] = ProofStep::Assume(equality);
    assert!(ay_proof::re_check_bundle_strict(&forged).is_err());
}

fn checked(executor: &Executor, proof: &Proof, count: usize) {
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let roots = executor.exact_concrete_authored_scope();
    ay_proof::validate_reachable_assumes_in_problem_scope(proof, &roots).unwrap();
    assert_bundle(
        &ay_proof::SerializableProofBundle::from_proof(proof, &executor.ctx.terms, roots),
        count,
    );
}

#[test]
fn nan_argument_units_use_derived_equalities_for_all_formats_and_orientations() {
    for (eb, sb) in [(5, 11), (8, 24), (11, 53)] {
        for reverse in [false, true] {
            let mut executor = parsed(&source(eb, sb, reverse, BOTH));
            let (outcome, proof, _) = attempt(&mut executor, MAX_WORK, 0);
            assert_eq!(outcome, Outcome::Committed);
            checked(&executor, &proof, 4);
        }
    }
}

#[test]
fn nan_mixed_and_repeated_arguments_preserve_authored_and_derived_evidence() {
    let mut executor = parsed(
        "(set-logic ALL)
        (declare-fun g (Int (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)) Bool)
        (declare-const a Int) (declare-const b Int)
        (declare-const x (_ FloatingPoint 8 24)) (declare-const y (_ FloatingPoint 8 24))
        (assert (g a x x)) (assert (not (g b y y))) (assert (= b a))
        (assert (fp.isNaN y)) (assert (fp.isNaN x))",
    );
    let (outcome, proof, _) = attempt(&mut executor, MAX_WORK, 0);
    assert_eq!(outcome, Outcome::Committed);
    checked(&executor, &proof, 5);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::FpClassification { .. },
                    ..
                }
            ))
            .count(),
        1
    );
    let clause = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::EufCongruentPred,
                ..
            } => Some(clause),
            _ => None,
        })
        .unwrap();
    assert_eq!(clause.len(), 5);
    assert_eq!(clause[1], clause[2]);
}

fn wide() -> String {
    conditional_source(&[
        "(g x63)",
        "(not (g x64))",
        "(fp.isNaN x63)",
        "(fp.isNaN x64)",
    ])
}

#[test]
fn nan_full_65_application_native_bundles_preserve_four_authored_roots() {
    for input in [wide(), wide().replace("(fp.isNaN x63)", "(fp.isNaN x0)")] {
        let mut solver = Solver::new(Logic::All);
        solver.set_produce_proofs(true);
        solver.parse_smtlib2(&input).unwrap();
        assert!(
            solver.check_sat().is_unsat(),
            "{:?}",
            solver.unknown_reason()
        );
        assert!(solver
            .last_strict_proof_quality()
            .unwrap()
            .unwrap()
            .is_complete());
        assert_bundle(&solver.export_last_unsat_bundle().unwrap(), 4);
    }
}

#[test]
fn nan_missing_each_root_remains_validated_sat_without_a_certificate() {
    for support in ["(assert (fp.isNaN x))", "(assert (fp.isNaN y))", ""] {
        let mut solver = Solver::new(Logic::All);
        solver.set_produce_proofs(true);
        solver
            .parse_smtlib2(&source(5, 11, false, support))
            .unwrap();
        let details = solver.check_sat_with_details();
        assert!(details.result.is_sat(), "{details:?}");
        assert!(details.verification.sat_model_validated);
        assert!(solver.export_last_unsat_bundle().is_none());
    }
}

#[test]
fn nan_scope_pop_and_foreign_positive_roots_cannot_authorize_a_proof() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&source(5, 11, false, "(assert (fp.isNaN x))"))
        .unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    solver.push();
    solver.parse_smtlib2("(assert (fp.isNaN y))").unwrap();
    assert!(solver.check_sat().is_unsat());
    assert_bundle(&solver.export_last_unsat_bundle().unwrap(), 4);
    solver.pop();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    assert!(solver.export_last_unsat_bundle().is_none());

    let mut executor = parsed(&source(5, 11, false, ""));
    let (mut roots, equalities) = scope(&executor);
    for name in ["x", "y"] {
        let term = executor.ctx.symbol_info(name).unwrap().term.unwrap();
        roots.push(
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("fp.isNaN"), [term], Sort::Bool),
        );
    }
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Declined
    );
    assert!(proof.steps.is_empty());
    executor
        .execute_all(&ay_frontend::parse(&format!("(push 1) {BOTH}")).unwrap())
        .unwrap();
    let (old_roots, old_equalities) = scope(&executor);
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &old_roots,
            &old_equalities,
            &mut Attempt::new(),
        ),
        Outcome::Declined
    );
    assert!(proof.steps.is_empty());
}

#[test]
fn nan_census_ignores_indexed_malformed_and_non_nan_classification_roots() {
    let mut executor = parsed(&source(5, 11, false, ""));
    let x = executor.ctx.symbol_info("x").unwrap().term.unwrap();
    let zero = executor.ctx.terms.mk_int(0.into());
    let bad = [
        (Symbol::indexed("fp.isNaN", vec![0]), vec![x], Sort::Bool),
        (Symbol::named("fp.isNaN"), vec![], Sort::Bool),
        (Symbol::named("fp.isNaN"), vec![x, x], Sort::Bool),
        (Symbol::named("fp.isNaN"), vec![zero], Sort::Bool),
        (Symbol::named("fp.isNaN"), vec![x], Sort::Int),
        (Symbol::named("fp.isZero"), vec![x], Sort::Bool),
        (Symbol::named("fp.isInfinite"), vec![x], Sort::Bool),
    ];
    let mut roots = Vec::new();
    for (symbol, args, sort) in bad {
        roots.push(executor.ctx.terms.mk_app(symbol, args, sort));
    }
    assert!(collect(&mut executor, &roots, &mut Attempt::new())
        .unwrap()
        .is_empty());
    let mut zero_budget = Attempt { work: 0, checks: 0 };
    assert!(collect(&mut executor, &roots, &mut zero_budget).is_none());
    assert_eq!(zero_budget.work, 0);
}

#[test]
fn nan_evidence_full_attempts_share_exact_work_and_commit_caps() {
    for input in [source(8, 24, false, BOTH), wide()] {
        let (outcome, _, measured) = attempt(&mut parsed(&input), MAX_WORK, 0);
        assert_eq!(outcome, Outcome::Committed);
        let used = MAX_WORK - measured.work;
        assert!(used > 0 && used < MAX_WORK, "metered NaN proof cost {used}");
        let (outcome, _, exact) = attempt(&mut parsed(&input), used, 0);
        assert_eq!(outcome, Outcome::Committed);
        assert_eq!(exact.work, 0);
        assert_eq!(
            attempt(&mut parsed(&input), used - 1, 0).0,
            Outcome::Declined
        );
        assert_eq!(
            attempt(&mut parsed(&input), MAX_WORK, MAX_COMMIT_ATTEMPTS).0,
            Outcome::Declined
        );
        let (outcome, _, last) = attempt(&mut parsed(&input), MAX_WORK, MAX_COMMIT_ATTEMPTS - 1);
        assert_eq!(outcome, Outcome::Committed);
        assert_eq!(last.checks, MAX_COMMIT_ATTEMPTS);
    }
}

#[test]
fn nan_census_and_evidence_respect_live_and_recorded_terminal_stops() {
    let mut executor = parsed(&source(8, 24, false, BOTH));
    let (roots, _) = scope(&executor);
    let mut allowance = Attempt::new();
    let nans = collect(&mut executor, &roots, &mut allowance).unwrap();
    let x = executor.ctx.symbol_info("x").unwrap().term.unwrap();
    let y = executor.ctx.symbol_info("y").unwrap().term.unwrap();
    let evidence = find_nan(&nans, x, y, &mut allowance.work).unwrap();
    let interrupt = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(interrupt.clone());
    assert!(evidence
        .literal(&mut executor, &mut allowance.work)
        .is_none());
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(attempt(&mut executor, MAX_WORK, 0).0, Outcome::Stopped);
    for origin in [
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::DeterministicResourceBudget,
    ] {
        let mut executor = parsed(&source(8, 24, false, BOTH));
        executor.record_unknown_from_origin(origin);
        assert_eq!(attempt(&mut executor, MAX_WORK, 0).0, Outcome::Stopped);
    }
    let mut executor = parsed(&source(8, 24, false, BOTH));
    executor.set_deadline(Some(Instant::now() - Duration::from_secs(1)));
    assert_eq!(attempt(&mut executor, MAX_WORK, 0).0, Outcome::Stopped);
}

#[test]
fn nan_evidence_cannot_generalize_zero_classes_or_ieee_equality() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&source(
            5,
            11,
            false,
            "(assert (fp.isZero x)) (assert (fp.isZero y)) (assert (fp.eq x y))
         (assert (= x (_ +zero 5 11))) (assert (= y (_ -zero 5 11)))",
        ))
        .unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    assert!(solver.export_last_unsat_bundle().is_none());
}

#[test]
fn nan_forged_endpoint_metadata_fails_independent_theory_replay() {
    let input = source(8, 24, false, BOTH).replace("(not (g y))", "(not (g z))");
    let mut executor = parsed(&input);
    let (roots, equalities) = scope(&executor);
    let mut allowance = Attempt::new();
    let mut nans = collect(&mut executor, &roots, &mut allowance).unwrap();
    let z = executor.ctx.symbol_info("z").unwrap().term.unwrap();
    nans[1].subject = z; // The actual authored premise remains isNaN(y).
    let TermData::Not(atom) = executor.ctx.terms.get(roots[1]) else {
        panic!()
    };
    let pair = executor
        .authored_predicate_pair(
            roots[0],
            roots[1],
            *atom,
            &equalities,
            &nans,
            &mut allowance.work,
        )
        .unwrap();
    let candidate = executor
        .emit_authored_predicate_pair(&pair, &mut allowance.work)
        .unwrap();
    assert!(executor
        .check_proof_strict_with_datatypes(&candidate)
        .is_err());
    let mut untouched = Proof::new();
    assert_eq!(
        executor.commit_predicate_candidate(
            &mut untouched,
            candidate,
            &roots,
            &pair,
            &mut allowance,
        ),
        Outcome::Declined
    );
    assert!(untouched.steps.is_empty());
}
