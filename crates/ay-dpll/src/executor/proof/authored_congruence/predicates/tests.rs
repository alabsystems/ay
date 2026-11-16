// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Solver};
use ay_core::ProofStep;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

pub(super) fn parsed(source: &str) -> Box<Executor> {
    let mut executor = Box::new(Executor::new());
    let commands = ay_frontend::parse(source).unwrap();
    executor.execute_all(&commands).unwrap();
    executor
}

pub(super) fn scope(executor: &Executor) -> (Vec<TermId>, Vec<(TermId, TermId, TermId)>) {
    let roots = executor.exact_concrete_authored_scope();
    let equalities = roots
        .iter()
        .filter_map(|&root| {
            super::super::super::decode_eq_local(&executor.ctx.terms, root)
                .map(|(left, right)| (root, left, right))
        })
        .collect();
    (roots, equalities)
}

fn attempt(executor: &mut Executor) -> (Outcome, Proof) {
    let (roots, equalities) = scope(executor);
    let mut proof = Proof::new();
    let result = executor.try_authored_predicate_congruence(&mut proof, &roots, &equalities);
    (result, proof)
}

fn direct_source(eb: u32, sb: u32, equality: &str) -> String {
    format!(
        "(set-logic ALL)
        (declare-fun g ((_ FloatingPoint {eb} {sb})) Bool)
        (declare-fun h ((_ FloatingPoint {eb} {sb})) Bool)
        (declare-const x (_ FloatingPoint {eb} {sb}))
        (declare-const y (_ FloatingPoint {eb} {sb}))
        (declare-const z (_ FloatingPoint {eb} {sb}))
        (assert (g x)) (assert (not (g y))) {equality}"
    )
}

fn assert_checked(executor: &Executor, proof: &Proof) {
    assert!(Executor::proof_derives_empty_clause(proof));
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &executor.exact_concrete_authored_scope(),
    )
    .unwrap();
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufCongruentPred,
            ..
        }
    )));
}

#[test]
fn predicate_units_use_structural_equality_for_each_fp_format_and_orientation() {
    for (eb, sb) in [(5, 11), (8, 24), (11, 53)] {
        for equality in ["(assert (= x y))", "(assert (= y x))"] {
            let mut executor = parsed(&direct_source(eb, sb, equality));
            let (outcome, proof) = attempt(&mut executor);
            assert_eq!(outcome, Outcome::Committed);
            assert_checked(&executor, &proof);
            assert_eq!(
                proof
                    .steps
                    .iter()
                    .filter(|step| matches!(step, ProofStep::Assume(_)))
                    .count(),
                3
            );
        }
    }
}

#[test]
fn predicate_units_discharge_repeated_and_reflexive_argument_positions() {
    let mut executor = parsed(
        "(set-logic ALL)
        (declare-fun g (Int Int Int) Bool)
        (declare-const x Int) (declare-const y Int) (declare-const z Int)
        (assert (g x x z)) (assert (not (g y y z))) (assert (= y x))",
    );
    let (outcome, proof) = attempt(&mut executor);
    assert_eq!(outcome, Outcome::Committed);
    assert_checked(&executor, &proof);
    let clause = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufCongruentPred,
                clause,
                ..
            } => Some(clause),
            _ => None,
        })
        .unwrap();
    assert_eq!(clause.len(), 4);
    assert_eq!(clause[0], clause[1]);
}

#[test]
fn predicate_units_decline_missing_wrong_ieee_and_partial_nan_premises() {
    for equality in [
        "",
        "(assert (= x z))",
        "(assert (fp.eq x y))",
        "(assert (fp.isNaN x))",
    ] {
        let mut executor = parsed(&direct_source(5, 11, equality));
        let (outcome, proof) = attempt(&mut executor);
        assert_eq!(outcome, Outcome::Declined, "{equality}");
        assert_eq!(proof.steps, [] as [ProofStep; 0]);
    }
    let source = direct_source(5, 11, "(assert (= x y))").replace("(not (g y))", "(not (h y))");
    assert_eq!(attempt(&mut parsed(&source)).0, Outcome::Declined);
}

#[test]
fn predicate_units_refuse_malformed_pair_metadata_and_nonordinary_heads() {
    let mut executor = parsed(&direct_source(5, 11, "(assert (= x y))"));
    let (roots, mut equalities) = scope(&executor);
    let positive = roots[0];
    let negative = roots[1];
    let TermData::Not(atom) = executor.ctx.terms.get(negative) else {
        panic!()
    };
    let atom = *atom;
    let mut work = MAX_WORK;
    assert!(executor
        .authored_predicate_pair(positive, negative, atom, &equalities, &[], &mut work)
        .is_some());
    assert!(executor
        .authored_predicate_pair(positive, positive, atom, &equalities, &[], &mut work)
        .is_none());
    let z = executor.ctx.symbol_info("z").unwrap().term.unwrap();
    equalities[0].2 = z;
    assert!(executor
        .authored_predicate_pair(positive, negative, atom, &equalities, &[], &mut work)
        .is_none());
    let bad = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![z, z], Sort::Bool);
    let bad_negative = executor.ctx.terms.mk_not_raw(bad);
    assert!(executor
        .authored_predicate_pair(positive, bad_negative, bad, &[], &[], &mut work)
        .is_none());
    let integer = executor.ctx.terms.mk_int(0.into());
    let bad_sort = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![integer], Sort::Bool);
    let bad_negative = executor.ctx.terms.mk_not_raw(bad_sort);
    assert!(executor
        .authored_predicate_pair(positive, bad_negative, bad_sort, &[], &[], &mut work)
        .is_none());

    let mut interpreted = parsed(
        "(set-logic ALL)
        (declare-const x Int) (declare-const y Int)
        (assert (< x 0)) (assert (not (< y 0))) (assert (= x y))",
    );
    assert_eq!(attempt(&mut interpreted).0, Outcome::Declined);
}

#[test]
fn predicate_units_reject_foreign_scope_and_popped_declaration() {
    let source = direct_source(5, 11, "(assert (= x y))").replacen(
        "(set-logic ALL)",
        "(set-logic ALL) (push 1)",
        1,
    );
    let mut executor = parsed(&source);
    let (roots, equalities) = scope(&executor);
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_congruence(&mut proof, &roots, &equalities),
        Outcome::Committed
    );
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    let mut untouched = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_congruence(&mut untouched, &roots, &equalities),
        Outcome::Declined
    );
    assert_eq!(untouched.steps, [] as [ProofStep; 0]);

    let mut executor = parsed(&direct_source(5, 11, ""));
    let (mut roots, _) = scope(&executor);
    let x = executor.ctx.symbol_info("x").unwrap().term.unwrap();
    let y = executor.ctx.symbol_info("y").unwrap().term.unwrap();
    let foreign = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    roots.push(foreign);
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_congruence(&mut proof, &roots, &[(foreign, x, y)]),
        Outcome::Declined
    );
    assert!(
        proof.steps.is_empty(),
        "passed-in roots do not grant source authority"
    );
}

#[test]
fn predicate_units_bound_search_and_keep_observed_stops_sticky() {
    let mut executor = parsed(&direct_source(5, 11, "(assert (= x y))"));
    let (roots, equalities) = scope(&executor);
    let TermData::Not(atom) = executor.ctx.terms.get(roots[1]) else {
        panic!()
    };
    assert!(executor
        .authored_predicate_pair(roots[0], roots[1], *atom, &equalities, &[], &mut 0)
        .is_none());
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_predicate_congruence(
            &mut proof,
            &vec![roots[0]; MAX_ROOTS + 1],
            &equalities
        ),
        Outcome::Declined
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
    let interrupted = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(interrupted.clone());
    assert_eq!(attempt(&mut executor).0, Outcome::Stopped);
    interrupted.store(false, Ordering::Relaxed);
    assert_eq!(attempt(&mut executor).0, Outcome::Stopped);
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Interrupted)
    );
    for origin in [
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::DeterministicResourceBudget,
    ] {
        let mut executor = parsed(&direct_source(5, 11, "(assert (= x y))"));
        executor.record_unknown_from_origin(origin);
        let (outcome, proof) = attempt(&mut executor);
        assert_eq!(outcome, Outcome::Stopped);
        assert_eq!(proof.steps, [] as [ProofStep; 0]);
    }
}

fn wide_source() -> String {
    let mut source = String::from(
        "(set-logic ALL)
        (declare-fun g ((_ FloatingPoint 5 11)) Bool)",
    );
    for index in 0..65 {
        source.push_str(&format!("(declare-const x{index} (_ FloatingPoint 5 11))"));
    }
    for index in 0..64 {
        source.push_str(&format!("(assert (g x{index}))"));
    }
    source.push_str("(assert (not (g x64))) (assert (= x0 x64))");
    source
}

#[test]
fn wide_fp_predicate_native_bundle_is_complete_offline_and_scope_bound() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2(&wide_source()).unwrap();
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
    assert!(solver
        .last_proof()
        .unwrap()
        .steps
        .iter()
        .any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufCongruentPred,
                ..
            }
        )));
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native proof bundle");
    let encoded = serde_json::to_vec(&bundle).unwrap();
    let mut restored: ay_proof::SerializableProofBundle = serde_json::from_slice(&encoded).unwrap();
    let checked = ay_proof::re_check_bundle_strict(&restored).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms.len(), 3);
    restored.obligation_assertions.clear();
    assert!(ay_proof::re_check_bundle_strict(&restored).is_err());
}

#[test]
fn wide_fp_predicate_external_self_check_keeps_unsupported_surface_refusal() {
    let mut executor = parsed(&wide_source());
    executor.set_produce_proofs(true);
    executor.set_self_check(true);
    let output = executor
        .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(output, ["unknown"]);
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::SelfCheckRejected)
    );
    assert!(executor.last_proof().is_none());
}

#[test]
fn fp_ieee_equal_signed_zeros_still_have_opposite_uf_outputs_and_no_certificate() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&direct_source(
            5,
            11,
            "(assert (fp.eq x y)) (assert (= x (_ +zero 5 11)))
         (assert (= y (_ -zero 5 11)))",
        ))
        .unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.verification.sat_model_validated);
    assert!(solver.export_last_unsat_bundle().is_none());
}

pub(super) const CONDITIONAL_OR: [&str; 4] = [
    "(or condition (g x63))",
    "(or condition (not (g x64)))",
    "(or (not condition) (not (g x63)))",
    "(or (not condition) (g x64))",
];

pub(super) fn conditional_source(clauses: &[&str]) -> String {
    let mut source = String::from(
        "(set-logic ALL) (declare-fun g ((_ FloatingPoint 5 11)) Bool)
         (declare-const condition Bool)",
    );
    for index in 0..65 {
        source.push_str(&format!("(declare-const x{index} (_ FloatingPoint 5 11))"));
    }
    for index in 0..63 {
        source.push_str(&format!("(assert (g x{index}))"));
    }
    for clause in clauses {
        source.push_str(&format!("(assert {clause})"));
    }
    source
}

pub(super) fn reachable_steps(proof: &Proof) -> Vec<bool> {
    let mut reachable = vec![false; proof.steps.len()];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            _ => false,
        };
        if empty {
            reachable[index] = true;
            stack.push(index);
        }
    }
    while let Some(index) = stack.pop() {
        let mut visit = |id: ProofId| {
            let index = id.0 as usize;
            assert!(index < reachable.len());
            if !reachable[index] {
                reachable[index] = true;
                stack.push(index);
            }
        };
        match &proof.steps[index] {
            ProofStep::Step { premises, .. } => premises.iter().copied().for_each(&mut visit),
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                visit(*clause1);
                visit(*clause2);
            }
            _ => {}
        }
    }
    reachable
}
