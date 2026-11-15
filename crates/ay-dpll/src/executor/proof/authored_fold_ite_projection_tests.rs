// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Executor;
use ay_core::{AletheRule, Proof, ProofStep};

fn candidate(root: &str) -> (Executor, Proof, Option<()>) {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(&format!(
        "(declare-const c Bool)(declare-const q (_ BitVec 2))\n\
         (declare-fun m ((_ BitVec 2)) (_ BitVec 2))(assert {root})"
    ))
    .expect("typed source fixture parses");
    executor.execute_all(&commands).expect("fixture elaborates");
    let ay_frontend::Command::Assert(assertion) = commands.last().unwrap() else {
        panic!("original assertion");
    };
    let raw = executor
        .raw_intern_surface(assertion)
        .expect("exact raw root");
    executor.record_rebuilt_authored_proof_premise(raw);
    let mut proof = Proof::new();
    let assume = proof.add_assume(raw, None);
    let result = super::super::refute_root(&mut executor.ctx.terms, &mut proof, assume, raw);
    (executor, proof, result)
}

#[test]
fn selected_ite_projection_preserves_orientation_polarity_and_side_clauses() {
    for root in [
        "(and c (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))))",
        "(and c (not (= (_ bv1 2) (ite c (_ bv1 2) (m q)))))",
        "(and (not c) (not (= (ite c (m q) (_ bv1 2)) (_ bv1 2))))",
        "(and (not c) (not (= (_ bv1 2) (ite c (m q) (_ bv1 2)))))",
        "(and c (or (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))) (not c)))",
    ] {
        let (executor, proof, result) = candidate(root);
        assert!(result.is_some(), "no derivation: {root}");
        assert!(Executor::proof_derives_empty_clause(&proof));
        assert!(
            executor
                .check_proof_strict_with_datatypes(&proof)
                .is_ok_and(|quality| quality.is_complete()),
            "whole proof rejected: {root}"
        );
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::IteBranchProjection,
                ..
            }
        )));
    }
}

#[test]
fn selected_ite_projection_never_borrows_missing_wrong_or_sibling_guards() {
    for root in [
        "(not (= (ite c (_ bv1 2) (m q)) (_ bv1 2)))",
        "(and (not c) (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))))",
        "(and c (not (= (ite c (_ bv2 2) (m q)) (_ bv1 2))))",
        "(and c (not (= (ite c (m q) (_ bv1 2)) (_ bv1 2))))",
        "(or (and c (not c)) (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))))",
        "(or c (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))))",
    ] {
        let (executor, proof, result) = candidate(root);
        assert!(result.is_none(), "satisfiable source was refuted: {root}");
        assert!(
            !Executor::proof_derives_empty_clause(&proof)
                || !executor
                    .check_proof_strict_with_datatypes(&proof)
                    .is_ok_and(|quality| quality.is_complete())
        );
    }
}

#[test]
fn selected_ite_fact_search_charges_the_existing_budget_before_emission() {
    let mut executor = Executor::new();
    let mut problem = String::from(
        "(declare-const c Bool)(declare-const q (_ BitVec 2))\n\
        (declare-fun m ((_ BitVec 2)) (_ BitVec 2))(assert c)",
    );
    for index in 0..6 {
        problem.push_str(&format!("(declare-const u{index} Bool)(assert u{index})"));
    }
    problem.push_str("(assert (not (= (ite c (_ bv1 2) (m q)) (_ bv1 2))))");
    let commands = ay_frontend::parse(&problem).expect("fixture parses");
    executor.execute_all(&commands).expect("fixture elaborates");
    let mut proof = Proof::new();
    let mut facts = Vec::new();
    for command in &commands {
        if let ay_frontend::Command::Assert(assertion) = command {
            let raw = executor
                .raw_intern_surface(assertion)
                .expect("raw assertion");
            executor.record_rebuilt_authored_proof_premise(raw);
            let id = proof.add_assume(raw, None);
            facts.push((
                raw,
                Derived {
                    id,
                    clause: vec![raw],
                },
            ));
        }
    }
    let (negative, derived) = facts.pop().unwrap();
    let TermData::Not(equality) = executor.ctx.terms.get(negative) else {
        panic!("disequality");
    };
    let equality = *equality;
    let before = proof.steps.len();
    // Four units could emit the three steps and copy the unit guard, but
    // cannot visit the six unrelated facts first. No new budget exists.
    let mut refuter = Refuter {
        terms: &mut executor.ctx.terms,
        proof: &mut proof,
        facts,
        budget: 4,
    };
    assert!(refuter
        .refute_selected_ite(equality, &derived, &[])
        .is_none());
    assert_eq!(proof.steps.len(), before);
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust | AletheRule::Hole,
            ..
        }
    )));
}
