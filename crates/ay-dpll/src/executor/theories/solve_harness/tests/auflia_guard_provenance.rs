// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The AUFLIA producer must retain checked evidence when substitution removes
//! an arithmetic guard from an authored disjunction.

use super::*;
use ay_core::{Proof, ProofStep};

fn prepared_guard(length: i64, duplicate_source: bool) -> (Executor, Vec<TermId>, TermId) {
    let script = format!(
        "(set-option :produce-proofs true)
         (set-logic QF_AUFLIA)
         (declare-const a (Array Int Int))
         (declare-const b (Array Int Int))
         (declare-const i Int)
         (declare-const j Int)
         (declare-const len Int)
         (declare-const e Bool)
         (declare-fun f (Int) Int)
         (assert (or (not e) (= (select a i) (select b j)) (not (< 0 len))))
         (assert (= len {length}))
         (assert (= (f i) 7))"
    );
    let mut exec = Executor::new();
    exec.execute_all(&parse(&script).unwrap()).unwrap();
    if duplicate_source {
        exec.ctx.assertions.push(exec.ctx.assertions[0]);
    }
    let originals = exec.ctx.assertions.clone();
    let TermData::App(op, args) = exec.ctx.terms.get(originals[0]) else {
        panic!("fixture guard must be a disjunction");
    };
    assert_eq!(op.name(), "or");
    let kept = args[..2].to_vec();
    let target = exec.ctx.terms.mk_or(kept);
    assert_ne!(target, originals[0]);
    exec.preprocess_auflia_assertions_with_proof_provenance();
    (exec, originals, target)
}

fn rewritten_refutation(exec: &mut Executor, roots: &[TermId], target: TermId) -> Proof {
    let mut proof = Proof::new();
    let assumed = proof.add_assume(target, None);
    let negated = exec.ctx.terms.mk_not_raw(target);
    let counter = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), target, assumed, counter);
    exec.derive_propagated_value_assumptions(&mut proof, roots);
    proof
}

fn assumes(proof: &Proof) -> Vec<TermId> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect()
}

#[test]
fn auflia_guard_rewrite_derives_from_exact_sources_and_strict_checks() {
    for duplicate in [false, true] {
        let (mut exec, roots, target) = prepared_guard(1, duplicate);
        let proof = rewritten_refutation(&mut exec, &roots, target);
        let negated = exec.ctx.terms.mk_not_raw(target);
        let assumptions = assumes(&proof);
        assert!(
            !assumptions.contains(&target),
            "reduced clause must be derived"
        );
        assert!(assumptions.contains(&roots[0]));
        assert!(assumptions.contains(&roots[1]));
        assert!(assumptions
            .iter()
            .all(|term| roots.contains(term) || *term == negated));
        let quality = ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
            .expect("arithmetic guard and Boolean resolution must independently check");
        assert_eq!(quality.trust_count, 0);
    }
}

#[test]
fn auflia_guard_rewrite_declines_without_active_licensing_equality() {
    let (mut exec, roots, target) = prepared_guard(1, false);
    let active_roots = vec![roots[0], roots[2]];
    let proof = rewritten_refutation(&mut exec, &active_roots, target);
    assert!(
        assumes(&proof).contains(&target),
        "inactive equality must not license guard removal"
    );
}

#[test]
fn auflia_guard_rewrite_declines_without_active_authored_clause() {
    let (mut exec, roots, target) = prepared_guard(1, false);
    let active_roots = vec![roots[1], roots[2]];
    let proof = rewritten_refutation(&mut exec, &active_roots, target);
    assert!(
        assumes(&proof).contains(&target),
        "inactive clause must not become an assumed source"
    );
}

#[test]
fn auflia_guard_rewrite_keeps_zero_length_escape() {
    let (mut exec, roots, target) = prepared_guard(0, false);
    let proof = rewritten_refutation(&mut exec, &roots, target);
    assert!(
        assumes(&proof).contains(&target),
        "zero length satisfies the escape guard and cannot imply the reduced clause"
    );
}

#[test]
fn auflia_guard_rewrite_declines_forged_guard_value() {
    let (mut exec, roots, target) = prepared_guard(0, false);
    exec.propagated_value_provenance
        .rewrites
        .push(crate::preprocess::PropagatedRewriteRecord {
            before: roots[0],
            after: target,
            stamp: u32::MAX,
        });
    let proof = rewritten_refutation(&mut exec, &roots, target);
    assert!(
        assumes(&proof).contains(&target),
        "a false record cannot override the authored zero length"
    );
}
