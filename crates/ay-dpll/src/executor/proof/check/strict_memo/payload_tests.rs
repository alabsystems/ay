// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::Executor;
use ay_core::{
    AletheRule, CuttingPlaneAnnotation, DatatypeConstructor, DatatypeField, DatatypeSort, ProofId,
    Symbol, TheoryLemmaKind,
};

fn empty_key() -> StrictWalkKey<'static> {
    StrictWalkKey {
        datatype_decls: &[],
        selector_decls: &[],
        member_signatures: &[],
        problem: &[],
    }
}

fn refutation(executor: &mut Executor) -> Proof {
    executor
        .execute_all(
            &ay_frontend::parse("(declare-const memo_p Bool)(assert memo_p)(assert (not memo_p))")
                .unwrap(),
        )
        .unwrap();
    let p = executor.ctx.assertions[0];
    let not_p = executor.ctx.assertions[1];
    let zero = executor.ctx.terms.mk_int(0.into());
    let identity = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [zero, zero], Sort::Bool);
    let mut proof = Proof::new();
    let yes = proof.add_assume(p, None);
    let no = proof.add_assume(not_p, None);
    proof.add_theory_lemma_with_kind("LIA", vec![identity], TheoryLemmaKind::ArithClauseTautology);
    proof.add_resolution(Vec::new(), p, yes, no);
    proof
}

#[test]
fn oversized_unused_nested_hint_skips_memo_but_preserves_native_checker_verdict() {
    let mut executor = Executor::new();
    let mut proof = refutation(&mut executor);
    let ProofStep::TheoryLemma { lia, .. } = &mut proof.steps[2] else {
        unreachable!()
    };
    *lia = Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::new(vec![
            num_rational::Rational64::from_integer(1);
            STRICT_WALK_MEMO_MAX_PAYLOAD + 1
        ]),
        divisor: 1,
    }));
    let first = executor
        .check_proof_strict_with_datatypes(&proof)
        .expect("retention refusal must not reject an intrinsically valid proof");
    assert!(first.is_complete());
    assert!(executor.strict_walk_memo.borrow().entries.is_empty());
    let hits = executor.strict_check_memo_hits.get();
    let second = executor.check_proof_strict_with_datatypes(&proof).unwrap();
    assert_eq!(first, second);
    assert_eq!(hits, executor.strict_check_memo_hits.get());
    assert!(executor.strict_walk_memo.borrow().entries.is_empty());
}

#[test]
fn sparse_named_capacity_and_unused_strings_are_priced_without_large_allocations() {
    let mut proof = Proof::new();
    proof.named_steps.reserve(128);
    assert_eq!(proof.named_steps.len(), 0);
    assert!(proof.named_steps.capacity() > 64);
    assert!(document(&proof, 64).is_none());

    let mut named = Proof::new();
    named.named_steps.insert("n".repeat(80), ProofId(0));
    assert!(document(&named, 64).is_none());

    let mut custom = Proof::new();
    custom.steps.push(ProofStep::Step {
        rule: AletheRule::Custom("r".repeat(80)),
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    assert!(document(&custom, 64).is_none());

    let mut theory = Proof::new();
    theory.steps.push(ProofStep::TheoryLemma {
        theory: "t".repeat(80),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::ArithClauseTautology,
        lia: None,
    });
    assert!(document(&theory, 64).is_none());
}

#[test]
fn context_sort_and_anchor_metadata_are_bounded_before_literal_comparison() {
    let datatype = Sort::Datatype(DatatypeSort::new(
        "D",
        vec![DatatypeConstructor::new(
            "Mk",
            vec![DatatypeField::new("field".repeat(20), Sort::Int)],
        )],
    ));
    assert!(Counter::new(64).sort(&datatype, 0).is_none());

    let mut deep = Sort::Int;
    for _ in 0..(MAX_SORT_DEPTH + 2) {
        deep = Sort::Seq(Box::new(deep));
    }
    assert!(Counter::new(usize::MAX).sort(&deep, 0).is_none());
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(1),
        variables: vec![("a".repeat(80), Sort::Int)],
    });
    assert!(document(&proof, 64).is_none());
}

#[test]
fn oversized_cloned_context_is_neither_retained_nor_used_for_a_cache_hit() {
    let mut executor = Executor::new();
    let proof = refutation(&mut executor);
    let declarations = vec![("D".repeat(STRICT_WALK_MEMO_MAX_PAYLOAD + 1), Vec::new())];
    let key = StrictWalkKey {
        datatype_decls: &declarations,
        ..empty_key()
    };
    executor.strict_walk_memo_store(&proof, &key, &Ok(ProofQuality::default()), 7);
    assert!(executor.strict_walk_memo.borrow().entries.is_empty());
    assert!(executor.strict_walk_memo_lookup(&proof, &key).is_none());

    let ordinary = empty_key();
    executor.strict_walk_memo_store(&proof, &ordinary, &Ok(ProofQuality::default()), 7);
    assert_eq!(executor.strict_walk_memo.borrow().entries.len(), 1);
    assert!(executor.strict_walk_memo_lookup(&proof, &key).is_none());
    assert_eq!(executor.strict_walk_memo.borrow().entries.len(), 1);
}

#[test]
fn oversized_error_diagnostics_are_not_cloned_into_the_memo() {
    let mut executor = Executor::new();
    let proof = refutation(&mut executor);
    let outcome = Err(ProofCheckError::InvalidTheoryLemma {
        step: ProofId(2),
        reason: "e".repeat(STRICT_WALK_MEMO_MAX_PAYLOAD + 1),
    });
    executor.strict_walk_memo_store(&proof, &empty_key(), &outcome, 7);
    assert!(executor.strict_walk_memo.borrow().entries.is_empty());
}

#[test]
fn actual_stop_owner_precedes_uncacheable_payload_on_lookup() {
    use std::sync::{atomic::AtomicBool, Arc};

    let mut executor = Executor::new();
    let proof = refutation(&mut executor);
    let key = empty_key();
    executor.strict_walk_memo_store(&proof, &key, &Ok(ProofQuality::default()), 7);
    let declarations = vec![("D".repeat(STRICT_WALK_MEMO_MAX_PAYLOAD + 1), Vec::new())];
    let large = StrictWalkKey {
        datatype_decls: &declarations,
        ..empty_key()
    };
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
    assert!(matches!(
        executor.strict_walk_memo_lookup(&proof, &large),
        Some((Err(ProofCheckError::Cancelled), 0))
    ));
}
