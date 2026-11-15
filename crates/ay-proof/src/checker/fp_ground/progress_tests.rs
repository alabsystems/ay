// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, ProofStep, TheoryLemmaKind};

fn ground_sum() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        vec![],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let one_bits = terms.mk_bitvec(BigInt::from(0x3f80_0000u64), 32);
    let two_bits = terms.mk_bitvec(BigInt::from(0x4000_0000u64), 32);
    let sort = Sort::FloatingPoint(8, 24);
    let one = terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![one_bits],
        sort.clone(),
    );
    let two = terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![two_bits],
        sort.clone(),
    );
    let sum = terms.mk_app(Symbol::named("fp.add"), vec![rm, one, one], sort);
    let equality = terms.mk_app(Symbol::named("="), vec![sum, two], Sort::Bool);
    (terms, equality)
}

#[test]
fn advisory_recognizer_declines_enumeration_but_keeps_exact_proofs() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(2, 3);
    let x = terms.mk_var("advisory_x", sort.clone());
    let zero = terms.mk_app(Symbol::indexed("+zero", vec![2, 3]), [], sort.clone());
    let abs = terms.mk_app(Symbol::named("fp.abs"), [x], sort.clone());
    let twice = terms.mk_app(Symbol::named("fp.abs"), [abs], sort);
    let identity = terms.mk_app(Symbol::named("="), [twice, abs], Sort::Bool);
    assert!(!recognize_fp_ground_eval_without_enumeration_with_progress(
        &terms,
        &[identity],
        &mut |_, _| true
    ));
    // Independent proof replay retains its bounded symbolic domain. Producer
    // eligibility is not a weaker checker or a theorem-authority bit.
    validate_fp_ground_eval(&terms, ProofId(0), &[identity]).unwrap();

    let pin = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
    let not_pin = terms.mk_not_raw(pin);
    let consequence = terms.mk_app(Symbol::named("="), [abs, zero], Sort::Bool);
    let clause = [not_pin, consequence];
    assert!(recognize_fp_ground_eval_without_enumeration_with_progress(
        &terms,
        &clause,
        &mut |_, _| true
    ));
    validate_fp_ground_eval(&terms, ProofId(0), &clause).unwrap();
    let mut refused = false;
    assert!(!recognize_fp_ground_eval_without_enumeration_with_progress(
        &terms,
        &clause,
        &mut |_, _| {
            assert!(!refused, "no restart after the original refusal");
            refused = true;
            false
        }
    ));
    assert!(refused);
    let (ground, sum) = ground_sum();
    assert!(recognize_fp_ground_eval_without_enumeration_with_progress(
        &ground,
        &[sum],
        &mut |_, _| true
    ));
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let y = terms.mk_var("advisory_y", terms.sort(x).clone());
    let xy = terms.mk_app(Symbol::named("fp.mul"), [rm, x, y], terms.sort(x).clone());
    let yx = terms.mk_app(Symbol::named("fp.mul"), [rm, y, x], terms.sort(x).clone());
    let commutative = terms.mk_app(Symbol::named("="), [xy, yx], Sort::Bool);
    assert!(recognize_fp_ground_eval_without_enumeration_with_progress(
        &terms,
        &[commutative],
        &mut |_, _| true
    ));
    validate_fp_ground_eval(&terms, ProofId(0), &[commutative]).unwrap();
}

#[test]
fn original_caller_refusal_is_sticky_and_a_fresh_request_can_succeed() {
    let (terms, equality) = ground_sum();
    let scratch_header = super::super::nra_poly::bounded_rational_scratch_bytes(0, 0).unwrap();
    let mut refused = false;
    let mut calls = 0;
    let error =
        validate_fp_ground_eval_with_progress(&terms, ProofId(0), &[equality], &mut |_, bytes| {
            assert!(
                !refused,
                "no callback or fallback after original caller refusal"
            );
            calls += 1;
            if bytes >= scratch_header {
                refused = true;
                false
            } else {
                true
            }
        })
        .unwrap_err();
    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(
        refused && calls > 1,
        "reach actual numeric work after structural admission"
    );
    let mut work = 0usize;
    let mut bytes = 0usize;
    validate_fp_ground_eval_with_progress(&terms, ProofId(0), &[equality], &mut |w, b| {
        work = work.checked_add(w).unwrap();
        bytes = bytes.checked_add(b).unwrap();
        true
    })
    .unwrap();
    assert!(work > 0 && bytes > 0);
    let negated = terms.get(equality);
    assert!(matches!(negated, TermData::App(..)));
    let mut false_terms = terms;
    let false_clause = false_terms.mk_not_raw(equality);
    assert!(validate_fp_ground_eval_with_progress(
        &false_terms,
        ProofId(0),
        &[false_clause],
        &mut |_, _| true
    )
    .is_err());
}

#[test]
fn shared_operand_probe_refusal_does_not_restart_enumeration() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(5, 11);
    let x = terms.mk_var("probe_x", sort.clone());
    let zero = terms.mk_app(Symbol::indexed("+zero", vec![5, 11]), vec![], sort.clone());
    let bits = terms.mk_bitvec(BigInt::zero(), 16);
    let same_zero = terms.mk_app(Symbol::indexed("to_fp", vec![5, 11]), vec![bits], sort);
    let first = terms.mk_app(Symbol::named("fp.eq"), vec![x, zero], Sort::Bool);
    let second = terms.mk_app(Symbol::named("fp.eq"), vec![x, same_zero], Sort::Bool);
    let clause = [terms.mk_not_raw(first), terms.mk_not_raw(second)];
    let scratch_header = super::super::nra_poly::bounded_rational_scratch_bytes(0, 0).unwrap();
    let mut refused = false;
    assert_eq!(
        validate_fp_ground_eval_with_progress(&terms, ProofId(0), &clause, &mut |_, bytes| {
            assert!(!refused, "fast-path refusal must not mint a fallback owner");
            if bytes >= scratch_header {
                refused = true;
                false
            } else {
                true
            }
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(refused);
    assert!(
        !recognize_fp_ground_eval(&terms, &clause),
        "IEEE-equal zeros do not contradict"
    );
}

#[test]
fn oversized_exact_literal_refuses_before_a_numeric_copy() {
    let mut terms = TermStore::new();
    let huge = terms.mk_int(BigInt::one() << (MAX_RATIONAL_BITS as usize + 1));
    let equality = terms.mk_app(Symbol::named("="), vec![huge, huge], Sort::Bool);
    let mut maximum = 0;
    let result =
        validate_fp_ground_eval_with_progress(&terms, ProofId(0), &[equality], &mut |_, bytes| {
            maximum = maximum.max(bytes);
            true
        });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(maximum < 8192, "no large numeric scratch/clone is admitted");
}

#[test]
fn local_remaining_bound_precedes_a_whole_argument_inspection() {
    let mut calls = 0;
    let mut caller = |_, _| {
        calls += 1;
        true
    };
    let mut meter = Meter::with_local_limit(&mut caller, 2);
    assert!(meter.inspect(3).is_none());
    assert!(meter.refused());
    assert!(meter.node().is_none());
    drop(meter);
    assert_eq!(
        calls, 0,
        "an over-bound source vector never begins its walk"
    );
}

#[test]
fn whole_integral_fixture_uses_actual_progress_inside_the_unchanged_envelope() {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(include_str!(
        "../../../tests/fixtures/fp-integral-remainder.smt2"
    ))
    .unwrap()
    {
        context.process_command(&command).unwrap();
    }
    assert_eq!(context.assertions.len(), 1);
    let root = context.assertions[0];
    assert!(clause_mentions_floating_point(&context.terms, &[root]));
    let negated = context.terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let checked = proof.add_step(ProofStep::TheoryLemma {
        theory: "FP".into(),
        clause: vec![negated],
        farkas: None,
        kind: TheoryLemmaKind::FpGroundEval,
        lia: None,
    });
    proof.add_resolution(vec![], root, assume, checked);
    let mut work = 0usize;
    let mut bytes = 0usize;
    let quality = crate::check_proof_strict_with_context_and_progress(
        &proof,
        &context.terms,
        None,
        None,
        Some(&[root]),
        &mut |w, b| {
            work = work.checked_add(w).unwrap();
            bytes = bytes.checked_add(b).unwrap();
            work <= 250_000_000 && bytes <= 512 * 1024 * 1024
        },
    )
    .unwrap();
    assert!(quality.is_complete());
    eprintln!("complete integral fixture: actual work={work}, bytes={bytes}");
    assert!(work > 0 && bytes > 0);
}
