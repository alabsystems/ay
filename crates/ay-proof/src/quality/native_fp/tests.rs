// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{QueryError, StopReason};
use ay_core::{FpOp, Symbol};
use std::{cell::Cell, ops::ControlFlow, time::Duration};

fn limits() -> ResolutionProofLimits {
    let mut limits = ResolutionProofLimits::default();
    limits.deadline = Some(Instant::now() + Duration::from_secs(30));
    limits.max_num_vars = 100_000;
    limits.max_conflicts = Some(50_000);
    limits.max_decisions = Some(100_000);
    limits.max_proof_output_bytes = 16 * 1024 * 1024;
    limits.max_codec_bytes = 32 * 1024 * 1024;
    limits.max_backward_reconstruction_bytes = 32 * 1024 * 1024;
    limits.validation.max_work = 2_000_000;
    limits.validation.max_bytes = 32 * 1024 * 1024;
    limits
}

fn fixture() -> (TermStore, Proof, Vec<TermId>, TermId) {
    let mut terms = TermStore::new();
    let word = terms.mk_var("x", Sort::bitvec(4));
    let x = terms.mk_app(
        Symbol::indexed("to_fp", vec![2, 2]),
        [word],
        Sort::FloatingPoint(2, 2),
    );
    let bits = terms.mk_bitvec(2u8.into(), 4);
    let one = terms.mk_app(
        Symbol::indexed("to_fp", vec![2, 2]),
        [bits],
        Sort::FloatingPoint(2, 2),
    );
    let rm = terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".into()));
    let product = terms.mk_app(
        Symbol::named("fp.mul"),
        [rm, x, one],
        Sort::FloatingPoint(2, 2),
    );
    let theorem = terms.mk_app(Symbol::named("="), [product, x], Sort::Bool);
    let negative = terms.mk_not_raw(theorem);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negative, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "FP",
        vec![theorem],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Mul,
        },
    );
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: theorem,
        clause1: assumption,
        clause2: lemma,
    });
    (terms, proof, vec![negative], theorem)
}

fn context<'a>(terms: &'a TermStore, assertions: &'a [TermId]) -> NativeFpProofContext<'a> {
    NativeFpProofContext {
        terms,
        datatype_declarations: None,
        constructor_selectors: None,
        datatype_member_signatures: &[],
        problem_assertions: assertions,
    }
}

#[test]
fn whole_strict_native_fp_entry_is_usable_but_legacy_callback_remains_schema_only() {
    let (terms, proof, assertions, _) = fixture();
    assert!(crate::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        Some(&assertions),
        &mut |_, _| true,
    )
    .is_err());
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let quality = check_proof_strict_with_native_fp_context(
        &proof,
        context(&terms, &assertions),
        &limits(),
        &mut work,
    )
    .expect("complete raw-source clause, ordinary assumptions and terminal replay");
    assert_eq!(quality.total_steps(), 3);
    assert!(work.remaining() < 50_000_000);
}

#[test]
fn canonical_clause_pass_cannot_replace_original_assumption_binding() {
    let (terms, proof, _, _) = fixture();
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(check_proof_strict_with_native_fp_context(
        &proof,
        context(&terms, &[]),
        &limits(),
        &mut work,
    )
    .is_err());
}

#[test]
fn canonical_clause_pass_cannot_replace_terminal_empty_clause_or_other_rules() {
    let (terms, proof, assertions, _) = fixture();
    for steps in [
        proof.steps[..2].to_vec(),
        vec![ProofStep::Step {
            rule: AletheRule::Hole,
            clause: vec![],
            premises: vec![],
            args: vec![],
        }],
    ] {
        let incomplete = Proof::from_steps(steps);
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(50_000_000, &mut live);
        assert!(check_proof_strict_with_native_fp_context(
            &incomplete,
            context(&terms, &assertions),
            &limits(),
            &mut work,
        )
        .is_err());
    }
}

#[test]
fn false_actual_fp_clause_does_not_gain_authority_from_operation_tag() {
    let (mut terms, _, _, _) = fixture();
    let a = terms.mk_bitvec(0u8.into(), 4);
    let b = terms.mk_bitvec(8u8.into(), 4);
    let a = terms.mk_app(
        Symbol::indexed("to_fp", vec![2, 2]),
        [a],
        Sort::FloatingPoint(2, 2),
    );
    let b = terms.mk_app(
        Symbol::indexed("to_fp", vec![2, 2]),
        [b],
        Sort::FloatingPoint(2, 2),
    );
    let false_theorem = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "FP",
        vec![false_theorem],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Mul,
        },
    );
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(matches!(
        check_proof_strict_with_native_fp_context(
            &proof,
            context(&terms, &[]),
            &limits(),
            &mut work,
        ),
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
}

#[test]
fn passed_inventory_cannot_be_installed_on_a_foreign_store_or_step() {
    let (terms, proof, _, theorem) = fixture();
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let accepted =
        ValidatedSteps::prepare(&proof, &terms, &limits(), &mut work).expect("actual source step");
    let other_store = terms.clone();
    assert!(accepted
        .clause(ProofId(1), &proof.steps[1], &other_store, &mut |_, _| true)
        .is_err());
    let other_step = ProofStep::TheoryLemma {
        theory: "FP".into(),
        clause: vec![theorem],
        farkas: None,
        kind: TheoryLemmaKind::FpToBv {
            operation: FpOp::Mul,
        },
        lia: None,
    };
    assert!(accepted
        .clause(ProofId(1), &other_step, &terms, &mut |_, _| true)
        .is_err());
}

#[test]
fn missing_original_absolute_limits_refuse_without_fresh_timeout_or_adapter() {
    let (terms, proof, assertions, _) = fixture();
    let mut unbounded = limits();
    unbounded.deadline = None;
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(check_proof_strict_with_native_fp_context(
        &proof,
        context(&terms, &assertions),
        &unbounded,
        &mut work,
    )
    .is_err());
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert!(check_proof_strict_with_native_fp_context(
        &proof,
        context(&terms, &assertions),
        &limits(),
        &mut work,
    )
    .is_err());
}

#[test]
fn one_remaining_owner_debits_all_fp_lemmas_and_the_ordinary_strict_walk() {
    let (terms, proof, assertions, _) = fixture();
    let observed = Cell::new(0usize);
    let mut sink = |units: usize, _: usize| {
        observed.set(observed.get() + units);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(50_000_000, &mut sink);
    check_proof_strict_with_native_fp_context(
        &proof,
        context(&terms, &assertions),
        &limits(),
        &mut work,
    )
    .expect("single cumulative original sink");
    assert_eq!(50_000_000 - work.remaining(), observed.get() as u64);
    assert!(
        observed.get() > 4_000_000,
        "search and second independent replay are both prepaid"
    );
}

#[test]
fn final_original_owner_refusal_cannot_publish_complete_whole_proof_quality() {
    let (terms, proof, assertions, _) = fixture();
    let calls = Cell::new(0usize);
    let fixed = limits();
    {
        let mut live = || {
            calls.set(calls.get() + 1);
            ControlFlow::Continue(())
        };
        let mut work = WorkBudget::new(50_000_000, &mut live);
        check_proof_strict_with_native_fp_context(
            &proof,
            context(&terms, &assertions),
            &fixed,
            &mut work,
        )
        .expect("healthy complete walk");
    }
    let final_call = calls.get();
    calls.set(0);
    let stopping = Cell::new(true);
    let mut live = || {
        calls.set(calls.get() + 1);
        if stopping.get() && calls.get() >= final_call {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(matches!(
        check_proof_strict_with_native_fp_context(
            &proof,
            context(&terms, &assertions),
            &fixed,
            &mut work,
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    stopping.set(false);
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn canonical_typed_entry_preserves_wrong_operation_and_extra_literal_refusals() {
    let (mut terms, original, assertions, _) = fixture();
    let unrelated = terms.mk_var("extra", Sort::Bool);
    for changed in [
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
        TheoryLemmaKind::FpToBv {
            operation: FpOp::IsNaN,
        },
    ] {
        let mut proof = original.clone();
        if let ProofStep::TheoryLemma { kind, .. } = &mut proof.steps[1] {
            *kind = changed;
        }
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(50_000_000, &mut live);
        assert!(matches!(
            check_proof_strict_with_native_fp_context(
                &proof,
                context(&terms, &assertions),
                &limits(),
                &mut work,
            ),
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
    }
    let mut proof = original;
    if let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[1] {
        clause.push(unrelated);
    }
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(matches!(
        check_proof_strict_with_native_fp_context(
            &proof,
            context(&terms, &assertions),
            &limits(),
            &mut work,
        ),
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
}

#[test]
fn terminal_refusal_preserves_first_semantic_error_and_stops_the_same_owner() {
    let (terms, proof, _, _) = fixture();
    let fixed = limits();
    let calls = Cell::new(0usize);
    {
        let mut live = || {
            calls.set(calls.get() + 1);
            ControlFlow::Continue(())
        };
        let mut work = WorkBudget::new(50_000_000, &mut live);
        assert!(matches!(
            check_proof_strict_with_native_fp_context(
                &proof,
                context(&terms, &[]),
                &fixed,
                &mut work,
            ),
            Err(ProofCheckError::UnauthorizedAssumption { .. })
        ));
    }
    let final_call = calls.get();
    calls.set(0);
    let stopping = Cell::new(true);
    let mut live = || {
        calls.set(calls.get() + 1);
        if stopping.get() && calls.get() == final_call {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(matches!(
        check_proof_strict_with_native_fp_context(&proof, context(&terms, &[]), &fixed, &mut work,),
        Err(ProofCheckError::UnauthorizedAssumption { .. })
    ));
    stopping.set(false);
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
