// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::proofs::EnvelopeStop;
use ay_core::resource::{enter_check_stop, ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::time::Instant;
use ay_proof::{ProofCheckError, ProofQuality};
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

fn fixture() -> (Executor, Proof, [TermId; 2]) {
    let mut executor = Executor::new();
    let positive = executor.ctx.terms.mk_var("finite-stop-p", Sort::Bool);
    let negative = executor.ctx.terms.mk_not(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![left, right], vec![]);
    (executor, proof, [positive, negative])
}

fn check(
    executor: &Executor,
    proof: &Proof,
    assumptions: &[TermId],
) -> Result<ProofQuality, ProofCheckError> {
    executor.check_bounded_finite_enum_proof(proof, assumptions, &[], &[], &[])
}

#[test]
fn finite_enum_walk_preserves_the_exact_unstopped_proof_verdict() {
    let (executor, mut proof, assumptions) = fixture();
    for _ in 0..2 {
        let direct = ay_proof::check_proof_strict_with_typed_context_and_progress(
            &proof,
            &executor.ctx.terms,
            Some(&[]),
            Some(&[]),
            &[],
            Some(&assumptions),
            &mut |_, _| true,
        );
        assert_eq!(check(&executor, &proof, &assumptions), direct);
        proof.steps[1] = ProofStep::Assume(assumptions[0]);
    }
}

#[test]
fn finite_enum_walk_honors_original_stop_at_every_offer_but_not_after_last() {
    let (executor, proof, assumptions) = fixture();
    let mut callbacks = 1;
    let direct = ay_proof::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &executor.ctx.terms,
        Some(&[]),
        Some(&[]),
        &[],
        Some(&assumptions),
        &mut |_, _| {
            callbacks += 1;
            true
        },
    );
    assert!(direct.is_ok());
    for stop in 1..=callbacks + 1 {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = calls.clone();
        let _owner = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) + 1 == stop
        }));
        let result = check(&executor, &proof, &assumptions);
        if stop <= callbacks {
            assert_eq!(result, Err(ProofCheckError::Cancelled));
            assert_eq!(calls.load(Ordering::SeqCst), stop);
            assert_eq!(
                executor.certification_stop.get(),
                Some(EnvelopeStop::Caller)
            );
        } else {
            assert_eq!(result, direct);
            assert_eq!(calls.load(Ordering::SeqCst), callbacks);
        }
    }
}

#[test]
fn finite_enum_walk_composes_guard_deadline_work_and_certify_cancel_only() {
    let (executor, proof, assumptions) = fixture();
    let search = Guard::root_child(
        ChildSpec::new(NodeLabel::Search).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let _search = search.enter();
    assert_eq!(
        check(&executor, &proof, &assumptions),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::Backstop)
    );
    let certify = search.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let _certify = certify.enter();
    assert!(check(&executor, &proof, &assumptions).is_ok());
    let spent = certify.child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let _spent = spent.enter();
    let fresh = Executor::new();
    // Admission must stop before the deliberately foreign proof is inspected.
    assert_eq!(
        check(&fresh, &proof, &assumptions),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(
        fresh.certification_stop.get(),
        Some(EnvelopeStop::WorkLimit)
    );
}

#[test]
fn finite_enum_walk_obeys_executor_interrupt_and_deadline() {
    for deadline in [false, true] {
        let (mut executor, proof, assumptions) = fixture();
        let (interrupt, wall, reason) = if deadline {
            (None, Some(Instant::now()), EnvelopeStop::Backstop)
        } else {
            (
                Some(Arc::new(AtomicBool::new(true))),
                None,
                EnvelopeStop::Interrupt,
            )
        };
        executor.set_solve_controls(interrupt, wall);
        assert_eq!(
            check(&executor, &proof, &assumptions),
            Err(ProofCheckError::Cancelled)
        );
        assert_eq!(executor.certification_stop.get(), Some(reason));
    }
}

#[test]
fn real_finite_enum_capability_route_cannot_bypass_original_cancellation() {
    let commands = ay_frontend::parse(
        "(set-logic QF_DT)
         (declare-datatype Two ((u0) (u1)))
         (declare-fun left () Two)
         (declare-fun middle () Two)
         (declare-fun right () Two)
         (assert (not (= left middle)))
         (assert (not (= left right)))
         (assert (not (= middle right)))",
    )
    .unwrap();
    let mut executor = Executor::new();
    assert_eq!(executor.execute_all(&commands).unwrap(), [] as [String; 0]);
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    // Singleton constants become their sole constructor during elaboration,
    // folding their disequality to false before the finite-enum route. Keep
    // three genuinely distinct terms and their authored edges over two values.
    let left = executor.ctx.symbol_info("left").unwrap().term.unwrap();
    let middle = executor.ctx.symbol_info("middle").unwrap().term.unwrap();
    let right = executor.ctx.symbol_info("right").unwrap().term.unwrap();
    assert_eq!(executor.ctx.assertions.len(), 3);
    let mut edge_sources = ay_core::kani_compat::DetHashMap::default();
    for (&source, (left, right)) in
        executor
            .ctx
            .assertions
            .iter()
            .zip([(left, middle), (left, right), (middle, right)])
    {
        assert_ne!(left, right);
        let TermData::Not(equality) = executor.ctx.terms.get(source) else {
            panic!("finite-enum fixture must retain an authored disequality");
        };
        let TermData::App(symbol, args) = executor.ctx.terms.get(*equality) else {
            panic!("finite-enum fixture must retain the original equality");
        };
        assert_eq!(symbol, &Symbol::named("="));
        assert_eq!(args.as_slice(), &[left, right]);
        let pair = if left.0 < right.0 {
            (left, right)
        } else {
            (right, left)
        };
        assert!(edge_sources.insert(pair, source).is_none());
    }
    assert_eq!(edge_sources.len(), 3);
    executor.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 2,
        members: vec![left, middle, right],
        edge_sources,
    });
    assert!(executor.try_install_bounded_finite_enum_pigeonhole_proof());
    let proof = executor.last_proof.as_ref().unwrap();
    assert!(executor
        .checked_finite_enum_capability_for_proof(proof)
        .is_some());
    assert!(executor.check_proof_strict_with_datatypes(proof).is_ok());
    let _owner = enter_check_stop(Arc::new(|| true));
    assert_eq!(
        executor.check_proof_strict_with_datatypes_reporting_work(proof),
        (Err(ProofCheckError::Cancelled), 0)
    );
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::Caller)
    );
}
