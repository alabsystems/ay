// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The raw strict check and the BV recognizer stop on this solve's signals.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::{time::Instant, Proof, Sort, Symbol, TermId, TheoryLemmaKind};
use ay_proof::ProofCheckError;

use crate::executor::Executor;

/// A 16-bit identity: too wide for the bounded evaluator, so deciding it
/// runs the proof-producing fallback, the part a stop must reach.
fn wide_identity_refutation(exec: &mut Executor) -> (Proof, TermId) {
    let terms = &mut exec.ctx.terms;
    let x = terms.mk_var("solve-stop-x", Sort::bitvec(16));
    let zero = terms.mk_bitvec(0.into(), 16);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(16));
    let identity = terms.mk_app(Symbol::named("="), [x, sum], Sort::Bool);
    let root = terms.mk_not_raw(identity);
    let lemma = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let step = proof.add_theory_lemma_with_kind("bv", vec![lemma], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], root, assume, step);
    (proof, lemma)
}

#[test]
fn raw_strict_checks_stop_on_the_solve_signals_and_are_otherwise_unchanged() {
    let mut exec = Executor::new();
    let (proof, lemma) = wide_identity_refutation(&mut exec);
    let stops: [(Option<Arc<AtomicBool>>, Option<Instant>); 2] = [
        (Some(Arc::new(AtomicBool::new(true))), None),
        (None, Some(Instant::now())),
    ];
    for (interrupt, deadline) in stops {
        exec.set_solve_controls(interrupt, deadline);
        assert_eq!(
            exec.check_proof_strict_until_stopped(&proof),
            Err(ProofCheckError::ResourceLimit),
            "a stopped solve fails the check closed"
        );
        assert!(!exec.recognize_bv_bitblast_until_stopped(&[lemma]));
    }
    // Unstopped, it is the unbounded checker's answer exactly -- and none of
    // the stops above was remembered as a refusal.
    exec.set_solve_controls(None, None);
    let unbounded = ay_proof::check_proof_strict(&proof, &exec.ctx.terms);
    assert!(unbounded.is_ok(), "{unbounded:?}");
    assert_eq!(
        format!("{:?}", exec.check_proof_strict_until_stopped(&proof)),
        format!("{unbounded:?}")
    );
    assert!(exec.recognize_bv_bitblast_until_stopped(&[lemma]));
}
