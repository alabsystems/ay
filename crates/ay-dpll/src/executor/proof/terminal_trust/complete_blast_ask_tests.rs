// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The wire-gap screen asks the complete bit-blast only for a document someone
//! can observe (`proof_document_observable`), and only until the stop proof
//! assembly observes (`make_proof_assembly_should_stop`).
//!
//! Both lemmas below are lowered by the complete bit-blast alone, so "no gap"
//! is the evidence that it was asked. The refutation-memo counters, which
//! stay at `(0, 0)` when it was not, count with the memo on (the default).

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::{Proof, Sort, Symbol, TermId, TheoryLemmaKind};
use ay_proof::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};

use crate::executor::Executor;

/// `(= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))` over 4 bits.
fn quotient_remainder_identity(executor: &mut Executor, prefix: &str) -> TermId {
    let terms = &mut executor.ctx.terms;
    let m = terms.mk_var(format!("{prefix}_m"), Sort::bitvec(4));
    let n = terms.mk_var(format!("{prefix}_n"), Sort::bitvec(4));
    let mut op =
        |name: &str, args: [TermId; 2]| terms.mk_app(Symbol::named(name), args, Sort::bitvec(4));
    let quotient = op("bvudiv", [m, n]);
    let product = op("bvmul", [quotient, n]);
    let remainder = op("bvurem", [m, n]);
    let sum = op("bvadd", [product, remainder]);
    terms.mk_app(Symbol::named("="), [m, sum], Sort::Bool)
}

/// `assume (not identity)` refuted by ONE `BvBitBlast` lemma
/// `(cl (not (not identity)))`.
fn bitblast_refutation(executor: &mut Executor) -> Proof {
    let identity = quotient_remainder_identity(executor, "screen_ask");
    let root = executor.ctx.terms.mk_not_raw(identity);
    let refuted = executor.ctx.terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![refuted], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), root, assumption, lemma);
    proof
}

/// `assume (not identity)` refuted by the POSITIVE unit `(cl identity)`
/// carried as an `ArithClauseTautology`: the 470d83f28 shape, which the
/// screen asks through `theory_lemma_bv_arithmetic_lowering_supported` (the
/// arm that hung on `bv_affine_source`).
fn positive_unit_arith_refutation(executor: &mut Executor) -> Proof {
    let identity = quotient_remainder_identity(executor, "screen_arith");
    let root = executor.ctx.terms.mk_not_raw(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![identity],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(Vec::new(), identity, lemma, assumption);
    proof
}

const REFUTATIONS: [fn(&mut Executor) -> Proof; 2] =
    [bitblast_refutation, positive_unit_arith_refutation];

/// With no proof requested and no strict presentation, nothing reads the
/// wire: each lemma is screened as a gap and no refutation runs. On an
/// elaborated 64-bit affine identity the same question did not return.
#[test]
fn an_unobservable_screen_does_not_blast() {
    for refutation in REFUTATIONS {
        let mut executor = Executor::new();
        assert!(!executor.proof_document_observable());
        let proof = refutation(&mut executor);
        reset_resolution_dag_memo();
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert_eq!(resolution_dag_memo_counters(), (0, 0));
    }
}

/// The twin: once proofs are requested the screen asks the complete
/// bit-blast, exactly as the exporter will render the lemma.
#[test]
fn an_observable_screen_still_asks_the_complete_blast() {
    for refutation in REFUTATIONS {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        assert!(executor.proof_document_observable());
        let proof = refutation(&mut executor);
        assert!(!executor.proof_has_known_wire_gap(&proof));
    }
}

/// Observable, but the solve's interrupt has fired: the question is answered
/// a gap without a refutation, as the rest of the assembly answers a stop.
/// Under a bare self-check with a 20 s timeout this question ran past 100 s.
#[test]
fn a_stopped_observable_screen_does_not_blast() {
    for refutation in REFUTATIONS {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        assert!(executor.proof_assembly_stop_requested());
        let proof = refutation(&mut executor);
        reset_resolution_dag_memo();
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert_eq!(resolution_dag_memo_counters(), (0, 0));
    }
}

/// The wire-repair choice's render (`proof_renders_without_unproved_step`)
/// asks the complete bit-blast only until the solve's stop, as the screen
/// does: stopped, it is answered not clean without a refutation; it rendered
/// through the exporter's ask, which no stop reached. The twin: unstopped,
/// the same proof renders clean.
#[test]
fn the_wire_repair_render_honours_the_solve_stop() {
    for refutation in REFUTATIONS {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        let proof = refutation(&mut executor);
        let ay_core::ProofStep::Assume(root) = proof.steps[0] else {
            panic!("the refutation starts from its assumption");
        };
        executor.ctx.assertions.push(root);
        let interrupt = Arc::new(AtomicBool::new(true));
        executor.set_solve_controls(Some(interrupt.clone()), None);
        reset_resolution_dag_memo();
        assert!(!executor.proof_renders_without_unproved_step(&proof));
        assert_eq!(resolution_dag_memo_counters(), (0, 0));

        interrupt.store(false, std::sync::atomic::Ordering::Relaxed);
        assert!(executor.proof_renders_without_unproved_step(&proof));
    }
}
