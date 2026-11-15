// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A support question asks the complete bit-blast only as `CompleteBlastAsk`
//! says: a lane not asked, or stopped by its caller, does no SAT work at all,
//! and a lane asked until a stop polls that stop in its refutation.

use super::*;
use crate::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};
use std::cell::Cell;

/// `(cl (not (not (= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n))))))` over
/// 4 bits: the quotient-remainder identity, which no named lowering spells
/// and the complete bit-blast refutes (it holds for `n = 0` too).
fn quotient_remainder_lemma(f: &mut Fixture) -> TermId {
    let m = f.bv("m", 4);
    let n = f.bv("n", 4);
    let quotient = f.op("bvudiv", &[m, n], 4);
    let product = f.op("bvmul", &[quotient, n], 4);
    let remainder = f.op("bvurem", &[m, n], 4);
    let sum = f.op("bvadd", &[product, remainder], 4);
    let identity = f.equals(m, sum);
    let assertion = f.not(identity);
    f.not(assertion)
}

#[test]
fn a_lane_not_asked_declines_before_any_refutation() {
    let mut f = Fixture::new();
    let lemma = quotient_remainder_lemma(&mut f);
    reset_resolution_dag_memo();
    let declined = AlethePrinter::new(&f.terms)
        .asking_complete_blast(CompleteBlastAsk::NotAsked)
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma]);
    assert!(declined.is_none());
    assert_eq!(resolution_dag_memo_counters(), (0, 0));

    let document = AlethePrinter::new(&f.terms)
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
        .expect("asked, the identity renders");
    assert_complete(&document);
}

/// A caller whose stop has fired is answered a decline at once: the stop is
/// polled once, at the lane's entry, and nothing is blasted or refuted.
#[test]
fn a_stopped_caller_is_declined_before_any_refutation() {
    let mut f = Fixture::new();
    let lemma = quotient_remainder_lemma(&mut f);
    let polls = Cell::new(0_u32);
    let stopped = || {
        polls.set(polls.get() + 1);
        true
    };
    reset_resolution_dag_memo();
    let declined = AlethePrinter::new(&f.terms)
        .asking_complete_blast(CompleteBlastAsk::AskedUntil(&stopped))
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma]);
    assert!(declined.is_none());
    assert_eq!(polls.get(), 1);
    assert_eq!(resolution_dag_memo_counters(), (0, 0));
}

/// The twin: a stop that never fires leaves the document as the exporter
/// renders it, and the refutation underneath polls it (the lane's entry is
/// one poll; the refutation's are the rest). Before the stop reached the
/// monolithic refutation, it polled nothing and ran unbounded.
#[test]
fn an_idle_stop_is_polled_by_the_refutation_and_changes_nothing() {
    let mut f = Fixture::new();
    let lemma = quotient_remainder_lemma(&mut f);
    let polls = Cell::new(0_u32);
    let idle = || {
        polls.set(polls.get() + 1);
        false
    };
    let polled = AlethePrinter::new(&f.terms)
        .asking_complete_blast(CompleteBlastAsk::AskedUntil(&idle))
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
        .expect("an idle stop renders the identity");
    assert_complete(&polled);
    assert!(polls.get() >= 2, "the refutation polled the stop");
    let rendered = AlethePrinter::new(&f.terms)
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
        .expect("the exporter renders the identity");
    assert_eq!(polled, rendered);
}

/// The public support questions carry the choice: asked, the identity is
/// supported through the complete bit-blast; not asked or stopped, it is not,
/// and no refutation runs.
#[test]
fn the_support_questions_ask_the_complete_blast_only_when_told_to() {
    let mut f = Fixture::new();
    let lemma = quotient_remainder_lemma(&mut f);
    let kind = ay_core::TheoryLemmaKind::BvBitBlast;
    let stopped = || true;
    reset_resolution_dag_memo();
    for ask in [
        CompleteBlastAsk::NotAsked,
        CompleteBlastAsk::AskedUntil(&stopped),
    ] {
        assert!(!crate::checked_bv_bitblast_lowering_supported_asking(
            &f.terms,
            &kind,
            &[lemma],
            None,
            ask,
        ));
        let mut budget = crate::ArithPolySimpPromotionBudget::standalone();
        assert!(
            !crate::theory_lemma_bv_arithmetic_lowering_supported_asking(
                &f.terms,
                &ay_core::TheoryLemmaKind::ArithClauseTautology,
                &[lemma],
                None,
                &mut budget,
                ask,
            ),
            "{ask:?}"
        );
    }
    assert_eq!(resolution_dag_memo_counters(), (0, 0));
    assert!(crate::checked_bv_bitblast_lowering_supported(
        &f.terms,
        &kind,
        &[lemma],
        None
    ));
}

/// A stop that fires part-way through the question starts no further lane.
/// Each lane pays unpolled work in the size of the circuit before its first
/// poll (a plan re-blasts, a sweep simulates, the monolithic solve loads every
/// clause), so once a poll has answered `true` no refutation is looked up
/// again, wherever it fired. Before the lanes polled at their start, a stop
/// that ended the monolithic refutation still let the sweep look up its
/// refutation, simulate the circuit and search.
#[test]
fn a_stop_that_fires_mid_question_starts_no_further_lane() {
    let mut f = Fixture::new();
    let lemma = quotient_remainder_lemma(&mut f);
    // The polls made, and the memo's counters when the stop first fired and
    // when the question returned.
    let ask = |fire_at: u32| {
        reset_resolution_dag_memo();
        let polls = Cell::new(0_u32);
        let at_fire = Cell::new(None);
        let stop = || {
            polls.set(polls.get() + 1);
            let fired = polls.get() >= fire_at;
            if fired && at_fire.get().is_none() {
                at_fire.set(Some(resolution_dag_memo_counters()));
            }
            fired
        };
        let _ = AlethePrinter::new(&f.terms)
            .asking_complete_blast(CompleteBlastAsk::AskedUntil(&stop))
            .format_bv_complete_blast_refutation(ProofId(1), &[lemma]);
        (polls.get(), at_fire.get(), resolution_dag_memo_counters())
    };
    // The plan's settled abstraction and the lane that printed are retained
    // on this thread by the first render (`lazy.rs`, `lane.rs`): render once
    // so that every question below takes one path.
    let _ = ask(u32::MAX);
    let (idle_polls, never_fired, _) = ask(u32::MAX);
    assert!(never_fired.is_none());
    assert!(idle_polls >= 2, "the refutation polled the stop");
    for fire_at in 1..=idle_polls.min(64) {
        let (_, at_fire, returned) = ask(fire_at);
        assert_eq!(
            at_fire,
            Some(returned),
            "a lane started after the stop fired at poll {fire_at} of {idle_polls}"
        );
    }
}

/// `assume (not identity)` refuted by the one bit-blast lemma
/// `(cl (not (not identity)))` that only the complete bit-blast spells, and
/// the problem scope it renders in.
fn bitblast_refutation(f: &mut Fixture) -> (ay_core::Proof, Vec<TermId>) {
    let lemma = quotient_remainder_lemma(f);
    let TermData::Not(root) = f.terms.get(lemma).clone() else {
        panic!("the lemma is a negation");
    };
    let mut proof = ay_core::Proof::new();
    let assumption = proof.add_assume(root, None);
    let step =
        proof.add_theory_lemma_with_kind("bv", vec![lemma], ay_core::TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), root, assumption, step);
    (proof, vec![root])
}

/// An in-solve render asks the complete bit-blast only until the solve's
/// stop: stopped, the lemma is the honest `hole` and nothing is refuted, so
/// the render is not clean. These renders went through the exporter's
/// `Asked`, which no stop reached.
#[test]
fn a_render_asked_until_a_stop_honours_it() {
    let mut f = Fixture::new();
    let (proof, scope) = bitblast_refutation(&mut f);
    let surfaces = crate::AletheAuthoredSurfaces::default();
    let render = |stop: &dyn Fn() -> bool| {
        crate::try_export_alethe_with_authored_surfaces_until(
            &proof,
            &f.terms,
            &scope,
            None,
            surfaces,
            Some(16 * 1024 * 1024),
            stop,
        )
    };
    reset_resolution_dag_memo();
    let stopped = render(&|| true);
    assert!(stopped.is_ok_and(|document| document.contains(":rule hole")));
    assert_eq!(resolution_dag_memo_counters(), (0, 0));

    // The twin: a stop that never fires renders the exporter's document.
    let idle = render(&|| false).expect("an idle stop renders");
    assert_complete(&idle);
    let exported = crate::try_export_alethe_with_authored_surfaces(
        &proof,
        &f.terms,
        &scope,
        None,
        surfaces,
        Some(16 * 1024 * 1024),
    )
    .expect("the exporter renders");
    assert_eq!(idle, exported);
}

/// The in-solve renders that still render as the exporter does carry no
/// bit-vector lemma kind: the fold-identity candidate only `LiaGeneric`
/// lemmas, the shared-tautology candidate none, the direct negated-conjunct
/// candidate arithmetic over `Int` (its `ArithClauseTautology` is an `Int`
/// polynomial identity), and the engine shadow the kernel's arithmetic
/// lemmas over QF_LRA, QF_RDL, QF_IDL or QF_LIA. Asked through every
/// dispatch that reaches the complete bit-blast, a lemma over `Int` (even one
/// that reads a bit-vector through `bv2nat`) is refused at its first node,
/// before any refutation, so those renders need no stop.
#[test]
fn an_integer_lemma_reaches_no_refutation() {
    let mut f = Fixture::new();
    let x = f.terms.mk_var("ix", Sort::Int);
    let w = f.bv("iw", 8);
    let nat = f.terms.mk_app(Symbol::named("bv2nat"), [w], Sort::Int);
    let sum = f.terms.mk_app(Symbol::named("+"), [x, nat], Sort::Int);
    let flipped = f.terms.mk_app(Symbol::named("+"), [nat, x], Sort::Int);
    let identity = f.equals(sum, flipped);
    let negated = f.not(identity);
    let refuted = f.not(negated);
    reset_resolution_dag_memo();
    let printer = AlethePrinter::new(&f.terms);
    for clause in [[identity], [refuted]] {
        assert!(printer
            .format_bv_complete_blast_refutation(ProofId(1), &clause)
            .is_none());
        assert!(printer
            .format_bv_structural_arithmetic_attempt(ProofId(1), &clause)
            .is_none());
    }
    assert_eq!(resolution_dag_memo_counters(), (0, 0));
}
