// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A solve keeps the unstopped declines of its support questions, and only
//! those, and only for itself.

use super::*;
use crate::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};
use ay_core::{Sort, Symbol};

/// `(= (bvadd m n) m)` over 4 bits: FALSE (any `n != 0`), so its bit-blast is
/// satisfiable and every question about it declines, deterministically.
fn false_identity(terms: &mut TermStore) -> TermId {
    let m = terms.mk_var("m", Sort::bitvec(4));
    let n = terms.mk_var("n", Sort::bitvec(4));
    let sum = terms.mk_app(Symbol::named("bvadd"), [m, n], Sort::bitvec(4));
    terms.mk_eq(sum, m)
}

/// `(= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))` over 4 bits: the
/// quotient-remainder identity, which only the complete bit-blast spells.
fn quotient_remainder_identity(terms: &mut TermStore) -> TermId {
    let m = terms.mk_var("qm", Sort::bitvec(4));
    let n = terms.mk_var("qn", Sort::bitvec(4));
    let mut op =
        |name: &str, args: [TermId; 2]| terms.mk_app(Symbol::named(name), args, Sort::bitvec(4));
    let quotient = op("bvudiv", [m, n]);
    let product = op("bvmul", [quotient, n]);
    let remainder = op("bvurem", [m, n]);
    let sum = op("bvadd", [product, remainder]);
    terms.mk_eq(m, sum)
}

fn question<'q>(terms: &'q TermStore, clause: &'q [TermId]) -> Question<'q> {
    Question {
        terms,
        kind: TheoryLemmaKind::BvBitBlast,
        clause,
        term_overrides: None,
        remembers_support: false,
    }
}

/// The caller's stop as a render polls it.
fn poll(ask: CompleteBlastAsk<'_>) -> bool {
    match ask {
        CompleteBlastAsk::AskedUntil(stop) => stop(),
        CompleteBlastAsk::Asked | CompleteBlastAsk::NotAsked => {
            panic!("a solve's question is asked until its stop")
        }
    }
}

#[test]
fn an_unstopped_decline_answers_every_later_ask_of_its_solve_only() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let clause = [lemma];
    let renders = Cell::new(0_u32);
    let render = |ask: CompleteBlastAsk<'_>| {
        renders.set(renders.get() + 1);
        assert!(!poll(ask));
        false
    };
    let never = || false;
    let solve = BvSupportDeclines::default();
    assert!(!question(&terms, &clause).answered(&never, &solve, render));
    assert!(!question(&terms, &clause).answered(&never, &solve, render));
    assert_eq!((renders.get(), solve.served()), (1, 1));
    // The store may grow: the lemma's terms are still the lemma's.
    let _ = terms.mk_var("later", Sort::bitvec(4));
    assert!(!question(&terms, &clause).answered(&never, &solve, render));
    assert_eq!((renders.get(), solve.served()), (1, 2));

    // Another solve asks again, and so does this record once emptied.
    let next = BvSupportDeclines::default();
    assert!(!question(&terms, &clause).answered(&never, &next, render));
    solve.clear();
    assert!(!question(&terms, &clause).answered(&never, &solve, render));
    assert_eq!((renders.get(), solve.served(), next.served()), (3, 0, 0));

    // Another store is never answered from this one's declines.
    let mut other = TermStore::new();
    let lemma = false_identity(&mut other);
    assert!(!question(&other, &[lemma]).answered(&never, &solve, render));
    assert_eq!(renders.get(), 4);
}

/// The twin: a decline the solve's stop caused is never kept, even when the
/// stop relented before the render returned (the poll is latched).
#[test]
fn a_decline_under_a_stop_is_never_kept() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let clause = [lemma];
    let solve = BvSupportDeclines::default();
    let renders = Cell::new(0_u32);

    let stopped = || true;
    let stopped_render = |ask: CompleteBlastAsk<'_>| {
        renders.set(renders.get() + 1);
        !poll(ask)
    };
    assert!(!question(&terms, &clause).answered(&stopped, &solve, stopped_render));

    let polls = Cell::new(0_u32);
    let relenting = || {
        polls.set(polls.get() + 1);
        polls.get() == 3
    };
    let polled_twice = |ask: CompleteBlastAsk<'_>| {
        renders.set(renders.get() + 1);
        let CompleteBlastAsk::AskedUntil(stop) = ask else {
            panic!("a solve's question is asked until its stop");
        };
        assert!(stop(), "the first poll sees the stop");
        assert!(stop(), "a later poll of the same ask still sees it");
        false
    };
    assert!(!question(&terms, &clause).answered(&relenting, &solve, polled_twice));
    assert_eq!(polls.get(), 3, "a latched stop is not asked again");

    let never = || false;
    let unstopped = |ask: CompleteBlastAsk<'_>| {
        renders.set(renders.get() + 1);
        assert!(!poll(ask));
        false
    };
    assert!(!question(&terms, &clause).answered(&never, &solve, unstopped));
    assert_eq!((renders.get(), solve.served()), (2, 0));
}

/// A `true` answer is never a decline: it joins the support memo when the
/// question is the bit-blast one, and is asked again otherwise.
#[test]
fn a_true_answer_is_not_a_decline() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let clause = [lemma];
    let solve = BvSupportDeclines::default();
    let never = || false;
    let renders = Cell::new(0_u32);
    let admits = |_: CompleteBlastAsk<'_>| {
        renders.set(renders.get() + 1);
        true
    };
    assert!(question(&terms, &clause).answered(&never, &solve, admits));
    assert!(question(&terms, &clause).answered(&never, &solve, admits));
    assert_eq!((renders.get(), solve.served()), (2, 0));

    let remembered = Question {
        remembers_support: true,
        ..question(&terms, &clause)
    };
    assert!(remembered.answered(&never, &solve, admits));
    let unasked = |_: CompleteBlastAsk<'_>| -> bool { unreachable!("the memo answers") };
    assert!(remembered.answered(&never, &solve, unasked));
    assert!(!remembered.answered(&|| true, &solve, unasked));
    assert_eq!((renders.get(), solve.served()), (3, 0));
}

#[test]
fn terminal_stop_after_unpolled_render_does_not_retain_a_decline() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let clause = [lemma];
    let solve = BvSupportDeclines::default();
    let stopped = Cell::new(false);
    assert!(
        !question(&terms, &clause).answered(&|| stopped.get(), &solve, |_| {
            stopped.set(true);
            false
        })
    );
    let rendered = Cell::new(false);
    assert!(!question(&terms, &clause).answered(&|| false, &solve, |_| {
        rendered.set(true);
        false
    }));
    assert!(
        rendered.get(),
        "the stopped decline must not answer a fresh ask"
    );
    assert_eq!(solve.served(), 0);
}

/// Through the printer: the false lemma's bit-blast is refuted by nothing,
/// and the second ask of the solve does no SAT work at all.
#[test]
fn the_bit_blast_question_asks_a_declined_lemma_once_per_solve() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let kind = TheoryLemmaKind::BvBitBlast;
    let solve = BvSupportDeclines::default();
    let never = || false;
    reset_resolution_dag_memo();
    assert!(!checked_bv_bitblast_lowering_supported_within_solve(
        &terms,
        &kind,
        &[lemma],
        None,
        &never,
        &solve,
    ));
    let asked = resolution_dag_memo_counters();
    assert_ne!(asked, (0, 0), "the first ask blasts the lemma");
    assert!(!checked_bv_bitblast_lowering_supported_within_solve(
        &terms,
        &kind,
        &[lemma],
        None,
        &never,
        &solve,
    ));
    assert_eq!(resolution_dag_memo_counters(), asked);
    assert_eq!(solve.served(), 1);
}

/// The twin: a lemma the complete bit-blast spells is admitted exactly as
/// the exporter's question admits it, and nothing is kept as a decline.
#[test]
fn the_bit_blast_question_still_admits_what_the_blast_spells() {
    let mut terms = TermStore::new();
    let identity = quotient_remainder_identity(&mut terms);
    let assertion = terms.mk_not_raw(identity);
    let lemma = terms.mk_not_raw(assertion);
    let kind = TheoryLemmaKind::BvBitBlast;
    let solve = BvSupportDeclines::default();
    let never = || false;
    reset_resolution_dag_memo();
    assert!(checked_bv_bitblast_lowering_supported_within_solve(
        &terms,
        &kind,
        &[lemma],
        None,
        &never,
        &solve,
    ));
    let asked = resolution_dag_memo_counters();
    assert_ne!(asked, (0, 0), "the solve's question blasts the lemma");
    // The exporter's question, from a store the support memo has never seen
    // (from `terms` it would be answered by the memo the call above filled).
    let mut exported = TermStore::new();
    let identity = quotient_remainder_identity(&mut exported);
    let assertion = exported.mk_not_raw(identity);
    let fresh = exported.mk_not_raw(assertion);
    assert!(crate::checked_bv_bitblast_lowering_supported(
        &exported,
        &kind,
        &[fresh],
        None
    ));
    assert_ne!(
        resolution_dag_memo_counters(),
        asked,
        "the exporter's question renders"
    );
    assert_eq!(solve.served(), 0);
}

/// The arithmetic question spends its attempt before the record answers, so
/// the proof's promotion cap is charged as if it asked again; a decline the
/// cap gave is the budget's and is never kept.
#[test]
fn the_arithmetic_question_charges_a_kept_decline_its_attempt() {
    let mut terms = TermStore::new();
    let lemma = false_identity(&mut terms);
    let kind = TheoryLemmaKind::ArithClauseTautology;
    let solve = BvSupportDeclines::default();
    let never = || false;
    let mut budget = ArithPolySimpPromotionBudget::standalone();
    let full = budget.remaining_attempts();
    for asked in 1..=2 {
        assert!(!theory_lemma_bv_arithmetic_lowering_supported_within_solve(
            &terms,
            &kind,
            &[lemma],
            None,
            &mut budget,
            &never,
            &solve,
        ));
        assert_eq!(budget.remaining_attempts(), full - asked);
    }
    assert_eq!(solve.served(), 1);

    // Out of attempts, the lemma is declined by the cap and nothing is kept.
    while budget.spend_attempt() {}
    let other = BvSupportDeclines::default();
    assert!(!theory_lemma_bv_arithmetic_lowering_supported_within_solve(
        &terms,
        &kind,
        &[lemma],
        None,
        &mut budget,
        &never,
        &other,
    ));
    assert_eq!(other.served(), 0);
    assert!(other.table.borrow().entries.is_empty());
}

/// `assume (not identity)` refuted by the one `kind` lemma `(cl identity)`,
/// and the problem scope it renders in.
fn refutation(
    terms: &mut TermStore,
    identity: TermId,
    kind: TheoryLemmaKind,
) -> (ay_core::Proof, Vec<TermId>) {
    let root = terms.mk_not_raw(identity);
    let mut proof = ay_core::Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![identity], kind);
    proof.add_resolution(Vec::new(), identity, lemma, assumption);
    (proof, vec![root])
}

/// A render asked from inside the solve reads the solve's record: a lemma
/// its screen declined is not blasted again, and the document is the one
/// blasting it again prints. Twins: a render before the screen asks, and one
/// reading a record that screen never wrote (a fresh solve's), blast it.
#[test]
fn a_render_inside_the_solve_reads_its_screens_declines() {
    let never = || false;
    let surfaces = crate::AletheAuthoredSurfaces::default();
    for kind in [
        TheoryLemmaKind::BvBitBlast,
        TheoryLemmaKind::ArithClauseTautology,
    ] {
        let mut terms = TermStore::new();
        let identity = false_identity(&mut terms);
        let (proof, scope) = refutation(&mut terms, identity, kind);
        let render = |declines: &BvSupportDeclines| {
            let solve = crate::AskingSolve {
                stop: &never,
                declines,
            };
            crate::try_export_alethe_with_authored_surfaces_within_solve(
                &proof,
                &terms,
                &scope,
                None,
                surfaces,
                Some(16 * 1024 * 1024),
                solve,
            )
            .expect("the render prints")
        };
        let solve = BvSupportDeclines::default();
        reset_resolution_dag_memo();
        let unread = render(&solve);
        assert!(unread.contains(":rule hole"), "{kind:?}");
        let rendered = resolution_dag_memo_counters();
        assert_ne!(
            rendered,
            (0, 0),
            "{kind:?}: an empty record is read for nothing"
        );

        let clause = [identity];
        let declined = match kind {
            TheoryLemmaKind::BvBitBlast => checked_bv_bitblast_lowering_supported_within_solve(
                &terms, &kind, &clause, None, &never, &solve,
            ),
            _ => theory_lemma_bv_arithmetic_lowering_supported_within_solve(
                &terms,
                &kind,
                &clause,
                None,
                &mut ArithPolySimpPromotionBudget::standalone(),
                &never,
                &solve,
            ),
        };
        assert!(!declined, "{kind:?}");
        let screened = resolution_dag_memo_counters();
        assert_eq!(render(&solve), unread, "{kind:?}");
        assert_eq!(resolution_dag_memo_counters(), screened, "{kind:?}");
        assert_eq!(solve.served(), 1, "{kind:?}");

        let _ = render(&BvSupportDeclines::default());
        assert_ne!(resolution_dag_memo_counters(), screened, "{kind:?}");
    }
}
