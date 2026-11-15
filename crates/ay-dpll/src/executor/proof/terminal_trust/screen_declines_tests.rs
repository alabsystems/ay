// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One public decision asks the complete bit-blast about a lemma it declined
//! once; the next decision, and a stopped ask, ask again.
//!
//! Each lemma below is FALSE, so its bit-blast is satisfiable and the screen
//! declines it deterministically; the refutation-memo counters move only when
//! the lemma is blasted.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::{Proof, Sort, Symbol, TermId, TheoryLemmaKind};
use ay_proof::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};

use crate::executor::Executor;

/// `(= (bvadd m n) m)` over 4 bits, false for every `n != 0`.
fn false_identity(executor: &mut Executor, prefix: &str) -> TermId {
    let terms = &mut executor.ctx.terms;
    let m = terms.mk_var(format!("{prefix}_m"), Sort::bitvec(4));
    let n = terms.mk_var(format!("{prefix}_n"), Sort::bitvec(4));
    let sum = terms.mk_app(Symbol::named("bvadd"), [m, n], Sort::bitvec(4));
    terms.mk_app(Symbol::named("="), [sum, m], Sort::Bool)
}

/// `(= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))` over 4 bits, which
/// only the complete bit-blast spells.
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

/// `assume (not identity)` against the POSITIVE unit `(cl identity)` of
/// `kind`: the bit-blast question's lemma, or the 470d83f28 arithmetic shape
/// the strict affine identity was asked through.
fn refutation(executor: &mut Executor, identity: TermId, kind: TheoryLemmaKind) -> Proof {
    let root = executor.ctx.terms.mk_not_raw(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![identity], kind);
    proof.add_resolution(Vec::new(), identity, lemma, assumption);
    proof
}

const KINDS: [TheoryLemmaKind; 2] = [
    TheoryLemmaKind::BvBitBlast,
    TheoryLemmaKind::ArithClauseTautology,
];

fn observable() -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    assert!(executor.proof_document_observable());
    executor
}

#[test]
fn a_decision_blasts_a_declined_lemma_once() {
    for kind in KINDS {
        let mut executor = observable();
        let identity = false_identity(&mut executor, "once");
        let proof = refutation(&mut executor, identity, kind);
        reset_resolution_dag_memo();
        assert!(executor.proof_has_known_wire_gap(&proof));
        let blasted = resolution_dag_memo_counters();
        assert_ne!(
            blasted,
            (0, 0),
            "{kind:?}: the first screen blasts the lemma"
        );
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
        for screen in 1..=3 {
            assert!(executor.proof_has_known_wire_gap(&proof));
            assert_eq!(resolution_dag_memo_counters(), blasted, "{kind:?}");
            assert_eq!(executor.wire_gap_screen_declines().served(), screen);
        }

        // The next public decision asks again: a decline may be a wall
        // clock's, and is this decision's alone.
        executor.advance_query_authority_epoch();
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert_ne!(resolution_dag_memo_counters(), blasted, "{kind:?}");
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
    }
}

/// The twin: a screen stopped by the decision's interrupt declines without a
/// blast and keeps nothing, so the unstopped screen after it still asks.
#[test]
fn a_stopped_screen_keeps_no_decline() {
    for kind in KINDS {
        let mut executor = observable();
        let interrupt = Arc::new(AtomicBool::new(true));
        executor.set_solve_controls(Some(interrupt.clone()), None);
        let identity = false_identity(&mut executor, "stopped");
        let proof = refutation(&mut executor, identity, kind);
        reset_resolution_dag_memo();
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert_eq!(resolution_dag_memo_counters(), (0, 0), "{kind:?}");

        interrupt.store(false, Ordering::Relaxed);
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert_ne!(resolution_dag_memo_counters(), (0, 0), "{kind:?}");
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
    }
}

/// The twin: a lemma the complete bit-blast spells is admitted at every
/// screen of the decision, and the record never answers for it.
#[test]
fn an_admitted_lemma_is_never_a_kept_decline() {
    for kind in KINDS {
        let mut executor = observable();
        let identity = quotient_remainder_identity(&mut executor, "admitted");
        let proof = refutation(&mut executor, identity, kind);
        for _ in 0..3 {
            assert!(!executor.proof_has_known_wire_gap(&proof), "{kind:?}");
        }
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
    }
}

/// The one assertion of a satisfiable query, as the export scope holds it.
fn satisfiable_root(executor: &mut Executor) -> TermId {
    let problem = "(set-logic QF_BV)
(declare-const render_m (_ BitVec 4))
(declare-const render_n (_ BitVec 4))
(assert (not (= (bvadd render_m render_n) render_m)))
(check-sat)";
    let results = executor
        .execute_all(&ay_frontend::parse(problem).unwrap())
        .unwrap();
    assert_eq!(results.first().map(String::as_str), Some("sat"));
    let scope = executor.proof_export_scope_assertions();
    assert_eq!(scope.len(), 1);
    scope[0]
}

/// The decision's in-solve renders read its record: a lemma its screen
/// declined is not blasted again by `proof_renders_without_unproved_step`
/// (`clean_render_len`), which still answers not clean. Twins: a render
/// before the screen, and one in the next decision, blast the lemma.
#[test]
fn a_render_reads_the_decisions_declines() {
    for kind in KINDS {
        let mut executor = observable();
        let root = satisfiable_root(&mut executor);
        // `(cl (not root))` is false: the root is satisfiable.
        let refuted = executor.ctx.terms.mk_not_raw(root);
        let mut proof = Proof::new();
        let assumption = proof.add_assume(root, None);
        let lemma = proof.add_theory_lemma_with_kind("bv", vec![refuted], kind);
        proof.add_resolution(Vec::new(), root, assumption, lemma);
        reset_resolution_dag_memo();
        assert!(!executor.proof_renders_without_unproved_step(&proof));
        let rendered = resolution_dag_memo_counters();
        assert_ne!(rendered, (0, 0), "{kind:?}: an unread render blasts");
        assert!(executor.proof_has_known_wire_gap(&proof));
        let screened = resolution_dag_memo_counters();
        assert_ne!(screened, rendered, "{kind:?}: the screen asks for itself");
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
        assert!(!executor.proof_renders_without_unproved_step(&proof));
        assert_eq!(resolution_dag_memo_counters(), screened, "{kind:?}");
        assert_eq!(executor.wire_gap_screen_declines().served(), 1);

        executor.advance_query_authority_epoch();
        assert!(!executor.proof_renders_without_unproved_step(&proof));
        assert_ne!(resolution_dag_memo_counters(), screened, "{kind:?}");
    }
}

/// The ground closure's presentation screen (`renders_wire_clean`, through
/// `presents_wire_clean`) reads the record as the choice render does: once
/// the decision's screen declined the lemma, the presented render is
/// answered from the record and is still not clean. Twin: before the
/// screen, the render has nothing to read.
#[test]
fn the_presentation_screen_reads_the_decisions_declines() {
    for kind in KINDS {
        let mut executor = Executor::new();
        // Unsatisfiable only with the first assertion, so the lemma
        // `(cl (= (bvadd m n) m))` the proof cites is false by itself.
        let problem = "(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const shown_m (_ BitVec 4))
(declare-const shown_n (_ BitVec 4))
(assert (= shown_n #x0))
(assert (not (= (bvadd shown_m shown_n) shown_m)))
(check-sat)";
        let results = executor
            .execute_all(&ay_frontend::parse(problem).unwrap())
            .unwrap();
        assert_eq!(results, vec!["unsat".to_string()]);
        assert!(executor.proof_document_observable());
        let root = *executor
            .ctx
            .assertions
            .last()
            .expect("the authored assertion");
        assert!(matches!(
            executor.ctx.terms.get(root),
            ay_core::TermData::Not(_)
        ));
        // Unstopped, as the solve that asks is while it runs.
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(false))), None);
        let refuted = executor.ctx.terms.mk_not_raw(root);
        let mut proof = Proof::new();
        let assumption = proof.add_assume(root, None);
        let lemma = proof.add_theory_lemma_with_kind("bv", vec![refuted], kind);
        proof.add_resolution(Vec::new(), root, assumption, lemma);
        assert!(!executor.presents_wire_clean(&proof));
        assert_eq!(executor.wire_gap_screen_declines().served(), 0, "{kind:?}");
        assert!(executor.proof_has_known_wire_gap(&proof));
        assert!(executor.proof_has_known_wire_gap(&proof));
        let served = executor.wire_gap_screen_declines().served();
        assert!(served >= 1, "{kind:?}: the screen keeps its decline");
        assert!(!executor.presents_wire_clean(&proof));
        assert_eq!(
            executor.wire_gap_screen_declines().served(),
            served + 1,
            "{kind:?}"
        );
    }
}

/// With no observable document the complete bit-blast is not asked, and its
/// "not asked" is not a decline the record keeps for an observable screen.
#[test]
fn an_unobservable_decline_is_not_kept() {
    for kind in KINDS {
        let mut executor = Executor::new();
        let identity = quotient_remainder_identity(&mut executor, "unobserved");
        let proof = refutation(&mut executor, identity, kind);
        assert!(executor.proof_has_known_wire_gap(&proof), "{kind:?}");
        executor.set_produce_proofs(true);
        assert!(!executor.proof_has_known_wire_gap(&proof), "{kind:?}");
        assert_eq!(executor.wire_gap_screen_declines().served(), 0);
    }
}
