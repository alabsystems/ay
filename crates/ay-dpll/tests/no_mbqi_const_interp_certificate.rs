// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BOTH DIRECTIONS of admitting a `no_mbqi` (E-matching-only, Hilbert-`choose`)
//! `forall` into the CONSTANT-INTERPRETATION SAT certificate's partition.
//!
//! The mark exists so a Hilbert witness axiom is never discharged by MBQI —
//! MBQI reads a finite model fragment and GENERALISES it, which for a witness
//! axiom would fabricate the very witness the program withholds. That guard is
//! untouched, and so is every sibling model-based certificate. This certificate
//! is a different animal: it mints a fresh constant per binder, substitutes a
//! candidate interpretation `I`, and requires a proof-certified `Unsat` on the
//! NEGATED body from a disposable checked solve. It PROVES `∀x̄. B[I]`; it never
//! guesses it. And it only ever turns a quantifier-class `Unknown` into `Sat`.
//!
//! So the pins come in pairs:
//!
//!   * GRANT — the witnessless Hilbert-`choose` shape is satisfiable and must
//!     now produce a model, marked or not.
//!   * DECLINE — an unsatisfiable snapshot has no interpretation to certify, so
//!     the certificate must keep refusing it however it is marked. That covers
//!     the exact shape whose deductive-checks regression the mark was introduced for.
//!
//! Do NOT "fix" a failure here by restoring a blanket `is_no_mbqi` refusal in
//! `const_interp_cert_inner`: that silently retires the grant half. The
//! reasoning is recorded at that site.

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

enum Verdict {
    Sat(String),
    Unsat,
    Unknown,
}

fn verdict(solver: &mut Solver) -> Verdict {
    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Sat) => Verdict::Sat(
            solver
                .try_get_model_str()
                .expect("a SAT from this certificate must publish its interpretation"),
        ),
        Ok(SolveResult::Unsat(_)) => Verdict::Unsat,
        Ok(SolveResult::Unknown) => Verdict::Unknown,
        other => panic!("unexpected solve outcome: {other:?}"),
    }
}

/// `forall x. P(x) => P(c)` (the combined Hilbert-`choose` axiom over an
/// UNINTERPRETED predicate) beside the negated goal `not P(c)`, with NO ground
/// witness asserted. `P := false` satisfies both, so this is SAT and the
/// certificate can prove it: under that `I` the body folds to `true` and the
/// ground conjunct folds to `true`.
fn witnessless_choose(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let body = s.try_implies(px, pc).expect("implies");
    let q = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let npc = s.try_not(pc).expect("not");
    s.try_assert_term(npc).expect("assert");
    verdict(&mut s)
}

/// The same axiom WITH a genuine ground witness `P(w)`. Now `P(w) => P(c)` and
/// `P(w)` force `P(c)`, contradicting `not P(c)`: the snapshot is UNSAT and no
/// interpretation certifies it.
fn ground_witness_choose(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let w = s.declare_const("w", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let pw = s.try_apply(&p, &[w]).expect("apply");
    let body = s.try_implies(px, pc).expect("implies");
    let q = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    s.try_assert_term(pw).expect("assert");
    let npc = s.try_not(pc).expect("not");
    s.try_assert_term(npc).expect("assert");
    verdict(&mut s)
}

/// The shape from `#no-mbqi-rewrite-transfer`: `forall i j. i<=j => c0<=c1`
/// beside `c1 < c0`. Instantiating at `i = j` forces `c0 <= c1`, so the
/// snapshot is UNSAT. The mark suppresses that refutation on purpose (Verus's
/// trigger-only `choose`), and the certificate must not convert the resulting
/// `Unknown` into a SAT — there is no model to find.
fn linear_choose_conclusion(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let c0 = s.declare_const("c0", Sort::Int);
    let c1 = s.declare_const("c1", Sort::Int);
    let i = s.fresh_var("i", Sort::Int);
    let j = s.fresh_var("j", Sort::Int);
    let ante = s.try_le(i, j).expect("le");
    let concl = s.try_le(c0, c1).expect("le");
    let body = s.try_implies(ante, concl).expect("implies");
    let q = s.try_forall(&[i, j], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let lt = s.try_lt(c1, c0).expect("lt");
    s.try_assert_term(lt).expect("assert");
    verdict(&mut s)
}

/// GRANT half. Before the admission this answered `unknown
/// (quantifier-unhandled)` while the byte-identical UNMARKED query answered
/// `sat`, so the mark alone was costing a sound refutation.
#[test]
fn no_mbqi_witnessless_choose_is_certified_sat() {
    let Verdict::Sat(model) = witnessless_choose(true) else {
        panic!(
            "a `no_mbqi` Hilbert-choose axiom with no ground witness is SATISFIABLE \
             (`P := false`) and the constant-interpretation certificate proves it by \
             refuting the negated body under that `I`. Answering anything else means \
             the blanket `is_no_mbqi` refusal is back in `const_interp_cert_inner` — \
             read the reasoning at that site before restoring it."
        );
    };
    // The published model IS the certified interpretation, so it must name the
    // head the proof is about.
    assert!(
        model.contains("define-fun P"),
        "the certificate's SAT must publish `I` itself, including the pinned \
         predicate: {model}"
    );
}

/// The capability dual: the unmarked query was always decided, and stays so.
#[test]
fn unmarked_witnessless_choose_still_sat() {
    assert!(
        matches!(witnessless_choose(false), Verdict::Sat(_)),
        "the unmarked witnessless choose axiom is satisfiable and must stay decided"
    );
}

/// DECLINE half #1 — a genuine ground witness makes the snapshot UNSAT, and it
/// must still refute with the mark on. A `Sat` here would be the wrong-SAT the
/// mark's "fires only on a genuine ground witness" discipline is about.
#[test]
fn no_mbqi_choose_with_ground_witness_still_refutes() {
    assert!(
        matches!(ground_witness_choose(true), Verdict::Unsat),
        "an asserted ground witness forces `P(c)`; the snapshot is UNSAT and no \
         interpretation may be certified for it"
    );
    assert!(
        matches!(ground_witness_choose(false), Verdict::Unsat),
        "and the unmarked query refutes identically"
    );
}

/// DECLINE half #2 — the `#no-mbqi-rewrite-transfer` shape. The mark keeps the
/// refutation suppressed (that is its job); the certificate must NOT step in
/// with a SAT, because the snapshot has no model at all.
#[test]
fn no_mbqi_linear_choose_conclusion_is_never_certified_sat() {
    assert!(
        matches!(linear_choose_conclusion(true), Verdict::Unknown),
        "`forall i j. i<=j => c0<=c1` beside `c1 < c0` is UNSAT: admitting the \
         marked forall into the certificate partition must leave it declining, \
         because no candidate interpretation can discharge both conjuncts"
    );
    assert!(
        matches!(linear_choose_conclusion(false), Verdict::Unsat),
        "and the unmarked query is still refuted outright"
    );
}
