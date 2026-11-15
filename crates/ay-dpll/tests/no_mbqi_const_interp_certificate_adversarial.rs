// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! ADVERSARIAL pins for admitting a `no_mbqi` (E-matching-only,
//! Hilbert-`choose`) `forall` into the CONSTANT-INTERPRETATION SAT
//! certificate's partition.
//!
//! The sibling file `no_mbqi_const_interp_certificate.rs` pins the two
//! headline directions (the witnessless choose GRANTS; the ground-witness and
//! linear-conclusion shapes do not). This file attacks the certificate on the
//! shapes a Hilbert `choose` actually produces, which differ from the
//! arithmetic `forall`s the lane was built for: the witness is a skolem
//! constant, the predicate is an uninterpreted spec fn, and one snapshot can
//! carry SEVERAL such axioms over shared symbols.
//!
//! Every UNSAT-truth probe here pins the same property: the certificate must
//! never answer `Sat`. A grant is a claim that an explicitly constructed
//! interpretation satisfies EVERY snapshot assertion, so a grant on an
//! unsatisfiable snapshot would be a wrong-SAT — a fabricated counterexample
//! for deductive-checks. Every SAT-truth probe additionally checks that the published
//! model names the symbols the proof is about; those models were also checked
//! by hand, OUTSIDE ay, when these pins were written.

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

#[derive(Debug)]
enum Verdict {
    Sat(String),
    Unsat,
    Unknown,
}

impl Verdict {
    fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    fn model(&self) -> &str {
        match self {
            Self::Sat(model) => model,
            _ => "",
        }
    }
}

fn verdict(solver: &mut Solver) -> Verdict {
    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Sat) => Verdict::Sat(
            solver
                .try_get_model_str()
                .expect("a SAT on this route must publish its interpretation"),
        ),
        Ok(SolveResult::Unsat(_)) => Verdict::Unsat,
        Ok(SolveResult::Unknown) => Verdict::Unknown,
        other => panic!("unexpected solve outcome: {other:?}"),
    }
}

/// TWO choose axioms over ONE predicate, different skolems, plus a ground
/// witness for the first. `P(c)` with the second axiom at `x = c` forces
/// `P(d)`, contradicting `not P(d)`. Truth: UNSAT.
fn two_axioms_one_predicate(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let d = s.declare_const("d", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let y = s.fresh_var("y", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let py = s.try_apply(&p, &[y]).expect("apply");
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let pd = s.try_apply(&p, &[d]).expect("apply");
    let b1 = s.try_implies(px, pc).expect("implies");
    let a1 = s.try_forall(&[x], b1).expect("forall");
    let b2 = s.try_implies(py, pd).expect("implies");
    let a2 = s.try_forall(&[y], b2).expect("forall");
    if mark {
        s.mark_no_mbqi(a1);
        s.mark_no_mbqi(a2);
    }
    s.try_assert_term(a1).expect("assert");
    s.try_assert_term(a2).expect("assert");
    s.try_assert_term(pc).expect("assert");
    let npd = s.try_not(pd).expect("not");
    s.try_assert_term(npd).expect("assert");
    verdict(&mut s)
}

/// SHARED-`I` DISCIPLINE. Two marked axioms chained through a `Bool` constant.
/// Each axiom ALONE has a satisfying constant interpretation; no single shared
/// one satisfies both beside the grounds (`P(a)` forces `R`, `R` forces
/// `Q(b)`, and `not Q(b)` is asserted). Truth: UNSAT. This is the pin for the
/// certificate enumerating ONE assignment per head for the WHOLE snapshot
/// rather than per axiom.
fn chained_marked_axioms(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let q = s.declare_fun("Q", &[Sort::Int], Sort::Bool);
    let r = s.declare_const("R", Sort::Bool);
    let a = s.declare_const("a", Sort::Int);
    let b = s.declare_const("b", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let y = s.fresh_var("y", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let qy = s.try_apply(&q, &[y]).expect("apply");
    let b1 = s.try_implies(px, r).expect("implies");
    let a1 = s.try_forall(&[x], b1).expect("forall");
    let b2 = s.try_implies(r, qy).expect("implies");
    let a2 = s.try_forall(&[y], b2).expect("forall");
    if mark {
        s.mark_no_mbqi(a1);
        s.mark_no_mbqi(a2);
    }
    s.try_assert_term(a1).expect("assert");
    s.try_assert_term(a2).expect("assert");
    let pa = s.try_apply(&p, &[a]).expect("apply");
    s.try_assert_term(pa).expect("assert");
    let qb = s.try_apply(&q, &[b]).expect("apply");
    let nqb = s.try_not(qb).expect("not");
    s.try_assert_term(nqb).expect("assert");
    verdict(&mut s)
}

/// The choose predicate is PROVABLY EMPTY (`forall z. not P(z)`) and the
/// program nonetheless asserts the chosen value satisfies it. Truth: UNSAT.
/// The lane must not invent the witness that does not exist.
fn empty_predicate_choose(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let z = s.fresh_var("z", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let pz = s.try_apply(&p, &[z]).expect("apply");
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let npz = s.try_not(pz).expect("not");
    let empty = s.try_forall(&[z], npz).expect("forall");
    let body = s.try_implies(px, pc).expect("implies");
    let hilbert = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(empty);
        s.mark_no_mbqi(hilbert);
    }
    s.try_assert_term(empty).expect("assert");
    s.try_assert_term(hilbert).expect("assert");
    s.try_assert_term(pc).expect("assert");
    verdict(&mut s)
}

/// A marked choose axiom NESTED under another quantifier. The partition
/// rejects a nested quantifier outright; the pin is that the rejection is
/// fail-closed (never `Sat`) rather than merely silent. Truth: UNSAT.
fn nested_choose(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let r = s.declare_fun("R", &[Sort::Int], Sort::Bool);
    let qf = s.declare_fun("Q", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let y = s.fresh_var("y", Sort::Int);
    let w = s.fresh_var("w", Sort::Int);
    let ry = s.try_apply(&r, &[y]).expect("apply");
    let inner = s.try_forall(&[y], ry).expect("forall");
    let qx = s.try_apply(&qf, &[x]).expect("apply");
    let body = s.try_implies(inner, qx).expect("implies");
    let outer = s.try_forall(&[x], body).expect("forall");
    let rw = s.try_apply(&r, &[w]).expect("apply");
    let rall = s.try_forall(&[w], rw).expect("forall");
    if mark {
        s.mark_no_mbqi(outer);
    }
    s.try_assert_term(outer).expect("assert");
    s.try_assert_term(rall).expect("assert");
    let qc = s.try_apply(&qf, &[c]).expect("apply");
    let nqc = s.try_not(qc).expect("not");
    s.try_assert_term(nqc).expect("assert");
    verdict(&mut s)
}

/// The witness is constrained by GROUND facts that contradict every minted
/// candidate: `f(c) = 3` and `f(d) = 4` beside `forall x. f(x) = f(c)`.
/// Truth: UNSAT. Pins that the ground conjuncts are DISCHARGED under the same
/// `I`, not skipped.
fn ground_pinned_contradiction(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
    let c = s.declare_const("c", Sort::Int);
    let d = s.declare_const("d", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let fx = s.try_apply(&f, &[x]).expect("apply");
    let fc = s.try_apply(&f, &[c]).expect("apply");
    let fd = s.try_apply(&f, &[d]).expect("apply");
    let body = s.try_eq(fx, fc).expect("eq");
    let q = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let three = s.int_const(3);
    let four = s.int_const(4);
    let e1 = s.try_eq(fc, three).expect("eq");
    let e2 = s.try_eq(fd, four).expect("eq");
    s.try_assert_term(e1).expect("assert");
    s.try_assert_term(e2).expect("assert");
    verdict(&mut s)
}

/// A head pinned AGAINST its own axiom: `forall x. h(x) >= 0` beside
/// `h(a) = -1`. Truth: UNSAT.
fn head_pinned_against_axiom(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let h = s.declare_fun("h", &[Sort::Int], Sort::Int);
    let a = s.declare_const("a", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let hx = s.try_apply(&h, &[x]).expect("apply");
    let zero = s.int_const(0);
    let body = s.try_ge(hx, zero).expect("ge");
    let q = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let ha = s.try_apply(&h, &[a]).expect("apply");
    let minus_one = s.int_const(-1);
    let eq = s.try_eq(ha, minus_one).expect("eq");
    s.try_assert_term(eq).expect("assert");
    verdict(&mut s)
}

/// BINDER / DECLARED-CONSTANT NAME COLLISION with a non-tautological body.
/// `c` is a declared `Int` constant AND the binder, so the bound occurrence and
/// the free occurrence are the SAME hash-consed term. `forall c. P(c)` beside
/// `not P(c)` is UNSAT under either reading, and the certificate's
/// binder-before-head substitution order must not turn it into a `Sat`.
fn binder_name_collision(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let Ok(q) = s.try_forall(&[c], pc) else {
        // The API may refuse a declared constant as a binder; then there is
        // nothing to pin here and the probe is vacuously satisfied.
        return Verdict::Unknown;
    };
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let npc = s.try_not(pc).expect("not");
    s.try_assert_term(npc).expect("assert");
    verdict(&mut s)
}

/// TWO marked axioms crossing two predicates, genuinely SATISFIABLE by
/// `P := false, Q := false`. Checked by hand outside ay: `P(x) => Q(c)` is
/// `false => false`, `Q(y) => P(d)` is `false => false`, and both grounds are
/// `not false`.
fn two_axioms_cross_sat(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let q = s.declare_fun("Q", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let d = s.declare_const("d", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let y = s.fresh_var("y", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let qc = s.try_apply(&q, &[c]).expect("apply");
    let qy = s.try_apply(&q, &[y]).expect("apply");
    let pd = s.try_apply(&p, &[d]).expect("apply");
    let b1 = s.try_implies(px, qc).expect("implies");
    let a1 = s.try_forall(&[x], b1).expect("forall");
    let b2 = s.try_implies(qy, pd).expect("implies");
    let a2 = s.try_forall(&[y], b2).expect("forall");
    if mark {
        s.mark_no_mbqi(a1);
        s.mark_no_mbqi(a2);
    }
    s.try_assert_term(a1).expect("assert");
    s.try_assert_term(a2).expect("assert");
    let npd = s.try_not(pd).expect("not");
    let nqc = s.try_not(qc).expect("not");
    s.try_assert_term(npd).expect("assert");
    s.try_assert_term(nqc).expect("assert");
    verdict(&mut s)
}

/// A marked choose axiom whose only workable value for the nullary head is
/// named by a GROUND EQUALITY outside the fixed `0/1` family (`g = 42`).
/// Truth: SAT. Pins that the widened-candidate pass composes with the mark.
fn widened_marked_grant(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let g = s.declare_const("g", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let zero = s.int_const(0);
    let nonneg = s.try_ge(g, zero).expect("ge");
    let body = s.try_implies(px, nonneg).expect("implies");
    let q = s.try_forall(&[x], body).expect("forall");
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).expect("assert");
    let fortytwo = s.int_const(42);
    let eq = s.try_eq(g, fortytwo).expect("eq");
    s.try_assert_term(eq).expect("assert");
    verdict(&mut s)
}

/// A grant on one query must not leak into the next. Query 1 is the
/// witnessless marked choose (SAT); query 2 pushes a ground witness that makes
/// it UNSAT.
fn grant_then_refute() -> (Verdict, Verdict) {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let w = s.declare_const("w", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).expect("apply");
    let pc = s.try_apply(&p, &[c]).expect("apply");
    let body = s.try_implies(px, pc).expect("implies");
    let q = s.try_forall(&[x], body).expect("forall");
    s.mark_no_mbqi(q);
    s.try_assert_term(q).expect("assert");
    let npc = s.try_not(pc).expect("not");
    s.try_assert_term(npc).expect("assert");
    let first = verdict(&mut s);
    s.push();
    let pw = s.try_apply(&p, &[w]).expect("apply");
    s.try_assert_term(pw).expect("assert");
    let second = verdict(&mut s);
    s.pop();
    (first, second)
}

/// The shape deductive-checks actually hands ay for `choose.rs::test1_fails1`, with the
/// spec fn `f` carried by its DEFINITIONAL BODY AXIOM: `forall x. f(x) = (5 <=
/// x)`, the marked Hilbert axiom `forall j. f(j) => f(sk)`, and the negated
/// goal `not (5 <= sk)`.
fn vc_shape_fails1(mark: bool, transparent: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
    let sk = s.declare_const("choose_sk", Sort::Int);
    let five = s.int_const(5);
    if transparent {
        let x = s.fresh_var("x", Sort::Int);
        let fx = s.try_apply(&f, &[x]).expect("apply");
        let le = s.try_le(five, x).expect("le");
        let eq = s.try_eq(fx, le).expect("eq");
        let body_axiom = s.try_forall(&[x], eq).expect("forall");
        s.try_assert_term(body_axiom).expect("assert");
    }
    let j = s.fresh_var("j", Sort::Int);
    let fj = s.try_apply(&f, &[j]).expect("apply");
    let fsk = s.try_apply(&f, &[sk]).expect("apply");
    let imp = s.try_implies(fj, fsk).expect("implies");
    let choose_axiom = s.try_forall(&[j], imp).expect("forall");
    if mark {
        s.mark_no_mbqi(choose_axiom);
    }
    s.try_assert_term(choose_axiom).expect("assert");
    let goal = s.try_le(five, sk).expect("le");
    let neg = s.try_not(goal).expect("not");
    s.try_assert_term(neg).expect("assert");
    verdict(&mut s)
}

#[test]
fn unsat_choose_snapshots_are_never_certified_sat() {
    for mark in [true, false] {
        assert!(
            !two_axioms_one_predicate(mark).is_sat(),
            "two choose axioms over one predicate with a ground witness for the \
             first are UNSAT; a Sat here is a fabricated counterexample \
             (mark={mark})"
        );
        assert!(
            !chained_marked_axioms(mark).is_sat(),
            "each axiom alone has a constant interpretation but no SHARED one \
             satisfies the whole snapshot; a Sat here means the certificate \
             stopped enumerating one assignment per head for the whole snapshot \
             (mark={mark})"
        );
        assert!(
            !empty_predicate_choose(mark).is_sat(),
            "the choose predicate is provably empty, so no witness exists; a Sat \
             here means the lane invented one (mark={mark})"
        );
        assert!(
            !nested_choose(mark).is_sat(),
            "a nested quantifier is out of the certificate's class and must \
             decline fail-closed (mark={mark})"
        );
        assert!(
            !ground_pinned_contradiction(mark).is_sat(),
            "the ground conjuncts contradict every candidate for the head; a Sat \
             here means they were skipped rather than discharged under the same \
             `I` (mark={mark})"
        );
        assert!(
            !head_pinned_against_axiom(mark).is_sat(),
            "`h(a) = -1` refutes every candidate for `forall x. h(x) >= 0` \
             (mark={mark})"
        );
        assert!(
            !binder_name_collision(mark).is_sat(),
            "a binder spelled like a declared constant must not let the \
             binder-before-head substitution turn an UNSAT snapshot into a Sat \
             (mark={mark})"
        );
    }
}

#[test]
fn satisfiable_choose_snapshots_publish_a_real_interpretation() {
    for mark in [true, false] {
        let v = two_axioms_cross_sat(mark);
        assert!(
            v.is_sat(),
            "`P := false, Q := false` satisfies both crossed choose axioms and \
             both grounds (mark={mark})"
        );
        let model = v.model();
        assert!(
            model.contains("define-fun P") && model.contains("define-fun Q"),
            "the published interpretation must name every predicate the proof is \
             about: {model}"
        );

        let v = widened_marked_grant(mark);
        assert!(
            v.is_sat(),
            "`g = 42` is named by the problem itself and satisfies the axiom \
             (mark={mark})"
        );
        assert!(
            v.model().contains("42"),
            "the published interpretation must carry the widened value: {}",
            v.model()
        );
    }
}

#[test]
fn a_grant_does_not_leak_into_the_next_query() {
    let (first, second) = grant_then_refute();
    assert!(
        first.is_sat(),
        "the witnessless marked choose is satisfiable and must be decided"
    );
    assert!(
        !second.is_sat(),
        "pushing a ground witness makes the same snapshot UNSAT; answering Sat \
         would mean the certificate's grant survived into the next query"
    );
}

/// The reason this admission does NOT unblock deductive-checks's
/// `choose.rs::test1_fails1`, pinned as a fact rather than left as an argument.
///
/// With the spec fn OPAQUE the snapshot is satisfiable and ay decides it. With
/// the definitional body axiom present — which is what deductive-checks actually
/// asserts for a `#[deductive_checks::spec]` fn — instantiating the choose axiom at any
/// `j >= 5` forces `f(sk)`, hence `5 <= sk`, contradicting the negated goal. The
/// snapshot is UNSAT, so NO satisfiability certificate can ever produce a model
/// for it, marked or not. Anything that makes this case report a counterexample
/// has to change what deductive-checks ASSERTS.
#[test]
fn transparent_spec_fn_choose_has_no_model_to_certify() {
    assert!(
        !vc_shape_fails1(true, true).is_sat(),
        "with the body axiom present the snapshot is UNSAT; a Sat would be a \
         fabricated counterexample"
    );
    assert!(
        matches!(vc_shape_fails1(false, true), Verdict::Unsat),
        "and without the mark ay refutes it outright, which is what makes the \
         `unknown` above a suppressed refutation rather than a missing model"
    );
    assert!(
        vc_shape_fails1(true, false).is_sat(),
        "with the spec fn OPAQUE there is no witness, `f := false` is a model, \
         and the marked query is still decided"
    );
}

/// The same transparent-spec-fn shape, but with the threshold named by a GROUND
/// EQUALITY (`g = 42`) so that the certificate's widened-candidate pass has a
/// real value to try for `g`. Instantiating the choose axiom at `j = 42` forces
/// `f(sk)`, hence `sk >= g`, contradicting the negated goal. Truth: UNSAT, and
/// the widening must not rescue it.
fn vc_shape_fails1_widened(mark: bool) -> Verdict {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
    let g = s.declare_const("g", Sort::Int);
    let sk = s.declare_const("choose_sk", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let fx = s.try_apply(&f, &[x]).expect("apply");
    let ge = s.try_ge(x, g).expect("ge");
    let eq = s.try_eq(fx, ge).expect("eq");
    let body_axiom = s.try_forall(&[x], eq).expect("forall");
    s.try_assert_term(body_axiom).expect("assert");
    let fortytwo = s.int_const(42);
    let pin = s.try_eq(g, fortytwo).expect("eq");
    s.try_assert_term(pin).expect("assert");
    let j = s.fresh_var("j", Sort::Int);
    let fj = s.try_apply(&f, &[j]).expect("apply");
    let fsk = s.try_apply(&f, &[sk]).expect("apply");
    let imp = s.try_implies(fj, fsk).expect("implies");
    let choose_axiom = s.try_forall(&[j], imp).expect("forall");
    if mark {
        s.mark_no_mbqi(choose_axiom);
    }
    s.try_assert_term(choose_axiom).expect("assert");
    let goal = s.try_ge(sk, g).expect("ge");
    let neg = s.try_not(goal).expect("not");
    s.try_assert_term(neg).expect("assert");
    verdict(&mut s)
}

#[test]
fn a_widened_candidate_does_not_rescue_an_unsat_choose_snapshot() {
    for mark in [true, false] {
        assert!(
            !vc_shape_fails1_widened(mark).is_sat(),
            "`g = 42` gives the widened pass a real candidate, but the snapshot \
             is still UNSAT and no interpretation satisfies it (mark={mark})"
        );
    }
}
