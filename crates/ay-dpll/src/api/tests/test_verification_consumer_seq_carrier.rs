// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regressions for UF-encoded sequences over the native `(Seq Int)` carrier
//! sort (verification-consumer's Seq encoding, 2026-07-05).
//!
//! verification-consumer models `Seq<T>` operations as plain uninterpreted functions
//! (`seq_concat`, `seq_push_back`, `seq_reverse`, ...) over `(Seq Int)`-sorted
//! terms, with NO native `seq.*` operations. Two independent defects broke
//! this fragment after the 2026-07-04 soundness salvage:
//!
//! 1. Conflict-domain classification mapped every Seq-SORTED equality to the
//!    String domain, whose structural verifier cannot verify plain UF
//!    equalities. Since the #8595 fail-open removal, those (EUF-valid)
//!    conflicts were never learned, so trivially-UNSAT ground congruence
//!    queries degraded to Unknown — or worse, the residual search space
//!    admitted a spurious model and the solve returned a wrong `Sat`.
//! 2. The UF-completion certificate accepted FIXPOINT-shaped axioms such as
//!    verification-consumer's Seq reverse rule R4
//!    `forall s x. reverse(push_back(s, x)) = push_front(reverse(s), x)`
//!    as pointwise-completable "UF definitions" (nested-application head and
//!    the defined symbol reappearing on the value side), promoting a ground
//!    Unknown/Sat to a validated `Sat` on a genuinely UNSAT query
//!    (z3: unsat).

use crate::api::{Logic, SolveResult, Solver, Sort};

/// Ground EUF congruence over the Seq carrier: a' = push_back(a, x),
/// b = push_front(b', x), concat(push_back(a,x), b') = concat(a, push_front(b',x))
/// entail concat(a, b) = concat(a', b') by congruence, so forcing that
/// equality's negation through a Bool bridge is UNSAT.
#[test]
fn seq_carrier_ground_congruence_chain_is_unsat() {
    let mut s = Solver::try_new(Logic::Auflia).expect("solver");
    let seq = Sort::seq(Sort::Int);
    let a = s.declare_const("a", seq.clone());
    let a_p = s.declare_const("a_prime", seq.clone());
    let b = s.declare_const("b", seq.clone());
    let b_p = s.declare_const("b_prime", seq.clone());
    let x = s.declare_const("x", Sort::Int);

    let push_back = s.declare_fun("seq_push_back", &[seq.clone(), Sort::Int], seq.clone());
    let push_front = s.declare_fun("seq_push_front", &[seq.clone(), Sort::Int], seq.clone());
    let concat = s.declare_fun("seq_concat", &[seq.clone(), seq.clone()], seq.clone());

    let pb = s.apply(&push_back, &[a, x]);
    let e1 = s.eq(a_p, pb);
    s.assert_term(e1);
    let pf = s.apply(&push_front, &[b_p, x]);
    let e2 = s.eq(b, pf);
    s.assert_term(e2);
    let concat_old = s.apply(&concat, &[a, b]);
    let concat_new = s.apply(&concat, &[a_p, b_p]);
    let concat_lhs = s.apply(&concat, &[pb, b_p]);
    let concat_rhs = s.apply(&concat, &[a, pf]);
    let bridge = s.eq(concat_lhs, concat_rhs);
    s.assert_term(bridge);
    let r = s.fresh_var("r", Sort::Bool);
    let ceq = s.eq(concat_old, concat_new);
    let imp = s.implies(ceq, r);
    s.assert_term(imp);
    let nr = s.not(r);
    s.assert_term(nr);

    let res = s.check_sat().into_inner();
    assert!(
        matches!(res, SolveResult::Unsat(_)),
        "ground congruence chain over the Seq carrier must be UNSAT, got {res:?}"
    );
}

/// Direct two-step congruence (a = a', b = b' |= concat(a,b) = concat(a',b'))
/// over the Seq carrier sort.
#[test]
fn seq_carrier_direct_congruence_is_unsat() {
    let mut s = Solver::try_new(Logic::QfAuflia).expect("solver");
    let seq = Sort::seq(Sort::Int);
    let a = s.declare_const("a", seq.clone());
    let a_p = s.declare_const("a_prime", seq.clone());
    let b = s.declare_const("b", seq.clone());
    let b_p = s.declare_const("b_prime", seq.clone());
    let concat = s.declare_fun("seq_concat", &[seq.clone(), seq.clone()], seq.clone());

    let e1 = s.eq(a, a_p);
    s.assert_term(e1);
    let e2 = s.eq(b, b_p);
    s.assert_term(e2);
    let c1 = s.apply(&concat, &[a, b]);
    let c2 = s.apply(&concat, &[a_p, b_p]);
    let r = s.fresh_var("r", Sort::Bool);
    let ceq = s.eq(c1, c2);
    let imp = s.implies(ceq, r);
    s.assert_term(imp);
    let nr = s.not(r);
    s.assert_term(nr);

    let res = s.check_sat().into_inner();
    assert!(
        matches!(res, SolveResult::Unsat(_)),
        "direct congruence over the Seq carrier must be UNSAT, got {res:?}"
    );
}

/// verification-consumer's Seq reverse preservation shape: the quantified R4/R5 rules are
/// FIXPOINT constraints on `seq_reverse`, not pointwise UF definitions. With
/// the ground facts
///   result = reverse(produced)
///   produced' = push_back(produced, x)
///   result' = push_front(result, x)
/// R4 entails reverse(produced') = push_front(reverse(produced), x) = result',
/// so `result' != reverse(produced')` is UNSAT (z3 agrees). The UF-completion
/// certificate must never certify these axioms as completable definitions and
/// promote this to `Sat`.
#[test]
fn seq_carrier_reverse_fixpoint_axioms_must_not_be_sat() {
    let mut s = Solver::try_new(Logic::Auflia).expect("solver");
    let seq = Sort::seq(Sort::Int);
    let result = s.declare_const("result", seq.clone());
    let produced = s.declare_const("produced", seq.clone());
    let result_p = s.declare_const("result_prime", seq.clone());
    let produced_p = s.declare_const("produced_prime", seq.clone());
    let x = s.declare_const("x", Sort::Int);

    let push_back = s.declare_fun("seq_push_back", &[seq.clone(), Sort::Int], seq.clone());
    let push_front = s.declare_fun("seq_push_front", &[seq.clone(), Sort::Int], seq.clone());
    let reverse = s.declare_fun("seq_reverse", std::slice::from_ref(&seq), seq.clone());

    // R4: forall s x. reverse(push_back(s, x)) = push_front(reverse(s), x)
    let qs = s.fresh_var("qs", seq.clone());
    let qx = s.fresh_var("qx", Sort::Int);
    let pb_q = s.apply(&push_back, &[qs, qx]);
    let rev_pb = s.apply(&reverse, &[pb_q]);
    let rev_qs = s.apply(&reverse, &[qs]);
    let pf_rev = s.apply(&push_front, &[rev_qs, qx]);
    let r4_body = s.eq(rev_pb, pf_rev);
    let r4 = s.forall_with_triggers(&[qs, qx], r4_body, &[&[rev_pb]]);
    s.assert_term(r4);

    // Ground preservation facts + negated goal.
    let rev_produced = s.apply(&reverse, &[produced]);
    let inv = s.eq(result, rev_produced);
    s.assert_term(inv);
    let pb = s.apply(&push_back, &[produced, x]);
    let eff_p = s.eq(produced_p, pb);
    s.assert_term(eff_p);
    let pf = s.apply(&push_front, &[result, x]);
    let eff_r = s.eq(result_p, pf);
    s.assert_term(eff_r);
    let rev_produced_p = s.apply(&reverse, &[produced_p]);
    let goal_neg = s.neq(result_p, rev_produced_p);
    s.assert_term(goal_neg);

    let res = s.check_sat().into_inner();
    assert!(
        !res.is_sat(),
        "R4 fixpoint axiom + contradicting ground facts is UNSAT (z3: unsat); \
         Sat would be a wrong verdict, got {res:?}"
    );
}
