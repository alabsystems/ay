// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression: the `premise_forced_binder_refutation` ADMISSION
//! FILTER must not decline a universal it is capable of refuting.
//!
//! The sibling `ufbv_fixpoint_premise_forced_unsat` pins that the probe DERIVES
//! `unsat` once it runs. This file pins the three gates that used to stop it
//! running at all — each one sufficient on its own to turn a derivable `unsat`
//! into a wrong `sat`, because when the probe declines, the UF-completion arm
//! grants `sat` unconditionally against an emitted model that is literally
//! `(model )` and therefore cannot falsify anything.
//!
//! Found by the 2026-07-25 full-corpus scoreboard: 12 UFBV wintersteiger
//! `fmsd13 fixpoint` files answered `sat` where z3, cvc5 and each file's own
//! `(set-info :status unsat)` all say UNSAT.
//!
//! GATE B (root cause). `forall_premise_candidate` asked
//! `term_mentions_completable_uf` which `or` disjuncts were the conclusion.
//! That bottoms out in `is_mbqi_completable_uf_symbol`, a hardcoded exclusion
//! list plus `!name.starts_with("bv")`. SMT-LIB's structural bit-vector
//! operators are `concat`, `extract`, `zero_extend`, `sign_extend`,
//! `rotate_left`, `rotate_right`, `repeat` — none start with `bv`, so all were
//! misread as user UFs. A premise conjunct mentioning one was booked as
//! conclusion and discarded, its binders stayed free, the candidate solve
//! returned an arbitrary value, and the substituted body was vacuously SAT on a
//! false premise. Replaced by a semantic test: is the head a user-DECLARED
//! symbol of arity > 0.
//!
//! GATE A. Binders were restricted to `Sort::BitVec(_)`, which is stricter than
//! the stated soundness argument ("exactly materializable as a
//! model-independent literal") — `pin_eval_const_for_sort` already materializes
//! `Sort::Bool` exactly. Bool is now admitted.
//!
//! GATE C. A 100,000-term store cap excluded industrial UFBV outright.
//!
//! Widening admission cannot produce a wrong answer: the probe returns UNSAT
//! only after independently ground-solving the WHOLE substituted body at
//! concrete literals, which is a sound instance of a conjunctive-position
//! universal. It can only add decided UNSATs or waste sub-solve time.

/// GATE B: a premise pinned through a structural BV operator (`zero_extend`)
/// must still be recognised as a premise. This is the shape of
/// `small-synabs-fixpoint-2/3/9`, whose `ite` conditions read
/// `(= ((_ zero_extend 26) v) (_ bvN 32))`.
#[test]
fn premise_pinned_through_zero_extend_is_still_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun g ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a (_ BitVec 6)) (b (_ BitVec 8)))
          (=> (and (= ((_ zero_extend 2) a) #x01) (= b (bvadd ((_ zero_extend 2) a) #x01)))
              (and (= (g b) #x05) (= b (g b))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "a `zero_extend`-pinned premise must not be mistaken for the conclusion \
         and dropped, leaving a vacuous SAT; got {results:?}"
    );
}

/// GATE A: a Bool binder is exactly materializable and must be admitted.
#[test]
fn bool_binder_universal_is_admitted_and_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun h (Bool) (_ BitVec 8))
        (assert (forall ((p Bool) (v (_ BitVec 8)))
          (=> (and p (= v #x02))
              (and (= (h p) #x07) (= v (h p))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "a Bool binder must not be rejected before premise recovery is attempted; \
         got {results:?}"
    );
}

/// The soundness floor for all three gates: whatever the admission filter
/// decides, `--self-check` must never certify SAT for a false universal.
#[test]
fn selfcheck_never_certifies_sat_for_these_shapes() {
    for smt in [
        r#"
        (set-logic UFBV)
        (declare-fun g ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a (_ BitVec 6)) (b (_ BitVec 8)))
          (=> (and (= ((_ zero_extend 2) a) #x01) (= b (bvadd ((_ zero_extend 2) a) #x01)))
              (and (= (g b) #x05) (= b (g b))))))
        (check-sat)
        "#,
        r#"
        (set-logic UFBV)
        (declare-fun h (Bool) (_ BitVec 8))
        (assert (forall ((p Bool) (v (_ BitVec 8)))
          (=> (and p (= v #x02))
              (and (= (h p) #x07) (= v (h p))))))
        (check-sat)
        "#,
    ] {
        let results = crate::common::solve_selfcheck_vec(smt);
        assert!(
            !results.iter().any(|r| r == "sat"),
            "self-check may derive unsat or fail closed to unknown, never SAT; \
             got {results:?}"
        );
    }
}
