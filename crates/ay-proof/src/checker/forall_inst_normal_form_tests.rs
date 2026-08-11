// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `forall_inst` must accept the instance the EMITTER actually builds.
//!
//! The obligation is `instance = body[vars := args]`, and the checker recomputes
//! that function itself. But "the substitution" is not one term — it is one term
//! per set of simplifications applied while rebuilding, and the emitter and the
//! checker apply DIFFERENT sets:
//!
//! | node    | emitter (`ematching::mk_app_simplified`) | checker (`TermStore::rebuild_app`) |
//! |---------|------------------------------------------|------------------------------------|
//! | `(= a b)` | `mk_eq_coerce` — folds `(= 5 5)` to `true` | `mk_eq_coerce` — same             |
//! | `(or ...)`| NO case; falls to the generic branch     | `mk_or` — folds `(or true X)` to `true` |
//!
//! So for a body containing `(or (= pushed x) (contains s x))` instantiated with
//! `pushed := 5, x := 5`, the emitter produces `(or true (contains s 5))` and the
//! checker's rebuild produces `true`. Both are correct instances; they are not
//! the same term, and the id comparison rejected the proof — publishing a correct
//! `unsat` as `unknown`.
//!
//! This is the real, dumped divergence from
//! `auflia_verification_consumer_9185_reducers` (captured with `AY_DEBUG_FORALL_INST`), not a
//! constructed one.
//!
//! The fix normalizes BOTH sides with the SAME function, `TermStore::simplify`,
//! whose contract is that every rewrite it applies is semantics-preserving. That
//! keeps the check independent — the checker still recomputes the substitution
//! from the step's own binder list and arguments, and an instance that is not the
//! substitution under either normal form is still rejected, as the rejecting
//! tests below require.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

const SEQ: &str = "SeqInt";

fn seq_sort() -> Sort {
    Sort::Uninterpreted(SEQ.to_string())
}

fn contains(terms: &mut TermStore, s: TermId, x: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq_contains"), vec![s, x], Sort::Bool)
}

fn push_back(terms: &mut TermStore, s: TermId, v: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq_push_back"), vec![s, v], seq_sort())
}

fn validate(
    terms: &TermStore,
    clause: Vec<TermId>,
    args: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule: AletheRule::ForallInst,
        clause,
        premises: vec![],
        args,
    };
    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// Build `(forall ((seq_1 SeqInt) (pushed_2 Int) (x_3 Int))
///           (= (seq_contains (seq_push_back seq_1 pushed_2) x_3)
///              (or (= pushed_2 x_3) (seq_contains seq_1 x_3))))`
/// and return `(not forall)` together with the binder vars.
fn source_forall(terms: &mut TermStore) -> TermId {
    let seq_v = terms.mk_var("seq_1", seq_sort());
    let pushed_v = terms.mk_var("pushed_2", Sort::Int);
    let x_v = terms.mk_var("x_3", Sort::Int);

    let lhs_seq = push_back(terms, seq_v, pushed_v);
    let lhs = contains(terms, lhs_seq, x_v);
    let eq_px = terms.mk_eq_coerce(pushed_v, x_v);
    let contains_sx = contains(terms, seq_v, x_v);
    let rhs = terms.mk_or(vec![eq_px, contains_sx]);
    let body = terms.mk_eq_coerce(lhs, rhs);

    terms.mk_forall(
        vec![
            ("seq_1".to_string(), seq_sort()),
            ("pushed_2".to_string(), Sort::Int),
            ("x_3".to_string(), Sort::Int),
        ],
        body,
    )
}

/// The dumped case: `pushed_2` and `x_3` both instantiate to `5`.
#[test]
fn forall_inst_accepts_the_emitters_partially_folded_instance() {
    let mut terms = TermStore::new();
    let quantified = source_forall(&mut terms);
    let not_forall = terms.mk_not(quantified);

    let s = terms.mk_var("s", seq_sort());
    let five = terms.mk_int(5.into());

    // Exactly what `subst_vars` + `mk_app_simplified` produce: `(= 5 5)` IS
    // folded (there is an `"="` case) but the enclosing `or` is NOT (there is
    // no `"or"` case), so `true` survives as a disjunct.
    let true_term = terms.true_term();
    let contains_s5 = contains(&mut terms, s, five);
    let or_unfolded = terms.mk_app(
        Symbol::named("or"),
        vec![true_term, contains_s5],
        Sort::Bool,
    );
    assert!(
        matches!(terms.get(or_unfolded), ay_core::TermData::App(..)),
        "precondition: this test needs the UNFOLDED (or true X); if mk_app \
         started folding, rebuild it another way"
    );

    let pushed_seq = push_back(&mut terms, s, five);
    let lhs = contains(&mut terms, pushed_seq, five);
    let instance = terms.mk_eq_coerce(lhs, or_unfolded);

    let conclusion = terms.mk_or(vec![not_forall, instance]);
    validate(&terms, vec![conclusion], vec![s, five, five]).expect(
        "forall_inst must accept the instance the emitter actually builds: the \
         checker's rebuild folds (or true X) to true, the emitter's does not, \
         and both are the same instance",
    );
}

/// REJECTING DIRECTION. A different constant is not the substitution under any
/// normal form.
#[test]
fn forall_inst_still_rejects_a_wrong_constant() {
    let mut terms = TermStore::new();
    let quantified = source_forall(&mut terms);
    let not_forall = terms.mk_not(quantified);

    let s = terms.mk_var("s", seq_sort());
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());

    // Instance built for `x := 6` while the step's argument list says `5`.
    let true_term = terms.true_term();
    let contains_s6 = contains(&mut terms, s, six);
    let or_unfolded = terms.mk_app(
        Symbol::named("or"),
        vec![true_term, contains_s6],
        Sort::Bool,
    );
    let pushed_seq = push_back(&mut terms, s, five);
    let lhs = contains(&mut terms, pushed_seq, six);
    let instance = terms.mk_eq_coerce(lhs, or_unfolded);

    let conclusion = terms.mk_or(vec![not_forall, instance]);
    validate(&terms, vec![conclusion], vec![s, five, five])
        .expect_err("forall_inst must reject an instance that is not the substitution");
}

/// REJECTING DIRECTION. Normalizing both sides must not let a LOGICALLY
/// unrelated instance through: `(or false X)` simplifies to `X`, which is not
/// what this substitution yields.
#[test]
fn forall_inst_still_rejects_a_dropped_disjunct() {
    let mut terms = TermStore::new();
    let quantified = source_forall(&mut terms);
    let not_forall = terms.mk_not(quantified);

    let s = terms.mk_var("s", seq_sort());
    let five = terms.mk_int(5.into());

    // `(seq_contains s 5)` alone — the `(= 5 5)` disjunct simply dropped. The
    // real substitution makes the whole disjunction `true`, so this is weaker
    // and must not be accepted.
    let contains_s5 = contains(&mut terms, s, five);
    let pushed_seq = push_back(&mut terms, s, five);
    let lhs = contains(&mut terms, pushed_seq, five);
    let instance = terms.mk_eq_coerce(lhs, contains_s5);

    let conclusion = terms.mk_or(vec![not_forall, instance]);
    validate(&terms, vec![conclusion], vec![s, five, five]).expect_err(
        "forall_inst must reject an instance that drops a disjunct the \
         substitution produces",
    );
}
