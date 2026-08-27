// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Publication coverage for the constant-`true` vacuous-quantifier collapse
//! (`simplify_vacuous_quantifiers`).
//!
//! A quantifier whose body is the constant `true` collapses to `true`. That
//! collapse is CERTIFIED (`add_vacuous_quantifier_collapse`), yet the
//! conservative `quantified_proof_translation_incomplete` marker used to be set
//! anyway, because the staged `--vacuous-marker-narrow` exemption is default
//! off. The marker's read site then demands a STRICTLY checkable proof to keep
//! a computed UNSAT; refutations in this BV fragment carry one residual `trust`
//! step, so the gate downgraded the verdict to
//! `Unknown(UnhandledQuantifier)` — and that Unknown in turn starved step (4)
//! of `discharge_trust_steps_for_certification`, whose fresh-`Executor`
//! corroboration re-solve requires an `unsat`. Net effect: a theorem AY had
//! proved was published as `unknown (incomplete self-check-rejected)`.
//!
//! The exemption is sound precisely because the collapse RESULT is `true`:
//! `true` is not a premise of anything, no proof step can cite it, and dropping
//! it changes no model — so there is no translation left to be incomplete
//! about. It is strictly narrower than `--vacuous-marker-narrow`, which exempts
//! every certified collapse including collapses onto real premises.

#![allow(clippy::panic)]

mod common;

/// Everything except the trailing conjunct list — a deductive-checks loop-invariant
/// overflow obligation (`i = i + 1` under `i < n`), reduced.
const PREFIX: &str = r"
    (set-logic ALL)
    (declare-const len Int)
    (declare-const len_pre Int)
    (declare-const v_pre (Array (_ BitVec 64) (_ BitVec 64)))
    (declare-const seed (_ BitVec 64))
    (declare-const seed_pre (_ BitVec 64))
    (declare-const i (_ BitVec 64))
    (declare-const i_pre (_ BitVec 64))
    (declare-const n (_ BitVec 64))
    (declare-const n_pre (_ BitVec 64))
    (assert (<= 0 len))
    (assert (<= len 18446744073709551615))
    (assert (<= 0 len_pre))
    (assert (<= len_pre 18446744073709551615))
    (assert (= (select v_pre #x0000000000000000) seed))
    (assert (= (select v_pre #x0000000000000000) seed_pre))
    (assert (= len_pre 5))
    (assert (= n n_pre))
    (assert (= i_pre i_pre))
";

/// `i < n` and `i + 1` wraps — unsatisfiable, since only `i = 0xFF..F` wraps
/// and that value cannot be unsigned-less-than anything.
const OVERFLOW_CONTRADICTION: &str =
    "(assert (and (bvult i n) (not (bvule i (bvadd i #x0000000000000001)))))";

/// The degenerate seq-equality axiom deductive-checks emits: a binder over a body that
/// is literally `true`.
const VACUOUS_FORALL: &str = "(assert (forall ((idx (_ BitVec 64))) true))";

fn solve(body: &str) -> Vec<String> {
    common::solve_vec(&format!("{PREFIX}{body}(check-sat)"))
}

#[test]
fn constant_true_vacuous_forall_does_not_withhold_a_computed_unsat() {
    // ACTIVE: the vacuous binder is present. This is the shape that published
    // `unknown (incomplete self-check-rejected)` before the exemption.
    let active = solve(&format!("{OVERFLOW_CONTRADICTION}{VACUOUS_FORALL}"));
    // CONTROL: byte-identical query with the vacuous conjunct deleted. It was
    // `unsat` before the fix too, so a green ACTIVE arm cannot be explained by
    // the whole family having become trivially decidable.
    let control = solve(OVERFLOW_CONTRADICTION);

    assert!(
        control.iter().any(|result| result == "unsat"),
        "control: the same obligation WITHOUT the vacuous binder must refute, \
         otherwise this test proves nothing about the binder; got {control:?}"
    );
    assert!(
        active.iter().any(|result| result == "unsat"),
        "a quantifier whose body is the constant `true` must not withhold a \
         computed refutation: `true` is not a premise, so the collapse cannot \
         make any derivation untranslatable; got {active:?} (control={control:?})"
    );
}

#[test]
fn constant_true_vacuous_forall_does_not_manufacture_a_refutation() {
    // NARROWNESS PIN, and the direction that would actually be a soundness
    // defect: with the contradiction removed the query is satisfiable, and the
    // exemption must leave it that way. A `true` conjunct constrains nothing,
    // so every model satisfies it unconditionally — dropping the marker must
    // not turn SAT into UNSAT.
    let satisfiable = solve(&format!("(assert (bvult i n)){VACUOUS_FORALL}"));
    assert!(
        satisfiable.iter().any(|result| result == "sat"),
        "the vacuous-collapse exemption must not disturb a satisfiable query; \
         got {satisfiable:?}"
    );
    assert!(
        !satisfiable.iter().any(|result| result == "unsat"),
        "the vacuous-collapse exemption must never mint a refutation; \
         got {satisfiable:?}"
    );
}
