// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness regression: a quantified wrong-SAT must NOT pass
//! `--self-check` (#quantified-deferred-selfcheck).
//!
//! Found 2026-07-23 by a z3-differential sweep of all 72 fetched divisions:
//! 20 UFBV + 1 UFNIRA `wintersteiger fmsd13 fixpoint` benchmarks were emitted
//! as `sat` under `ay solve --self-check` while z3 4.16, cvc5, AND each file's
//! own `(set-info :status unsat)` all say UNSAT — a wrong SAT passing AY's own
//! fail-closed oracle, the same cardinal-failure class as the QF_AUFNIA
//! nested-array wrong-SAT.
//!
//! Root cause: the quantified model gate
//! (`apply_quantified_model_failclosed_gate`) confirms `sat` when every
//! quantified conjunct is Confirmed OR **Deferred**. A conjunct is `Deferred`
//! when the emitted witness prints no interpretation for its functions, so it
//! "cannot falsify" the assertion — and the gate then trusts the solver's
//! `sat`. But on quantified fragments the SOLVER is the unsound component, so
//! deferred-keeps-sat inherited its wrong `sat`. The independent evaluator
//! fails at the quantifier node itself (`eval.rs`: "quantifier is not evaluable
//! by the gate"), so the model NEVER actually verifies the universal.
//!
//! Fix: under `--self-check` (fail-closed) a Deferred quantified conjunct is
//! NOT confirmed, so the gate now degrades `sat` -> `unknown` (the self-check
//! contract emits `sat` only when EVERY authored assertion is confirmed). This
//! can only ADD unknowns to the fail-closed mode, never a wrong answer. DEFAULT
//! mode is deliberately unchanged (keeps the completeness-favoring deferred-sat
//! — default mode is documented not-sound and still answers `sat` here).
//!
//! The fixture is the verbatim `AR-fixpoint-5` benchmark (a single
//! `(assert (forall … (=> premise conclusion)))` over twelve `(_ BitVec 2501)`
//! vars; solves in ~0.2s). The only WRONG self-check verdict is `sat`;
//! `unknown` (fail-closed) or `unsat` (were AY ever to decide it) are both fine.

const WINTERSTEIGER_DEFERRED_WRONG_SAT: &str =
    include_str!("../fixtures/ufbv_wintersteiger_fixpoint_deferred_wrong_sat.smt2");

/// THE regression: under `--self-check`, this quantified UNSAT must never be
/// certified `sat`. Before the fix it was `sat` (cardinal failure); after, the
/// deferred quantified conjunct fails closed to `unknown`.
#[test]
fn ufbv_wintersteiger_fixpoint_never_selfcheck_sat() {
    let results = crate::common::solve_selfcheck_vec(WINTERSTEIGER_DEFERRED_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "quantified UFBV fixpoint check is UNSAT (z3, cvc5, and its own \
         `:status unsat` agree) — `--self-check` must NOT confirm a `sat` it \
         cannot verify (deferred quantified conjunct must fail closed to \
         unknown); got {results:?}"
    );
}
