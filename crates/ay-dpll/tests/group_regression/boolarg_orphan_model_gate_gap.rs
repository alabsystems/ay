// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Executable spec for #boolarg-orphan: a COMPLETENESS defect in which the
//! Boolean-argument purification pass orphans the very terms the independent
//! model gate is asked about.
//!
//! MECHANISM. `purify_bool_args` (crates/ay-dpll/src/executor/purify_bool_args.rs)
//! rewrites `f(<compound Bool>)` to `f(boolarg_k)` and appends
//! `(= boolarg_k <compound Bool>)`. The substitution is applied to
//! `ctx.assertions` in place, so the solver only ever registers the REWRITTEN
//! terms — they are the only ones a model pins. `check_sat` then RESTORES the
//! original assertions on exit, and the independent model gate evaluates THOSE.
//! Every enclosing application it meets (`(mem (bool (or p q)) S)`) is a term
//! that appeared in no assertion the solver saw: no SAT literal, no EUF class,
//! and no function-table row can match it (its argument key degrades to the
//! opaque `@?id` of the orphaned `(bool (or p q))`, while the row's key resolves
//! to the twin's committed element). The gate correctly fails closed with
//!
//!   "model commits no value for this application of `mem`"
//!
//! and a satisfiable input is answered `unknown`.
//!
//! THE GATE IS NOT AT FAULT. A model that pins no value for an application is
//! not evidence, and no assertion here is ever refuted (`n_false=0`). The
//! producer is at fault: the purification pass decided a value for the twin and
//! never published it under the id its consumers ask about.
//!
//! GROUND TRUTH NEEDS NO ORACLE. `mem` and `bool` are uninterpreted and
//! constrained by nothing else, so interpreting `mem` as constantly false
//! satisfies every fixture below; the negated ones are satisfied by the constant
//! `true`. z3 4.15.4 independently answers `sat` on all of them. `unknown` is a
//! sound incompleteness — which is exactly why it went unnoticed — but it is a
//! lost answer on every B-method / CLEARSY proof obligation of this shape, the
//! family `purify_bool_args` was written for in the first place.
//!
//! NARROWNESS PINS. Each `..._control` case differs from its paired defect case
//! in exactly the ingredient that triggers purification, and was `sat` even
//! before the fix. They are what proves the defect is the purification rewrite
//! and not "nested applications" or "Bool-sorted UF predicates" in general.

/// A compound Boolean argument under a UF, itself the argument of another UF.
/// The defect case: `(bool (or p q))` is purified away, orphaning the enclosing
/// `mem` application.
const ORPHANED_OUTER_APP: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun bool (Bool) U)
(declare-fun mem (U U) Bool)
(declare-fun S () U)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (mem (bool (or p q)) S)))
(check-sat)
"#;

/// Same shape with the compound argument hoisted BY HAND into a plain Bool
/// variable — precisely what purification does, except the proxy is authored, so
/// no rewrite happens and nothing is orphaned.
const MANUAL_PROXY_CONTROL: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun bool (Bool) U)
(declare-fun mem (U U) Bool)
(declare-fun S () U)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (= r (or p q)))
(assert (not (mem (bool r) S)))
(check-sat)
"#;

/// A nested UF application as an argument, with NO Boolean argument anywhere.
/// Proves the gate handles application-valued arguments fine when the
/// application is one the solver actually registered.
const NESTED_APP_ARG_CONTROL: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun h (U) U)
(declare-fun mem (U U) Bool)
(declare-fun S () U)
(assert (not (mem (h S) S)))
(check-sat)
"#;

/// The defect is independent of the outer application's RESULT sort: an
/// Int-returning outer UF loses its answer the same way, which rules out the
/// Bool SAT-literal fallback being the whole story.
const ORPHANED_OUTER_APP_INT_RESULT: &str = r#"
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun bool (Bool) U)
(declare-fun g (U) Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= 5 (g (bool (or p q)))))
(check-sat)
"#;

/// Same, with a plain Bool VARIABLE argument — `needs_proxy` deliberately skips
/// it, so no purification and no orphan.
const PLAIN_BOOL_VAR_ARG_CONTROL: &str = r#"
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun bool (Bool) U)
(declare-fun g (U) Int)
(declare-fun p () Bool)
(assert (= 5 (g (bool p))))
(check-sat)
"#;

/// A refutation over the SAME orphaning shape. Purification must keep doing its
/// job: this is the congruence the pass exists to restore, and no completeness
/// repair may be bought by weakening it.
const CONTRADICTION_STILL_REFUTED: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun bool (Bool) U)
(declare-fun mem (U U) Bool)
(declare-fun S () U)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (mem (bool (or p q)) S)))
(assert (mem (bool (or p q)) S))
(check-sat)
"#;

fn solve_one(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 1, "fixture has exactly one check-sat");
    outputs[0].clone()
}

/// THE spec. Satisfiable, and the model gate must be able to CONFIRM it on its
/// own unchanged terms.
#[test]
fn purified_bool_arg_does_not_orphan_the_enclosing_application() {
    assert_eq!(
        solve_one(ORPHANED_OUTER_APP),
        "sat",
        "LOST ANSWER (#boolarg-orphan): `mem` and `bool` are uninterpreted and \
         otherwise unconstrained, so interpreting `mem` as constantly false is a \
         model (z3 agrees: sat). `unknown` here means the model gate was asked \
         about `(mem (bool (or p q)) S)` — a term `purify_bool_args` rewrote out \
         of every assertion the solver saw — and correctly found no committed \
         value for it. Do NOT fix this by relaxing the gate; publish the value \
         the solve already decided for the rewritten twin."
    );
    assert_eq!(
        solve_one(ORPHANED_OUTER_APP_INT_RESULT),
        "sat",
        "LOST ANSWER (#boolarg-orphan), Int-returning outer application"
    );
}

/// Narrowness: every control is `sat` with or without the repair. If one of
/// these ever goes red the diagnosis above is wrong — the defect would not be
/// the purification rewrite.
#[test]
fn controls_isolate_the_purification_rewrite() {
    assert_eq!(
        solve_one(MANUAL_PROXY_CONTROL),
        "sat",
        "an AUTHORED proxy is the same formula purification produces; if this \
         is not sat the defect is not the rewrite"
    );
    assert_eq!(
        solve_one(NESTED_APP_ARG_CONTROL),
        "sat",
        "an application-valued argument the solver registered must evaluate; if \
         this is not sat the defect is not orphaning"
    );
    assert_eq!(
        solve_one(PLAIN_BOOL_VAR_ARG_CONTROL),
        "sat",
        "a plain Bool VARIABLE argument is never purified"
    );
}

/// Soundness pin: the completeness repair must not cost the congruence
/// `purify_bool_args` exists to provide.
#[test]
fn orphaning_shape_is_still_refuted_when_contradictory() {
    assert_eq!(
        solve_one(CONTRADICTION_STILL_REFUTED),
        "unsat",
        "`(mem X S)` and `(not (mem X S))` for the SAME X is a contradiction \
         only congruence over the purified Bool argument exposes — the exact \
         property the pass was written for"
    );
}
