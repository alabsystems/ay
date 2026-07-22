// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! DT+BV selector-over-ite regressions (#multi-hop-flattened-option).
//!
//! The combined DT+BV/DT+Array routes (`DtUfbv`/`DtAufbv` ->
//! `solve_with_dt_axioms`) did not Shannon-lift non-Bool ITEs, so
//! `(sel (ite g A B))` reached the eager bit-blast core as an unconstrained
//! UF: the SAT core invented a spurious model, the strict `ite_uf_definition`
//! oracle rejected it, and the deepening loop fixpointed to
//! unknown-incomplete — and on the free-DT-vars variant the validation
//! evaluator could not concretize, so ay returned an outright WRONG `sat`
//! on an UNSAT instance (a bogus counterexample surface for model-checker-consumer).
//!
//! The fix lifts ITEs in `solve_with_dt_axioms` exactly as `solve_dt` does
//! (`lift_arithmetic_ite_all`, #5082). These pins keep both directions
//! honest: `sat` on the UNSAT instances is a SOUNDNESS bug; `unknown` is a
//! completeness regression; and the genuinely-satisfiable control must never
//! flip to `unsat`.
//!
//! Extracted from the ay-pb `eval_lit` whole-function VC
//! (`(value_Option_u32 (ite .. (Some_Option_u32 ..) None_Option_u32))`).

use ntest::timeout;

const OPTION_U32: &str = "(declare-datatype Option_u32 ((None_Option_u32) \
     (Some_Option_u32 (value_Option_u32 (_ BitVec 32)))))";

/// Selector over a DT-sorted ite with the guard asserted true: UNSAT.
/// Pre-fix: unknown (:reason-unknown incomplete).
#[test]
#[timeout(60_000)]
fn selector_over_dt_ite_proves_unsat() {
    let smt = format!(
        "(set-logic ALL)\n{OPTION_U32}\n\
         (declare-const c Bool)\n\
         (declare-const x (_ BitVec 32))\n\
         (declare-const y (_ BitVec 32))\n\
         (assert (= y (value_Option_u32 (ite c (Some_Option_u32 x) (as None_Option_u32 Option_u32)))))\n\
         (assert c)\n\
         (assert (not (= y x)))\n\
         (check-sat)\n"
    );
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "selector-over-DT-ite with true guard must prove UNSAT (sat = SOUNDNESS bug, \
         unknown = the pre-fix incompleteness)"
    );
}

/// Free-DT-vars variant that ay previously answered `sat` on (WRONG — z3
/// proves UNSAT; the returned model violated the instance's own asserts).
/// The hard bar is never-sat; the fixed solver proves UNSAT.
#[test]
#[timeout(60_000)]
fn guarded_dt_ite_free_vars_never_spuriously_sat() {
    let smt = format!(
        "(set-logic ALL)\n{OPTION_U32}\n\
         (declare-const c Bool)\n\
         (declare-const a Option_u32)\n\
         (declare-const b Option_u32)\n\
         (declare-const y (_ BitVec 32))\n\
         (assert (= y (value_Option_u32 (ite c a b))))\n\
         (assert (= a (Some_Option_u32 #x00000005)))\n\
         (assert c)\n\
         (assert (not (= y #x00000005)))\n\
         (check-sat)\n"
    );
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "free-DT-var guarded ite instance is UNSAT (z3-confirmed); `sat` here is the \
         bogus-counterexample soundness bug, `unknown` a completeness regression"
    );
}

/// BV8 payload variant of the same shape: UNSAT. Pre-fix: unknown.
#[test]
#[timeout(60_000)]
fn selector_over_dt_ite_bv8_proves_unsat() {
    let smt = "(set-logic ALL)\n\
         (declare-datatype Opt8 ((None8) (Some8 (val8 (_ BitVec 8)))))\n\
         (declare-const c Bool)\n\
         (declare-const x (_ BitVec 8))\n\
         (declare-const y (_ BitVec 8))\n\
         (assert (= y (val8 (ite c (Some8 x) (as None8 Opt8)))))\n\
         (assert c)\n\
         (assert (not (= y x)))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// Genuinely-satisfiable control: guard asserted FALSE, so `y` is a
/// selector applied to `None` — an unconstrained UF value that may differ
/// from `x`. The lift must never turn this into a false UNSAT; a sound
/// fail-closed `unknown` is acceptable, `unsat` is not.
#[test]
#[timeout(60_000)]
fn selector_over_dt_ite_false_guard_stays_satisfiable() {
    let smt = format!(
        "(set-logic ALL)\n{OPTION_U32}\n\
         (declare-const c Bool)\n\
         (declare-const x (_ BitVec 32))\n\
         (declare-const y (_ BitVec 32))\n\
         (assert (= y (value_Option_u32 (ite c (Some_Option_u32 x) (as None_Option_u32 Option_u32)))))\n\
         (assert (not c))\n\
         (assert (not (= y x)))\n\
         (check-sat)\n"
    );
    let result = crate::common::solve(&smt);
    assert_ne!(
        result.trim(),
        "unsat",
        "false-guard control is satisfiable; a lift-induced false UNSAT is a soundness bug"
    );
}
