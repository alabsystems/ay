// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #free-dt-array-residual — end-to-end controls for the independent gate's
//! residual joint-satisfiability decision over FREE datatype-element arrays
//! (model-checker-consumer parity wishlist item 8, g4 "Site-3").
//!
//! Shape: arrays with datatype elements that are genuinely UNPINNED — only
//! mutually aliased `(= a b)` and element-constrained
//! `(= scalar (fld (select a i)))`. Such a model used to be unconfirmable
//! (every touching assertion `Unevaluable` ⇒ blanket `CannotConfirm`), which
//! the `#dt-array-defer-to-independent-gate` wiring turned into a degraded
//! `unknown` for a whole class of genuinely-SAT VCs. The residual decision
//! confirms exactly the jointly-satisfiable residue (no two constraints
//! forcing different values at one `(class, index, field)` slot) and refuses
//! everything else.

use super::*;
use ay_frontend::parse;
use ay_model_check::GateVerdict;

/// Solve `input` through the full executor pipeline (independent gate included).
fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

/// CONTROL (genuinely SAT): free aliased dt-element arrays + CONSISTENT
/// element reads. The residual decision must let the gate confirm, so the
/// `sat` ships instead of degrading to `unknown` (z3: sat).
#[test]
fn free_dt_array_alias_consistent_reads_is_sat() {
    let input = r#"
        (declare-datatype S ((mk (f Int) (g Int))))
        (declare-const a (Array Int S))
        (declare-const b (Array Int S))
        (assert (= a b))
        (assert (= 5 (f (select a 0))))
        (assert (= 7 (g (select b 0))))
        (assert (= 6 (f (select a 1))))
        (check-sat)
    "#;
    let (exec, verdict) = solve(input);
    let gate = exec.confirm_sat_with_independent_gate();
    assert_eq!(
        verdict, "sat",
        "free aliased dt-element arrays with consistent element reads are \
         genuinely SAT (z3 agrees); the residual gate decision must confirm \
         instead of degrading to unknown (gate: {gate:?})"
    );
    assert!(
        matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ConfirmedSat
        ),
        "the independent gate must confirm via the residual decision"
    );
}

/// ADVERSARIAL control (genuinely UNSAT): the SAME shape with CONFLICTING
/// reads at one (class, index, field) slot — `f(a[0]) = 5` vs `f(b[0]) = 6`
/// under `a = b`. The residual decision must NOT confirm; the verdict must
/// never be `sat` (unsat or unknown are both honest).
#[test]
fn free_dt_array_alias_conflicting_reads_never_sat() {
    let input = r#"
        (declare-datatype S ((mk (f Int) (g Int))))
        (declare-const a (Array Int S))
        (declare-const b (Array Int S))
        (assert (= a b))
        (assert (= 5 (f (select a 0))))
        (assert (= 6 (f (select b 0))))
        (check-sat)
    "#;
    let (exec, verdict) = solve(input);
    assert_ne!(
        verdict, "sat",
        "conflicting reads at one (class, index, field) slot are UNSAT; the \
         residual decision must never confirm them"
    );
    // Belt-and-suspenders: even if a future search path produced a candidate
    // model, the independent gate must not confirm it.
    if exec.last_model.is_some() {
        assert!(
            !matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::ConfirmedSat
            ),
            "the gate must not confirm a conflicting residual"
        );
    }
}

/// Free-array DISEQUALITY residue stays refused (hard constraint: only
/// eq-alias + element-read shapes are decided). `(not (= b c))` over free
/// arrays is satisfiable, but outside the fragment: the verdict must not
/// become a CONFIRMED sat through the residual decision. (`sat` is only
/// acceptable if some other, complete engine path decides it and the gate
/// genuinely confirms — today it does not.)
#[test]
fn free_dt_array_disequality_residue_not_confirmed_by_residual_decision() {
    let input = r#"
        (declare-datatype S ((mk (f Int) (g Int))))
        (declare-const a (Array Int S))
        (declare-const b (Array Int S))
        (declare-const c (Array Int S))
        (assert (= a b))
        (assert (not (= b c)))
        (assert (= 5 (f (select a 0))))
        (check-sat)
    "#;
    let (_exec, verdict) = solve(input);
    // The essential invariant: never a wrong verdict. z3 says sat here, so
    // unsat would be a false theorem. (A `sat` is acceptable only if a
    // complete engine path decides it — the residual decision itself refuses
    // any residue containing a disequality, which the ay-model-check unit
    // test `residual_free_dt_array_disequality_stays_unknown` pins directly.)
    assert_ne!(
        verdict, "unsat",
        "(not (= b c)) over free arrays is satisfiable — unsat would be a \
         false theorem"
    );
}
