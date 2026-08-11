// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #dt-element-canon — the independent gate must see ONE encoding per model
//! value for a nullary-constructor datatype value.
//!
//! REGRESSION ACCOUNT. The enum-SAT lane's producer `decode_enum_model`
//! (`executor/theories/euf/enum_sat.rs`) builds an `EufModel` whose elements
//! are the constructor NAMES, so a datatype-sorted UF application `(u p0)`
//! reaches the gate as `EvalValue::Element("u0")` → `Uninterpreted("u0")`,
//! while the bare constructor leaf `u0` reaches it — through
//! `nullary_constructor_leaf` — as `Datatype { ctor: "u0", args: [] }`. One
//! value, two encodings. `ay-model-check`'s `value_eq` refuses the comparison
//! ("equality between incomparable model values (Datatype vs Uninterpreted)")
//! and the gate answers `CannotConfirm`.
//!
//! Before `66538b006f` a `CannotConfirm` was recorded as an incompleteness and
//! the `sat` was kept; `66538b006f` made it downgrade `Sat` to `Unknown`. That
//! turned this latent encoding split into 107 lost `sat` answers in SQ
//! QF_Datatypes, including 100/100 of `QF_UFDT/20210312-Bouvier` — measured on
//! `vlsat3_k13.smt2`, where the probe counted 891 such refused comparisons.
//!
//! The fix normalizes the PRODUCER (`canonical_dt_element`), exactly as
//! `ay-model-check/src/lib.rs:254-260` prescribes; `value_eq` is untouched.
//!
//! `enum_uf_nullary_ctor_model_is_confirmed_sat` FAILS without that
//! normalization — verified by running this file against a second worktree at
//! the pre-fix HEAD, where the gate returns `CannotConfirm` and the verdict
//! degrades to `unknown`. The other three are adversarial controls that must
//! hold with and without it.

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

/// The Bouvier `vlsat` shape in miniature: an all-nullary "place" enum, an
/// all-nullary "unit" enum, and a UF from one to the other, constrained by
/// `or`-of-equalities against bare constructor constants and by `distinct`.
///
/// Genuinely SAT (z3 agrees). The gate must CONFIRM it, so `sat` ships.
///
/// SHAPE MATTERS — this is the SMALLEST flipping instance, found by searching
/// the (places x units x style) grid against the `AY_DT_ELEMENT_CANON` opt-out.
/// A first attempt at this test used 3 places / 2 units and pinned `(u p0)`
/// with a TOP-LEVEL `(assert (= (u p0) u0))`, and it PASSED at the pre-fix
/// HEAD: an unconditional definitional equality lets `datatype_leaf` resolve
/// the application structurally, so no opaque element token ever reaches
/// `value_eq` and there is nothing to collide. The collision needs a UF
/// application whose value comes from the enum lane's decode ALONE — here
/// `(u p0)`, which occurs only inside `(distinct (u p0) (u p3))`.
#[test]
fn enum_uf_nullary_ctor_model_is_confirmed_sat() {
    let input = r#"
        (set-logic QF_UFDT)
        (declare-datatype Place ((p0) (p1) (p2) (p3)))
        (declare-datatype Unit ((u0) (u1) (u2)))
        (declare-fun u (Place) Unit)
        (assert (or (= (u p1) u0) (= (u p1) u1)))
        (assert (or (= (u p2) u0) (= (u p2) u1) (= (u p2) u2)))
        (assert (or (= (u p3) u0) (= (u p3) u1) (= (u p3) u2)))
        (assert (distinct (u p0) (u p3)))
        (assert (distinct (u p1) (u p2)))
        (check-sat)
    "#;
    let (exec, verdict) = solve(input);
    let gate = exec.confirm_sat_with_independent_gate();
    assert_eq!(
        verdict, "sat",
        "an enum datatype + UF instance is genuinely SAT; the gate must confirm \
         the model instead of degrading it to unknown (gate: {gate:?})"
    );
    assert!(
        matches!(gate, GateVerdict::ConfirmedSat),
        "the independent gate must CONFIRM: the UF application's value and the \
         bare constructor constant it is equated to are the SAME value and must \
         reach the gate in the SAME encoding (gate: {gate:?})"
    );
}

/// ADVERSARIAL control: the same shape, but UNSATISFIABLE — three places all
/// pairwise distinct over a two-constructor `Unit` (pigeonhole). Normalizing
/// the encoding must not manufacture a `sat`.
#[test]
fn enum_uf_nullary_ctor_pigeonhole_is_never_sat() {
    let input = r#"
        (declare-datatype Place ((p0) (p1) (p2)))
        (declare-datatype Unit ((u0) (u1)))
        (declare-fun u (Place) Unit)
        (assert (distinct (u p0) (u p1)))
        (assert (distinct (u p1) (u p2)))
        (assert (distinct (u p0) (u p2)))
        (check-sat)
    "#;
    let (_exec, verdict) = solve(input);
    assert_ne!(
        verdict, "sat",
        "three pairwise-distinct values do not fit a two-constructor enum; \
         the canonical re-encoding must not turn this into a sat"
    );
}

/// ADVERSARIAL control: a constructor constant equated to a UF application that
/// an assertion also requires to DIFFER from it. Comparable values must make the
/// gate REFUTE (or the solver report unsat) — never confirm.
#[test]
fn enum_uf_contradictory_constraint_is_never_sat() {
    let input = r#"
        (declare-datatype Place ((p0) (p1)))
        (declare-datatype Unit ((u0) (u1)))
        (declare-fun u (Place) Unit)
        (assert (= (u p0) u0))
        (assert (not (= (u p0) u0)))
        (check-sat)
    "#;
    let (_exec, verdict) = solve(input);
    assert_ne!(
        verdict, "sat",
        "the assertions are directly contradictory; no encoding change may \
         produce a sat"
    );
}

/// The re-encoding must be confined to NULLARY constructors of the term's OWN
/// datatype. A datatype with FIELDS keeps its existing resolution: the gate may
/// confirm it through the structured paths, but it must never invent field
/// values for an opaque token. Genuinely SAT (z3 agrees), so the control is
/// that the verdict is not a wrong `unsat`.
#[test]
fn selector_bearing_datatype_is_unaffected() {
    let input = r#"
        (declare-datatype Box ((mk (val Int))))
        (declare-fun f (Int) Box)
        (assert (= (val (f 0)) 7))
        (assert (= (val (f 1)) 9))
        (check-sat)
    "#;
    let (_exec, verdict) = solve(input);
    assert_ne!(
        verdict, "unsat",
        "a selector-bearing datatype instance is satisfiable; the nullary-only \
         re-encoding must not disturb it"
    );
}
