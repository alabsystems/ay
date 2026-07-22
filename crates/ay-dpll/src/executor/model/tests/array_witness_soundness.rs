// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #arr-neg-default: the EMITTED array witness must satisfy the formula
//! whenever `check-sat` answers `sat` (differential-fuzz `arrays` seed 179).
//!
//! ROOT CAUSE — a base array whose reconstructed interpretation default was a
//! NEGATIVE literal rendered as the s-expr `(- 5)` failed to resolve during
//! `select` evaluation: the reconstructed interpretation carries no
//! `index_sort`/`element_sort`, and the sort-unknown branch of
//! `parse_model_value_string` only read BARE integers. The dropped default let
//! the `#6191` don't-care LIA `select` fallback ship as the array's value at a
//! store-missed index — a phantom store `A0[-6] = -1` that falsifies the
//! implication. The reached scalar assignment IS satisfiable (`A0 = const(-5)`
//! witnesses it), so the honest answer is a VALID `sat` model, not `unknown`.
//! Fixed by making the sort-unknown value parse read `(- n)` / rationals too.
//!
//! These tests pin the value-parse fix and the end-to-end invariant: a `sat`
//! answer implies the independent model-check gate CONCRETELY confirms the
//! emitted witness (a semantic re-evaluation of the emitted model), and every
//! ground assertion re-evaluates to `true` under it.

use super::*;
use ay_frontend::parse;
use ay_model_check::GateVerdict;

/// The differential-fuzz `arrays` seed-179 formula (z3 `sexpr` rendering). Its
/// A0 witness pre-fix was `(store ((as const ...) (- 5)) (- 6) (- 1))` — an
/// invalid model (the phantom `A0[-6] = -1` falsifies the implication). The
/// only sound witness for the reached assignment reads the `-5` default at the
/// store-missed index.
const SEED_179: &str = r#"
(declare-fun i3 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun b0 () Bool)
(declare-fun i0 () Int)
(declare-fun A1 () (Array Int Int))
(declare-fun A0 () (Array Int Int))
(assert (let ((a!1 (distinct (select (store (store A0 i0 0) (- i1 1) (- 5))
                             (- (ite b0 i2 6)))
                     (- (- i1) i3)))
      (a!2 (ite (> (ite b0 (- i1 i1) (- i1 i2)) i1) (+ 2 (- 6)) (- i3))))
(let ((a!3 (distinct (select A1 1)
                     (select (store (store A1 (- 1) (- 5)) (+ i0 i3) (- (- 3)))
                             a!2))))
  (=> a!1 a!3))))
(check-sat)
"#;

/// Solve `input` through the full executor pipeline (independent gate included).
fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

/// SOUNDNESS INVARIANT — whenever `check-sat` answers `sat`, the emitted witness
/// must satisfy the formula. We re-establish that TWO independent ways:
///   * the independent model-check gate must `ConfirmedSat` — it ground-composes
///     every assertion over the model's array interpretation with its OWN
///     (solver-independent) evaluator; and
///   * no ground assertion re-evaluates to `false` under the model.
/// A `sat` with an unconfirmable or refuted witness is exactly the shipped-lie
/// this guards against; `unknown` (honest incapacity) is always acceptable.
fn assert_sat_implies_valid_emitted_witness(exec: &Executor, verdict: &str) {
    if verdict != "sat" {
        return; // unknown / unsat — nothing emitted to validate.
    }
    // 1. Independent gate: a concrete confirmation of the emitted witness.
    match exec.confirm_sat_with_independent_gate() {
        GateVerdict::ConfirmedSat => {}
        GateVerdict::ModelViolates { assertion } => panic!(
            "sat shipped an INVALID model: the independent gate ground-refuted \
             assertion {assertion:?} under the emitted witness"
        ),
        GateVerdict::CannotConfirm { reason } => panic!(
            "sat shipped a model the independent gate could not concretely \
             confirm ({reason}); the emitted array witness must be ground-checkable"
        ),
    }

    // 2. Belt-and-suspenders: re-evaluate every ground assertion under the model.
    let model = exec.last_model.as_ref().expect("sat retains its model");
    eval_memo_clear();
    for &assertion in &exec.ctx.assertions {
        let v = exec.evaluate_term(model, assertion);
        assert!(
            !matches!(v, EvalValue::Bool(false)),
            "sat shipped a model that falsifies a ground assertion (got {v:?})"
        );
    }
}

/// #arr-neg-default (root cause): the sort-unknown value parse must read the
/// SMT-LIB negated literal `(- n)`, not only bare integers. Reconstructed array
/// interpretations carry no element sort, so a NEGATIVE default reaches this
/// path; before the fix it returned `Unknown`, dropping the default and letting
/// a don't-care LIA `select` value ship as the array's value.
#[test]
fn sort_unknown_value_parse_reads_negative_literal() {
    let exec = Executor::new();
    assert_eq!(
        exec.parse_model_value_string("(- 5)", &None),
        EvalValue::Rational(BigRational::from(BigInt::from(-5))),
        "sort-unknown parse of the negated literal (- 5) must be -5, not Unknown"
    );
    assert_eq!(
        exec.parse_model_value_string("7", &None),
        EvalValue::Rational(BigRational::from(BigInt::from(7))),
        "a bare integer must still parse under an unknown sort"
    );
    assert_eq!(
        exec.parse_model_value_string("(- 0)", &None),
        EvalValue::Rational(BigRational::from(BigInt::from(0))),
    );
    // A genuinely non-numeric token stays Unknown (an uninterpreted element).
    assert!(matches!(
        exec.parse_model_value_string("u!3", &None),
        EvalValue::Unknown
    ));
}

/// arrays seed 179: the primary bug. The reached assignment IS satisfiable
/// (const arrays witness it), so AY must answer `sat` with a VALID emitted
/// model — the independent gate concretely confirms the emitted array witness.
/// Pre-fix the FFI route shipped `sat` with the invalid `A0[-6] = -1` phantom.
#[test]
fn arrays_seed_179_emits_a_valid_model() {
    let (exec, verdict) = solve(SEED_179);
    assert_eq!(
        verdict, "sat",
        "the seed-179 assignment is satisfiable (const arrays witness it); \
         AY must not lazily answer unknown"
    );
    assert_sat_implies_valid_emitted_witness(&exec, &verdict);
}

/// SOUNDNESS INVARIANT (weaker than [`assert_sat_implies_valid_emitted_witness`],
/// for a FREE array read): a `sat` witness may not be *gate-confirmable* when a
/// read hits a truly-unconstrained array that carries no reconstructed
/// interpretation — the independent gate then honestly `CannotConfirm`, which is
/// acceptable. What is NOT acceptable, and what this pins, is shipping a `sat`
/// whose model AY's OWN evaluator refutes (or that the gate ground-*refutes*).
fn assert_sat_never_ships_self_refuted_model(exec: &Executor, verdict: &str) {
    if verdict != "sat" {
        return;
    }
    // The gate may CannotConfirm a free array read, but it must never REFUTE.
    if let GateVerdict::ModelViolates { assertion } = exec.confirm_sat_with_independent_gate() {
        panic!(
            "sat shipped an INVALID model: the independent gate ground-refuted \
             assertion {assertion:?} under the emitted witness"
        );
    }
    // Core invariant: AY's own evaluator must not refute the emitted model.
    let model = exec.last_model.as_ref().expect("sat retains its model");
    eval_memo_clear();
    for &assertion in &exec.ctx.assertions {
        let v = exec.evaluate_term(model, assertion);
        assert!(
            !matches!(v, EvalValue::Bool(false)),
            "sat shipped a model AY's own eval refutes (assertion -> {v:?})"
        );
    }
}

/// #arr-lia-subst-select-recover (arr_lia seed 5397, minimized): a substituted
/// integer variable whose defining RHS READS a free array — `i2 -> (+ (select A1
/// 1) 3)` — must recover to a value CONSISTENT with the emitted array. Pre-fix,
/// model recovery could not evaluate the opaque `select` (LIA modelled it as a
/// fresh variable with no listed value), so `i2` fell through to the
/// unconstrained-constant default (0) INDEPENDENTLY of the emitted `A1`
/// (`const-array 0`): AY shipped `sat` with `(select A1 1) + 3 = 3 != 0 = i2`, a
/// witness its OWN evaluator refutes. The read is now seeded with the array's
/// canonical default (0) — the SAME value the emitted array yields for an
/// unconstrained entry, and the same seed flows into array-model extraction — so
/// `i2` recovers to 3 and the model satisfies the formula. z3 confirms `sat`.
#[test]
fn arr_lia_substituted_free_array_read_emits_valid_model() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun i2 () Int)
        (declare-fun A1 () (Array Int Int))
        (assert (= (+ (select A1 1) 3) i2))
        (check-sat)
    "#;
    let (exec, verdict) = solve(input);
    assert_eq!(
        verdict, "sat",
        "the read is unconstrained; a valid witness exists (z3: i2 = 3)"
    );
    assert_sat_never_ships_self_refuted_model(&exec, &verdict);
}

/// The full arr_lia seed-5397 formula (z3 `sexpr` rendering): a select over a
/// free array `A1` wrapped in linear arithmetic and equated to a bare Int `i2`,
/// alongside an independent `A0` read. Pre-fix AY shipped `sat` with `i2 = 0`,
/// which its own eval refutes (`(select A1 (1+i1)) + 3 = 3 != 0`). Post-fix `i2`
/// recovers consistently and the emitted model satisfies the formula.
#[test]
fn arr_lia_seed_5397_emits_a_valid_model() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun i2 () Int)
        (declare-fun i1 () Int)
        (declare-fun A1 () (Array Int Int))
        (declare-fun i0 () Int)
        (declare-fun A0 () (Array Int Int))
        (assert (let ((a!1 (+ (select A0 (* (- 3) (- i0 5))) i1))
              (a!2 (= (+ (select A1 (+ 1 i1)) (- (- 3))) i2)))
          (and (< a!1 i1) a!2)))
        (check-sat)
    "#;
    let (exec, verdict) = solve(input);
    assert_eq!(
        verdict, "sat",
        "seed-5397 is satisfiable (const arrays witness it)"
    );
    assert_sat_never_ships_self_refuted_model(&exec, &verdict);
}
