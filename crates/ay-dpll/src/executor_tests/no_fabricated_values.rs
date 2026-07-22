// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #no-fabricated-model-values: the removal of the
//! print-time fabrication machine (`format_value`) that invented sort defaults
//! for ANY value the evaluator could not determine, directly into user-visible
//! `(get-model)` / `(get-value)` output.
//!
//! After the fix:
//! * A variable UNCONSTRAINED by the formula is completed IN THE MODEL before
//!   the outer validation gates run (model/completion.rs), so the printers
//!   only read values that exist in the gate-checked model.
//! * A constrained variable the solver left unpinned (a model gap) is
//!   completed as a GATE-VERIFIED candidate: derived from its defining
//!   equality where possible, defaulted otherwise, and RETRACTED if the
//!   strict oracles or the independent gate refute the completed model.
//! * A `(get-value)` read of a UF application at an argument point its table
//!   does not list answers the printed `define-fun`'s ELSE branch, never a
//!   fabricated sort default that contradicts the printed model.
//! * A genuinely missing value is an explicit `(error ...)` — never a lie.
//! * Total datatype model construction (model/dt_construct.rs,
//!   #dt-total-model) is PRINCIPLED COMPLETION, not fabrication: a genuinely
//!   FREE datatype leaf receives a well-founded default constructor value —
//!   the standard model-completion move every SMT solver makes for
//!   unconstrained variables — committed into the model BEFORE every
//!   validation gate runs, so the gates and printers read one identical total
//!   assignment. An UNDERDETERMINED-BUT-CONSTRAINED term never gets a guessed
//!   value: all committed sources must agree (else construction fails closed
//!   and the class stays unpinned), a cyclic constraint chain fails the
//!   occurs-check (no value, verdict degrades to unknown), and the full
//!   validation pipeline re-evaluates every assertion under the constructed
//!   assignment, so a wrong candidate can never ship as `sat`.

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    (exec, outputs)
}

/// Unconstrained declared constants of every completable sort print their
/// canonical completion default — values that now EXIST in the model rather
/// than being fabricated at print time.
#[test]
#[timeout(30000)]
fn unconstrained_constants_complete_in_model_and_print_defaults() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-const p Bool)
        (declare-const x Int)
        (declare-const r Real)
        (declare-const s String)
        (assert true)
        (check-sat)
        (get-model)
        (get-value (p x r s))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(model.contains("(define-fun p () Bool false)"), "{model}");
    assert!(model.contains("(define-fun x () Int 0)"), "{model}");
    assert!(model.contains("(define-fun r () Real 0.0)"), "{model}");
    assert!(model.contains("(define-fun s () String \"\")"), "{model}");
    assert_eq!(outputs[2], r#"((p false) (x 0) (r 0.0) (s ""))"#);
}

/// Trivially-satisfiable declared arrays are completed in `ArrayModel`, not by
/// a last-minute printer fallback.  Both whole-model and get-value output must
/// consume that same committed const-array value.
#[test]
#[timeout(30000)]
fn unconstrained_declared_array_completes_in_model_and_prints() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (assert true)
        (check-sat)
        (get-model)
        (get-value (a))
    "#);
    assert_eq!(outputs[0], "sat");
    let expected = "((as const (Array Int Int)) 0)";
    assert!(outputs[1].contains(expected), "{}", outputs[1]);
    assert!(outputs[2].contains(expected), "{}", outputs[2]);
}

/// An unconstrained constant alongside a real constraint: the constrained
/// value is the solver's, the unconstrained one is the completion default,
/// and both live in the same validated model.
#[test]
#[timeout(30000)]
fn unused_constant_beside_constraint_gets_completion_default() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 5))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(define-fun x () Int 5)"),
        "{}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("(define-fun y () Int 0)"),
        "{}",
        outputs[1]
    );
}

/// QF_AX model-gap completion (the shape that used to be silently fabricated):
/// `i` and `v` live only in the array constraint and the array solver records
/// no value for them. They must be completed IN the model (gate-verified),
/// and the printed model must be total.
#[test]
#[timeout(30000)]
fn qf_ax_constrained_gap_variables_complete_and_print() {
    let (_exec, outputs) = run(r#"
        (set-logic QF_AX)
        (set-option :produce-models true)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select a i) v))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("define-fun i"),
        "i must have a value: {model}"
    );
    assert!(
        model.contains("define-fun v"),
        "v must have a value: {model}"
    );
    assert!(
        model.contains("define-fun a"),
        "a must have a value: {model}"
    );
    assert!(
        !model.contains("(error"),
        "a total gate-checked model must print without errors: {model}"
    );
}

/// The outer-level completion must NOT default a variable whose defining
/// equality was consumed by an inner (lowered) solve: `q` is defined by the
/// asserted `(= q (seq.unit 3))`, which the seq path substitutes away during
/// its inner solve. Defaulting `q` to the empty sequence there flipped this
/// genuinely-sat query to unknown (strict sequences oracle refutation) while
/// the fix was being developed — pin sat + the real witness.
#[test]
#[timeout(30000)]
fn seq_defining_equality_variable_is_not_defaulted_by_completion() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-const q (Seq Int))
        (declare-const w (Seq Int))
        (assert (= q (seq.unit 3)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat", "seq defining equality must stay sat");
    let model = &outputs[1];
    assert!(
        model.contains("(define-fun q () (Seq Int) (seq.unit 3))"),
        "q must print its real witness: {model}"
    );
    assert!(
        model.contains("(define-fun w () (Seq Int) (as seq.empty (Seq Int)))"),
        "unconstrained w completes to the empty sequence: {model}"
    );
}

/// `(get-value)` of a UF application at an unlisted argument point must agree
/// with the printed `define-fun`'s else branch. The former fabricator answered
/// the sort default (`0`) while `(get-model)` printed a table whose else was
/// `5` — two contradictory answers about one model.
#[test]
#[timeout(30000)]
fn get_value_of_unlisted_uf_point_matches_printed_else_branch() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 5))
        (check-sat)
        (get-model)
        (get-value ((f 1) (f 0)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(define-fun f ((x0 Int)) Int\n    5)"),
        "printed table must have else 5: {}",
        outputs[1]
    );
    assert_eq!(
        outputs[2], "(((f 1) 5) ((f 0) 5))",
        "the unlisted point must read the printed else branch, not a fabricated default"
    );
}

/// A Seq variable pinned only by `(seq.len q) = 2` / `(seq.nth q 0) = 4`: the
/// witness those constraints pin is derived INTO the model (gate-verified
/// candidate completion), its unconstrained cell completes to the element
/// default, and the printed model contains only concrete elements — never the
/// internal value-unavailable marker (a mid-fix regression printed
/// `(seq.unit (_ ay.value-unavailable seq-elem Int))` here).
#[test]
#[timeout(30000)]
fn seq_len_nth_gap_derives_concrete_witness_in_model() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-const q (Seq Int))
        (assert (= (seq.len q) 2))
        (assert (= (seq.nth q 0) 4))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("(define-fun q () (Seq Int) (seq.++ (seq.unit 4) (seq.unit 0)))"),
        "q must print the derived concrete witness: {model}"
    );
    assert!(
        !model.contains("ay.value-unavailable"),
        "the internal marker must never reach user output: {model}"
    );
}

// NOTE: the "genuinely missing value prints an explicit error" regression
// lives in `executor/model/tests/no_fabricated_output.rs` — it corrupts the
// private `last_model` synthetically, which needs module-private access.

/// Trivially-sat query paths (`last_model == None`) answer from the completed
/// default model — values exist in a model object, nothing is fabricated in
/// the printer.
#[test]
#[timeout(30000)]
fn trivially_sat_get_value_reads_completed_default_model() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-const b Bool)
        (declare-const bv (_ BitVec 12))
        (declare-const s String)
        (assert true)
        (check-sat)
        (get-value (b bv s))
    "#);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], r#"((b false) (bv #x000) (s ""))"#);
}

/// Declared arity>0 FUNCTIONS that occur in NO assertion are unconstrained: any
/// total interpretation is a valid witness, so they complete with a canonical
/// constant body — Z3 parity for `(get-model)`
/// (`(define-fun g ((x0 S)) T <default>)`) and `(get-value)`. The former
/// behavior OMITTED them from the model and errored on the read
/// (`value of (g 3) is not available`). Covers unary, multi-arg, and
/// Bool/Int/BV result sorts; the constrained constant beside them keeps the
/// solver's real value.
#[test]
#[timeout(30000)]
fn unconstrained_functions_complete_in_model_and_print_defaults() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-const x Int)
        (declare-fun g (Int) Int)
        (declare-fun h (Int Int) Int)
        (declare-fun p (Int) Bool)
        (declare-fun b (Int) (_ BitVec 8))
        (assert (= x 1))
        (check-sat)
        (get-model)
        (get-value ((g 3) (h 1 2) (p 7) (b 2)))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("(define-fun g ((x0 Int)) Int\n    0)"),
        "{model}"
    );
    assert!(
        model.contains("(define-fun h ((x0 Int) (x1 Int)) Int\n    0)"),
        "{model}"
    );
    assert!(
        model.contains("(define-fun p ((x0 Int)) Bool\n    false)"),
        "{model}"
    );
    assert!(
        model.contains("(define-fun b ((x0 Int)) (_ BitVec 8)\n    #x00)"),
        "{model}"
    );
    assert!(model.contains("(define-fun x () Int 1)"), "{model}");
    assert_eq!(
        outputs[2],
        "(((g 3) 0) ((h 1 2) 0) ((p 7) false) ((b 2) #x00))"
    );
}

/// A partially-constrained function's ELSE branch must remain the real,
/// EUF-extracted value — the unconstrained-function completion is fill-only and
/// must NEVER fabricate over `g`'s asserted point. `g` occurs in an assertion,
/// so completion skips it entirely; the printed else stays `5`.
#[test]
#[timeout(30000)]
fn partially_constrained_function_else_is_not_overwritten_by_completion() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic QF_UFLIA)
        (declare-fun g (Int) Int)
        (assert (= (g 0) 5))
        (check-sat)
        (get-model)
        (get-value ((g 0) (g 3)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(define-fun g ((x0 Int)) Int\n    5)"),
        "the asserted point pins the else branch to 5, not the completion default: {}",
        outputs[1]
    );
    assert_eq!(outputs[2], "(((g 0) 5) ((g 3) 5))");
}

/// Trivially-sat query paths (`last_model == None`) also complete unconstrained
/// FUNCTIONS: the completed default model carries their constant interpretation
/// for both `(get-model)` and `(get-value)`.
#[test]
#[timeout(30000)]
fn trivially_sat_completes_unconstrained_functions() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (declare-fun g (Int) Int)
        (assert true)
        (check-sat)
        (get-model)
        (get-value ((g 42)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(define-fun g ((x0 Int)) Int\n    0)"),
        "{}",
        outputs[1]
    );
    assert_eq!(outputs[2], "(((g 42) 0))");
}
