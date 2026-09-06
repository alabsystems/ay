// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bool-range, BitVec-index arrays (`(Array (_ BitVec n) Bool)`) under QF_ABV
//! and QF_AUFBV.
//!
//! A Bool-element `select` has no bit-blasted term bits — its value is a single
//! atom literal. The post-SAT array functional-consistency audit used to treat
//! that missing bit vector as an incomplete audit and fail every satisfiable
//! instance with two such reads closed to `unknown` (`(:reason-unknown
//! incomplete)`), while z3 answered `sat` instantly. These tests pin the
//! verdicts on both sides of the fix and the model/value output they unlock.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

/// The original reproducer (benchmarks/smt/array_bv_simple.smt2): two reads at
/// distinct constant indices are trivially satisfiable.
#[test]
fn test_qf_abv_bool_range_const_index_reads_sat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (assert (select a #x00000000))
        (assert (not (select a #x00000001)))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["sat"]);
}

/// Contradicting reads at the SAME symbolic index are unsat — the atoms of the
/// two Bool selects must be tied together, not left as free SAT variables.
#[test]
fn test_qf_abv_bool_range_same_symbolic_index_unsat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (select a i))
        (assert (not (select a i)))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);

    // Indices forced equal by a BV constraint, not syntactically.
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (declare-fun j () (_ BitVec 32))
        (assert (= i j))
        (assert (select a i))
        (assert (not (select a j)))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);
}

/// Reads at `i` and `i + 1` may differ; the audit must read the Bool atoms and
/// compare their concrete index values instead of failing closed.
#[test]
fn test_qf_abv_bool_range_symbolic_offset_reads_sat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (select a i))
        (assert (not (select a (bvadd i #x00000001))))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["sat"]);
}

/// `store`/`select` on a Bool range: read-back at the stored index (ROW1) and
/// pass-through at a different index (ROW2), each on both sides of the verdict.
#[test]
fn test_qf_abv_bool_range_store_select() {
    let readback_sat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (declare-fun b () Bool)
        (assert (= (select (store a i b) i) b))
        (assert (select (store a i true) i))
        (check-sat)
    "#;
    assert_eq!(run(readback_sat), vec!["sat"]);

    let readback_unsat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (not (select (store a i true) i)))
        (check-sat)
    "#;
    assert_eq!(run(readback_unsat), vec!["unsat"]);

    let row2_unsat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (declare-fun j () (_ BitVec 32))
        (assert (not (= i j)))
        (assert (select a j))
        (assert (not (select (store a i false) j)))
        (check-sat)
    "#;
    assert_eq!(run(row2_unsat), vec!["unsat"]);
}

/// Extensionality: equal arrays cannot differ at an index, and a store that
/// flips one cell makes the arrays unequal.
#[test]
fn test_qf_abv_bool_range_extensionality() {
    let differ_unsat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun b () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (= a b))
        (assert (select a i))
        (assert (not (select b i)))
        (check-sat)
    "#;
    assert_eq!(run(differ_unsat), vec!["unsat"]);

    let store_unequal_sat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (not (select a i)))
        (assert (not (= a (store a i true))))
        (check-sat)
    "#;
    assert_eq!(run(store_unequal_sat), vec!["sat"]);
}

/// Constant Bool arrays: a read from `(as const ...) true` is true everywhere,
/// and a single store over `(as const ...) false` pins the only true index.
#[test]
fn test_qf_abv_bool_range_const_array() {
    let const_unsat = r#"
        (set-logic QF_ABV)
        (declare-fun i () (_ BitVec 32))
        (assert (not (select ((as const (Array (_ BitVec 32) Bool)) true) i)))
        (check-sat)
    "#;
    assert_eq!(run(const_unsat), vec!["unsat"]);

    let const_store_sat = r#"
        (set-logic QF_ABV)
        (declare-fun i () (_ BitVec 32))
        (declare-fun j () (_ BitVec 32))
        (declare-fun c () (Array (_ BitVec 32) Bool))
        (assert (= c (store ((as const (Array (_ BitVec 32) Bool)) false) i true)))
        (assert (select c j))
        (assert (not (= i #x00000007)))
        (check-sat)
        (get-value ((= i j)))
    "#;
    let outputs = run(const_store_sat);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "(((= i j) true))");
}

/// `(get-model)` / `(get-value)` round trip: the printed definitions re-assert
/// to `sat` on top of the original constraints, and they PIN the reads — the
/// negated conjunction of the assertions is unsat under the printed model.
#[test]
fn test_qf_abv_bool_range_get_model_round_trip() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 32) Bool))
        (declare-fun i () (_ BitVec 32))
        (assert (select a #x00000000))
        (assert (not (select a #x00000001)))
        (assert (select a i))
        (assert (not (select a (bvadd i #x00000001))))
        (check-sat)
        (get-value ((select a #x00000000) (select a #x00000001)))
        (get-model)
    "#;
    let outputs = run(input);
    assert_eq!(outputs[0], "sat");
    assert_eq!(
        outputs[1],
        "(((select a #x00000000) true) ((select a #x00000001) false))"
    );
    let model = outputs[2].trim();
    // `(model <definitions>)`: keep only the define-funs.
    let definitions = model
        .strip_prefix('(')
        .and_then(|body| body.strip_suffix(')'))
        .map(|body| body.trim_start())
        .and_then(|body| body.strip_prefix("model"))
        .unwrap_or_else(|| panic!("unexpected get-model shape: {model}"));
    assert!(
        definitions.contains("(define-fun a ()"),
        "model must define the Bool-range array: {model}"
    );

    let assertions = r#"
        (assert (select a #x00000000))
        (assert (not (select a #x00000001)))
        (assert (select a i))
        (assert (not (select a (bvadd i #x00000001))))
    "#;
    let round_trip = format!("(set-logic QF_ABV)\n{definitions}\n{assertions}\n(check-sat)");
    assert_eq!(run(&round_trip), vec!["sat"], "printed model: {model}");

    let pinned = format!(
        "(set-logic QF_ABV)\n{definitions}\n(assert (not (and (select a #x00000000) \
         (not (select a #x00000001)) (select a i) (not (select a (bvadd i #x00000001))))))\n\
         (check-sat)"
    );
    assert_eq!(run(&pinned), vec!["unsat"], "printed model: {model}");
}

/// QF_AUFBV: an uninterpreted function computes the index. Congruence must
/// reach the Bool reads (unsat when the arguments are equal) without
/// over-constraining distinct reads (sat otherwise).
#[test]
fn test_qf_aufbv_bool_range_uf_index() {
    let congruent_unsat = r#"
        (set-logic QF_AUFBV)
        (declare-fun a () (Array (_ BitVec 8) Bool))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun i () (_ BitVec 8))
        (declare-fun j () (_ BitVec 8))
        (assert (= i j))
        (assert (select a (f i)))
        (assert (not (select a (f j))))
        (check-sat)
    "#;
    assert_eq!(run(congruent_unsat), vec!["unsat"]);

    let mixed_sat = r#"
        (set-logic QF_AUFBV)
        (declare-fun a () (Array (_ BitVec 8) Bool))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun i () (_ BitVec 8))
        (assert (select a #x00))
        (assert (select a #x01))
        (assert (not (select a #x02)))
        (assert (not (select a (f i))))
        (assert (= (f i) (f #x00)))
        (check-sat)
    "#;
    assert_eq!(run(mixed_sat), vec!["sat"]);
}

/// A Bool select steering a BV `ite` is registered by the bit-blaster, not the
/// Boolean skeleton; the audit must find that atom too.
#[test]
fn test_qf_abv_bool_range_ite_on_select() {
    let sat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) Bool))
        (declare-fun i () (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (assert (= x (ite (select a i) #x10 #x20)))
        (assert (= x #x20))
        (assert (select a (bvadd i #x01)))
        (check-sat)
    "#;
    assert_eq!(run(sat), vec!["sat"]);

    let unsat = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) Bool))
        (declare-fun i () (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (assert (= x (ite (select a i) #x10 #x20)))
        (assert (= x #x20))
        (assert (select a i))
        (check-sat)
    "#;
    assert_eq!(run(unsat), vec!["unsat"]);
}
