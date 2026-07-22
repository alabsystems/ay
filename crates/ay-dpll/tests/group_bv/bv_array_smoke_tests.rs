// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Smoke tests for QF_ABV (solve_abv) and QF_AUFBV (solve_aufbv) logic paths.
//!
//! Part of #5466: zero test coverage for QF_ABV and QF_AUFBV.
//! Split from theory_smoke_tests.rs to stay within file size limits.

use ay_frontend::sexp::{parse_sexp, SExpr};
use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

fn get_value_binding(output: &str, name: &str) -> Option<SExpr> {
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))?;
    let parsed = parse_sexp(value_line).ok()?;
    let SExpr::List(ref bindings) = parsed else {
        return None;
    };
    for binding in bindings {
        let SExpr::List(ref items) = binding else {
            continue;
        };
        if items.len() != 2 {
            continue;
        }
        if items[0].as_symbol() == Some(name) {
            return Some(items[1].clone());
        }
    }
    None
}

fn get_value_binding_for_expr(output: &str, key_str: &str) -> Option<SExpr> {
    let expected_key = parse_sexp(key_str).ok()?;
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))?;
    let parsed = parse_sexp(value_line).ok()?;
    let SExpr::List(ref bindings) = parsed else {
        return None;
    };
    for binding in bindings {
        let SExpr::List(ref items) = binding else {
            continue;
        };
        if items.len() != 2 {
            continue;
        }
        if items[0] == expected_key {
            return Some(items[1].clone());
        }
    }
    None
}

fn sexpr_to_bv_u64(expr: &SExpr) -> Option<u64> {
    match expr {
        SExpr::Hexadecimal(h) => u64::from_str_radix(h.trim_start_matches("#x"), 16).ok(),
        SExpr::Binary(b) => u64::from_str_radix(b.trim_start_matches("#b"), 2).ok(),
        _ => None,
    }
}

// ---- ABV (QF_ABV) ----

/// Array store/select with BV indices and values: store at idx, select at idx => SAT.
/// Exercises array_axioms + materialize_array_terms in solve_bv_core.
#[test]
#[timeout(10_000)]
fn test_abv_store_select_sat() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (assert (= (select (store arr idx #x2A) idx) #x2A))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Contradictory array store/select: store 42 at idx, assert select at idx != 42.
#[test]
#[timeout(10_000)]
fn test_abv_store_select_unsat() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (assert (not (= (select (store arr idx #x2A) idx) #x2A)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// ABV model extraction: verify get-value returns correct BV values.
/// NOTE: array select model extraction returns #x00 for constrained array
/// elements (known gap, see #5454). BV variable values work correctly.
#[test]
#[timeout(10_000)]
fn test_abv_model_extraction() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (declare-const val (_ BitVec 8))
        (assert (= idx #x03))
        (assert (= val #xFF))
        (assert (= (select arr idx) val))
        (check-sat)
        (get-value (idx val))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let idx_val = get_value_binding(&output, "idx").expect("missing get-value for idx");
    assert_eq!(
        sexpr_to_bv_u64(&idx_val),
        Some(0x03),
        "expected idx = #x03, got: {idx_val:?}"
    );
    let val_binding = get_value_binding(&output, "val").expect("missing get-value for val");
    assert_eq!(
        sexpr_to_bv_u64(&val_binding),
        Some(0xFF),
        "expected val = #xFF, got: {val_binding:?}"
    );
}

/// ABV with two arrays: distinct select results at same index => SAT (arrays differ).
#[test]
#[timeout(10_000)]
fn test_abv_two_arrays_sat() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a1 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const a2 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select a1 i) #x01))
        (assert (= (select a2 i) #x02))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// ABV: contradictory select values at same index from same array => UNSAT.
#[test]
#[timeout(10_000)]
fn test_abv_contradictory_selects_unsat() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select arr i) #x01))
        (assert (= (select arr i) #x02))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- AUFBV (QF_AUFBV) ----

/// AUFBV basic SAT: array + UF + BV combination.
/// f(x) used as array index; exercises both array_axioms and euf_axioms.
#[test]
#[timeout(10_000)]
fn test_aufbv_basic_sat() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (select arr (f x)) #xAB))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// AUFBV UNSAT via UF congruence over array arguments:
/// x = y => f(x) = f(y), so select(arr, f(x)) must equal select(arr, f(y)).
#[test]
#[timeout(10_000)]
fn test_aufbv_uf_congruence_unsat() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (select arr (f x)) (select arr (f y))))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// AUFBV model extraction: verify get-value for BV variables and UF application.
/// NOTE: array select model extraction returns #x00 for constrained array
/// elements (known gap, see #5454). BV and UF model values work correctly.
#[test]
#[timeout(10_000)]
fn test_aufbv_model_extraction() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (f x) #x03))
        (assert (= (select arr (f x)) #xCD))
        (check-sat)
        (get-value (x (f x)))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing get-value for x");
    assert_eq!(
        sexpr_to_bv_u64(&x_val),
        Some(0x07),
        "expected x = #x07, got: {x_val:?}"
    );
    let fx_val = get_value_binding_for_expr(&output, "(f x)").expect("missing get-value for (f x)");
    assert_eq!(
        sexpr_to_bv_u64(&fx_val),
        Some(0x03),
        "expected f(x) = #x03, got: {fx_val:?}"
    );
}

/// AUFBV non-BV-return UF over arrays: regression for #5459.
/// When f returns a non-BV sort (U), congruence x=y => f(x)=f(y)
/// must still be enforced via non_bv_euf_axioms.
#[test]
#[timeout(10_000)]
fn test_aufbv_non_bv_return_uf_congruence_5459() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["unsat"],
        "Bug #5459: non-BV-return UF congruence must be enforced in AUFBV"
    );
}

/// AUFBV: store via UF-computed index, select back.
/// Exercises interaction between array store/select and UF evaluation.
#[test]
#[timeout(10_000)]
fn test_aufbv_store_via_uf_index_sat() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (f x) #x05))
        (assert (= (select (store arr (f x) #xBB) (f x)) #xBB))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}
