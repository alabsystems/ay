// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gate tests for [`AlethePrinter::lower_ground_bv_disequality`].
//!
//! The lowering replaces the honest `hole` on a premise-free unit
//! `(cl (not (= C1 C2)))` over two DISTINCT closed bitvector constants with a
//! four-step `evaluate` / `equiv1` / `false` / `resolution` derivation that
//! carcara re-derives itself. Everything the gate must NOT fire on is pinned
//! here: a mislabelled step is strictly worse than the hole it replaces.

use crate::AlethePrinter;
use ay_core::ProofId;

fn lower(clause_str: &str) -> Option<String> {
    AlethePrinter::lower_ground_bv_disequality(ProofId(7), clause_str)
}

#[test]
fn ground_binary_disequality_lowers_to_the_evaluate_derivation() {
    let text = lower("(cl (not (= #b11111010 #b10011101)))").expect("distinct 8-bit constants");
    assert_eq!(
        text,
        "(step t7.ev (cl (= (= #b11111010 #b10011101) false)) :rule evaluate)\n\
         (step t7.q (cl (not (= #b11111010 #b10011101)) false) :rule equiv1 :premises (t7.ev))\n\
         (step t7.f (cl (not false)) :rule false)\n\
         (step t7 (cl (not (= #b11111010 #b10011101))) :rule resolution :premises (t7.q t7.f))"
    );
}

#[test]
fn the_final_step_reproduces_the_original_id_and_clause() {
    // Downstream `:premises` references point at the original id, so the
    // derivation MUST close on `(step t7 <original clause> ...)`.
    let clause = "(cl (not (= #b0000 #b1111)))";
    let text = lower(clause).expect("distinct 4-bit constants");
    let last = text.lines().last().expect("non-empty rendering");
    assert!(
        last.starts_with(&format!("(step t7 {clause} :rule resolution ")),
        "unexpected closing step: {last}"
    );
    // Every intermediate id is namespaced under the original one, so it cannot
    // collide with another step in the document.
    for line in text.lines().take(3) {
        assert!(line.starts_with("(step t7."), "unexpected sub-step: {line}");
    }
}

#[test]
fn ground_hex_disequality_lowers_and_is_case_insensitive() {
    assert!(lower("(cl (not (= #xf0cc #x09ec)))").is_some());
    // Same value, different spelling: NOT a disequality, must stay a hole.
    assert_eq!(lower("(cl (not (= #xABCD #xabcd)))"), None);
}

#[test]
fn equal_constants_are_never_lowered() {
    // `(not (= c c))` is FALSE, not a theorem. If this ever fired, the step
    // would be a false certificate (carcara's `evaluate` would also reject it,
    // but the gate must not offer it in the first place).
    assert_eq!(lower("(cl (not (= #b0101 #b0101)))"), None);
    assert_eq!(lower("(cl (not (= #x2a #x2a)))"), None);
}

#[test]
fn non_constant_operands_are_never_lowered() {
    // A variable side makes the clause a genuine theory fact, not a ground
    // evaluation; carcara could not fold it.
    assert_eq!(lower("(cl (not (= x #b0101)))"), None);
    assert_eq!(lower("(cl (not (= #b0101 x)))"), None);
    assert_eq!(lower("(cl (not (= (bvor v0 v2) #b0101)))"), None);
}

#[test]
fn mismatched_widths_are_never_lowered() {
    // Different digit counts are different SORTS; carcara's parser would
    // reject the `=` outright.
    assert_eq!(lower("(cl (not (= #b0000 #b00000)))"), None);
    assert_eq!(lower("(cl (not (= #x0f #x00f)))"), None);
    // Mixed radix: `#b1111` and `#xf` denote the same value at different
    // widths; the gate does not attempt to relate the two spellings.
    assert_eq!(lower("(cl (not (= #b1111 #xf)))"), None);
}

#[test]
fn non_bitvector_constants_are_never_lowered() {
    // Int/Real/String are deliberately out of scope: distinct printed
    // spellings there need not denote distinct values (`1.0` vs `1.00`), so
    // "the strings differ" is not a disequality proof.
    assert_eq!(lower("(cl (not (= 1.0 1.00)))"), None);
    assert_eq!(lower("(cl (not (= 3 4)))"), None);
    assert_eq!(lower("(cl (not (= \"a\" \"b\")))"), None);
    // The `(_ bvN W)` spelling would need numeric parsing to compare values.
    assert_eq!(lower("(cl (not (= (_ bv5 8) (_ bv6 8))))"), None);
}

#[test]
fn malformed_bitvector_literals_are_never_lowered() {
    assert_eq!(lower("(cl (not (= #b #b)))"), None);
    assert_eq!(lower("(cl (not (= #b012 #b010)))"), None);
    assert_eq!(lower("(cl (not (= #xzz #x00)))"), None);
}

#[test]
fn only_the_negated_unit_shape_is_lowered() {
    // Positive equality: `(= C1 C2)` between distinct constants is FALSE.
    assert_eq!(lower("(cl (= #b0000 #b1111))"), None);
    // Multi-literal clauses: the derivation proves the unit only.
    assert_eq!(lower("(cl (not (= #b0000 #b1111)) p)"), None);
    assert_eq!(lower("(cl)"), None);
    // Double negation is not the shape either.
    assert_eq!(lower("(cl (not (not (= #b0000 #b1111))))"), None);
    // A three-argument `=` is not what `equiv1` consumes.
    assert_eq!(lower("(cl (not (= #b0000 #b1111 #b0101)))"), None);
}
