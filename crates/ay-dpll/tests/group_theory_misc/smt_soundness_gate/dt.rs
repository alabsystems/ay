// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_DT soundness gate tests.
//!
//! Datatype formulas do not currently dominate the consumer-triage queue, but
//! they are a supported public logic and already have known model-validation
//! edge cases. This gate keeps constructor/selector/tester basics under the
//! same soundness harness as the other SMT logics.

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_DT)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (assert (is-Just x))
        (assert (= (value x) 42))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_unsat_proof_envelope() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_DT)
        (set-option :produce-proofs true)
        (declare-datatypes ((Option 0)) (((None) (Some (value Int)))))
        (declare-const x Option)
        (declare-const y Int)
        (assert (= x None))
        (assert (= x (Some y)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: selector values must validate against constructor terms ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_selector_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mk-pair (fst Int) (snd Int)))))
        (declare-const p Pair)
        (assert (= (fst p) 10))
        (assert (= (snd p) 20))
        (check-sat)
    "#,
    );
}

// --- 3b. Finite-enum cardinality (pigeonhole) over an `ite`-valued operand ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_enum_cardinality_ite_distinct_unsat() {
    // `Enum` has exactly 3 inhabitants, so four pairwise-distinct values are
    // impossible (pigeonhole) — UNSAT. Regression for the false-SAT where an
    // `ite`-valued `distinct` operand is Shannon-lifted + CNF'd into guarded
    // clauses that the finite-enum pigeonhole edge collector failed to count,
    // shrinking the clique below the cardinality and reporting SAT
    // (#dt-enum-pigeonhole-ite). z3 and cvc5 both report unsat.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
        (declare-fun f (Enum) Enum)
        (declare-const a Enum)
        (declare-const b Enum)
        (declare-const v1 Enum)
        (declare-const v2 Enum)
        (declare-const p Bool)
        (assert (distinct (ite p v1 v2) (f a) a b))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_enum_cardinality_ite_distinct_three_terms_sat() {
    // Control: only THREE pairwise-distinct values over a 3-inhabitant enum is
    // satisfiable — the pigeonhole recovery must not over-refute this to UNSAT.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
        (declare-fun f (Enum) Enum)
        (declare-const a Enum)
        (declare-const v1 Enum)
        (declare-const v2 Enum)
        (declare-const p Bool)
        (assert (distinct (ite p v1 v2) (f a) a))
        (check-sat)
    "#,
        &["sat"],
    );
}

// --- 3b'. Finite-enum cardinality (pigeonhole) beyond the old 96-node cap ---

/// Build a QF_DT coloring-style script over a `k`-inhabitant enum with
/// `n` constants: an embedded (k+1)-clique of pairwise `distinct` asserts on
/// the first `k + 1` constants (iff `with_conflict`) plus a low-degree
/// disequality chain across all `n` (mirrors SMT-LIB 20210312-Bouvier).
fn enum_pigeonhole_script(n: usize, k: usize, with_conflict: bool) -> String {
    use std::fmt::Write;
    let mut smt = String::from("(set-logic QF_DT)\n(declare-datatypes ((Unit 0)) ((");
    for c in 0..k {
        write!(smt, "(u{c})").unwrap();
    }
    smt.push_str(")))\n");
    for v in 0..n {
        writeln!(smt, "(declare-const x{v} Unit)").unwrap();
    }
    if with_conflict {
        for i in 0..=k {
            for j in (i + 1)..=k {
                writeln!(smt, "(assert (distinct x{i} x{j}))").unwrap();
            }
        }
    }
    for v in (k + 1)..n {
        writeln!(smt, "(assert (distinct x{} x{v}))", v - 1).unwrap();
    }
    smt.push_str("(check-sat)\n");
    smt
}

#[test]
#[timeout(30_000)]
fn test_gate_qf_dt_enum_pigeonhole_large_graph_unsat() {
    // Regression (#smtcomp-2025 Bouvier unsat cliff): 120 disequality-graph
    // nodes exceed the OLD hard cap of 96, under which the finite-enum
    // pigeonhole pass silently skipped and the 5-clique over the 4-inhabitant
    // enum went unrefuted by the pre-dispatch pass. The budgeted search must
    // find + re-verify the clique and conclude unsat.
    assert_scope_results(&enum_pigeonhole_script(120, 4, true), &["unsat"]);
}

#[test]
#[timeout(30_000)]
fn test_gate_qf_dt_enum_pigeonhole_large_graph_sat_control() {
    // Control at the same scale: chain disequalities only (max clique 2 over a
    // 4-inhabitant enum) — satisfiable, and the raised-cap pass must not
    // over-refute it. The model must survive validation.
    assert_sat_validates(&enum_pigeonhole_script(120, 4, false));
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ufdt_enum_function_pigeonhole_unsat() {
    // dt_residual_falsesat_4 (reduced): over the 2-inhabitant enum `Enum`,
    // `f : Enum -> Enum`, `(= (f v1) v2)` plus `(distinct (f v1) (f (f v2)))`
    // is UNSAT — a FUNCTIONAL pigeonhole: v2 must lie in the image of f and
    // satisfy v2 != f(f(v2)), but no f over {c0,c1} admits that. The
    // `distinct`-clique check cannot see it (only one diseq edge, a 2-clique
    // that never exceeds k=2). The finite-enum DOMAIN-COVERAGE pass pins every
    // enum-sorted application term to {c0,c1} so the SAT/EUF layer case-splits
    // and refutes it. z3 AND cvc5 both report unsat (#dt-enum-func-coverage).
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1))))
        (declare-fun f (Enum) Enum)
        (declare-const v1 Enum)
        (declare-const v2 Enum)
        (assert (= (f v1) v2))
        (assert (distinct (f v1) (f (f v2))))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ufdt_enum_function_pigeonhole_full_unsat() {
    // The full dt_residual_falsesat_4 benchmark (extra unrelated datatype sorts
    // and declarations present). ay must not float the enum-sorted `fEnum`
    // applications free of {c0,c1}. z3 AND cvc5 both report unsat.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-sort E 0)
        (declare-datatypes ((Enum 0) (Rec 0) (Opt 0) (Lst 0))
          (((c0) (c1))
           ((mkRec (rs0 E) (rs1 Bool)))
           ((none) (some (val E)))
           ((cons (hd Bool) (tl Lst)) (nil))))
        (declare-const v1 Enum)
        (declare-const v2 Enum)
        (declare-fun fEnum (Enum) Enum)
        (assert (= (fEnum v1) v2))
        (assert (distinct (fEnum v1) (fEnum (fEnum v2))))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ufdt_enum_function_satisfiable_no_overrefute() {
    // Control: over a 3-inhabitant enum the analogous single application
    // disequality is SATISFIABLE — the domain-coverage pass must not
    // over-refute it. `(distinct (f a) (f (f (f a))))` over {c0,c1,c2} has a
    // model (e.g. f a 3-cycle). z3 AND cvc5 report sat.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
        (declare-fun f (Enum) Enum)
        (declare-const a Enum)
        (assert (distinct (f a) (f (f (f a)))))
        (check-sat)
    "#,
        &["sat"],
    );
}

// --- 3d. FIELD-BEARING finite datatype cardinality (pigeonhole) ---
//
// Regression for the false-SAT where a datatype with FIELDS (not all-nullary)
// is provably finite — its cardinality is `sum over ctors of product of field
// cardinalities` — so a `distinct` over more than that many values is UNSAT.
// The enum-only finite-domain machinery missed these. Each `unsat` is confirmed
// by z3 AND cvc5; the `sat` controls keep the pass from over-refuting.
// (#dt-field-finite-card)

/// `Rec = C(b:Bool)` has exactly 2 inhabitants (`C(false)`, `C(true)`), so three
/// pairwise-distinct `Rec` values are impossible — UNSAT by pigeonhole. The
/// finite-domain cardinality pass only handled all-nullary enums; it now computes
/// a single-constructor datatype's cardinality as the product of its field
/// cardinalities (`Bool = 2`). z3 AND cvc5 report unsat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_field_bearing_bool_card_distinct_three_unsat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Rec ((C (b Bool))))
        (declare-const x1 Rec)
        (declare-const x2 Rec)
        (declare-const x3 Rec)
        (assert (distinct x1 x2 x3))
        (check-sat)
    "#,
        &["unsat"],
    );
}

/// CONTROL: with an INFINITE field (`Int`) the datatype is NOT provably finite,
/// so three distinct values are SATISFIABLE — the cardinality pass must SKIP it
/// (it must never assert a wrong finite bound). z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_field_bearing_int_field_infinite_sat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Rec ((C (i Int))))
        (declare-const x1 Rec)
        (declare-const x2 Rec)
        (declare-const x3 Rec)
        (assert (distinct x1 x2 x3))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// CONTROL: only TWO distinct values over the 2-inhabitant `C(b:Bool)` is
/// satisfiable (a 2-clique does not exceed `k = 2`) — the pass must not
/// over-refute. z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_field_bearing_bool_card_distinct_two_sat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Rec ((C (b Bool))))
        (declare-const x1 Rec)
        (declare-const x2 Rec)
        (assert (distinct x1 x2))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// Multi-constructor finite datatype: `D = A | B(p:Bool)` has cardinality
/// `1 + 2 = 3`, so four pairwise-distinct `D` values are impossible — UNSAT.
/// Exercises the SUM-over-constructors part of the cardinality formula. z3 AND
/// cvc5 report unsat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_multi_ctor_finite_card_distinct_four_unsat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype D ((A) (B (p Bool))))
        (declare-const x1 D)
        (declare-const x2 D)
        (declare-const x3 D)
        (declare-const x4 D)
        (assert (distinct x1 x2 x3 x4))
        (check-sat)
    "#,
        &["unsat"],
    );
}

/// CONTROL for the multi-ctor formula: exactly THREE distinct values over the
/// cardinality-3 `D = A | B(p:Bool)` is satisfiable (`A`, `B(false)`, `B(true)`)
/// — the pass must not over-refute the at-capacity case. z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_multi_ctor_finite_card_distinct_three_sat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype D ((A) (B (p Bool))))
        (declare-const x1 D)
        (declare-const x2 D)
        (declare-const x3 D)
        (assert (distinct x1 x2 x3))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// Two Bool fields: `C(b1:Bool)(b2:Bool)` has cardinality `2 * 2 = 4`, so five
/// pairwise-distinct values are impossible — UNSAT. Exercises the PRODUCT of
/// multiple field cardinalities. z3 AND cvc5 report unsat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_two_bool_fields_card_distinct_five_unsat() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Rec ((C (b1 Bool) (b2 Bool))))
        (declare-const x1 Rec)
        (declare-const x2 Rec)
        (declare-const x3 Rec)
        (declare-const x4 Rec)
        (declare-const x5 Rec)
        (assert (distinct x1 x2 x3 x4 x5))
        (check-sat)
    "#,
        &["unsat"],
    );
}

// --- 3c. Datatype acyclicity hidden behind nested ite/cons/selector layers ---
//
// Regression cluster for the false-SAT where a constructor self-containment
// cycle is buried inside nested `ite`/`cons`/selector structure that the DT
// occurs-check did not decompose. z3 AND cvc5 both report unsat on all four.
// (#dt-acyclic-nested-ite-cons)

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_acyclic_selfcons_behind_ite_fuzz800() {
    // fuzz_dt_falsesat_800: `v7 = (cons v11 (ite g1 (ite v13 v8 (cons v11 v7))
    // (ite v13 v8 v7)))` with `(not (and v13 true))` forcing `v13 = false`.
    // Under v13=false both inner branches reduce to a subterm chain that
    // contains `v7` unconditionally (g1's then-branch `(cons v11 v7)` and
    // else-branch `v7` both contain v7), so `v7` is a proper subterm of a
    // constructor application rooted at `cons` — a well-foundedness cycle,
    // UNSAT.
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-sort E 0)
        (declare-datatypes ((Enum 0) (Rec 0) (Opt 0) (Lst 0) (Tree 0))
          (((c0) (c1))
           ((mkRec (rs0 E) (rs1 E) (rs2 Bool)))
           ((none) (some (val Bool)))
           ((cons (hd E) (tl Lst)) (nil))
           ((leaf (lv Enum)) (node (left Tree) (nv Rec) (right Tree)))))
        (declare-const v6 Opt)
        (declare-const v7 Lst)
        (declare-const v8 Lst)
        (declare-const v11 E)
        (declare-const v13 Bool)
        (assert (= v7 (cons v11 (ite ((_ is none) v6) (ite v13 v8 (cons v11 v7)) (ite v13 v8 v7)))))
        (assert (not (and v13 true)))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_acyclic_node_eq_ite_with_false_tester_guard_fuzz3() {
    // dt_residual_falsesat_3: `(= (node v11 _ v10) (ite (is-nil (cons v16 nil))
    // (..) (ite v15 v11 (leaf v2))))`. The outer guard `(is-nil (cons ..))` is
    // structurally false, so the RHS is `(ite v15 v11 (leaf v2))`. v15=true ⇒
    // `node(v11,..) = v11` (v11 is the `left` subterm → cycle); v15=false ⇒
    // `node(..) = leaf(..)` (constructor clash). Both branches UNSAT ⇒ UNSAT.
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-sort E 0)
        (declare-datatypes ((Enum 0) (Rec 0) (Opt 0) (Lst 0) (Tree 0))
          (((c0) (c1) (c2) (c3))
           ((mkRec (rs0 E) (rs1 E) (rs2 E)))
           ((none) (some (val E)))
           ((cons (hd Bool) (tl Lst)) (nil))
           ((leaf (lv Enum)) (node (left Tree) (nv Rec) (right Tree)))))
        (declare-const v2 Enum)
        (declare-const v5 Rec)
        (declare-const v10 Tree)
        (declare-const v11 Tree)
        (declare-const v12 Tree)
        (declare-const v15 Bool)
        (declare-const v16 Bool)
        (assert (= (node v11 (ite v15 v5 v5) v10)
                   (ite ((_ is nil) (cons v16 nil))
                        (ite v16 v12 (leaf c2))
                        (ite v15 v11 (leaf v2)))))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_acyclic_list_eq_own_tail_fuzz1() {
    // dt_residual_falsesat_1: `(distinct (tl v9) v8 nil)` ⇒ `(tl v9) != nil`,
    // and `(= v9 (tl v9))`. From `(tl v9) != nil` over the two-constructor list
    // `{cons, nil}`, `(tl v9) = cons(..)`; equality propagates `v9 = cons(..)`,
    // so `v9 = cons(hd v9, tl v9) = cons(hd v9, v9)` — `v9` a proper subterm of
    // itself, UNSAT by well-foundedness.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-sort E 0)
        (declare-datatypes ((Enum 0) (Rec 0) (Opt 0) (Lst 0))
          (((c0) (c1) (c2) (c3))
           ((mkRec (rs0 E) (rs1 Bool)))
           ((none) (some (val Bool)))
           ((cons (hd E) (tl Lst)) (nil))))
        (declare-const v8 Lst)
        (declare-const v9 Lst)
        (assert (distinct (tl v9) v8 nil))
        (assert (= v9 (tl v9)))
        (check-sat)
    "#,
        &["unsat"],
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ufdt_acyclic_node_selfcontain_fuzz881() {
    // fuzz_ufdt_falsesat_881: `v12 = (node (right (ite v17 v12 (node ..))) v5
    // (left (node v13 v5 v13)))`. The outer term is a `node(..)` constructor
    // whose middle argument `v5`/etc. and structure make `v12` reachable as a
    // proper subterm under every branch selection of the inner ite (the
    // selector `right`/`left` are opaque, but the `(node ..)` arguments that
    // wrap `v12` are constructor edges), a structural cycle ⇒ UNSAT.
    assert_scope_results(
        r#"
        (set-logic QF_UFDT)
        (declare-sort E 0)
        (declare-datatypes ((Enum 0) (Rec 0) (Opt 0) (Lst 0) (Tree 0))
          (((c0) (c1))
           ((mkRec (rs0 Bool) (rs1 E)))
           ((none) (some (val Bool)))
           ((cons (hd Bool) (tl Lst)) (nil))
           ((leaf (lv Enum)) (node (left Tree) (nv Rec) (right Tree)))))
        (declare-const v2 Enum)
        (declare-const v5 Rec)
        (declare-const v12 Tree)
        (declare-const v13 Tree)
        (declare-const v15 E)
        (declare-const v17 Bool)
        (declare-const v18 Bool)
        (declare-fun gE (E) E)
        (assert (= v12 (node (right (ite v17 v12 (node v13 (mkRec v18 (gE v15)) v12))) v5 (left (node v13 v5 v13)))))
        (assert (or (and (not v18) (not v17)) (distinct (right v12) (ite false v13 (node (leaf v2) (mkRec v18 v15) v13)) (ite v18 v12 v13) v12)))
        (check-sat)
    "#,
        &["unsat"],
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green)))
        (declare-const c Color)
        (assert (= c Red))
        (check-sat)
        (push 1)
        (assert (= c Green))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
