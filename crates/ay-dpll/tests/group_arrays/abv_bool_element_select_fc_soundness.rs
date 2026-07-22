// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Bool-element array select congruence regressions (#multi-hop-flattened-option).
//!
//! `generate_array_bv_axioms` emitted its ROW1/ROW2/functional-consistency/
//! select-over-ITE consequents only for elements WITH bit-blasted term bits.
//! Bool-sorted selects have none (`ensure_term_bits` is BitVec-only): each
//! Bool select atom was an unconstrained fresh SAT variable, so the SAT core
//! could assign `select(a, i)` and `select(a, j)` opposite values even when
//! `i = j` is provable — an outright WRONG `sat` on z3-UNSAT instances, whose
//! internally-inconsistent models surfaced in model-checker-consumer as bogus "Genuine"
//! counterexamples (and blocked the ay-pb eval_lit whole-function VC, whose
//! harness assignment is an `(Array (_ BitVec 64) Bool)`).
//!
//! The fix (`scalar_elem_lits`) resolves a Bool element to its single CNF
//! literal (BV solver's `bool_to_var`, else the Tseitin skeleton var) and
//! emits the same consequents literal-wise. Pins below: `sat` on the UNSAT
//! instances is the SOUNDNESS bug; the BV1/BV8-element controls stayed
//! correct throughout and must remain so; genuinely-satisfiable probes must
//! never flip to `unsat` (the added clauses are array-congruence instances —
//! they can only remove spurious models).

use ntest::timeout;

/// The minimized wrong-`sat` repro: FC between `select(arr, i)` and
/// `select(arr, ite(<BV tautology>, i, j0))` on a Bool-element array.
/// Pre-fix: `sat` with a model violating the instance's own assert.
#[test]
#[timeout(60_000)]
fn bool_element_fc_over_tautological_ite_index_unsat() {
    let smt = "(declare-const arr (Array (_ BitVec 8) Bool))\n\
         (declare-const i (_ BitVec 8))\n\
         (declare-const j0 (_ BitVec 8))\n\
         (declare-const g (_ BitVec 1))\n\
         (declare-const b Bool)\n\
         (assert (= b (= (select arr i) (select arr (ite (or (= g #b0) (= g #b1)) i j0)))))\n\
         (assert (not b))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bool-element FC must connect equal-index selects (`sat` = the \
         inconsistent-model soundness bug; `unknown` = completeness regression)"
    );
}

/// Same shape with a `bvule` tautology as the ite condition.
#[test]
#[timeout(60_000)]
fn bool_element_fc_bvule_tautology_unsat() {
    let smt = "(declare-const arr (Array (_ BitVec 8) Bool))\n\
         (declare-const i (_ BitVec 8))\n\
         (declare-const j0 (_ BitVec 8))\n\
         (declare-const g (_ BitVec 1))\n\
         (assert (not (= (select arr i) (select arr (ite (bvule g #b1) i j0)))))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// BV64-index variant matching the model-checker-consumer harness-assignment shape
/// (`(Array (_ BitVec 64) Bool)` with point constraints).
#[test]
#[timeout(60_000)]
fn bool_element_bv64_point_reads_unsat() {
    let smt = "(declare-const a (Array (_ BitVec 64) Bool))\n\
         (declare-const v Bool)\n\
         (declare-const i (_ BitVec 64))\n\
         (assert (= (select a #x0000000000000002) v))\n\
         (assert (= i #x0000000000000002))\n\
         (assert (not (= (select a i) v)))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// ROW1 on a Bool-element store: reading the stored index must return the
/// stored value.
#[test]
#[timeout(60_000)]
fn bool_element_store_row1_unsat() {
    let smt = "(declare-const a (Array (_ BitVec 8) Bool))\n\
         (declare-const i (_ BitVec 8))\n\
         (declare-const j (_ BitVec 8))\n\
         (declare-const v Bool)\n\
         (assert (= i j))\n\
         (assert (not (= (select (store a i v) j) v)))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// CONTROL: (_ BitVec 1) elements were handled correctly before the fix
/// (term bits exist) and must stay UNSAT.
#[test]
#[timeout(60_000)]
fn bv1_element_fc_control_unsat() {
    let smt = "(declare-const arr (Array (_ BitVec 8) (_ BitVec 1)))\n\
         (declare-const i (_ BitVec 8))\n\
         (declare-const j0 (_ BitVec 8))\n\
         (declare-const g (_ BitVec 1))\n\
         (assert (not (= (select arr i) (select arr (ite (or (= g #b0) (= g #b1)) i j0)))))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// COMPLETENESS control: genuinely-satisfiable Bool-element instance — the
/// two indices are free, so unequal selects are realizable. The added
/// congruence clauses must never flip this to `unsat`.
#[test]
#[timeout(60_000)]
fn bool_element_distinct_indices_stays_sat() {
    let smt = "(declare-const arr (Array (_ BitVec 8) Bool))\n\
         (declare-const i (_ BitVec 8))\n\
         (declare-const j (_ BitVec 8))\n\
         (assert (not (= (select arr i) (select arr j))))\n\
         (check-sat)\n";
    let result = crate::common::solve(smt);
    assert_ne!(
        result.trim(),
        "unsat",
        "distinct-index Bool selects are satisfiable; a false UNSAT here means the \
         added congruence clauses over-constrain"
    );
}
