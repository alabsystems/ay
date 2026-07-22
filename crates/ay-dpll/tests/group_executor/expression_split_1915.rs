// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for NeedExpressionSplit handling (#1915).
//!
//! These tests verify that the solver correctly handles multi-variable
//! disequality splits where single-value enumeration doesn't work.

use ay_core::{
    ExpressionSplitRequest, Sort, TermId, TermStore, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver, Tseitin,
};
use ay_dpll::{DpllT, SolveStepResult};
use ay_sat::SatResult;
use ntest::timeout;

#[derive(Clone)]
struct DummyTheoryExpressionSplit {
    disequality_term: TermId,
    lt_atom: TermId,
    gt_atom: TermId,
    asserted: std::collections::HashMap<TermId, bool>,
}

impl DummyTheoryExpressionSplit {
    fn new(disequality_term: TermId, lt_atom: TermId, gt_atom: TermId) -> Self {
        Self {
            disequality_term,
            lt_atom,
            gt_atom,
            asserted: std::collections::HashMap::new(),
        }
    }
}

impl TheorySolver for DummyTheoryExpressionSplit {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.asserted.insert(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        // If either split branch is chosen, report a conflict so the SAT solver learns ¬lt/¬gt.
        if self.asserted.get(&self.lt_atom).copied().unwrap_or(false) {
            return TheoryResult::Unsat(vec![TheoryLit::new(self.lt_atom, true)]);
        }
        if self.asserted.get(&self.gt_atom).copied().unwrap_or(false) {
            return TheoryResult::Unsat(vec![TheoryLit::new(self.gt_atom, true)]);
        }

        // If the disequality is active (represented as an equality atom asserted false),
        // request an expression split.
        if self
            .asserted
            .get(&self.disequality_term)
            .copied()
            .is_some_and(|v| !v)
        {
            return TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                disequality_term: self.disequality_term,
            });
        }

        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {
        self.asserted.clear();
    }
}

/// Ensure the regression actually exercises `NeedExpressionSplit`.
///
/// Historically, missing `NeedExpressionSplit` plumbing caused executor paths to surface `Unknown`
/// on multi-variable disequalities. This test forces the DPLL(T) solver to receive an expression
/// split request and checks that applying it leads to a final UNSAT result.
#[test]
#[timeout(60_000)]
fn test_dpll_plumbs_need_expression_split() {
    let mut terms = TermStore::new();

    // Create an equality atom (a theory atom) that we will assert as false (disequality active).
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_eq(x, y);
    let not_eq_xy = terms.mk_not(eq_xy);

    // Create split atoms that are self-contradictory so the dummy theory's
    // single-literal conflicts pass semantic verification in debug builds.
    // x < x and x > x are always false, so [x < x = true] is UNSAT.
    let lt_atom = terms.mk_lt(x, x);
    let gt_atom = terms.mk_gt(x, x);

    // CNF asserts `not_eq_xy` (i.e., eq_xy=false).
    let tseitin = Tseitin::new(&terms).transform_all(&[not_eq_xy]);

    let theory = DummyTheoryExpressionSplit::new(eq_xy, lt_atom, gt_atom);
    let mut dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let split = match dpll.solve_step().unwrap() {
        SolveStepResult::NeedExpressionSplit(split) => split,
        other => panic!("expected NeedExpressionSplit, got: {other:?}"),
    };
    assert_eq!(split.disequality_term, eq_xy);

    // Treat `eq_xy` as an equality term asserted false (is_distinct=false) so the split clause is:
    //   (eq_xy) OR lt OR gt
    // which forces lt/gt only when eq_xy is false (i.e., disequality holds).
    dpll.apply_expression_split(lt_atom, gt_atom, split.disequality_term, false);

    match dpll.solve_step().unwrap() {
        SolveStepResult::Done(SatResult::Unsat(_)) => {}
        other => panic!("expected UNSAT after split, got: {other:?}"),
    }
}

/// Test that expression splits are handled for multi-variable Real disequalities.
///
/// This formula has a disequality (not (= (+ x y) z)) with tight bounds on all
/// variables. When x=1, y=0, z=1 is the only feasible assignment, the disequality
/// x+y != z is violated and requires an expression split E < F or E > F.
///
/// Regression test for #1915: NeedExpressionSplit must not return Unknown.
#[test]
#[timeout(60_000)]
fn test_qf_lra_expression_split_multi_var_disequality() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        ; Tight bounds: x=1, y=0, z=1 is the only solution
        (assert (= x 1.0))
        (assert (= y 0.0))
        (assert (= z 1.0))
        ; Disequality: x + y != z forces a split
        (assert (not (= (+ x y) z)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // With tight bounds x=1, y=0, z=1, we have x+y=1=z, violating x+y!=z.
    // The solver should return UNSAT (not Unknown).
    assert_eq!(outputs, vec!["unsat"]);
}

/// Test expression split with Int variables (via LIRA).
///
/// Similar to the LRA test but uses Int variables for the disequality.
#[test]
#[timeout(60_000)]
fn test_qf_lira_expression_split_multi_var_int_disequality() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        ; Tight bounds: x=1, y=0, z=1 is the only Int solution
        (assert (= x 1))
        (assert (= y 0))
        (assert (= z 1))
        ; Disequality: x + y != z forces a split
        (assert (not (= (+ x y) z)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // With tight bounds x=1, y=0, z=1, we have x+y=1=z, violating x+y!=z.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Test that SAT cases with disequalities don't spuriously fail.
///
/// Here x + y != z is satisfiable because x=0, y=0, z=1 works.
#[test]
#[timeout(60_000)]
fn test_qf_lra_expression_split_satisfiable() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        ; Bounds that allow x+y != z
        (assert (>= x 0.0))
        (assert (<= x 1.0))
        (assert (>= y 0.0))
        (assert (<= y 1.0))
        (assert (= z 1.0))
        ; Disequality: x + y != z
        ; Satisfiable with x=0, y=0, z=1 (0+0=0 != 1)
        (assert (not (= (+ x y) z)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // This should be SAT since x=0, y=0 satisfies 0+0 != 1
    assert_eq!(outputs, vec!["sat"]);
}

/// Test with distinct instead of not equals.
#[test]
#[timeout(60_000)]
fn test_qf_lra_expression_split_distinct() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        ; Tight bounds
        (assert (= x 1.0))
        (assert (= y 0.0))
        (assert (= z 1.0))
        ; distinct is semantically equivalent to not equals here
        (assert (distinct (+ x y) z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Should be UNSAT: x+y = 1 = z, so distinct is violated
    assert_eq!(outputs, vec!["unsat"]);
}
