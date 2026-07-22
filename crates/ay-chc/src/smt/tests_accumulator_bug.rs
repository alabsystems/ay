// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the SMT solver bug found via accumulator_unsafe_000.
//!
//! The PDR verify_model formula `body(x,y) AND NOT(head(x+1, y+x))` from the
//! accumulator_unsafe_000 benchmark is SAT at (x=1, y=0), but AY's SMT solver
//! incorrectly returns UNSAT. The concrete transition check (#5381) works around
//! this at the verify_model level. These tests document the bug surface.

#![allow(clippy::unwrap_used)]

use super::context::SmtContext;
use super::types::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use serial_test::serial;
use std::sync::Arc;

/// Shared expressions for the accumulator_unsafe_000 invariant model.
struct AccumulatorExprs {
    x: ChcExpr,
    y: ChcExpr,
    x_plus_1: ChcExpr,
    y_plus_x: ChcExpr,
    y_2x_1: ChcExpr,
    y_3x_3: ChcExpr,
}

impl AccumulatorExprs {
    fn new() -> Self {
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        let x_plus_1 = ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::new(x.clone()), Arc::new(ChcExpr::Int(1))],
        );
        let y_plus_x = ChcExpr::Op(ChcOp::Add, vec![Arc::new(y.clone()), Arc::new(x.clone())]);
        let y_2x_1 = ChcExpr::Op(
            ChcOp::Add,
            vec![
                Arc::new(y.clone()),
                Arc::new(x.clone()),
                Arc::new(x.clone()),
                Arc::new(ChcExpr::Int(1)),
            ],
        );
        let y_3x_3 = ChcExpr::Op(
            ChcOp::Add,
            vec![
                Arc::new(y_plus_x.clone()),
                Arc::new(x_plus_1.clone()),
                Arc::new(x_plus_1.clone()),
                Arc::new(ChcExpr::Int(1)),
            ],
        );
        Self {
            x,
            y,
            x_plus_1,
            y_plus_x,
            y_2x_1,
            y_3x_3,
        }
    }

    /// NOT(a = c0 AND b = c1)
    fn not_eq_pair(a: &ChcExpr, c0: i128, b: &ChcExpr, c1: i128) -> ChcExpr {
        ChcExpr::not(ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::eq(a.clone(), ChcExpr::Int(c0))),
                Arc::new(ChcExpr::eq(b.clone(), ChcExpr::Int(c1))),
            ],
        ))
    }

    /// Body with duplicate conjuncts (as PDR produces).
    fn body_with_dups(&self) -> ChcExpr {
        let e = self;
        ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(e.x.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x, 0, &e.y, 1)),
                Arc::new(ChcExpr::ge(e.x.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x, 0, &e.y, 1)),
                Arc::new(ChcExpr::not(ChcExpr::ge(e.y_2x_1.clone(), ChcExpr::Int(4)))),
                Arc::new(Self::not_eq_pair(&e.x, 0, &e.y, 2)),
            ],
        )
    }

    /// Body WITHOUT duplicate conjuncts.
    fn body_no_dups(&self) -> ChcExpr {
        let e = self;
        ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(e.x.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x, 0, &e.y, 1)),
                Arc::new(ChcExpr::not(ChcExpr::ge(e.y_2x_1.clone(), ChcExpr::Int(4)))),
                Arc::new(Self::not_eq_pair(&e.x, 0, &e.y, 2)),
            ],
        )
    }

    /// Head with duplicate conjuncts: Inv(x+1, y+x).
    fn head_with_dups(&self) -> ChcExpr {
        let e = self;
        ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(e.x_plus_1.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y_plus_x.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x_plus_1, 0, &e.y_plus_x, 1)),
                Arc::new(ChcExpr::ge(e.x_plus_1.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y_plus_x.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x_plus_1, 0, &e.y_plus_x, 1)),
                Arc::new(ChcExpr::not(ChcExpr::ge(e.y_3x_3.clone(), ChcExpr::Int(4)))),
                Arc::new(Self::not_eq_pair(&e.x_plus_1, 0, &e.y_plus_x, 2)),
            ],
        )
    }

    /// Head WITHOUT duplicate conjuncts: Inv(x+1, y+x).
    fn head_no_dups(&self) -> ChcExpr {
        let e = self;
        ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(e.x_plus_1.clone(), ChcExpr::Int(0))),
                Arc::new(ChcExpr::ge(e.y_plus_x.clone(), ChcExpr::Int(0))),
                Arc::new(Self::not_eq_pair(&e.x_plus_1, 0, &e.y_plus_x, 1)),
                Arc::new(ChcExpr::not(ChcExpr::ge(e.y_3x_3.clone(), ChcExpr::Int(4)))),
                Arc::new(Self::not_eq_pair(&e.x_plus_1, 0, &e.y_plus_x, 2)),
            ],
        )
    }
}

/// Body-only formula from accumulator_unsafe_000 should be SAT at x=0, y=0.
#[test]
fn test_check_sat_accumulator_body_only() {
    let mut ctx = SmtContext::new();
    let e = AccumulatorExprs::new();
    let body = e.body_with_dups();
    let result = ctx.check_sat(&body);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "body-only check_sat returned {result:?} but formula is SAT at x=0,y=0",
    );
}

/// Body + simplified negated head (only h1 and h7) should be SAT at x=1, y=0.
#[test]
fn test_check_sat_accumulator_body_plus_simple_negated_head() {
    let mut ctx = SmtContext::new();
    let e = AccumulatorExprs::new();
    let body = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::ge(e.x.clone(), ChcExpr::Int(0))),
            Arc::new(ChcExpr::ge(e.y.clone(), ChcExpr::Int(0))),
            Arc::new(ChcExpr::not(ChcExpr::ge(e.y_2x_1.clone(), ChcExpr::Int(4)))),
        ],
    );
    let head = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::ge(e.x_plus_1.clone(), ChcExpr::Int(0))),
            Arc::new(ChcExpr::not(ChcExpr::ge(e.y_3x_3, ChcExpr::Int(4)))),
        ],
    );
    let query = ChcExpr::and(body, ChcExpr::not(head));
    let result = ctx.check_sat(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "body+simple-head returned {result:?} but formula is SAT at x=1, y=0",
    );
}

/// Full formula WITHOUT duplicate conjuncts. Fixed in #5384:
/// Two bugs in disequality split clause generation caused false UNSAT:
/// 1. Model-derived bounds pruning (can_lt/can_gt) removed split branches
///    based on the current SAT model, which is unsound because the SAT
///    solver can backtrack to different Boolean assignments.
/// 2. Missing guard atoms when find_diseq_guard_atom couldn't find a direct
///    (= x k) atom (e.g., disequality from compound expression y+x=1),
///    producing unguarded clauses that permanently eliminated valid values.
#[test]
fn test_check_sat_accumulator_no_dups() {
    let mut ctx = SmtContext::new();
    let e = AccumulatorExprs::new();
    let query = ChcExpr::and(e.body_no_dups(), ChcExpr::not(e.head_no_dups()));
    let result = ctx.check_sat(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "check_sat returned {result:?} but formula is SAT at x=1, y=0",
    );
}

/// Full formula WITH duplicate conjuncts (as PDR produces). Same fix as above.
/// Uses executor fallback (#7109) because the internal DPLL(T) is incomplete
/// on this formula (returns Unknown due to disequality splits).
#[test]
fn test_check_sat_accumulator_verify_model_formula_known_smt_bug() {
    let mut ctx = SmtContext::new();
    let e = AccumulatorExprs::new();
    let query = ChcExpr::and(e.body_with_dups(), ChcExpr::not(e.head_with_dups()));
    let result = ctx.check_sat_with_executor_fallback(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "check_sat returned {result:?} but formula is SAT at x=1, y=0",
    );
}

#[test]
#[serial]
fn test_check_sat_accumulator_reuses_theory_solvers_between_sat_models_6359() {
    super::check_sat::reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let e = AccumulatorExprs::new();
    let query = ChcExpr::and(e.body_no_dups(), ChcExpr::not(e.head_no_dups()));
    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "check_sat returned {result:?} but formula is SAT at x=1, y=0",
    );

    let (builds, sat_models) = super::check_sat::reuse_counters_for_tests();
    assert!(
        sat_models >= 2,
        "expected accumulator regression to explore multiple SAT models, saw {sat_models}",
    );
    assert!(
        builds < sat_models,
        "expected theory solver reuse across SAT models, saw {builds} builds for {sat_models} SAT models",
    );
}

#[test]
#[serial]
fn test_check_sat_fixed_term_lia_contradiction_unsat_6359() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let x_expr = ChcExpr::var(x);
    let y_expr = ChcExpr::var(y);
    // Use a formula that requires LIA theory reasoning to detect UNSAT.
    // x >= y+1 ∧ y >= x is infeasible (implies x >= x+1), but the
    // preprocessor can't catch it — no var=var or var=const equalities
    // to propagate. This ensures the theory loop actually runs.
    let query = ChcExpr::and(
        ChcExpr::ge(
            x_expr.clone(),
            ChcExpr::add(y_expr.clone(), ChcExpr::int(1)),
        ),
        ChcExpr::ge(y_expr, x_expr),
    );

    let result = ctx.check_sat(&query);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "expected fixed-term query to be UNSAT, got {result:?}",
    );
}

/// Standalone SAT-level test: batch version.
/// Creates the exact clause database from the DPLL(T) trace for the
/// accumulator_no_dups test (18 Tseitin + 8 blocking + 3 split = 29 clauses)
/// and checks satisfiability with a FRESH solver. If this passes but the
/// incremental version fails, the bug is in ay-sat's incremental solving.
#[test]
fn test_sat_accumulator_clauses_batch() {
    use ay_sat::{Literal, Solver};

    fn lit(d: i32) -> Literal {
        Literal::from_dimacs(d)
    }

    let mut sat = Solver::new(23);

    // === Tseitin clauses ===
    // v3 = OR(NOT(v4), NOT(v5))
    sat.add_clause(vec![lit(-3), lit(-4), lit(-5)]);
    sat.add_clause(vec![lit(4), lit(3)]);
    sat.add_clause(vec![lit(5), lit(3)]);
    // v7 = OR(NOT(v4), NOT(v8))
    sat.add_clause(vec![lit(-7), lit(-4), lit(-8)]);
    sat.add_clause(vec![lit(4), lit(7)]);
    sat.add_clause(vec![lit(8), lit(7)]);
    // v12 = AND(v13, v14)
    sat.add_clause(vec![lit(-12), lit(13)]);
    sat.add_clause(vec![lit(-12), lit(14)]);
    sat.add_clause(vec![lit(-13), lit(-14), lit(12)]);
    // v16 = AND(v13, v17)
    sat.add_clause(vec![lit(-16), lit(13)]);
    sat.add_clause(vec![lit(-16), lit(17)]);
    sat.add_clause(vec![lit(-13), lit(-17), lit(16)]);
    // v9 = OR(v10, v11, v12, v15, v16)
    sat.add_clause(vec![lit(-9), lit(10), lit(11), lit(12), lit(15), lit(16)]);
    sat.add_clause(vec![lit(-10), lit(9)]);
    sat.add_clause(vec![lit(-11), lit(9)]);
    sat.add_clause(vec![lit(-12), lit(9)]);
    sat.add_clause(vec![lit(-15), lit(9)]);
    sat.add_clause(vec![lit(-16), lit(9)]);

    // === Blocking clauses (from DPLL(T) iterations 1-11) ===
    sat.add_clause(vec![lit(-1), lit(-13)]); // iter 1
    sat.add_clause(vec![lit(8), lit(-4), lit(-17)]); // iter 2
    sat.add_clause(vec![lit(-19), lit(-18)]); // iter 4
    sat.add_clause(vec![lit(-21), lit(-20)]); // iter 6
    sat.add_clause(vec![lit(-4), lit(-21), lit(-6)]); // iter 7
    sat.add_clause(vec![lit(-1), lit(-21), lit(-6)]); // iter 8
    sat.add_clause(vec![lit(-23), lit(-22)]); // iter 10
    sat.add_clause(vec![lit(-8), lit(-23), lit(-6)]); // iter 11

    // === Split clauses (guarded) ===
    sat.add_clause(vec![lit(5), lit(18), lit(19)]); // y=1 OR y≤0 OR y≥2
    sat.add_clause(vec![lit(8), lit(20), lit(21)]); // y=2 OR y≤1 OR y≥3
    sat.add_clause(vec![lit(4), lit(22), lit(23)]); // x=0 OR x≤-1 OR x≥1

    // === Assumptions ===
    let assumptions = vec![lit(1), lit(2), lit(3), lit(6), lit(7), lit(9)];

    let result = sat.solve_with_assumptions(&assumptions);
    let result_str = match result.result() {
        ay_sat::AssumeResult::Sat(_) => "Sat".to_string(),
        ay_sat::AssumeResult::Unsat(core, _) => format!("Unsat(core={core:?})"),
        ay_sat::AssumeResult::Unknown => "Unknown".to_string(),
        #[allow(unreachable_patterns)]
        _ => "Other".to_string(),
    };
    assert!(
        result.is_sat(),
        "Batch SAT solver returned {result_str} but formula is SAT \
         (target: v1=T v2=T v3=T v4=F v5=F v6=T v7=T v8=F v9=T \
         v10=F v11=F v12=F v13=F v14=T v15=T v16=F v17=F \
         v18=T v19=F v20=T v21=F v22=F v23=T)",
    );
}

/// Standalone SAT-level test: incremental version.
/// Simulates the exact sequence of solve_with_assumptions + add_clause calls
/// from the DPLL(T) loop. If batch passes but incremental fails, the bug is
/// in ay-sat's incremental state management.
#[test]
fn test_sat_accumulator_clauses_incremental() {
    use ay_sat::{Literal, Solver};

    fn lit(d: i32) -> Literal {
        Literal::from_dimacs(d)
    }

    let mut sat = Solver::new(17); // Initially 17 vars

    // === Tseitin clauses ===
    sat.add_clause(vec![lit(-3), lit(-4), lit(-5)]);
    sat.add_clause(vec![lit(4), lit(3)]);
    sat.add_clause(vec![lit(5), lit(3)]);
    sat.add_clause(vec![lit(-7), lit(-4), lit(-8)]);
    sat.add_clause(vec![lit(4), lit(7)]);
    sat.add_clause(vec![lit(8), lit(7)]);
    sat.add_clause(vec![lit(-12), lit(13)]);
    sat.add_clause(vec![lit(-12), lit(14)]);
    sat.add_clause(vec![lit(-13), lit(-14), lit(12)]);
    sat.add_clause(vec![lit(-16), lit(13)]);
    sat.add_clause(vec![lit(-16), lit(17)]);
    sat.add_clause(vec![lit(-13), lit(-17), lit(16)]);
    sat.add_clause(vec![lit(-9), lit(10), lit(11), lit(12), lit(15), lit(16)]);
    sat.add_clause(vec![lit(-10), lit(9)]);
    sat.add_clause(vec![lit(-11), lit(9)]);
    sat.add_clause(vec![lit(-12), lit(9)]);
    sat.add_clause(vec![lit(-15), lit(9)]);
    sat.add_clause(vec![lit(-16), lit(9)]);

    let assumptions = vec![lit(1), lit(2), lit(3), lit(6), lit(7), lit(9)];

    // Iteration 1: SAT → theory UNSAT → blocking clause
    let r1 = sat.solve_with_assumptions(&assumptions);
    assert!(r1.is_sat(), "iter 1 should be SAT");
    sat.add_clause(vec![lit(-1), lit(-13)]);

    // Iteration 2: SAT → theory UNSAT → blocking clause
    let r2 = sat.solve_with_assumptions(&assumptions);
    assert!(r2.is_sat(), "iter 2 should be SAT");
    sat.add_clause(vec![lit(8), lit(-4), lit(-17)]);

    // Iteration 3: SAT → theory NeedDisequalitySplit → add split vars + clause
    let r3 = sat.solve_with_assumptions(&assumptions);
    assert!(r3.is_sat(), "iter 3 should be SAT");
    sat.ensure_num_vars(19);
    sat.add_clause(vec![lit(5), lit(18), lit(19)]);

    // Iteration 4: SAT → theory UNSAT → blocking clause
    let r4 = sat.solve_with_assumptions(&assumptions);
    assert!(r4.is_sat(), "iter 4 should be SAT");
    sat.add_clause(vec![lit(-19), lit(-18)]);

    // Iteration 5: SAT → theory NeedDisequalitySplit → add split vars + clause
    let r5 = sat.solve_with_assumptions(&assumptions);
    assert!(r5.is_sat(), "iter 5 should be SAT");
    sat.ensure_num_vars(21);
    sat.add_clause(vec![lit(8), lit(20), lit(21)]);

    // Iteration 6: SAT → theory UNSAT → blocking clause
    let r6 = sat.solve_with_assumptions(&assumptions);
    assert!(r6.is_sat(), "iter 6 should be SAT");
    sat.add_clause(vec![lit(-21), lit(-20)]);

    // Iteration 7: SAT → theory UNSAT → blocking clause
    let r7 = sat.solve_with_assumptions(&assumptions);
    assert!(r7.is_sat(), "iter 7 should be SAT");
    sat.add_clause(vec![lit(-4), lit(-21), lit(-6)]);

    // Iteration 8: SAT → theory UNSAT → blocking clause
    let r8 = sat.solve_with_assumptions(&assumptions);
    assert!(r8.is_sat(), "iter 8 should be SAT");
    sat.add_clause(vec![lit(-1), lit(-21), lit(-6)]);

    // Iteration 9: SAT → theory NeedDisequalitySplit → add split vars + clause
    let r9 = sat.solve_with_assumptions(&assumptions);
    assert!(r9.is_sat(), "iter 9 should be SAT");
    sat.ensure_num_vars(23);
    sat.add_clause(vec![lit(4), lit(22), lit(23)]);

    // Iteration 10: SAT → theory UNSAT → blocking clause
    let r10 = sat.solve_with_assumptions(&assumptions);
    assert!(r10.is_sat(), "iter 10 should be SAT");
    sat.add_clause(vec![lit(-23), lit(-22)]);

    // Iteration 11: SAT → theory UNSAT → blocking clause
    let r11 = sat.solve_with_assumptions(&assumptions);
    assert!(r11.is_sat(), "iter 11 should be SAT");
    sat.add_clause(vec![lit(-8), lit(-23), lit(-6)]);

    // Iteration 12: This SHOULD return SAT but the bug makes it return UNSAT
    let r12 = sat.solve_with_assumptions(&assumptions);
    assert!(
        r12.is_sat(),
        "iter 12: incremental solver returned {:?} but formula is SAT at \
         v1=T v2=T v3=T v4=F v5=F v6=T v7=T v8=F v9=T v10=F v11=F v12=F \
         v13=F v14=T v15=T v16=F v17=F v18=T v19=F v20=T v21=F v22=F v23=T",
        match r12.result() {
            ay_sat::AssumeResult::Sat(_) => "Sat".to_string(),
            ay_sat::AssumeResult::Unsat(core, _) => format!(
                "Unsat(core={})",
                core.iter()
                    .map(|l| l.to_dimacs())
                    .collect::<Vec<_>>()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            ay_sat::AssumeResult::Unknown => "Unknown".to_string(),
            #[allow(unreachable_patterns)]
            _ => "Other".to_string(),
        },
    );
}
