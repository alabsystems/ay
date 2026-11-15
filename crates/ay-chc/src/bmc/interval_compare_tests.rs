// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::ClauseBody;

const COMPARISONS: [ChcOp; 6] = [
    ChcOp::Lt,
    ChcOp::Le,
    ChcOp::Gt,
    ChcOp::Ge,
    ChcOp::Eq,
    ChcOp::Ne,
];

fn variable(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn compare(op: ChcOp, lhs: IntInterval, rhs: IntInterval) -> Option<bool> {
    let env = FxHashMap::from_iter([("x".to_owned(), lhs), ("y".to_owned(), rhs)]);
    BmcSolver::interval_compare_result(op, &variable("x"), &variable("y"), &env)
}

#[test]
fn missing_interval_endpoints_do_not_prove_equality_or_disequality() {
    for op in COMPARISONS {
        assert_eq!(compare(op, IntInterval::top(), IntInterval::top()), None);
        assert_eq!(
            BmcSolver::interval_compare_result(
                op,
                &variable("x"),
                &variable("y"),
                &FxHashMap::default(),
            ),
            None,
        );
    }
    let disequality = ChcExpr::not(ChcExpr::eq(variable("x"), variable("y")));
    let simplified = BmcSolver::simplify_interval_expr(&disequality, &FxHashMap::default());
    let model = FxHashMap::from_iter([
        ("x".to_owned(), SmtValue::Int(0)),
        ("y".to_owned(), SmtValue::Int(1)),
    ]);
    assert_eq!(
        crate::expr::evaluate_expr(&simplified, &model),
        Some(SmtValue::Bool(true)),
    );
}

#[test]
fn singleton_and_one_sided_bounds_use_both_proof_directions() {
    let cases = [
        (
            IntInterval::exact(0),
            IntInterval::exact(0),
            [
                Some(false),
                Some(true),
                Some(false),
                Some(true),
                Some(true),
                Some(false),
            ],
        ),
        (
            IntInterval::upper(0),
            IntInterval::lower(1),
            [
                Some(true),
                Some(true),
                Some(false),
                Some(false),
                Some(false),
                Some(true),
            ],
        ),
        (
            IntInterval::lower(1),
            IntInterval::upper(0),
            [
                Some(false),
                Some(false),
                Some(true),
                Some(true),
                Some(false),
                Some(true),
            ],
        ),
        (
            IntInterval::upper(0),
            IntInterval::lower(0),
            [None, Some(true), Some(false), None, None, None],
        ),
        (
            IntInterval::lower(0),
            IntInterval::upper(0),
            [Some(false), None, None, Some(true), None, None],
        ),
        (
            IntInterval::exact(i128::MIN),
            IntInterval::exact(i128::MAX),
            [
                Some(true),
                Some(true),
                Some(false),
                Some(false),
                Some(false),
                Some(true),
            ],
        ),
    ];
    for (lhs, rhs, expected) in cases {
        for (op, expected) in COMPARISONS.into_iter().zip(expected) {
            assert_eq!(compare(op, lhs, rhs), expected, "{lhs:?} {op:?} {rhs:?}");
        }
    }
}

#[test]
fn overlapping_or_unbounded_ranges_remain_unknown() {
    let cases = [
        (IntInterval::top(), IntInterval::exact(0)),
        (IntInterval::exact(0), IntInterval::top()),
        (IntInterval::lower(0), IntInterval::lower(1)),
        (IntInterval::upper(0), IntInterval::upper(1)),
        (
            IntInterval {
                lower: Some(0),
                upper: Some(2),
            },
            IntInterval {
                lower: Some(1),
                upper: Some(3),
            },
        ),
    ];
    for (lhs, rhs) in cases {
        for op in COMPARISONS {
            assert_eq!(compare(op, lhs, rhs), None, "{lhs:?} {op:?} {rhs:?}");
        }
    }
}

#[test]
fn every_interval_verdict_agrees_with_finite_concrete_members() {
    let intervals = [
        IntInterval::top(),
        IntInterval::lower(-1),
        IntInterval::lower(1),
        IntInterval::upper(-1),
        IntInterval::upper(1),
        IntInterval::exact(-1),
        IntInterval::exact(0),
        IntInterval::exact(1),
        IntInterval {
            lower: Some(-1),
            upper: Some(1),
        },
    ];
    let contains = |interval: IntInterval, value| {
        interval.lower.is_none_or(|lower| lower <= value)
            && interval.upper.is_none_or(|upper| value <= upper)
    };
    let mut checked = 0;
    for lhs in intervals {
        for rhs in intervals {
            for op in COMPARISONS {
                let Some(verdict) = compare(op, lhs, rhs) else {
                    continue;
                };
                let mut witnesses = 0;
                for x in -3..=3 {
                    for y in -3..=3 {
                        if !contains(lhs, x) || !contains(rhs, y) {
                            continue;
                        }
                        let concrete = match op {
                            ChcOp::Lt => x < y,
                            ChcOp::Le => x <= y,
                            ChcOp::Gt => x > y,
                            ChcOp::Ge => x >= y,
                            ChcOp::Eq => x == y,
                            ChcOp::Ne => x != y,
                            _ => unreachable!(),
                        };
                        assert_eq!(verdict, concrete, "{lhs:?} {op:?} {rhs:?} at {x},{y}");
                        witnesses += 1;
                    }
                }
                assert!(witnesses > 0, "each reported comparison is exercised");
                checked += witnesses;
            }
        }
    }
    assert!(checked > 100);
}

fn unconstrained_pair_problem(constraint: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![variable("x"), variable("y")]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(pred, vec![variable("u"), variable("v")])],
        Some(constraint),
    )));
    problem.validate().expect("well-typed original CHC");
    problem
}

fn exact_formula(problem: ChcProblem) -> ChcExpr {
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let queries: Vec<_> = solver.problem.queries().collect();
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    // Real exact expansion and simplification, with no SMT call.
    solver.acyclic_symbolic_query(&queries, &mut names).unwrap()
}

#[test]
fn exact_query_preserves_a_reachable_unconstrained_disequality() {
    let formula = exact_formula(unconstrained_pair_problem(ChcExpr::not(ChcExpr::eq(
        variable("u"),
        variable("v"),
    ))));
    let variables = formula.vars();
    assert!(variables.len() <= 4);
    let mut satisfying = 0;
    for mask in 0..(1_usize << variables.len()) {
        let model = variables
            .iter()
            .enumerate()
            .map(|(index, var)| {
                (
                    var.name.clone(),
                    SmtValue::Int(((mask >> index) & 1) as i128),
                )
            })
            .collect();
        match crate::expr::evaluate_expr(&formula, &model) {
            Some(SmtValue::Bool(true)) => satisfying += 1,
            Some(SmtValue::Bool(false)) => {}
            other => panic!("closed integer test formula must evaluate: {other:?}"),
        }
    }
    assert!(
        satisfying > 0,
        "P contains every pair, including 0 != 1; got {formula}"
    );
}

#[test]
fn exact_query_still_refutes_a_genuinely_contradictory_pair() {
    let equality = ChcExpr::eq(variable("u"), variable("v"));
    let formula = exact_formula(unconstrained_pair_problem(ChcExpr::and(
        equality.clone(),
        ChcExpr::not(equality),
    )));
    assert_eq!(formula, ChcExpr::Bool(false));
}
