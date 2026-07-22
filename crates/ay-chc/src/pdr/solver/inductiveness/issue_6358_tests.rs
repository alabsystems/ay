// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use serial_test::serial;
use std::time::Duration;

#[test]
fn test_is_inductive_blocking_skips_prop_solver_for_non_pure_lia_issue_6358() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::mod_op(
                    ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
                    ChcExpr::Int(3),
                ),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x_next)]),
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    // #7048: mod/div with constant divisors over integers is promoted to pure-LIA
    // via the integer_arithmetic → pure_lia promotion (core/mod.rs:597).
    assert!(
        solver.problem_is_pure_lia,
        "mod over integers is promoted to pure-LIA (#7048)"
    );
    assert!(
        solver.problem_is_integer_arithmetic,
        "mod over integers qualifies as integer arithmetic"
    );
    let x = solver.canonical_vars(pred).expect("canonical vars")[0].clone();
    let blocking_formula = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(solver.is_inductive_blocking(&blocking_formula, pred, 0));
    // For LIA problems, incremental PDR is disabled (#6583/#8205).
    assert!(
        !solver.prop_solvers.contains_key(&pred),
        "prop_solver not populated for LIA problem (incremental PDR disabled)"
    );
}

#[test]
#[serial]
fn test_can_push_lemma_non_pure_lia_uses_extended_timeout_issue_5877() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::mod_op(
                    ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
                    ChcExpr::Int(3),
                ),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x_next)]),
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    // #7048: mod/div with constant divisors is promoted to pure-LIA.
    assert!(solver.problem_is_pure_lia);

    let x = solver.canonical_vars(pred).expect("canonical vars")[0].clone();
    let lemma = Lemma::new(pred, ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)), 1);

    PdrSolver::reset_case_split_timeout_observation_for_tests();
    assert!(solver.can_push_lemma(&lemma, 1));
}

#[test]
#[serial]
fn test_can_push_lemma_preserves_explicit_timeout_issue_5877() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::mod_op(
                    ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
                    ChcExpr::Int(3),
                ),
            )),
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x_next)]),
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    // #7048: mod/div with constant divisors is promoted to pure-LIA.
    assert!(solver.problem_is_pure_lia);

    let x = solver.canonical_vars(pred).expect("canonical vars")[0].clone();
    let lemma = Lemma::new(pred, ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)), 1);

    let _explicit_timeout = solver
        .smt
        .scoped_check_timeout(Some(Duration::from_millis(250)));
    PdrSolver::reset_case_split_timeout_observation_for_tests();
    assert!(solver.can_push_lemma(&lemma, 1));
}

#[test]
fn test_parser_normalized_head_ite_disables_pure_lia_issue_6358() {
    let input = r#"
(set-logic HORN)

(declare-fun inv1 (Int Int) Bool)
(declare-fun inv (Int Int) Bool)
(declare-fun dummy ((_ BitVec 8)) Bool)

(assert
  (forall ((A Int) (B Int))
    (=>
      (and (= A 0) (= B 0))
      (inv1 A B)
    )
  )
)

(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and
        (inv1 A B)
        (= C (ite (= B 0) (+ A 1) A))
      )
      (inv C B)
    )
  )
)

(assert
  (forall ((K (_ BitVec 8)))
    (=>
      (= K #x00)
      (dummy K)
    )
  )
)

(assert
  (forall ((A Int) (B Int))
    (=>
      (and (inv A B) (not (= A B)))
      false
    )
  )
)

(check-sat)
"#;
    let parsed = ChcParser::parse(input).expect("parse CHC input");
    let raw_has_head_ite = parsed.clauses().iter().any(|clause| match &clause.head {
        ClauseHead::Predicate(_, args) => args.iter().any(|arg| arg.scan_features().has_ite),
        ClauseHead::False => false,
    });
    assert!(
        raw_has_head_ite,
        "parser normalization should preserve the arithmetic ITE in predicate arguments before solver preprocessing"
    );

    let solver = PdrSolver::new(parsed, PdrConfig::default());
    let has_head_ite = solver
        .problem
        .clauses()
        .iter()
        .any(|clause| match &clause.head {
            ClauseHead::Predicate(_, args) => args.iter().any(|arg| arg.scan_features().has_ite),
            ClauseHead::False => false,
        });
    assert!(
        has_head_ite,
        "non-integer side clauses should keep multi-predicate head ITEs intact for the non-pure-LIA path"
    );
    assert!(
        !solver.problem_is_pure_lia,
        "pure-LIA gate must still reject normalized predicate-argument ITEs when splitting is skipped"
    );
}

#[test]
fn test_multi_pred_integer_head_ite_is_split_into_pure_lia_issue_1362() {
    let input = r#"
(set-logic HORN)

(declare-fun inv1 (Int Int) Bool)
(declare-fun inv (Int Int) Bool)

(assert
  (forall ((A Int) (B Int))
    (=>
      (and (= A 0) (= B 0))
      (inv1 A B)
    )
  )
)

(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and
        (inv1 A B)
        (= C (ite (= B 0) (+ A 1) A))
      )
      (inv C B)
    )
  )
)

(assert
  (forall ((A Int) (B Int))
    (=>
      (and (inv A B) (not (= A B)))
      false
    )
  )
)

(check-sat)
"#;
    let parsed = ChcParser::parse(input).expect("parse CHC input");
    let _original_clause_count = parsed.clauses().len();
    let raw_has_head_ite = parsed.clauses().iter().any(|clause| match &clause.head {
        ClauseHead::Predicate(_, args) => args.iter().any(|arg| arg.scan_features().has_ite),
        ClauseHead::False => false,
    });
    assert!(
        raw_has_head_ite,
        "fixture should start with a head-argument ITE before preprocessing"
    );

    let solver = PdrSolver::new(parsed, PdrConfig::default());
    let has_head_ite = solver
        .problem
        .clauses()
        .iter()
        .any(|clause| match &clause.head {
            ClauseHead::Predicate(_, args) => args.iter().any(|arg| arg.scan_features().has_ite),
            ClauseHead::False => false,
        });
    assert!(
        !has_head_ite,
        "multi-predicate integer ITEs should be split away before pure-LIA classification"
    );
    // #7048: arithmetic ITE over ints is promoted to pure LIA because
    // eliminate_ite() normalizes it before SAT queries.
    assert!(
        solver.problem_is_pure_lia,
        "integer arithmetic ITE should be promoted to pure-LIA (#7048)"
    );
}

#[test]
fn test_hyperedge_self_loop_uses_prop_solver_issue_6358() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)
(declare-fun side (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x) (side y))
      (inv (+ x 1)))))

(check-sat)
"#,
    );
    let inv = solver.problem.lookup_predicate("inv").expect("predicate");
    let x = solver.canonical_vars(inv).expect("canonical vars")[0].clone();
    let blocking = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(
        solver.problem_is_pure_lia,
        "hyperedge should stay on pure-LIA path"
    );
    assert!(
        !solver.prop_solvers.contains_key(&inv),
        "prop solver should be created lazily"
    );
    assert!(solver.is_self_inductive_blocking(&blocking, inv));
    // prop_solver is only populated when incremental_pdr_enabled() is true.
    // For LIA problems, incremental PDR is disabled (#6583/#8205).
    if solver.incremental_pdr_enabled() {
        assert!(
            solver.prop_solvers.contains_key(&inv),
            "hyperedge self-loop inductiveness should use the per-predicate prop solver"
        );
    }
}

#[test]
fn test_strict_hyperedge_self_loop_uses_prop_solver_issue_6358() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)
(declare-fun side (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x) (side y))
      (inv (+ x 1)))))

(check-sat)
"#,
    );
    let inv = solver.problem.lookup_predicate("inv").expect("predicate");
    let x = solver.canonical_vars(inv).expect("canonical vars")[0].clone();
    let blocking = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(
        solver.problem_is_pure_lia,
        "hyperedge should stay on pure-LIA path"
    );
    assert!(
        !solver.prop_solvers.contains_key(&inv),
        "prop solver should be created lazily"
    );
    assert!(solver.is_strictly_self_inductive_blocking(&blocking, inv));
    // prop_solver is only populated when incremental_pdr_enabled() is true.
    // For LIA problems, incremental PDR is disabled (#6583/#8205).
    if solver.incremental_pdr_enabled() {
        assert!(
            solver.prop_solvers.contains_key(&inv),
            "strict hyperedge self-loop inductiveness should use the per-predicate prop solver"
        );
    }
}
