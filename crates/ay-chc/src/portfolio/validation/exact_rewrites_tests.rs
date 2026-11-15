// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Safe validation may use the verifier's solve-time rewrites only when they
//! are exact for the submitted model; every original clause stays checked.

use super::*;
use crate::portfolio::accept::AcceptDecision;
use crate::portfolio::PortfolioConfig;
use crate::ChcParser;

// Two nullary query predicates behind an intermediate nullary link, plus an
// arithmetic ITE transition (the s_split_12 clause shape) that the
// rewriting verifier case-splits.
const SOURCE: &str = r#"
(set-logic HORN)
(declare-rel State (Int Int))
(declare-rel error_p0 ())
(declare-rel error ())
(declare-rel error2 ())
(declare-var x Int)
(declare-var y Int)
(declare-var xp Int)
(declare-var yp Int)
(rule (=> (and (= x 0) (= y 0)) (State x y)))
(rule (=> (and (State x y) (= xp (+ x 1)) (= yp (ite (= (mod x 2) 0) (+ y 1) y))) (State xp yp)))
(rule (=> (and (State x y) (< y 0)) error_p0))
(rule (=> error_p0 error))
(rule (=> (and (State x y) (< x 0)) error2))
(query error)
(query error2)
"#;

fn solver(strict_proofs: bool) -> PortfolioSolver {
    let problem = ChcParser::parse(SOURCE).unwrap();
    assert_eq!(problem.clauses().len(), 7);
    PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: Vec::new(),
            parallel: false,
            enable_preprocessing: false,
            strict_proofs,
            ..PortfolioConfig::default()
        },
    )
}

/// `State := state`, `error_p0 := p0`, `error := e`, `error2 := e2`.
fn model(solver: &PortfolioSolver, state: ChcExpr, p0: bool, e: bool, e2: bool) -> InvariantModel {
    let problem = &solver.original_problem;
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        problem.lookup_predicate("State").unwrap(),
        PredicateInterpretation::new(vec![x, y], state),
    );
    for (name, value) in [("error_p0", p0), ("error", e), ("error2", e2)] {
        model.set(
            problem.lookup_predicate(name).unwrap(),
            PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(value)),
        );
    }
    model.individually_inductive = true;
    model.convergence_proven = true;
    model
}

/// The inductive invariant `x >= 0 ∧ y >= 0`.
fn invariant() -> ChcExpr {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    ChcExpr::and(
        ChcExpr::ge(x, ChcExpr::Int(0)),
        ChcExpr::ge(y, ChcExpr::Int(0)),
    )
}

fn validate_all_modes(solver: &PortfolioSolver, model: &InvariantModel) -> [bool; 2] {
    [ValidationBudget::Standard, ValidationBudget::PerRule].map(|mode| {
        let translated = solver.back_translate_safe_model(model).unwrap();
        solver
            .validate_safe_with_mode_pre_translated(translated, mode)
            .is_ok()
    })
}

#[test]
fn rewrites_are_exact_only_when_every_nullary_query_predicate_is_false() {
    let solver = solver(true);
    let good = model(&solver, invariant(), false, false, false);
    assert!(solver.solve_time_rewrites_exact_for_model(&good));
    // The intermediate link is not a query predicate; its value does not
    // decide exactness (the expansion keeps its obligations).
    let p0_true = model(&solver, invariant(), true, false, false);
    assert!(solver.solve_time_rewrites_exact_for_model(&p0_true));
    for (e, e2) in [(true, false), (false, true), (true, true)] {
        let bad = model(&solver, invariant(), false, e, e2);
        assert!(!solver.solve_time_rewrites_exact_for_model(&bad));
    }
    // A formula that merely denotes false is not accepted syntactically.
    let mut not_true = good.clone();
    not_true.set(
        solver.original_problem.lookup_predicate("error").unwrap(),
        PredicateInterpretation::new(Vec::new(), ChcExpr::not(ChcExpr::Bool(true))),
    );
    assert!(!solver.solve_time_rewrites_exact_for_model(&not_true));
    // A missing interpretation is never exact.
    let mut missing = InvariantModel::new();
    for (pid, interp) in good.iter() {
        if Some(*pid) != solver.original_problem.lookup_predicate("error2") {
            missing.set(*pid, interp.clone());
        }
    }
    assert!(!solver.solve_time_rewrites_exact_for_model(&missing));
}

#[test]
fn rewrites_are_exact_without_nullary_queries() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel S (Int))
(declare-var x Int)
(rule (=> (= x 0) (S x)))
(rule (=> (and (S x) (< x 0)) false))
"#,
    )
    .unwrap();
    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: Vec::new(),
            parallel: false,
            enable_preprocessing: false,
            ..PortfolioConfig::default()
        },
    );
    assert!(solver.solve_time_rewrites_exact_for_model(&InvariantModel::new()));
}

#[test]
fn exact_valid_model_passes_on_rewritten_clauses() {
    for strict_proofs in [false, true] {
        let solver = solver(strict_proofs);
        let good = model(&solver, invariant(), false, false, false);
        assert!(solver.solve_time_rewrites_exact_for_model(&good));
        assert_eq!(validate_all_modes(&solver, &good), [true, true]);
    }
}

#[test]
fn false_query_predicates_cannot_hide_a_reachable_error() {
    // `error = error2 = false`, so the rewritten clauses are used, but the
    // state interpretation admits `y < 0`: the defining clause
    // `State ∧ y < 0 → error_p0` is violated (error_p0 = false) and must be
    // caught. Same for `State ∧ x < 0 → error2` with the error2 query
    // predicate itself expanded.
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    for state in [
        ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
        ChcExpr::ge(y, ChcExpr::Int(0)),
        ChcExpr::Bool(true),
    ] {
        for strict_proofs in [false, true] {
            let solver = solver(strict_proofs);
            let bad = model(&solver, state.clone(), false, false, false);
            assert!(solver.solve_time_rewrites_exact_for_model(&bad));
            assert_eq!(validate_all_modes(&solver, &bad), [false, false], "{state}");
        }
    }
}

#[test]
fn false_query_predicate_cannot_hide_a_true_intermediate_link() {
    // error_p0 = true with error = false violates `error_p0 → error`; after
    // expansion that obligation is the query `error_p0 → false`.
    for strict_proofs in [false, true] {
        let solver = solver(strict_proofs);
        let bad = model(&solver, invariant(), true, false, false);
        assert!(solver.solve_time_rewrites_exact_for_model(&bad));
        assert_eq!(validate_all_modes(&solver, &bad), [false, false]);
    }
}

#[test]
fn true_query_predicate_is_rejected_on_original_clauses() {
    // Any non-false query predicate keeps the original clauses, where
    // `error → false` / `error2 → false` refute it (f40f8c9d8).
    for (e, e2) in [(true, false), (false, true), (true, true)] {
        for strict_proofs in [false, true] {
            let solver = solver(strict_proofs);
            let bad = model(&solver, invariant(), false, e, e2);
            assert!(!solver.solve_time_rewrites_exact_for_model(&bad));
            assert_eq!(validate_all_modes(&solver, &bad), [false, false]);
            let decision = solver.accept_or_reject(PortfolioResult::Safe(bad), false, "PDR", 0);
            assert!(
                matches!(decision, AcceptDecision::Reject),
                "got {decision:?}"
            );
        }
    }
}

#[test]
fn acceptance_keeps_the_exact_original_model() {
    for strict_proofs in [false, true] {
        let solver = solver(strict_proofs);
        let good = model(&solver, invariant(), false, false, false);
        let expected = format!("{good:?}");
        let decision = solver.accept_or_reject(PortfolioResult::Safe(good), false, "PDR", 0);
        let AcceptDecision::Accept(PortfolioResult::Safe(checked)) = decision else {
            panic!("expected the valid model to be accepted, got {decision:?}");
        };
        assert_eq!(format!("{checked:?}"), expected);
    }
}

// aeval-benchmarks/multi-phase/s_split_12_000 (CHC-COMP 2026), verbatim.
const S_SPLIT_12: &str = r#"
(set-logic HORN)
(declare-fun |inv| ( Int Int Int ) Bool)
(declare-fun |fail| ( ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) )
  (=> (and (and (= B 0) (= C 0) (= A 0))) (inv A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
  (=> (and (inv B A C)
           (let ((a!1 (= E (ite (= (mod B 2) 0) (+ 1 A) A)))
                 (a!2 (= F (ite (= (mod B 2) 0) C (+ 1 C)))))
             (and a!1 a!2 (= D (+ 1 B)))))
      (inv D E F))))
(assert (forall ( (A Int) (B Int) (C Int) )
  (=> (and (inv A B C) (and (not (= B C)) (= A 1342342))) fail)))
(assert (forall ( (CHC_COMP_UNUSED Bool) ) (=> (and fail true) false)))
(check-sat)
"#;

/// The Safe model PDR returned for s_split_12 in the regressed run: the
/// invariant is inductive only by parity (`a0 = a1 + a2 ∧ a2 ≤ a1 ≤ a2 + 1`
/// forces `a1 = a2` exactly when `a0` is even). On the unsplit ITE
/// transition every verifier fallback returns Unknown and the model was
/// rejected; each exact ITE case is decided directly.
fn s_split_12_model(solver: &PortfolioSolver, inv: &str, fail: &str) -> InvariantModel {
    InvariantModel::parse_smtlib(
        &format!(
            "(define-fun |fail| () Bool {fail})\n\
             (define-fun |inv| ((a0 Int) (a1 Int) (a2 Int)) Bool {inv})\n"
        ),
        &solver.original_problem,
    )
    .unwrap()
}

#[test]
fn s_split_12_parity_model_validates_on_exact_case_split() {
    const GOOD: &str =
        "(and (= (+ (+ a0 (- a1)) (- a2)) 0) (<= a1 (+ a2 1)) (<= a1 a0) (<= a2 a1))";
    // Admits a1 < a2, e.g. (1342342, 0, 1342342): the error clause fires.
    const BAD_QUERY: &str = "(and (= (+ (+ a0 (- a1)) (- a2)) 0) (<= a1 (+ a2 1)) (<= a1 a0))";
    // Not inductive: (0,0,0) steps to (1,1,0).
    const BAD_STEP: &str = "(and (= (+ (+ a0 (- a1)) (- a2)) 0) (= a1 a2))";
    let problem = ChcParser::parse(S_SPLIT_12).unwrap();
    assert_eq!(problem.clauses().len(), 4);
    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: Vec::new(),
            parallel: false,
            enable_preprocessing: false,
            strict_proofs: true,
            ..PortfolioConfig::default()
        },
    );
    let good = s_split_12_model(&solver, GOOD, "false");
    assert!(solver.solve_time_rewrites_exact_for_model(&good));
    assert_eq!(validate_all_modes(&solver, &good), [true, true]);
    for inv in [BAD_QUERY, BAD_STEP] {
        let bad = s_split_12_model(&solver, inv, "false");
        assert!(solver.solve_time_rewrites_exact_for_model(&bad));
        assert_eq!(validate_all_modes(&solver, &bad), [false, false], "{inv}");
    }
    let fail_true = s_split_12_model(&solver, GOOD, "true");
    assert!(!solver.solve_time_rewrites_exact_for_model(&fail_true));
    assert_eq!(validate_all_modes(&solver, &fail_true), [false, false]);
}
