// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::monolithic::{
    check_obligations, single_predicate_obligations, with_forced_smt, ForcedSmt, ObligationKind,
    PassBoundary, MONOLITHIC_CHECK_TIMEOUT,
};
use super::*;
use crate::portfolio::accept::AcceptDecision;
use crate::portfolio::PortfolioConfig;
use crate::smt::dag_smtlib::{count_dag, DagCaps};
use crate::ChcParser;
use std::sync::Arc;

/// `x = 0` initially, `x' = x + 1`, bad: `x < 0`.
const COUNTER: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (= xp (+ x 1))) (Inv xp)))
(rule (=> (and (Inv x) (< x 0)) false))
"#;

/// A Real phase counter with ITE updates, IMC-shaped: `pc` goes 0..3 and
/// stays, `r` is bumped once at phase 2; bad: phase 3 with `r ≠ 1`.
const PHASES: &str = r#"
(set-logic HORN)
(declare-rel Inv (Real Real))
(declare-var pc Real)
(declare-var r Real)
(declare-var pcp Real)
(declare-var rp Real)
(rule (=> (and (= pc 0.0) (= r 0.0)) (Inv pc r)))
(rule (=> (and (Inv pc r)
               (= pcp (ite (< pc 3.0) (+ pc 1.0) pc))
               (= rp (ite (= pc 2.0) (+ r 1.0) r)))
          (Inv pcp rp)))
(rule (=> (and (Inv pc r) (>= pc 3.0) (not (= r 1.0))) false))
"#;

const TWO_PREDICATES: &str = r#"
(set-logic HORN)
(declare-rel A (Int))
(declare-rel B (Int))
(declare-var x Int)
(rule (=> (= x 0) (A x)))
(rule (=> (A x) (B x)))
(rule (=> (and (B x) (< x 0)) false))
"#;

const NONLINEAR: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)
(declare-var y Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (Inv y)) (Inv (+ x y))))
(rule (=> (and (Inv x) (< x 0)) false))
"#;

fn int(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn real(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Real)
}

fn rat(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

fn counter_model(problem: &ChcProblem, formula: impl Fn(ChcExpr) -> ChcExpr) -> InvariantModel {
    let inv = problem.lookup_predicate("Inv").unwrap();
    let x = int("__p0_a0");
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![x.clone()], formula(ChcExpr::var(x))),
    );
    model
}

/// The exact reachable set of [`PHASES`], one disjunct per phase.
fn phases_model(problem: &ChcProblem, final_r: i64) -> InvariantModel {
    let inv = problem.lookup_predicate("Inv").unwrap();
    let pc = real("__p0_a0");
    let r = real("__p0_a1");
    let phase = |p: i64, v: i64| {
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(pc.clone()), rat(p)),
            ChcExpr::eq(ChcExpr::var(r.clone()), rat(v)),
        )
    };
    let formula = ChcExpr::or_all([phase(0, 0), phase(1, 0), phase(2, 0), phase(3, final_r)]);
    let mut model = InvariantModel::new();
    model.set(inv, PredicateInterpretation::new(vec![pc, r], formula));
    model
}

fn verdict(problem: &ChcProblem, model: &InvariantModel) -> MonolithicVerdict {
    let obligations = single_predicate_obligations(problem, model).expect("single-predicate shape");
    check_obligations(
        &obligations,
        MONOLITHIC_CHECK_TIMEOUT,
        PassBoundary {
            cancellation: None,
            deadline: None,
            stopped: || false,
        },
    )
}

fn solver(source: &str) -> PortfolioSolver {
    PortfolioSolver::new(
        ChcParser::parse(source).unwrap(),
        PortfolioConfig {
            engines: Vec::new(),
            parallel: false,
            enable_preprocessing: false,
            ..PortfolioConfig::default()
        },
    )
}

#[test]
fn obligations_cover_every_original_clause_by_kind() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    let obligations = single_predicate_obligations(&problem, &model).unwrap();
    let kinds: Vec<_> = obligations.iter().map(|o| (o.clause_idx, o.kind)).collect();
    assert_eq!(
        kinds,
        vec![
            (0, ObligationKind::Initiation),
            (1, ObligationKind::Consecution),
            (2, ObligationKind::Safety),
        ]
    );
    // No binder of the interpretation survives instantiation.
    for obligation in &obligations {
        assert!(
            obligation.query.vars().iter().all(|v| v.name != "__p0_a0"),
            "binder left free in {}",
            obligation.query
        );
    }
}

#[test]
fn monolithic_accepts_an_inductive_safe_model() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    assert!(matches!(
        verdict(&problem, &model),
        MonolithicVerdict::Valid
    ));
}

#[test]
fn monolithic_rejects_a_non_inductive_model() {
    // 0 ≤ x ≤ 5 holds initially and excludes x < 0, but x = 5 steps out.
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model = counter_model(&problem, |x| {
        ChcExpr::and(
            ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
            ChcExpr::le(x, ChcExpr::Int(5)),
        )
    });
    match verdict(&problem, &model) {
        MonolithicVerdict::Invalid(reason) => assert!(reason.contains("Consecution"), "{reason}"),
        other => panic!("non-inductive model must be refuted, got {other:?}"),
    }
}

#[test]
fn monolithic_rejects_a_model_that_does_not_exclude_the_query() {
    // x ≥ -1 is initiated and inductive, but admits the bad state x = -1.
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(-1)));
    match verdict(&problem, &model) {
        MonolithicVerdict::Invalid(reason) => assert!(reason.contains("Safety"), "{reason}"),
        other => panic!("unsafe model must be refuted, got {other:?}"),
    }
}

#[test]
fn monolithic_rejects_a_model_that_misses_the_initial_states() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(1)));
    match verdict(&problem, &model) {
        MonolithicVerdict::Invalid(reason) => assert!(reason.contains("Initiation"), "{reason}"),
        other => panic!("non-initiated model must be refuted, got {other:?}"),
    }
}

#[test]
fn monolithic_decides_ite_transitions_over_reals_without_splitting() {
    let problem = ChcParser::parse(PHASES).unwrap();
    assert!(matches!(
        verdict(&problem, &phases_model(&problem, 1)),
        MonolithicVerdict::Valid
    ));
    // Phase 3 with r = 2 is not reachable from phase 2 with r = 0 (not
    // inductive), and its query obligation is satisfiable as well.
    assert!(matches!(
        verdict(&problem, &phases_model(&problem, 2)),
        MonolithicVerdict::Invalid(_)
    ));
}

#[test]
fn shape_is_one_predicate_with_linear_clauses_only() {
    let two = ChcParser::parse(TWO_PREDICATES).unwrap();
    let mut model = InvariantModel::new();
    for name in ["A", "B"] {
        let x = int("__a");
        model.set(
            two.lookup_predicate(name).unwrap(),
            PredicateInterpretation::new(
                vec![x.clone()],
                ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)),
            ),
        );
    }
    assert!(single_predicate_obligations(&two, &model).is_none());

    let nonlinear = ChcParser::parse(NONLINEAR).unwrap();
    let model = counter_model(&nonlinear, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    assert!(single_predicate_obligations(&nonlinear, &model).is_none());
}

#[test]
fn shape_leaves_ill_formed_models_to_the_per_rule_validator() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    // A free variable outside the binders.
    let free = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::var(int("captured"))));
    assert!(single_predicate_obligations(&problem, &free).is_none());
    // A missing interpretation.
    assert!(single_predicate_obligations(&problem, &InvariantModel::new()).is_none());
    // #5930: a Real-argument predicate with a Real-free interpretation.
    let phases = ChcParser::parse(PHASES).unwrap();
    let mut bool_only = InvariantModel::new();
    bool_only.set(
        phases.lookup_predicate("Inv").unwrap(),
        PredicateInterpretation::new(vec![real("__p0_a0"), real("__p0_a1")], ChcExpr::Bool(true)),
    );
    assert!(single_predicate_obligations(&phases, &bool_only).is_none());
}

#[test]
fn instantiation_keeps_the_invariant_dag_shared() {
    // A Real term shared 2^12 times by doubling one node: the obligations
    // must stay a small DAG so the Verification-lane script is `let`-printed.
    let problem = ChcParser::parse(PHASES).unwrap();
    let inv = problem.lookup_predicate("Inv").unwrap();
    let pc = real("__p0_a0");
    let r = real("__p0_a1");
    let mut node = Arc::new(ChcExpr::var(r.clone()));
    for _ in 0..12 {
        node = Arc::new(ChcExpr::Op(
            crate::ChcOp::Add,
            vec![Arc::clone(&node), Arc::clone(&node)],
        ));
    }
    let scaled = Arc::try_unwrap(node).unwrap_or_else(|shared| (*shared).clone());
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(pc.clone()), rat(0)),
        ChcExpr::ge(scaled, rat(0)),
    );
    let mut model = InvariantModel::new();
    model.set(inv, PredicateInterpretation::new(vec![pc, r], formula));
    let obligations = single_predicate_obligations(&problem, &model).unwrap();
    let caps = DagCaps {
        max_unique_nodes: 1 << 20,
        max_depth: 512,
    };
    for obligation in &obligations {
        let stats = count_dag(&[&obligation.query], caps).unwrap();
        assert!(
            stats.unique_nodes < 200,
            "clause {} obligation lost its sharing: {} unique nodes",
            obligation.clause_idx,
            stats.unique_nodes
        );
    }
}

#[test]
fn acceptance_uses_the_monolithic_verdict_for_single_predicate_systems() {
    let solver = solver(COUNTER);
    let problem = solver.original_problem.clone();
    let good = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    assert!(matches!(
        solver.validate_safe_monolithic(&good),
        Some(MonolithicVerdict::Valid)
    ));
    assert!(matches!(
        solver.accept_or_reject(PortfolioResult::Safe(good), true, "IMC", 0),
        AcceptDecision::Accept(PortfolioResult::Safe(_))
    ));
    for bad in [
        counter_model(&problem, |x| {
            ChcExpr::and(
                ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
                ChcExpr::le(x, ChcExpr::Int(5)),
            )
        }),
        counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(-1))),
    ] {
        assert!(matches!(
            solver.accept_or_reject(PortfolioResult::Safe(bad), true, "IMC", 0),
            AcceptDecision::Reject
        ));
    }
}

#[test]
fn acceptance_of_other_shapes_is_unchanged() {
    let solver = solver(TWO_PREDICATES);
    let problem = solver.original_problem.clone();
    let mut model = InvariantModel::new();
    for name in ["A", "B"] {
        let x = int("__a");
        model.set(
            problem.lookup_predicate(name).unwrap(),
            PredicateInterpretation::new(
                vec![x.clone()],
                ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)),
            ),
        );
    }
    assert!(solver.validate_safe_monolithic(&model).is_none());
    assert!(matches!(
        solver.accept_or_reject(PortfolioResult::Safe(model), true, "PDR", 0),
        AcceptDecision::Accept(PortfolioResult::Safe(_))
    ));
}

/// #5803 / #5381 on the monolithic path: when the SMT check of an Int
/// obligation answers a false UNSAT, the concrete cross-check finds the
/// counterexample and the model is refuted, not accepted (review of
/// 54243b804: Step 4.4 had dropped the per-rule validator's concrete check).
#[test]
fn a_false_unsat_is_refuted_by_the_concrete_cross_check() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    // Admits the bad state x = -1: the Safety obligation is satisfiable.
    let unsafe_model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(-1)));
    match with_forced_smt(ForcedSmt::Unsat, || verdict(&problem, &unsafe_model)) {
        MonolithicVerdict::Invalid(reason) => assert!(reason.contains("Safety"), "{reason}"),
        other => panic!("a false UNSAT on Safety must be refuted concretely, got {other:?}"),
    }
    // Initiated and safe, but x = 5 steps out: Consecution is satisfiable.
    let non_inductive = counter_model(&problem, |x| {
        ChcExpr::and(
            ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
            ChcExpr::le(x, ChcExpr::Int(5)),
        )
    });
    match with_forced_smt(ForcedSmt::Unsat, || verdict(&problem, &non_inductive)) {
        MonolithicVerdict::Invalid(reason) => {
            assert!(reason.contains("Consecution"), "{reason}")
        }
        other => panic!("a false UNSAT on Consecution must be refuted concretely, got {other:?}"),
    }
    // A correct model has no concrete counterexample: still accepted.
    let good = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    assert!(matches!(
        with_forced_smt(ForcedSmt::Unsat, || verdict(&problem, &good)),
        MonolithicVerdict::Valid
    ));
}

/// The same false UNSAT through `accept_or_reject`: rejected, never
/// published as Safe.
#[test]
fn acceptance_rejects_a_false_unsat_the_concrete_check_refutes() {
    let solver = solver(COUNTER);
    let problem = solver.original_problem.clone();
    let unsafe_model = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(-1)));
    assert!(matches!(
        with_forced_smt(ForcedSmt::Unsat, || solver.accept_or_reject(
            PortfolioResult::Safe(unsafe_model),
            true,
            "IMC",
            0
        )),
        AcceptDecision::Reject
    ));
}

/// A deadline already passed decides nothing: the pass answers Unknown
/// without a check, so it never runs past the end of the solve.
#[test]
fn a_passed_solve_deadline_decides_nothing() {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let good = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    let obligations = single_predicate_obligations(&problem, &good).unwrap();
    let passed = ay_core::time::Instant::now();
    match check_obligations(
        &obligations,
        MONOLITHIC_CHECK_TIMEOUT,
        PassBoundary {
            cancellation: None,
            deadline: Some(passed),
            stopped: || false,
        },
    ) {
        MonolithicVerdict::Unknown(reason) => assert!(reason.contains("boundary"), "{reason}"),
        other => panic!("a passed deadline must leave the model undecided, got {other:?}"),
    }
    // A cancelled solve likewise.
    let token = crate::CancellationToken::new();
    token.cancel();
    assert!(matches!(
        check_obligations(
            &obligations,
            MONOLITHIC_CHECK_TIMEOUT,
            PassBoundary {
                cancellation: Some(&token),
                deadline: None,
                stopped: || false,
            },
        ),
        MonolithicVerdict::Unknown(_)
    ));
}

/// The fallback path: when a monolithic check is undecided, the per-rule
/// validator (Step 5) decides, accepting a correct model and rejecting
/// non-inductive and unsafe ones exactly as without Step 4.4.
#[test]
fn an_undecided_monolithic_check_falls_back_to_the_per_rule_validator() {
    let solver = solver(COUNTER);
    let problem = solver.original_problem.clone();
    let good = counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(0)));
    with_forced_smt(ForcedSmt::Undecided, || {
        assert!(matches!(
            solver.validate_safe_monolithic(&good),
            Some(MonolithicVerdict::Unknown(_))
        ));
        assert!(matches!(
            solver.accept_or_reject(PortfolioResult::Safe(good.clone()), true, "IMC", 0),
            AcceptDecision::Accept(PortfolioResult::Safe(_))
        ));
        for bad in [
            counter_model(&problem, |x| {
                ChcExpr::and(
                    ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
                    ChcExpr::le(x, ChcExpr::Int(5)),
                )
            }),
            counter_model(&problem, |x| ChcExpr::ge(x, ChcExpr::Int(-1))),
        ] {
            assert!(matches!(
                solver.accept_or_reject(PortfolioResult::Safe(bad), true, "IMC", 0),
                AcceptDecision::Reject
            ));
        }
    });
}
