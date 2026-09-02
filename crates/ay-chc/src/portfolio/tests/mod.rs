#![allow(clippy::unwrap_used)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portfolio solver tests — validation, solving, engine-specific, panic/spawn, BV regression.

use super::engines::translate_trl_singleloop_safe_model;
use super::schedule::{
    FORCE_SOLVER_THREAD_SPAWN_FAILURE, PARALLEL_TEST_DISABLE_LANE_TIMER,
    PARALLEL_TEST_PREPARE_DELAY,
};
use super::*;
use crate::bmc::BmcConfig;
use crate::cegar::{CegarConfig, CegarResult};
use crate::decomposition::DecompositionConfig;
use crate::engine_result::build_single_pred_model;
use crate::engine_result::ChcEngineResult;
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lawi::LawiConfig;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PredicateInterpretation,
};
use crate::tpa::{TpaConfig, TpaResult};
use crate::trl::TrlConfig;
use crate::CancellationToken;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ntest::timeout;
use serial_test::serial;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

mod bv_regression;
mod engine_specific;
mod lemma_transfer;
mod panic_and_spawn;
mod solving;
mod trivial_solver;
mod validation;

fn create_safe_problem() -> ChcProblem {
    // Safe: x = 0 => Inv(x), Inv(x) /\ x < 5 => Inv(x+1), Inv(x) /\ x >= 10 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_unsafe_problem() -> ChcProblem {
    // Unsafe: x = 0 => Inv(x), Inv(x) => Inv(x+1), Inv(x) /\ x >= 5 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Create a multi-predicate chain problem: P1 -> P2
/// P1(x) := x = 0
/// P2(x) := P1(x-1) (i.e., x = 1)
/// Query: P2(x) /\ x > 10 => false (should be safe)
fn create_multi_predicate_chain_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));

    // P1(x-1) => P2(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            p1,
            vec![ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        )]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));

    // P2(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_multi_predicate_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));

    // P1(x) => P2(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));

    // P2(x) => false
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p2, vec![ChcExpr::var(x)])]),
        ClauseHead::False,
    ));

    problem
}
