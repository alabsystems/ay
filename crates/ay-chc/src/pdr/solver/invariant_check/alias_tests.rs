// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward-chain safety (`check_backward_chain_safety`) conjoins the query's
//! error constraint — which keeps the query clause's local variables — with a
//! fact or step clause. Clause variables are scoped per clause but keep the
//! user's names, so the other clause is renamed apart first
//! (`rename_clause_apart`); unrenamed, a shared letter equates a query local
//! with an unrelated fact local and the check is spuriously UNSAT.

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::PdrConfig;
use crate::ChcParser;

/// `q(0)` is initial (the fact's local `C = 3` is irrelevant) and the query
/// needs only `A = 0` and some `C = 7`: the system is UNSAFE.
const FACT_QUERY_SHARED_LOCAL: &str = r#"
(set-logic HORN)
(declare-fun |q| (Int) Bool)
(assert (forall ((A Int) (C Int)) (=> (and (= A 0) (= C 3)) (q A))))
(assert (forall ((A Int) (C Int)) (=> (and (q A) (= A 0) (= C 7)) false)))
(check-sat)
"#;

#[test]
fn backward_chain_renames_the_fact_apart_from_query_locals() {
    let problem = ChcParser::parse(FACT_QUERY_SHARED_LOCAL).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let q = solver.problem.get_predicate_by_name("q").unwrap().id;
    let canonical = solver.canonical_vars(q).unwrap().to_vec();
    // The error constraint as `constraint_to_canonical_state` builds it from
    // the query: the query's local `C` stays free.
    let error = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(canonical[0].clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
            ChcExpr::int(7),
        ),
    );
    assert!(
        !solver.check_backward_chain_safety(q, &error, &canonical),
        "the initial state q(0) meets the error; unifying the fact's `C = 3` with the \
         query's `C = 7` must not make it look unreachable"
    );
}
