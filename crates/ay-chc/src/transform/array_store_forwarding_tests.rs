// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for clause-local array store-to-load forwarding + dead-store
//! elimination (model-checker-consumer parity item 4a).

use super::*;
use crate::parser::ChcParser;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::transform::{DeadParamEliminator, TransformationPipeline};
use std::fmt::Write as _;

fn parse(smt: &str) -> ChcProblem {
    let problem =
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
    problem
}

fn int_int_array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn arr_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, int_int_array_sort()))
}

fn constraint_of(problem: &ChcProblem, clause_idx: usize) -> ChcExpr {
    problem.clauses()[clause_idx]
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true))
}

// ---------------------------------------------------------------------------
// Dead-store absorption (pure expression identity)
// ---------------------------------------------------------------------------

#[test]
fn absorb_adjacent_same_const_index() {
    let m = arr_var("m");
    let chain = ChcExpr::store(
        ChcExpr::store(m.clone(), ChcExpr::Int(5), ChcExpr::Int(1)),
        ChcExpr::Int(5),
        ChcExpr::Int(2),
    );
    let expected = ChcExpr::store(m, ChcExpr::Int(5), ChcExpr::Int(2));
    assert_eq!(absorb_dead_stores(&chain), expected);
}

#[test]
fn absorb_non_adjacent_same_const_index() {
    let m = arr_var("m");
    // store(store(store(m, 4, a), 9, c), 4, b) -> store(store(m, 9, c), 4, b)
    let chain = ChcExpr::store(
        ChcExpr::store(
            ChcExpr::store(m.clone(), ChcExpr::Int(4), ChcExpr::Int(10)),
            ChcExpr::Int(9),
            ChcExpr::Int(30),
        ),
        ChcExpr::Int(4),
        ChcExpr::Int(20),
    );
    let expected = ChcExpr::store(
        ChcExpr::store(m, ChcExpr::Int(9), ChcExpr::Int(30)),
        ChcExpr::Int(4),
        ChcExpr::Int(20),
    );
    assert_eq!(absorb_dead_stores(&chain), expected);
}

#[test]
fn absorb_identical_symbolic_index() {
    let m = arr_var("m");
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let chain = ChcExpr::store(
        ChcExpr::store(m.clone(), i.clone(), ChcExpr::Int(1)),
        i.clone(),
        ChcExpr::Int(2),
    );
    let expected = ChcExpr::store(m, i, ChcExpr::Int(2));
    assert_eq!(absorb_dead_stores(&chain), expected);
}

#[test]
fn absorb_keeps_distinct_indices() {
    let m = arr_var("m");
    let chain = ChcExpr::store(
        ChcExpr::store(m, ChcExpr::Int(4), ChcExpr::Int(10)),
        ChcExpr::Int(9),
        ChcExpr::Int(30),
    );
    assert_eq!(absorb_dead_stores(&chain), chain);
}

#[test]
fn absorb_keeps_possibly_aliasing_symbolic_indices() {
    // store(store(m, i, a), 3, b): i may or may not equal 3 — both writes stay.
    let m = arr_var("m");
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let chain = ChcExpr::store(
        ChcExpr::store(m, i, ChcExpr::Int(10)),
        ChcExpr::Int(3),
        ChcExpr::Int(30),
    );
    assert_eq!(absorb_dead_stores(&chain), chain);
}

// ---------------------------------------------------------------------------
// Clause-level forwarding
// ---------------------------------------------------------------------------

/// Const-index forwarding: the read folds to the stored value and the
/// clause-local store temporary's definition is dropped, leaving an
/// array-free constraint.
#[test]
fn forwards_const_index_and_drops_local_def() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int) Int) Bool)
(declare-fun Q ((Array Int Int) Int) Bool)
(assert (forall ((m (Array Int Int)) (x Int)) (=> (= x 0) (P m x))))
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (x Int) (y Int))
  (=> (and (P m x) (= t (store m 3 9)) (= y (select t 3))) (Q m y))))
(assert (forall ((m (Array Int Int)) (y Int)) (=> (and (Q m y) (not (= y 9))) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("forwarding must fire");
    let constraint = constraint_of(&result, 1);
    assert!(
        !constraint.contains_array_ops(),
        "hop constraint must be array-free after forwarding, got: {constraint}"
    );
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(9)
        )),
        "read must fold to y = 9, got: {constraint}"
    );
}

/// Identical-symbolic-index forwarding: ROW1 fires on a syntactically
/// identical (but non-constant) index.
#[test]
fn forwards_identical_symbolic_index() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int) Int Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((m (Array Int Int)) (i Int) (v Int)) (=> (= v 7) (P m i v))))
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (i Int) (v Int) (y Int))
  (=> (and (P m i v) (= t (store m i v)) (= y (select t i))) (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (not (= y 7))) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("forwarding must fire");
    let constraint = constraint_of(&result, 1);
    assert!(
        !constraint.contains_array_ops(),
        "hop constraint must be array-free after ROW1 on identical symbolic index, got: {constraint}"
    );
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::var(ChcVar::new("v", ChcSort::Int))
        )),
        "read must fold to y = v, got: {constraint}"
    );
}

/// NO forwarding across a possibly-aliasing symbolic store: the select index
/// and the store index are neither identical nor provably distinct, so the
/// clause must be left completely untouched.
#[test]
fn no_forwarding_across_possibly_aliasing_symbolic_store() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int) Int Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((m (Array Int Int)) (i Int) (v Int)) (=> (= v 7) (P m i v))))
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (i Int) (v Int) (y Int))
  (=> (and (P m i v) (= t (store m i v)) (= y (select t 3))) (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (not (= y 7))) false)))
(check-sat)
"#,
    );
    assert!(
        ArrayStoreForwarder::new().apply(&problem).is_none(),
        "possibly-aliasing symbolic store must not be rewritten"
    );
}

/// ROW2 skip-over-store on provably distinct constant indices: the read
/// resolves to the base array; the temporary's definition is dropped.
#[test]
fn skips_store_on_distinct_const_index() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (y Int))
  (=> (and (P m) (= t (store m 4 7)) (= y (select t 9))) (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (< y 0) (> y 0)) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("ROW2 must fire");
    let constraint = constraint_of(&result, 0);
    let expected_read = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::select(arr_var("m"), ChcExpr::Int(9)),
    );
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&expected_read),
        "read must skip the distinct-index store: {constraint}"
    );
    assert!(
        !format!("{constraint}").contains("store"),
        "dead local store def must be dropped: {constraint}"
    );
}

/// A chain of N stores through separate temporaries collapses to the stored
/// value, and every temporary definition is dropped.
#[test]
fn chain_of_stores_collapses() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((m (Array Int Int)) (t1 (Array Int Int)) (t2 (Array Int Int)) (t3 (Array Int Int)) (y Int))
  (=> (and (P m)
           (= t1 (store m 1 10))
           (= t2 (store t1 2 20))
           (= t3 (store t2 3 30))
           (= y (select t3 1)))
      (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (not (= y 10))) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("chain forwarding must fire");
    let constraint = constraint_of(&result, 0);
    assert!(
        !constraint.contains_array_ops(),
        "chain must fully collapse, got: {constraint}"
    );
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(10)
        )),
        "read must fold through the chain to y = 10, got: {constraint}"
    );
}

/// Dead-store elimination inside a definition: the overwritten inner write
/// disappears and the read folds to the outer write's value.
#[test]
fn dead_store_in_definition_folds_to_last_write() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (y Int))
  (=> (and (P m) (= t (store (store m 5 1) 5 2)) (= y (select t 5))) (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (not (= y 2))) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("dead-store elim must fire");
    let constraint = constraint_of(&result, 0);
    assert!(
        !constraint.contains_array_ops(),
        "constraint must be array-free, got: {constraint}"
    );
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(2)
        )),
        "read must fold to the last write y = 2, got: {constraint}"
    );
}

/// A definition whose variable is a predicate argument must be KEPT (only the
/// read is forwarded).
#[test]
fn keeps_definition_of_predicate_argument() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(declare-fun Q ((Array Int Int) Int) Bool)
(assert (forall ((m (Array Int Int)) (t (Array Int Int)) (y Int))
  (=> (and (P m) (= t (store m 3 9)) (= y (select t 3))) (Q t y))))
(assert (forall ((t (Array Int Int)) (y Int)) (=> (and (Q t y) (not (= y 9))) false)))
(check-sat)
"#,
    );
    let result = ArrayStoreForwarder::new()
        .apply(&problem)
        .expect("read forwarding must fire");
    let constraint = constraint_of(&result, 0);
    let conjuncts = constraint.collect_conjuncts_nontrivial();
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            arr_var("t"),
            ChcExpr::store(arr_var("m"), ChcExpr::Int(3), ChcExpr::Int(9))
        )),
        "definition of head-arg t must be kept: {constraint}"
    );
    assert!(
        conjuncts.contains(&ChcExpr::eq(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(9)
        )),
        "read must still fold to y = 9: {constraint}"
    );
}

/// Self-referential array equality is a constraint, not a definition
/// (occurs check) — the clause must be untouched.
#[test]
fn occurs_check_rejects_self_referential_store() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(assert (forall ((m (Array Int Int)))
  (=> (= m (store m 3 9)) (P m))))
(assert (forall ((m (Array Int Int))) (=> (and (P m) (not (= (select m 3) 9))) false)))
(check-sat)
"#,
    );
    assert!(
        ArrayStoreForwarder::new().apply(&problem).is_none(),
        "self-referential store equality must not be treated as a definition"
    );
}

#[test]
fn enabled_by_default() {
    if std::env::var("AY_CHC_DISABLE_ARRAY_STORE_FORWARDING").is_err() {
        assert!(array_store_forwarding_enabled());
    }
}

/// The Transformer returns an identity-grade back-translator when nothing
/// changes, so untouched problems keep their identity transform stack.
#[test]
fn identity_grade_when_no_change() {
    let problem = parse(
        r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))
(check-sat)
"#,
    );
    let result = TransformationPipeline::new()
        .with(ArrayStoreForwarder::new())
        .transform(problem);
    assert!(result.transform_memory().is_identity_grade());
}

// ---------------------------------------------------------------------------
// Integration: arity collapse on the threaded-memory shape (item 4a)
// ---------------------------------------------------------------------------

/// Synthetic high-arity acyclic memory-threading CHC: `relations` predicates
/// of arity `1 + arrays` (one Int counter plus `arrays` type-indexed memory
/// arrays). Each hop stores into one array through a clause-local temporary
/// and reads the value back from the temporary at the same constant address
/// (the Cell::set→replace→ptr inline-chain shape). The query keeps the last
/// array and the counter live.
fn threaded_memory_problem(relations: usize, arrays: usize, query_bound: i64) -> ChcProblem {
    assert!(relations >= 2 && arrays >= 1);
    let mut smt = String::from("(set-logic HORN)\n");
    let arr_params: String = (1..=arrays)
        .map(|_| "(Array Int Int) ".to_string())
        .collect();
    for k in 0..relations {
        smt.push_str(&format!("(declare-fun P{k} (Int {arr_params}) Bool)\n"));
    }
    let mut mvars = String::new();
    for j in 1..=arrays {
        write!(mvars, "(m{j} (Array Int Int)) ").expect("writing to a String cannot fail");
    }
    let margs = |_: usize| -> String {
        let mut args = String::new();
        for j in 1..=arrays {
            write!(args, " m{j}").expect("writing to a String cannot fail");
        }
        args
    };
    smt.push_str(&format!(
        "(assert (forall ((x Int) {mvars}) (=> (= x 0) (P0 x{}))))\n",
        margs(0)
    ));
    for k in 1..relations {
        let j = (k - 1) % arrays + 1;
        smt.push_str(&format!(
            "(assert (forall ((x Int) (x2 Int) (t (Array Int Int)) {mvars})
  (=> (and (P{prev} x{args})
           (= t (store m{j} 7 5))
           (= x2 (+ x (select t 7))))
      (P{k} x2{args}))))\n",
            prev = k - 1,
            args = margs(k),
        ));
    }
    let last = relations - 1;
    smt.push_str(&format!(
        "(assert (forall ((x Int) {mvars})
  (=> (and (P{last} x{args}) (= (select m{arrays} 3) 999) (> x {query_bound})) false)))\n",
        args = margs(last),
    ));
    smt.push_str("(check-sat)\n");
    parse(&smt)
}

/// 30 relations × arity 21: forwarding + DeadParamEliminator collapse every
/// relation to arity 2 (the counter plus the one query-live array), while
/// DeadParamEliminator ALONE cannot collapse anything (the store equalities
/// keep every threaded array constraint-live — rule 2b).
#[test]
fn forwarding_enables_dead_param_arity_collapse_30x20() {
    let problem = threaded_memory_problem(30, 20, 1000);
    assert!(problem.predicates().iter().all(|p| p.arity() == 21));

    // Control: the slicer alone keeps the threaded arrays live.
    let control = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .transform(problem.clone());
    assert!(
        control.problem.predicates().iter().any(|p| p.arity() > 2),
        "control: DeadParamEliminator alone must NOT collapse the threaded arrays"
    );

    // Forwarding first makes the arrays dead; the trailing slicer collapses.
    let result = TransformationPipeline::new()
        .with(ArrayStoreForwarder::new())
        .with(DeadParamEliminator::new())
        .transform(problem.clone());
    for pred in result.problem.predicates() {
        assert!(
            pred.arity() <= 2,
            "arity must collapse to <= 2 (counter + query-live array), {} has {}",
            pred.name,
            pred.arity()
        );
    }
    assert_eq!(
        result.problem.clauses().len(),
        problem.clauses().len(),
        "clause count must be preserved"
    );
}

fn pdr_only_portfolio(problem: ChcProblem) -> PortfolioResult {
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    PortfolioSolver::new(problem, config).solve()
}

/// End-to-end Safe: the collapsed problem is proved Safe fast by PDR alone,
/// and the full portfolio (whose Safe answers are validated fail-closed
/// against the ORIGINAL clauses because the transform stack is non-identity)
/// confirms Safe on the original high-arity problem.
#[test]
fn threaded_memory_safe_end_to_end() {
    // 10 hops of +5 reach exactly 45; bound 100 is unreachable -> Safe.
    let problem = threaded_memory_problem(10, 6, 100);

    let result = TransformationPipeline::new()
        .with(ArrayStoreForwarder::new())
        .with(DeadParamEliminator::new())
        .transform(problem.clone());
    assert!(result.problem.predicates().iter().all(|p| p.arity() <= 2));

    // The DeadParam back-translator re-inserts the sliced array params as
    // unconstrained vars, so translated interpretations keep the original
    // arity (required for original-clause validation).
    let pdr_config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_mins(1)),
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(result.problem.clone(), pdr_config);
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);
            for pred in problem.predicates() {
                let interp = translated
                    .get(&pred.id)
                    .unwrap_or_else(|| panic!("missing interpretation for {}", pred.name));
                assert_eq!(
                    interp.vars.len(),
                    pred.arity(),
                    "translated interpretation for {} must have original arity",
                    pred.name
                );
            }
        }
        other => panic!("expected Safe on collapsed threaded-memory chain, got {other:?}"),
    }

    // Production gate: the portfolio validates Safe against the ORIGINAL
    // clauses (fail-closed on non-identity transform stacks); an invalid
    // model would degrade to Unknown and fail this assertion.
    match pdr_only_portfolio(problem) {
        PortfolioResult::Safe(_) => {}
        other => panic!("expected Safe end-to-end on the original problem, got {other:?}"),
    }
}

/// End-to-end Unsafe through the full portfolio (which now runs the
/// forwarding pass inside condense): the reachable counter value must still
/// be found and the witness must replay on the original clauses — a verdict
/// flip or a fail-closed Unknown fails this test.
#[test]
fn threaded_memory_unsafe_end_to_end() {
    // 6 hops of +5 reach exactly 25; bound 20 is exceeded -> Unsafe.
    let problem = threaded_memory_problem(6, 4, 20);
    match pdr_only_portfolio(problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe (x reaches 25 > 20), got {other:?}"),
    }
}

/// End-to-end Safe through the full portfolio on the original problem.
#[test]
fn threaded_memory_safe_full_portfolio() {
    let problem = threaded_memory_problem(6, 4, 100);
    match pdr_only_portfolio(problem) {
        PortfolioResult::Safe(_) => {}
        other => panic!("expected Safe (x reaches only 25), got {other:?}"),
    }
}
