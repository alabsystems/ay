// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane's model half of the unread-array elimination: an eliminated array
//! gets its definition's value from the lane itself (check-sat-level
//! completion would otherwise hide a missing rebuild), the authored window is
//! restored exactly, and a definition the lane cannot evaluate withholds the
//! `sat` instead of publishing an unpinned array.

use crate::executor_types::{SolveResult, UnknownReason};
use crate::Executor;
use ay_arrays::ArrayInterpretation;
use ay_core::TermId;
use ay_frontend::parse;
use ntest::timeout;

const ELIMINATED: &str = "abvfp_unread_arrays.eliminated";

fn executor_for(input: &str) -> Executor {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB setup should execute");
    exec
}

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .terms
        .find_var(name)
        .unwrap_or_else(|| panic!("{name} is declared"))
}

fn lane_array_value(exec: &Executor, array: TermId) -> ArrayInterpretation {
    exec.last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&array))
        .cloned()
        .expect("the lane attaches the eliminated array")
}

/// The lane itself gives an eliminated array the value of its definition,
/// before any check-sat-level completion runs.
#[test]
#[timeout(60_000)]
fn an_eliminated_array_gets_its_definition_value_from_the_lane() {
    let mut exec = executor_for(
        r#"
(set-logic QF_ABVFP)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const x (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const v (_ BitVec 8))
(assert (= x (store a #x3 v)))
(assert (= (select a #x0) #x11))
(assert (= v #x2a))
"#,
    );
    let x = declared(&exec, "x");
    let result = exec.solve_abvfp().expect("ABVFP solve should not error");
    assert_eq!(result, SolveResult::Sat);
    assert_eq!(exec.statistics().get_int(ELIMINATED), Some(1));
    let x_value = lane_array_value(&exec, x);
    assert_eq!(
        x_value.stores.first(),
        Some(&("#x3".to_string(), "#x2a".to_string())),
        "{x_value:?}"
    );
    assert!(
        x_value
            .stores
            .iter()
            .any(|(at, value)| at == "#x0" && value == "#x11"),
        "x inherits a's cells: {x_value:?}"
    );
}

/// The exact-restoration twin of
/// `qf_abvfp_incomplete_final_finite_array_closure_preserves_unsat` in its
/// original shape: `(= a b)` over two otherwise unused arrays is eliminated,
/// the refutation of `p` and `(not p)` survives, and the authored window is
/// put back exactly.
#[test]
#[timeout(60_000)]
fn the_elimination_restores_the_authored_window_and_keeps_unsat() {
    let mut exec = executor_for(
        r#"
(set-logic QF_ABVFP)
(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const p Bool)
(assert (= a b))
(assert p)
(assert (not p))
"#,
    );
    let authored = exec.ctx.assertions.clone();
    let result = exec.solve_abvfp().expect("ABVFP solve should not error");
    assert!(result.is_unsat(), "{result:?}");
    assert_eq!(exec.statistics().get_int(ELIMINATED), Some(1));
    assert_eq!(exec.ctx.assertions, authored);
}

/// A constant-array definition is rebuilt as that constant array.
#[test]
#[timeout(60_000)]
fn a_constant_array_definition_is_rebuilt() {
    let mut exec = executor_for(
        r#"
(set-logic QF_ABVFP)
(declare-const x (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= x ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x2a)))
(assert (= (select a #x1) #x07))
"#,
    );
    let x = declared(&exec, "x");
    let result = exec.solve_abvfp().expect("ABVFP solve should not error");
    assert_eq!(result, SolveResult::Sat);
    let x_value = lane_array_value(&exec, x);
    assert_eq!(x_value.default.as_deref(), Some("#x2a"), "{x_value:?}");
    assert!(x_value.stores.is_empty(), "{x_value:?}");
}

/// A floating-point constant only the definition mentions is completed with
/// `+zero` (its sort's canonical default) before the definition is evaluated,
/// so the stored `fp.to_ubv` reads `#x00`.
#[test]
#[timeout(60_000)]
fn a_scalar_only_the_definition_mentions_is_completed_first() {
    let mut exec = executor_for(
        r#"
(set-logic QF_ABVFP)
(declare-const x (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const g Float32)
(assert (= x (store a #x0 ((_ fp.to_ubv 8) RTZ g))))
(assert (= (select a #x1) #x07))
"#,
    );
    let x = declared(&exec, "x");
    let result = exec.solve_abvfp().expect("ABVFP solve should not error");
    assert_eq!(result, SolveResult::Sat);
    let x_value = lane_array_value(&exec, x);
    assert_eq!(
        x_value.stores.first(),
        Some(&("#x0".to_string(), "#x00".to_string())),
        "{x_value:?}"
    );
}

/// FAIL-CLOSED: a definition the lane cannot evaluate (a read of a nested
/// array) withholds the rewritten window's `sat` with a reason naming the gap,
/// rather than publishing a model that leaves `x` unpinned.
#[test]
#[timeout(60_000)]
fn an_unevaluable_definition_withholds_the_sat() {
    let mut exec = executor_for(
        r#"
(set-logic QF_ABVFP)
(declare-const m (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 8))))
(declare-const x (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= x (select m #x0)))
(assert (= (select a #x1) #x07))
"#,
    );
    let result = exec.solve_abvfp().expect("ABVFP solve should not error");
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(exec.statistics().get_int(ELIMINATED), Some(1));
    assert!(exec.last_model.is_none());
    assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
    let detail = exec
        .statistics()
        .get_string("unknown.detail")
        .unwrap_or_default();
    assert!(detail.contains("unread-array elimination"), "{detail}");
}
