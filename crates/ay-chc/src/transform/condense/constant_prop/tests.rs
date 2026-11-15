// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use std::time::Duration;

use crate::parser::ChcParser;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::ChcSort;
use crate::{ChcVar, ClauseBody, ClauseHead};

use super::evaluate::{evaluate, Pins};
use super::ground::{BoolArray, Budget, Value};
use super::*;

mod ground_values;
mod projection;
mod resources;

fn parse(input: &str) -> ChcProblem {
    ChcParser::parse(input).expect("valid test CHC")
}

fn config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(Duration::from_secs(10)),
        ..PdrConfig::default()
    }
}

fn array(width: u32, value: bool) -> ChcExpr {
    ChcExpr::ConstArray(ChcSort::BitVec(width), Arc::new(ChcExpr::Bool(value)))
}

fn store(base: ChcExpr, index: ChcExpr, value: ChcExpr) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Store,
        vec![Arc::new(base), Arc::new(index), Arc::new(value)],
    )
}

fn evaluated(expr: &ChcExpr) -> Value {
    evaluate(expr, &Pins::default(), &mut Budget::new(), 0)
        .expect("within test budget")
        .expect("ground value")
}

fn multi_block(index: &str) -> ChcProblem {
    parse(&format!(
        r#"
(set-logic HORN)
(declare-fun Entry ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun Allocated ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun Grown ((Array (_ BitVec 32) Bool)) Bool)
(assert (forall ((a (Array (_ BitVec 32) Bool)))
  (=> (= a ((as const (Array (_ BitVec 32) Bool)) true)) (Entry a))))
(assert (forall ((a (Array (_ BitVec 32) Bool)) (b (Array (_ BitVec 32) Bool)))
  (=> (and (Entry a) (= b (store a #x00000042 true))) (Allocated b))))
(assert (forall ((a (Array (_ BitVec 32) Bool)) (b (Array (_ BitVec 32) Bool))
                 (c (Array (_ BitVec 32) Bool)))
  (=> (and (Allocated a) (= c (store b #x00000043 true))
    (= b (store a ((_ extract 63 32) (concat #x00000042 #x00000000)) false))) (Grown c))))
(assert (forall ((a (Array (_ BitVec 32) Bool)))
  (=> (and (Grown a) (not (select a {index}))) false)))
(check-sat)
"#
    ))
}

#[test]
fn ground_array_multiblock_safe_model_revalidates_on_original() {
    let problem = multi_block("#x00000043");
    let result = Box::new(ConstantPropagator::new()).transform(problem.clone());
    assert!(
        result.problem.clauses().iter().any(|clause| {
            clause.is_query() && clause.body.constraint == Some(ChcExpr::Bool(false))
        }),
        "unreachable read folds while retaining its source ordinal"
    );
    let PdrResult::Safe(model) = PdrSolver::new(result.problem, config()).solve() else {
        panic!("ground-array safe chain must solve");
    };
    let translated = result.back_translator.translate_validity(model);
    assert!(PdrSolver::new(problem, config()).verify_model(&translated));
    let memory = result.back_translator.transform_memory();
    assert!(!memory.is_identity_grade());
    assert!(memory.unsafe_backtranslation_complete());
}

#[test]
fn ground_array_multiblock_freed_object_remains_unsafe() {
    let problem = multi_block("#x00000042");
    let result = Box::new(ConstantPropagator::new()).transform(problem.clone());
    assert_eq!(result.problem.clauses().len(), problem.clauses().len());
    let PdrResult::Unsafe(witness) = PdrSolver::new(result.problem, config()).solve() else {
        panic!("projected arrays must retain their real refutation");
    };
    let ground = witness
        .ground_derivation
        .as_ref()
        .expect("exact transformed ground witness");
    let original_ground = result
        .back_translator
        .translate_ground_derivation(ground)
        .expect("constant projection must reconstruct the original array argument");
    crate::ground_derivation::validate_ground_derivation(&problem, &original_ground)
        .expect("all original clauses and finite-domain equalities must re-evaluate");
    assert!(matches!(
        PdrSolver::new(problem, config()).solve(),
        PdrResult::Unsafe(_)
    ));
}

#[test]
fn finite_domain_equal_pins_cannot_erase_a_reachable_fact() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-fun P ((Array (_ BitVec 1) Bool)) Bool)
(assert (forall ((a (Array (_ BitVec 1) Bool)))
  (=> (and (= a (store ((as const (Array (_ BitVec 1) Bool)) false) #b0 true))
           (= a (store ((as const (Array (_ BitVec 1) Bool)) true) #b1 false))) (P a))))
(assert (forall ((a (Array (_ BitVec 1) Bool))) (=> (P a) false)))
(check-sat)
"#,
    );
    let constants = analysis::constants(&problem, &mut Budget::new()).expect("bounded analysis");
    let p = problem.lookup_predicate("P").expect("P");
    assert_eq!(
        constants[&p].len(),
        1,
        "equivalent pins must not make the fact vacuous"
    );
    let result = Box::new(ConstantPropagator::new()).transform(problem.clone());
    assert_eq!(result.problem.clauses().len(), problem.clauses().len());
    let PdrResult::Unsafe(witness) = PdrSolver::new(result.problem, config()).solve() else {
        panic!("equivalent finite arrays must retain their real refutation");
    };
    let ground = witness
        .ground_derivation
        .as_ref()
        .expect("exact transformed ground witness");
    let original_ground = result
        .back_translator
        .translate_ground_derivation(ground)
        .expect("restore the original finite array argument");
    crate::ground_derivation::validate_ground_derivation(&problem, &original_ground)
        .expect("re-evaluate all original finite-array clauses");
}

#[test]
fn distinct_predecessor_arrays_demote_instead_of_cutting_unsafe_path() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-fun P ((Array (_ BitVec 1) Bool)) Bool)
(assert (P ((as const (Array (_ BitVec 1) Bool)) false)))
(assert (P ((as const (Array (_ BitVec 1) Bool)) true)))
(assert (forall ((a (Array (_ BitVec 1) Bool))) (=> (and (P a) (select a #b0)) false)))
(check-sat)
"#,
    );
    assert!(analysis::constants(&problem, &mut Budget::new())
        .expect("analysis")
        .is_empty());
    let result = Box::new(ConstantPropagator::new()).transform(problem);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert!(matches!(
        PdrSolver::new(result.problem, config()).solve(),
        PdrResult::Unsafe(_)
    ));
}

#[test]
fn recursive_store_cannot_freeze_the_initial_array() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-fun P ((Array (_ BitVec 1) Bool)) Bool)
(assert (P ((as const (Array (_ BitVec 1) Bool)) false)))
(assert (forall ((a (Array (_ BitVec 1) Bool))) (=> (P a) (P (store a #b0 true)))))
(assert (forall ((a (Array (_ BitVec 1) Bool))) (=> (and (P a) (select a #b0)) false)))
(check-sat)
"#,
    );
    assert!(analysis::constants(&problem, &mut Budget::new())
        .expect("analysis")
        .is_empty());
    let result = Box::new(ConstantPropagator::new()).transform(problem);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
    assert!(matches!(
        PdrSolver::new(result.problem, config()).solve(),
        PdrResult::Unsafe(_)
    ));
}

#[test]
fn symbol_splitter_shared_literal_and_pin_apis_stay_scalar_only() {
    let value = array(1, false);
    assert!(!ConstantPropagator::is_literal(&value));
    let var = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(ChcSort::Bool)),
    );
    let clause = HornClause::new(
        ClauseBody::new(vec![], Some(ChcExpr::eq(ChcExpr::var(var), value))),
        ClauseHead::False,
    );
    assert!(ConstantPropagator::constraint_pins(&clause)
        .expect("no conflicting scalar pins")
        .is_empty());
    assert!(ConstantPropagator::is_literal(&ChcExpr::Int(7)));
}

#[test]
fn typed_equal_names_do_not_alias_scalar_and_array_pins() {
    let scalar = ChcVar::new("same", ChcSort::Bool);
    let arr = ChcVar::new(
        "same",
        ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(ChcSort::Bool)),
    );
    let mut pins = Pins::default();
    pins.insert(scalar.clone(), Value::Scalar(ChcExpr::Bool(true)));
    pins.insert(arr.clone(), evaluated(&array(1, false)));
    assert_eq!(
        evaluate(&ChcExpr::var(scalar), &pins, &mut Budget::new(), 0).expect("scalar"),
        Some(Value::Scalar(ChcExpr::Bool(true)))
    );
    assert!(matches!(
        evaluate(&ChcExpr::var(arr), &pins, &mut Budget::new(), 0).expect("array"),
        Some(Value::Array(_))
    ));
}
