// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ModelView;
use ay_core::{Symbol, TermStore};
use num_traits::ToPrimitive;

struct EmptyModel;

impl ModelView for EmptyModel {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn boolean(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn singleton(terms: &mut TermStore) -> (Vec<(String, Sort)>, TermId) {
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let j = terms.mk_var("j", sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let first = boolean(terms, "=", &[i, zero]);
    let second = boolean(terms, "=", &[j, zero]);
    let guard = boolean(terms, "and", &[first, second]);
    let no = terms.mk_bool(false);
    let body = boolean(terms, "=>", &[guard, no]);
    (vec![("i".into(), sort.clone()), ("j".into(), sort)], body)
}

#[test]
fn joint_quantifier_plan_retains_all_dependent_negative_int_tuples_and_restores_scope() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let lower = terms.mk_int(BigInt::from(-1));
    let upper = terms.mk_int(BigInt::from(2));
    let lower_i = boolean(&mut terms, ">=", &[i, lower]);
    let upper_i = boolean(&mut terms, "<", &[i, upper]);
    let lower_j = boolean(&mut terms, ">=", &[j, i]);
    let upper_j = boolean(&mut terms, "<", &[j, upper]);
    let guard = boolean(&mut terms, "and", &[lower_i, upper_i, lower_j, upper_j]);
    let no = terms.mk_bool(false);
    let body = boolean(&mut terms, "=>", &[guard, no]);
    let bindings = vec![("i".into(), Sort::Int), ("j".into(), Sort::Int)];
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    evaluator.local_bindings.borrow_mut().push(LocalBinding {
        variable: LocalVariable::Named("i".into(), Sort::Int),
        value: ModelValue::Int(BigInt::from(99)),
    });
    let tuples = plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0).unwrap();
    let actual: Vec<Vec<i64>> = tuples
        .iter()
        .map(|tuple| {
            tuple
                .iter()
                .map(|value| {
                    let ModelValue::Int(value) = value else {
                        panic!("integer tuple")
                    };
                    value.to_i64().unwrap()
                })
                .collect()
        })
        .collect();
    assert_eq!(
        actual,
        vec![
            vec![-1, -1],
            vec![-1, 0],
            vec![-1, 1],
            vec![0, 0],
            vec![0, 1],
            vec![1, 1]
        ]
    );
    let locals = evaluator.local_bindings.borrow();
    assert_eq!(locals.len(), 1);
    assert!(matches!(&locals[0].value, ModelValue::Int(value) if value == &BigInt::from(99)));
}

#[test]
fn joint_quantifier_plan_reserves_body_work_after_prefix_assignments() {
    let mut terms = TermStore::new();
    let (bindings, body) = singleton(&mut terms);
    let model = EmptyModel;
    for allowance in [2, 3] {
        let evaluator = Evaluator::new(&terms, &model);
        evaluator.quantifier_state.nesting.set(1);
        evaluator.quantifier_state.assignments_left.set(allowance);
        let result = plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0);
        if allowance == 2 {
            assert_eq!(result.unwrap_err(), QuantifierRejection::AssignmentBudget);
        } else {
            assert_eq!(result.unwrap().len(), 1);
            assert_eq!(evaluator.quantifier_state.assignments_left.get(), 1);
        }
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
}

#[test]
fn joint_quantifier_plan_copy_budget_is_shared_and_refusal_restores_bindings() {
    let mut terms = TermStore::new();
    let (bindings, body) = singleton(&mut terms);
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let initial = evaluator.quantifier_state.plan_bytes_left.get();
    assert_eq!(
        plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0)
            .unwrap()
            .len(),
        1
    );
    let charged = initial - evaluator.quantifier_state.plan_bytes_left.get();
    assert!(charged >= 2 * 2 * std::mem::size_of::<ModelValue>());
    evaluator.quantifier_state.plan_bytes_left.set(charged - 1);
    assert_eq!(
        plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0).unwrap_err(),
        QuantifierRejection::EvaluationBudget
    );
    assert_eq!(evaluator.quantifier_state.plan_bytes_left.get(), 0);
    assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0).is_err());
    let fresh = Evaluator::new(&terms, &model);
    fresh.quantifier_state.nesting.set(1);
    fresh.quantifier_state.plan_bytes_left.set(charged);
    assert_eq!(
        plan(&fresh, QuantifierKind::Forall, &bindings, body, 0)
            .unwrap()
            .len(),
        1
    );
    assert_eq!(fresh.quantifier_state.plan_bytes_left.get(), 0);
}

#[test]
fn joint_quantifier_plan_authenticates_all_binders_before_a_vacuous_domain() {
    let mut terms = TermStore::new();
    let (bindings, _) = singleton(&mut terms);
    let i = terms.mk_var("i", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let impossible = boolean(&mut terms, "bvult", &[i, zero]);
    let no = terms.mk_bool(false);
    let body = boolean(&mut terms, "=>", &[impossible, no]);
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let duplicate = vec![bindings[0].clone(), bindings[0].clone()];
    assert_eq!(
        plan(&evaluator, QuantifierKind::Forall, &duplicate, body, 0).unwrap_err(),
        QuantifierRejection::DuplicateBinder
    );
    let unsupported = vec![
        bindings[0].clone(),
        ("array".into(), Sort::array(Sort::Bool, Sort::Bool)),
    ];
    assert_eq!(
        plan(&evaluator, QuantifierKind::Forall, &unsupported, body, 0).unwrap_err(),
        QuantifierRejection::UnsupportedDomain
    );
    let too_many = (0..17)
        .map(|i| (format!("v{i}"), Sort::Bool))
        .collect::<Vec<_>>();
    assert_eq!(
        plan(&evaluator, QuantifierKind::Forall, &too_many, body, 0).unwrap_err(),
        QuantifierRejection::BinderLimit
    );
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(plan(&evaluator, QuantifierKind::Forall, &bindings, body, 0)
        .unwrap()
        .is_empty());
}
