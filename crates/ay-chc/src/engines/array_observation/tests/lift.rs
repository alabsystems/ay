// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::problem::ArrayScalarizedArg;

#[test]
fn lift_recovers_original_array_select_formulas_and_exact_full_signatures() {
    let original = source(9, false);
    let projected = project(&original);
    let reduced_model = candidate(projected.reduced());
    let lifted = projected.lift(&reduced_model, &mut || true).unwrap();
    assert_eq!(lifted.len(), original.predicates().len());
    for predicate in original.predicates() {
        let interpretation = lifted.get(&predicate.id).unwrap();
        assert_eq!(
            interpretation
                .vars
                .iter()
                .map(|var| var.sort.clone())
                .collect::<Vec<_>>(),
            predicate.arg_sorts
        );
        assert!(interpretation
            .formula
            .vars()
            .iter()
            .any(|var| matches!(var.sort, ChcSort::Array(..))));
    }
    let id = original.lookup_predicate("B").unwrap();
    let body = lifted.get(&id).unwrap();
    let expected = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(body.vars[0].clone()), bv(1, 64)),
            bv(9, 32),
        ),
        operation(ChcOp::BvULt, ChcExpr::var(body.vars[1].clone()), bv(4, 64)),
    );
    assert_eq!(body.formula, expected);
}

#[test]
fn lift_drops_search_inductiveness_convergence_and_production_flags() {
    use crate::pdr::model::InvariantVerificationMethod;
    let original = source(9, false);
    let projected = project(&original);
    let mut model = candidate(projected.reduced());
    model.individually_inductive = true;
    model.convergence_proven = true;
    model.verification_method = InvariantVerificationMethod::TrlExpandedSystem;
    let lifted = projected.lift(&model, &mut || true).unwrap();
    assert!(!lifted.individually_inductive);
    assert!(!lifted.convergence_proven);
    assert_eq!(
        lifted.verification_method,
        InvariantVerificationMethod::Unspecified
    );
    assert!(!lifted.has_quantified_array_certificate());
}

#[test]
fn missing_extra_wrong_sort_and_duplicate_formal_models_are_refused() {
    let original = source(9, false);
    let projected = project(&original);
    let id = original.lookup_predicate("B").unwrap();
    for case in 0..5 {
        let mut bad = candidate(projected.reduced());
        match case {
            0 => {
                bad.interpretations.remove(&id);
            }
            1 => bad.set(
                PredicateId::new(999),
                PredicateInterpretation::new(vec![], ChcExpr::Bool(true)),
            ),
            2 => bad.interpretations.get_mut(&id).unwrap().vars.clear(),
            3 => bad.interpretations.get_mut(&id).unwrap().vars[0].sort = ChcSort::Int,
            _ => {
                let variables = &mut bad.interpretations.get_mut(&id).unwrap().vars;
                variables[1].name = variables[0].name.clone();
            }
        }
        assert!(projected.lift(&bad, &mut || true).is_none(), "case {case}");
    }
}

#[test]
fn free_wrongly_sorted_nonboolean_and_uninterpreted_formulas_are_refused() {
    let original = source(9, false);
    let projected = project(&original);
    let id = original.lookup_predicate("B").unwrap();
    let model = candidate(projected.reduced());
    let name = &model.get(&id).unwrap().vars[0].name;
    let formulas = [
        ChcExpr::eq(variable("unbound", ChcSort::BitVec(32)), bv(9, 32)),
        ChcExpr::eq(variable(name, ChcSort::Int), ChcExpr::Int(9)),
        variable(name, ChcSort::BitVec(32)),
        ChcExpr::FuncApp("opaque".into(), ChcSort::Bool, vec![]),
    ];
    for formula in formulas {
        let mut bad = model.clone();
        bad.interpretations.get_mut(&id).unwrap().formula = formula;
        assert!(projected.lift(&bad, &mut || true).is_none());
    }
}

#[test]
fn missing_foreign_reordered_and_wrong_width_maps_are_refused() {
    let original = source(9, false);
    let id = original.lookup_predicate("B").unwrap();
    for case in 0..7 {
        let mut projected = project(&original);
        let model = candidate(projected.reduced());
        match case {
            0 => {
                projected.map.pred_args.remove(&id);
            }
            1 => {
                projected
                    .map
                    .pred_args
                    .insert(PredicateId::new(999), vec![]);
            }
            2 => {
                projected.map.original_predicates[0].name = "different".into();
            }
            3 => projected.map.pred_args.get_mut(&id).unwrap().swap(0, 1),
            4 => {
                projected.map.pred_args.get_mut(&id).unwrap()[0] = ArrayScalarizedArg::Select {
                    original_arg: 99,
                    index: bv(1, 64),
                }
            }
            5 => {
                projected.map.pred_args.get_mut(&id).unwrap()[0] = ArrayScalarizedArg::Select {
                    original_arg: 0,
                    index: bv(1, 32),
                }
            }
            _ => {
                projected.map.pred_args.get_mut(&id).unwrap()[0] = ArrayScalarizedArg::Select {
                    original_arg: 0,
                    index: variable("unbound_key", ChcSort::BitVec(64)),
                }
            }
        }
        assert!(
            projected.lift(&model, &mut || true).is_none(),
            "case {case}"
        );
    }
}

#[test]
fn duplicate_observation_keys_cannot_fabricate_a_wider_signature() {
    let original = source(9, false);
    let id = original.lookup_predicate("B").unwrap();
    let mut projected = project(&original);
    let model = candidate(projected.reduced());
    let mapping = projected.map.pred_args.get_mut(&id).unwrap();
    mapping.insert(
        1,
        ArrayScalarizedArg::Select {
            original_arg: 0,
            index: bv(1, 64),
        },
    );
    assert!(projected.lift(&model, &mut || true).is_none());
}
