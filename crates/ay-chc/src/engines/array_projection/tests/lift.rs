// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::expr::evaluate::evaluate_expr;
use crate::smt::SmtValue;

#[test]
fn lifting_restores_exact_source_signatures_and_preserves_the_scalar_relation() {
    let original = source();
    let projection = project(&original);
    let candidate = model(projection.reduced());
    let before = format!("{candidate:?}");
    let lifted = projection.lift(&candidate, &mut || true).unwrap();
    assert_eq!(lifted.len(), original.predicates().len());
    for predicate in original.predicates() {
        let old = candidate.get(&predicate.id).unwrap();
        let new = lifted.get(&predicate.id).unwrap();
        assert_eq!(
            new.vars
                .iter()
                .map(|var| var.sort.clone())
                .collect::<Vec<_>>(),
            predicate.arg_sorts
        );
        assert_eq!(
            new.formula, old.formula,
            "no substitution/normalization of retained formals"
        );
        let retained: Vec<_> = new
            .vars
            .iter()
            .filter(|var| !matches!(var.sort, ChcSort::Array(..)))
            .cloned()
            .collect();
        assert_eq!(retained, old.vars);
        for i in 0..8 {
            let mut valuation = DetHashMap::default();
            for variable in &old.vars {
                valuation.insert(variable.name.clone(), SmtValue::BitVec(i, 64));
            }
            let expected = evaluate_expr(&old.formula, &valuation).unwrap();
            assert_eq!(
                evaluate_expr(&new.formula, &valuation),
                Some(expected.clone())
            );
            for value in [0, 1, u32::MAX] {
                for variable in new
                    .vars
                    .iter()
                    .filter(|var| matches!(var.sort, ChcSort::Array(..)))
                {
                    valuation.insert(
                        variable.name.clone(),
                        SmtValue::ConstArray(Box::new(SmtValue::BitVec(u128::from(value), 32))),
                    );
                }
                assert_eq!(
                    evaluate_expr(&new.formula, &valuation),
                    Some(expected.clone())
                );
            }
        }
    }
    assert_eq!(format!("{candidate:?}"), before);
}

#[test]
fn restored_multiple_array_formals_are_fresh_even_against_generated_name_collisions() {
    let original = signature_problem(vec![
        array_sort(),
        ChcSort::Int,
        array_sort(),
        ChcSort::Bool,
    ]);
    let projection = project(&original);
    let mut candidate = model(projection.reduced());
    let id = original.predicates()[0].id;
    let first = projection.lift(&candidate, &mut || true).unwrap();
    let collision = first.get(&id).unwrap().vars[0].name.clone();
    let vars = vec![
        ChcVar::new(collision.clone(), ChcSort::Int),
        ChcVar::new("flag", ChcSort::Bool),
    ];
    let formula = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Var(vars[0].clone())),
            Arc::new(ChcExpr::Int(3)),
        ],
    );
    candidate.set(
        id,
        PredicateInterpretation::new(vars.clone(), formula.clone()),
    );
    let lifted = projection.lift(&candidate, &mut || true).unwrap();
    let value = lifted.get(&id).unwrap();
    assert_eq!(value.vars[1], vars[0]);
    assert_eq!(value.vars[3], vars[1]);
    assert_eq!(value.formula, formula);
    assert_eq!(value.vars.len(), 4);
    let names: DetHashSet<_> = value.vars.iter().map(|var| &var.name).collect();
    assert_eq!(names.len(), 4);
    for index in [0, 2] {
        assert_eq!(value.vars[index].sort, array_sort());
        assert_ne!(value.vars[index].name, collision);
        assert_ne!(value.vars[index].name, "flag");
    }
}

#[test]
fn missing_extra_or_wrong_signature_models_are_not_repaired_or_partially_lifted() {
    let original = source();
    let projection = project(&original);
    let id = original.lookup_predicate("body").unwrap();
    for case in 0..5 {
        let mut bad = model(projection.reduced());
        match case {
            0 => {
                bad.interpretations.remove(&id);
            }
            1 => {
                bad.set(
                    PredicateId::new(999),
                    PredicateInterpretation::new(vec![], ChcExpr::Bool(true)),
                );
            }
            2 => {
                bad.interpretations.get_mut(&id).unwrap().vars.clear();
            }
            3 => {
                bad.interpretations.get_mut(&id).unwrap().vars[0].sort = ChcSort::Int;
            }
            _ => {
                bad.interpretations
                    .get_mut(&id)
                    .unwrap()
                    .vars
                    .push(ChcVar::new("extra", ChcSort::BitVec(64)));
            }
        }
        let before = format!("{bad:?}");
        assert!(projection.lift(&bad, &mut || true).is_none(), "case {case}");
        assert_eq!(format!("{bad:?}"), before);
    }
}

#[test]
fn free_wrongly_sorted_or_nonboolean_model_formulas_decline_without_weakening() {
    let original = source();
    let projection = project(&original);
    let id = original.lookup_predicate("body").unwrap();
    let baseline = model(projection.reduced());
    let name = baseline.get(&id).unwrap().vars[0].name.clone();
    let formulas = [
        ChcExpr::eq(
            variable("undeclared", ChcSort::BitVec(64)),
            ChcExpr::BitVec(0, 64),
        ),
        ChcExpr::eq(variable(&name, ChcSort::Int), ChcExpr::Int(0)),
        variable(&name, ChcSort::BitVec(64)),
        ChcExpr::FuncApp("uninterpreted_bool".into(), ChcSort::Bool, vec![]),
        ChcExpr::PredicateApp(
            "error".into(),
            original.lookup_predicate("error").unwrap(),
            vec![],
        ),
    ];
    for formula in formulas {
        let mut bad = baseline.clone();
        bad.interpretations.get_mut(&id).unwrap().formula = formula;
        let before = format!("{bad:?}");
        assert!(projection.lift(&bad, &mut || true).is_none());
        assert_eq!(format!("{bad:?}"), before);
    }
    let original = signature_problem(vec![array_sort(), ChcSort::Int, ChcSort::Bool]);
    let projection = project(&original);
    let mut bad = model(projection.reduced());
    let interpretation = bad
        .interpretations
        .get_mut(&original.predicates()[0].id)
        .unwrap();
    interpretation.vars[1].name = interpretation.vars[0].name.clone();
    assert!(
        projection.lift(&bad, &mut || true).is_none(),
        "same name with a different sort is still ambiguous"
    );
}

#[test]
fn closed_well_typed_array_formula_is_preserved_instead_of_blanket_rejected() {
    let original = source();
    let projection = project(&original);
    let mut candidate = model(projection.reduced());
    let head = original.lookup_predicate("head").unwrap();
    let constant = ChcExpr::ConstArray(ChcSort::BitVec(64), Arc::new(ChcExpr::BitVec(9, 32)));
    let formula = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::select(constant, ChcExpr::BitVec(7, 64))),
            Arc::new(ChcExpr::BitVec(9, 32)),
        ],
    );
    candidate.interpretations.get_mut(&head).unwrap().formula = formula.clone();
    let lifted = projection.lift(&candidate, &mut || true).unwrap();
    assert_eq!(lifted.get(&head).unwrap().formula, formula);
}

#[test]
fn lifting_is_only_a_candidate_transform_and_does_not_copy_validation_authority_flags() {
    let original = source();
    let projection = project(&original);
    let mut candidate = model(projection.reduced());
    candidate.individually_inductive = true;
    candidate.convergence_proven = true;
    // A deliberately invalid safety invariant still has a structurally valid
    // lift. Only the separate ORIGINAL-problem verifier may accept it as Safe.
    let error = original.lookup_predicate("error").unwrap();
    candidate.interpretations.get_mut(&error).unwrap().formula = ChcExpr::Bool(true);
    let lifted = projection.lift(&candidate, &mut || true).unwrap();
    assert_eq!(lifted.get(&error).unwrap().formula, ChcExpr::Bool(true));
    assert!(!lifted.individually_inductive);
    assert!(!lifted.convergence_proven);
    assert!(!lifted.has_quantified_array_certificate());
}
