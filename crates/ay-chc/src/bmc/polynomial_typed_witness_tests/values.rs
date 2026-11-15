// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::ground_derivation::validate_ground_derivation;
use crate::{ChcDtConstructor, ChcDtSelector};
use num_bigint::{BigInt, BigUint};

fn check_value(sort: ChcSort, value: SmtValue) {
    for collision in [false, true] {
        let mut solver = fixture(sort.clone());
        if collision {
            solver
                .problem
                .declare_predicate("__bmc_poly_p0_a0", Vec::new());
        }
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let mut model = model(&solver, &value, &mut names);
        // Original source spellings cannot substitute for generated locals.
        model.insert("x".to_owned(), SmtValue::Int(99));
        model.insert("z".to_owned(), SmtValue::Int(100));
        let witness = witness(&solver, &model, &mut names).unwrap();
        assert_eq!(witness.query_clause, Some(1));
        let entry = &witness.entries[witness.root];
        for key in ["x", "z", "__p0_a0"] {
            assert_eq!(entry.instances[key], value, "{sort:?} {key}");
        }
        let derivation = ground(&solver, &witness, &model, &mut names).unwrap();
        assert_eq!(derivation.query_step, 1);
        assert_eq!(derivation.steps.len(), 2);
        assert_eq!(derivation.steps[0].env.len(), 1);
        assert_eq!(derivation.steps[1].env.len(), 1);
        assert_eq!(derivation.steps[0].env["x"], value);
        assert_eq!(derivation.steps[1].env["z"], value);
        assert_eq!(
            validate_ground_derivation(&solver.problem, &derivation),
            Ok(())
        );
        let published = solver.verified_acyclic_dag_unsafe_from_model(
            witness,
            &model,
            &solver.problem.queries().collect::<Vec<_>>(),
            &mut names,
            deadline(),
        );
        let ChcEngineResult::Unsafe(counterexample) = published else {
            panic!("validated typed ground witness must be retained")
        };
        let ground = counterexample.ground_derivation.unwrap();
        assert_eq!(ground.steps[0].env["x"], value);
        assert_eq!(ground.steps[1].env["z"], value);
        assert_eq!(validate_ground_derivation(&solver.problem, &ground), Ok(()));
    }
}

#[test]
fn typed_scalar_witnesses_preserve_bool_int_and_high_bit_vectors() {
    for value in [false, true] {
        check_value(ChcSort::Bool, SmtValue::Bool(value));
    }
    for value in [i128::MIN, 0, i128::MAX] {
        check_value(ChcSort::Int, SmtValue::Int(value));
    }
    for width in [1, 8, 64, 128, 129, 257] {
        let high = BigUint::from(1_u8) << (width - 1) as usize;
        let max = (BigUint::from(1_u8) << width as usize) - BigUint::from(1_u8);
        for value in [BigUint::from(0_u8), high, max] {
            check_value(
                ChcSort::BitVec(width),
                SmtValue::bitvec_from_biguint(value, width),
            );
        }
    }
}

#[test]
fn typed_witnesses_preserve_integers_outside_the_legacy_i128_environment() {
    let large = (BigInt::from(1_u8) << 200_usize) + BigInt::from(19_u8);
    for value in [large.clone(), -large] {
        check_value(ChcSort::Int, SmtValue::int_from_bigint(value));
    }
}

#[test]
fn typed_array_and_datatype_witnesses_preserve_wide_payloads() {
    let high = SmtValue::bitvec_from_biguint(BigUint::from(1_u8) << 128_usize, 129);
    let zero = SmtValue::bitvec_from_biguint(BigUint::from(0_u8), 129);
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(129)));
    check_value(
        array_sort.clone(),
        SmtValue::ConstArray(Box::new(high.clone())),
    );
    check_value(
        array_sort,
        SmtValue::ArrayMap {
            default: Box::new(zero),
            entries: vec![(SmtValue::BitVec(255, 8), high.clone())],
        },
    );
    let sort = ChcSort::Datatype {
        name: "WidePair".to_owned(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "pair".to_owned(),
            selectors: vec![
                ChcDtSelector {
                    name: "payload".to_owned(),
                    sort: ChcSort::BitVec(129),
                },
                ChcDtSelector {
                    name: "flag".to_owned(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    };
    check_value(
        sort,
        SmtValue::Datatype("pair".to_owned(), vec![high, SmtValue::Bool(true)]),
    );
}

#[test]
fn absent_or_wrong_width_evidence_never_creates_a_ground_default() {
    let solver = fixture(ChcSort::BitVec(8));
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = model(&solver, &SmtValue::BitVec(255, 8), &mut names);
    let correct = witness(&solver, &model, &mut names).unwrap();
    let p = PredicateId::new(0);
    let predicate_key = name(solver.dag_arg(p, 0, &mut names).unwrap());
    let clause_vars = solver
        .mk_dag_clause_vars(&solver.problem.clauses()[0], p, 0, &mut names)
        .unwrap();
    let query_vars = solver
        .mk_dag_query_vars(&solver.problem.clauses()[1], 0, &mut names)
        .unwrap();
    for key in [
        predicate_key.clone(),
        name(clause_vars["x"].clone()),
        name(query_vars["z"].clone()),
    ] {
        for replacement in [None, Some(SmtValue::BitVec(127, 7))] {
            let mut broken = model.clone();
            broken.remove(&key);
            if let Some(value) = replacement {
                broken.insert(key.clone(), value);
            }
            if let Some(candidate) = witness(&solver, &broken, &mut names) {
                assert_ne!(key, predicate_key);
                assert!(ground(&solver, &candidate, &broken, &mut names).is_none());
            }
            assert!(
                !names.stopped(),
                "incomplete evidence is not resource refusal"
            );
        }
    }
    assert!(ground(&solver, &correct, &model, &mut names).is_some());
}

#[test]
fn an_explicit_incompatible_int_value_cannot_retry_via_the_legacy_scalar_environment() {
    let solver = fixture(ChcSort::Int);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    for malformed in [SmtValue::BitVec(7, 8), SmtValue::Bool(true)] {
        let model = model(&solver, &malformed, &mut names);
        let scalar = BmcSolver::model_i128_env(&model);
        let expression = solver.dag_arg(PredicateId::new(0), 0, &mut names).unwrap();
        // Pin the inherited fallback behavior without changing its other users.
        assert!(BmcSolver::model_expr_smt_value_for_sort(
            &expression,
            &ChcSort::Int,
            &model,
            &scalar,
        )
        .is_some());
        assert!(witness(&solver, &model, &mut names).is_none());
        assert!(!names.stopped());
    }
}

#[test]
fn intentional_integer_to_bitvector_model_normalization_is_preserved() {
    let solver = fixture(ChcSort::BitVec(8));
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = model(&solver, &SmtValue::Int(-1), &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    let derivation = ground(&solver, &witness, &model, &mut names).unwrap();
    assert_eq!(derivation.steps[0].env["x"], SmtValue::BitVec(255, 8));
    assert_eq!(derivation.steps[1].env["z"], SmtValue::BitVec(255, 8));
    assert_eq!(
        validate_ground_derivation(&solver.problem, &derivation),
        Ok(())
    );
}
