// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::ground_derivation::validate_ground_derivation;

#[test]
fn compiler_and_witness_reuse_names_but_retain_original_clause_bindings() {
    for collision in [false, true] {
        let mut solver = fixture(None);
        if collision {
            solver.problem.declare_predicate(STEMS[2], Vec::new());
        }
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let formula = compile(&solver, &mut names).unwrap();
        let mut model = model(&solver, &mut names);
        // Original spellings in an SMT map cannot substitute for the encoded
        // locals. They must not leak into the recovered source bindings.
        model.insert("x".to_owned(), SmtValue::Int(99));
        model.insert("z".to_owned(), SmtValue::Int(100));
        assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(true)));
        let witness = witness(&solver, &model, &mut names).unwrap();
        assert_eq!(witness.query_clause, Some(1));
        assert_eq!(witness.root, 0);
        assert_eq!(witness.entries.len(), 1);
        let entry = &witness.entries[0];
        assert_eq!(entry.incoming_clause, Some(0));
        assert_eq!(entry.level, 0);
        assert!(entry.premises.is_empty());
        assert_eq!(entry.instances["x"], SmtValue::Int(7));
        assert_eq!(entry.instances["z"], SmtValue::Int(7));
        assert_eq!(entry.instances["__p0_a0"], SmtValue::Int(7));
        assert_eq!(entry.instances.len(), 3);

        // Real original-source validation, not a claim that every UF model
        // can already be exported through the legacy scalar witness path.
        let derivation = GroundDerivation {
            query_step: 1,
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    premises: Vec::new(),
                    env: FxHashMap::from_iter([("x".to_owned(), entry.instances["x"].clone())]),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    premises: vec![0],
                    env: FxHashMap::from_iter([("z".to_owned(), entry.instances["z"].clone())]),
                },
            ],
        };
        assert_eq!(
            validate_ground_derivation(&solver.problem, &derivation),
            Ok(())
        );
    }
}

#[test]
fn stale_or_missing_required_model_keys_do_not_select_the_old_namespace() {
    let mut solver = fixture(None);
    solver.problem.declare_predicate(STEMS[0], Vec::new());
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let keys = generated(&solver, &mut names);
    let correct = model(&solver, &mut names);
    assert!(witness(&solver, &correct, &mut names).is_some());
    let stale = STEMS
        .into_iter()
        .enumerate()
        .map(|(index, name)| {
            (
                name.to_owned(),
                if index < 2 {
                    SmtValue::Bool(true)
                } else {
                    SmtValue::Int(7)
                },
            )
        })
        .collect();
    assert!(witness(&solver, &stale, &mut names).is_none());
    assert!(!names.stopped());
    for required in &keys[..3] {
        let mut missing = correct.clone();
        missing.remove(required);
        assert!(witness(&solver, &missing, &mut names).is_none());
        assert!(!names.stopped());
    }
    assert!(witness(&solver, &correct, &mut names).is_some());
}

#[test]
fn ordinary_missing_local_values_remain_incomplete_candidates_not_shape_refusals() {
    let solver = fixture(None);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let query = &solver.problem.clauses()[1];
    assert!(solver
        .acyclic_dag_query_instances(
            query,
            0,
            &FxHashMap::default(),
            &FxHashMap::default(),
            &mut names,
        )
        .unwrap()
        .is_empty());
    assert!(solver
        .acyclic_dag_clause_instances(
            PredicateId::new(0),
            0,
            &solver.problem.clauses()[0],
            &FxHashMap::default(),
            &FxHashMap::default(),
            &mut names,
        )
        .unwrap()
        .is_empty());
    assert!(!names.stopped());
}
