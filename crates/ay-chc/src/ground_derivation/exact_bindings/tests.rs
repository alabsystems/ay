// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::ground_derivation::artifact::encode_ground_derivation_artifact;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `P(x) <= x = 3.  false <= P(y) /\ y > 1.`
fn problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("x"), ChcExpr::int(3))),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("y")])],
            Some(ChcExpr::gt(var("y"), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn env(pairs: &[(&str, i64)]) -> FxHashMap<String, SmtValue> {
    pairs
        .iter()
        .map(|(name, value)| ((*name).to_string(), SmtValue::Int((*value).into())))
        .collect()
}

/// The shape a back-translated derivation can have: both steps carry the
/// other clause's variable too (`y` in the fact, `x` in the query).
fn padded_derivation() -> GroundDerivation {
    GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: env(&[("x", 3), ("y", 3)]),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 3), ("y", 3)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    }
}

/// A padded derivation validates natively but cannot be exported; with
/// its bindings narrowed to each clause's variables it still validates and
/// now exports.
#[test]
fn narrowed_bindings_keep_validation_and_make_the_derivation_exportable() {
    let problem = problem();
    let mut derivation = padded_derivation();
    validate_ground_derivation(&problem, &derivation).expect("setup: padding validates");
    assert!(
        encode_ground_derivation_artifact(&problem, &derivation).is_err(),
        "setup: the artifact refuses bindings a clause does not mention"
    );

    derivation.retain_clause_bindings(&problem);
    assert_eq!(derivation.steps[0].env, env(&[("x", 3)]));
    assert_eq!(derivation.steps[1].env, env(&[("y", 3)]));
    validate_ground_derivation(&problem, &derivation).expect("narrowing keeps validity");
    encode_ground_derivation_artifact(&problem, &derivation)
        .expect("each step now binds exactly its clause's variables");
}

/// AY's private UF observations (NUL-prefixed names) are not clause
/// variables, but validation reads them, so they stay.
#[test]
fn private_uf_observations_are_kept() {
    let problem = problem();
    let mut derivation = padded_derivation();
    let marker = "\0ay.test-observation\0".to_string();
    derivation.steps[1]
        .env
        .insert(marker.clone(), SmtValue::Bool(true));
    derivation.retain_clause_bindings(&problem);
    assert!(derivation.steps[1].env.contains_key(&marker));
    assert!(!derivation.steps[1].env.contains_key("x"));
}
