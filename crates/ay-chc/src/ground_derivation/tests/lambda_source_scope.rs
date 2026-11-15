// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additional regressions for `ground_derivation::tests::lambda_source`.

use super::*;

#[test]
fn native_lambda_free_capture_can_share_a_private_slot_spelling() {
    for capture in ["ay!lambda!index", "ay!lambda!capture0"] {
        let index = ChcVar::new("i", ChcSort::Int);
        let body = ChcExpr::add(ChcExpr::Var(index.clone()), var(capture));
        let lambda = ChcExpr::array_lambda(index, body).expect("typed lambda");
        let read = ChcExpr::Op(
            crate::ChcOp::Select,
            vec![Arc::new(lambda), Arc::new(ChcExpr::Int(7))],
        );
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
            true,
        ))));
        problem.clauses_mut()[0].body.constraint = Some(ChcExpr::Op(
            crate::ChcOp::Eq,
            vec![Arc::new(read), Arc::new(var("expect"))],
        ));
        let mut cache = GroundSourceSurfaceCache::new(&problem);
        let surface = cache.surface(0).expect("small scoped lambda");
        let names: Vec<_> = surface
            .variables
            .iter()
            .map(|variable| variable.name.as_str())
            .collect();
        assert_eq!(names, [capture, "expect"]);
        for (expected, result) in [
            (12, Ok(())),
            (11, Err(GroundDerivationError::ConstraintFalse { step: 0 })),
        ] {
            let derivation = GroundDerivation {
                steps: vec![GroundDerivationStep {
                    clause_index: 0,
                    env: env(&[(capture, 5), ("expect", expected)]),
                    premises: vec![],
                }],
                query_step: 0,
            };
            assert_eq!(validate_ground_derivation(&problem, &derivation), result);
        }
    }
}
