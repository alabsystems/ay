// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcDtConstructor, ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseBody, HornClause};
use std::sync::Arc;

#[test]
fn repeated_datatype_testers_fit_the_real_key_representation() {
    let mut problem = ChcProblem::new();
    let sort = ChcSort::Datatype {
        name: "Tagged".into(),
        constructors: ChcDtConstructors::new(
            (0..96)
                .map(|tag| ChcDtConstructor {
                    name: format!("constructor_with_long_common_prefix_{tag}"),
                    selectors: Vec::new(),
                })
                .collect(),
        ),
    };
    let variable = Arc::new(ChcExpr::Var(ChcVar::new("value", sort.clone())));
    let tester = Arc::new(ChcExpr::FuncApp(
        "is-constructor_with_long_common_prefix_0".into(),
        ChcSort::Bool,
        vec![variable],
    ));
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    problem.clauses_mut()[0].body.constraint = Some(ChcExpr::Op(ChcOp::And, vec![tester; 24]));
    let mut cache = GroundSourceSurfaceCache::new(&problem);
    assert_eq!(cache.charge_step_reuse(0), Ok((1, 0)));
    let larger = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(sort));
    let cost = cache
        .reserve_nested_sort_identity(&larger, 1, &mut GroundValidationControl::new(&mut || true))
        .unwrap();
    assert!(cost >= format!("{larger:?}").len());
    let escaped = ChcSort::Uninterpreted("\"\0\u{7}Ω".to_string());
    let escaped_cost = cache
        .reserve_nested_sort_identity(&escaped, 3, &mut GroundValidationControl::new(&mut || true))
        .unwrap();
    assert!(escaped_cost >= format!("{escaped:?}").len() * 3);
}

#[test]
fn reference_pricing_refuses_a_conflicting_handle_for_the_same_id() {
    let problem = ChcProblem::new();
    let mut cache = GroundSourceSurfaceCache::new(&problem);
    let list = |name: &str| {
        ChcDtConstructors::new(vec![ChcDtConstructor {
            name: name.to_owned(),
            selectors: Vec::new(),
        }])
    };
    let constructors = list("one");
    // Inject the state a hash collision would produce without relying on one.
    cache
        .identity_datatypes
        .insert(constructors.id(), list("two"));
    let sort = ChcSort::Datatype {
        name: "D".into(),
        constructors,
    };
    assert_eq!(
        cache.reserve_nested_sort_identity(
            &sort,
            1,
            &mut GroundValidationControl::new(&mut || true)
        ),
        Err(GroundSourceSurfaceError::SourceWorkLimitExceeded)
    );
}
