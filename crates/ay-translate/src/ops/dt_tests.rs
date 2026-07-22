// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, Solver};

fn tuple_pair() -> DatatypeSort {
    match Sort::struct_type("Pair", [("_0", Sort::Int), ("_1", Sort::Bool)]) {
        Sort::Datatype(dt) => dt,
        other => panic!("expected datatype sort, got {other:?}"),
    }
}

#[test]
fn test_datatype_constructor_with_context() {
    let dt = tuple_pair();
    let ctor = dt.constructors[0].name.clone();
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfDt);
    declare(&mut ctx, &dt);
    let forty_two = ctx.int_const(42);
    let truth = ctx.bool_const(true);
    let pair = constructor(&mut ctx, &dt, &ctor, &[forty_two, truth]);
    let fst = selector(&mut ctx, "_0", pair, Sort::Int);
    let is_ctor = tester(&mut ctx, &ctor, pair);
    let eq = ctx
        .solver()
        .try_eq(fst, forty_two)
        .expect("matching selector result should compare");
    ctx.assert_term(eq);
    ctx.assert_term(is_ctor);
    let result = ctx.check_sat();

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_datatype_constructor_with_session() {
    let dt = tuple_pair();
    let ctor = dt.constructors[0].name.clone();
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfDt).expect("QfDt should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        declare(&mut session, &dt);
        let forty_two = session.solver().int_const(42);
        let truth = session.solver().bool_const(true);
        let pair = constructor(&mut session, &dt, &ctor, &[forty_two, truth]);
        let fst = selector(&mut session, "_0", pair, Sort::Int);
        let is_ctor = tester(&mut session, &ctor, pair);
        let eq = session
            .solver()
            .try_eq(fst, forty_two)
            .expect("matching selector result should compare");
        session.assert_term(eq);
        session.assert_term(is_ctor);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}
