// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use ay_core::time::Instant;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

mod resources;
mod schema;
mod sorting;

fn owner(work: u64, storage: usize, observer: ay_core::resource::CheckStop) -> OriginalAdmission {
    owner_at(
        Instant::now() + Duration::from_secs(20),
        work,
        storage,
        observer,
    )
}

fn owner_at(
    end: Instant,
    work: u64,
    storage: usize,
    observer: ay_core::resource::CheckStop,
) -> OriginalAdmission {
    OriginalAdmission::new(FiniteAdmissionGrant::new(work, storage), end, observer)
}

fn quiet_owner() -> OriginalAdmission {
    owner(20_000_000, 128 * 1024 * 1024, Arc::new(|| false))
}

fn raw(problem: &mut ChcProblem, clause: HornClause) {
    let index = problem.clauses().len();
    problem.add_clause(HornClause::query(ClauseBody::empty()));
    problem.clauses_mut()[index] = clause;
}

fn fixture() -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.set_fixedpoint_format();
    let first = problem.declare_predicate(
        "P\n\"λ",
        vec![
            ChcSort::Int,
            ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool)),
        ],
    );
    problem.declare_predicate(
        "P\n\"λ",
        vec![
            ChcSort::Int,
            ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool)),
        ],
    );
    let action = problem.declare_action("step\t\\\0");
    problem.declare_action("a\u{001f}\u{0008}\u{000c}/é");
    let args = vec![
        ChcExpr::Int(i128::MIN),
        ChcExpr::BitVec(u128::MAX, u32::MAX),
    ];
    let exprs = vec![
        ChcExpr::Bool(false),
        ChcExpr::Int(i128::MAX),
        ChcExpr::Real(i64::MIN, i64::MAX),
        ChcExpr::Real(1, 0),
        ChcExpr::Var(ChcVar::new(
            "v\r\n\"",
            ChcSort::Uninterpreted("U\tλ".to_string()),
        )),
        ChcExpr::PredicateApp(
            "unknown\\name".to_string(),
            PredicateId::new(31),
            Vec::new(),
        ),
        ChcExpr::ConstArrayMarker(ChcSort::BitVec(0)),
        ChcExpr::IsTesterMarker("Ctor\n".to_string()),
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Bool(true))),
    ];
    raw(
        &mut problem,
        HornClause::new(
            ClauseBody::new(
                vec![(first, args.clone()), (first, args)],
                Some(ChcExpr::FuncApp(
                    "all".to_string(),
                    ChcSort::Bool,
                    exprs.into_iter().map(Arc::new).collect(),
                )),
            ),
            ClauseHead::Predicate(PredicateId::new(63), vec![ChcExpr::Int(0)]),
        )
        .with_action(action),
    );
    raw(&mut problem, HornClause::query(ClauseBody::empty()));
    problem
}

fn consume(
    original: &OriginalAdmission,
    problem: &ChcProblem,
) -> Result<(), OriginalAdmissionError> {
    // The frozen unpriced byte oracle is fixture-only, not inside the component.
    let expected =
        super::super::text::normalized_input(problem, &mut super::super::AlwaysContinue).unwrap();
    original.with_work(|work| {
        prepare_normalized_chc_input_with_work(problem, work)?.with_input(|source, bytes, _| {
            assert!(std::ptr::eq(source, problem));
            assert_eq!(bytes, expected);
            Ok(())
        })
    })
}

fn totals(problem: &ChcProblem) -> (u64, usize) {
    let (mut units, mut bytes) = (0u64, 0usize);
    let mut sink = |work: usize, storage: usize| {
        units = units.checked_add(work as u64).unwrap();
        bytes = bytes.checked_add(storage).unwrap();
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    prepare_normalized_chc_input_with_work(problem, &mut work)
        .unwrap()
        .with_input(|_, _, _| Ok(()))
        .unwrap();
    drop(work);
    (units, bytes)
}

#[test]
fn empty_and_all_supported_payload_forms_match_the_legacy_byte_oracle() {
    let original = quiet_owner();
    consume(&original, &ChcProblem::new()).unwrap();
    consume(&original, &fixture()).unwrap();
}

#[test]
fn every_operator_tag_and_indexed_parameter_matches_derived_debug_spelling() {
    let original = quiet_owner();
    let ops = [
        ChcOp::Not,
        ChcOp::And,
        ChcOp::Or,
        ChcOp::Implies,
        ChcOp::Iff,
        ChcOp::Add,
        ChcOp::Sub,
        ChcOp::Mul,
        ChcOp::Div,
        ChcOp::Mod,
        ChcOp::Neg,
        ChcOp::Eq,
        ChcOp::Ne,
        ChcOp::Lt,
        ChcOp::Le,
        ChcOp::Gt,
        ChcOp::Ge,
        ChcOp::Ite,
        ChcOp::Select,
        ChcOp::Store,
        ChcOp::BvAdd,
        ChcOp::BvSub,
        ChcOp::BvMul,
        ChcOp::BvUDiv,
        ChcOp::BvURem,
        ChcOp::BvSDiv,
        ChcOp::BvSRem,
        ChcOp::BvSMod,
        ChcOp::BvAnd,
        ChcOp::BvOr,
        ChcOp::BvXor,
        ChcOp::BvNand,
        ChcOp::BvNor,
        ChcOp::BvXnor,
        ChcOp::BvNot,
        ChcOp::BvNeg,
        ChcOp::BvShl,
        ChcOp::BvLShr,
        ChcOp::BvAShr,
        ChcOp::BvULt,
        ChcOp::BvULe,
        ChcOp::BvUGt,
        ChcOp::BvUGe,
        ChcOp::BvSLt,
        ChcOp::BvSLe,
        ChcOp::BvSGt,
        ChcOp::BvSGe,
        ChcOp::BvComp,
        ChcOp::BvConcat,
        ChcOp::Bv2Nat,
        ChcOp::BvExtract(u32::MAX, 0),
        ChcOp::BvZeroExtend(u32::MAX),
        ChcOp::BvSignExtend(1),
        ChcOp::BvRotateLeft(0),
        ChcOp::BvRotateRight(7),
        ChcOp::BvRepeat(u32::MAX),
        ChcOp::Int2Bv(128),
    ];
    for op in ops {
        let mut problem = ChcProblem::new();
        raw(
            &mut problem,
            HornClause::query(ClauseBody::constraint(ChcExpr::Op(
                op,
                vec![Arc::new(ChcExpr::Int(4)), Arc::new(ChcExpr::Int(-2))],
            ))),
        );
        consume(&original, &problem).unwrap();
    }
}

#[test]
fn every_control_byte_and_utf8_name_preserves_json_escaping() {
    let original = quiet_owner();
    let mut name = String::new();
    for byte in 0u8..32 {
        name.push(char::from(byte));
    }
    name.push_str("/\\\"éλ😀");
    let mut problem = ChcProblem::new();
    problem.declare_predicate(name.clone(), vec![ChcSort::Uninterpreted(name.clone())]);
    problem.declare_action(name);
    consume(&original, &problem).unwrap();
}

#[test]
fn repeated_shared_edges_are_preserved_and_cost_more_than_one_occurrence() {
    let shared = Arc::new(ChcExpr::Int(7));
    let mut first = ChcProblem::new();
    raw(
        &mut first,
        HornClause::query(ClauseBody::constraint(ChcExpr::FuncApp(
            "wide".to_string(),
            ChcSort::Bool,
            vec![shared.clone()],
        ))),
    );
    let mut repeated = ChcProblem::new();
    raw(
        &mut repeated,
        HornClause::query(ClauseBody::constraint(ChcExpr::FuncApp(
            "wide".to_string(),
            ChcSort::Bool,
            vec![shared; 128],
        ))),
    );
    let original = quiet_owner();
    consume(&original, &first).unwrap();
    consume(&original, &repeated).unwrap();
    let a = totals(&first);
    let b = totals(&repeated);
    assert!(b.0 > a.0 && b.1 > a.1);
}

#[test]
fn nested_expression_and_array_sort_walks_are_iterative_and_exact() {
    let mut expression = ChcExpr::Int(-1);
    let mut sort = ChcSort::Bool;
    for _ in 0..128 {
        expression = ChcExpr::Op(ChcOp::Not, vec![Arc::new(expression)]);
        sort = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(sort));
    }
    let mut problem = ChcProblem::new();
    problem.declare_predicate("nested", vec![sort]);
    raw(
        &mut problem,
        HornClause::query(ClauseBody::constraint(expression)),
    );
    consume(&quiet_owner(), &problem).unwrap();
}

#[test]
fn array_lambda_normalized_payload_binds_body_and_captures() {
    let index = ChcVar::new("i", ChcSort::Int);
    let free = ChcVar::new("x", ChcSort::Int);
    let lambda = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::add(ChcExpr::Var(index), ChcExpr::Var(free.clone())),
    )
    .unwrap();
    let changed = lambda.substitute(&[(free, ChcExpr::Int(7))]);
    let mut originals = Vec::new();
    for expression in [lambda, changed] {
        let mut problem = ChcProblem::new();
        raw(
            &mut problem,
            HornClause::query(ClauseBody::constraint(expression)),
        );
        consume(&quiet_owner(), &problem).unwrap();
        originals.push(
            super::super::text::normalized_input(&problem, &mut super::super::AlwaysContinue)
                .unwrap(),
        );
    }
    assert_ne!(originals[0], originals[1]);
    assert!(originals[0].contains(r#"array-lambda("ay!lambda!index":Int;["ay!lambda!capture0":Int];op:Add(var:"ay!lambda!capture0":Int,var:"ay!lambda!index":Int);[var:"x":Int])"#), "{}", originals[0]);
}
