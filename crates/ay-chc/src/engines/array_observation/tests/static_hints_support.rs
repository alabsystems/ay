// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Synthetic typed AY signatures and exact hint-shape fixtures, UNRUN.
//! These do not construct a MODEL_CHECKER_CONSUMER MIR obligation or consumer authority.

use super::super::hints::Admitted;
use super::*;
use crate::{ClauseBody, HornClause, LemmaHint};

pub(super) fn scalar_hint(problem: &ChcProblem, name: &str, position: usize) -> LemmaHint {
    let predicate = problem.lookup_predicate(name).unwrap();
    let sort = problem.get_predicate(predicate).unwrap().arg_sorts[position].clone();
    LemmaHint::new(
        predicate,
        operation(
            ChcOp::BvULe,
            variable(&crate::canonical_var_name(predicate, position), sort),
            bv(4, 64),
        ),
        37,
        "native-auto-invariant",
    )
}

pub(super) fn rebase(projected: &Projection<'_>, hints: &[LemmaHint]) -> Option<Vec<LemmaHint>> {
    Admitted::new(hints, &mut || true)?.rebase(projected, &mut || true)
}

pub(super) fn hint_snapshot(hints: &[LemmaHint]) -> String {
    format!("{hints:?}")
}

pub(super) fn shifted_source() -> ChcProblem {
    ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-fun H ((_ BitVec 8) (Array (_ BitVec 64) (_ BitVec 32))
                        (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 16)) Bool) Bool)
        (assert (H (_ bv3 8) ((as const (Array (_ BitVec 64) (_ BitVec 32))) (_ bv5 32))
                   (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 16))) (_ bv7 16)) true))
        (assert (forall ((tag (_ BitVec 8)) (a (Array (_ BitVec 64) (_ BitVec 32)))
                         (i (_ BitVec 64)) (b (Array (_ BitVec 64) (_ BitVec 16))) (flag Bool))
          (=> (and (H tag a i b flag) (bvult i (_ bv4 64)))
              (H tag (store a (_ bv1 64) (_ bv9 32)) (bvadd i (_ bv1 64)) b flag))))
        (assert (forall ((tag (_ BitVec 8)) (a (Array (_ BitVec 64) (_ BitVec 32)))
                         (i (_ BitVec 64)) (b (Array (_ BitVec 64) (_ BitVec 16))) (flag Bool))
          (=> (and (H tag a i b flag)
              (not (and (= (select a (_ bv1 64)) (_ bv9 32))
                        (= (select a (_ bv2 64)) (_ bv5 32))
                        (= (select b (_ bv1 64)) (_ bv7 16))
                        (= (select b (_ bv2 64)) (_ bv7 16))))) false)))
        (check-sat)
        "#,
    )
    .unwrap()
}

/// Direct typed constructors mirror the array/BV sorts and store/select shape
/// of a two-observation loop; there is no text-to-problem authority shortcut.
pub(super) fn typed_shape(expected: u128) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32)));
    let id = problem.declare_predicate("H", vec![array_sort.clone(), ChcSort::BitVec(64)]);
    let array = variable("typed_array", array_sort);
    let counter = variable("typed_counter", ChcSort::BitVec(64));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            id,
            vec![
                ChcExpr::const_array(ChcSort::BitVec(64), bv(5, 32)),
                bv(0, 64),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(id, vec![array.clone(), counter.clone()])],
            Some(operation(ChcOp::BvULt, counter.clone(), bv(4, 64))),
        ),
        ClauseHead::Predicate(
            id,
            vec![
                ChcExpr::store(array.clone(), bv(1, 64), bv(9, 32)),
                operation(ChcOp::BvAdd, counter.clone(), bv(1, 64)),
            ],
        ),
    ));
    let read = |key| ChcExpr::select(array.clone(), bv(key, 64));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(id, vec![array.clone(), counter.clone()])],
        Some(ChcExpr::and(
            operation(ChcOp::BvUGe, counter, bv(1, 64)),
            ChcExpr::not(ChcExpr::and(
                ChcExpr::eq(read(1), bv(expected, 32)),
                ChcExpr::eq(read(2), bv(5, 32)),
            )),
        )),
    )));
    problem
}

pub(super) fn shape_candidate(projected: &Projection<'_>) -> InvariantModel {
    use crate::problem::ArrayScalarizedArg;
    let predicate = projected.reduced.predicates().first().unwrap();
    let variables: Vec<_> = predicate
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(position, sort)| ChcVar::new(format!("typed_cell_{position}"), sort.clone()))
        .collect();
    let mappings = projected.map.pred_args.get(&predicate.id).unwrap();
    let get = |key: Option<u128>| {
        let position = mappings
            .iter()
            .position(|entry| match (entry, key) {
                (ArrayScalarizedArg::Original(1), None) => true,
                (
                    ArrayScalarizedArg::Select {
                        original_arg: 0,
                        index: ChcExpr::BitVec(value, 64),
                    },
                    Some(key),
                ) => *value == key,
                _ => false,
            })
            .unwrap();
        ChcExpr::var(variables[position].clone())
    };
    let counter = get(None);
    let first = get(Some(1));
    let formula = ChcExpr::and_all([
        operation(ChcOp::BvULe, counter.clone(), bv(4, 64)),
        ChcExpr::eq(get(Some(2)), bv(5, 32)),
        ChcExpr::or(
            ChcExpr::and(
                ChcExpr::eq(counter.clone(), bv(0, 64)),
                ChcExpr::eq(first.clone(), bv(5, 32)),
            ),
            ChcExpr::and(
                operation(ChcOp::BvUGe, counter, bv(1, 64)),
                ChcExpr::eq(first, bv(9, 32)),
            ),
        ),
    ]);
    let mut model = InvariantModel::new();
    model.set(
        predicate.id,
        PredicateInterpretation::new(variables, formula),
    );
    model
}

pub(super) fn scalar_family() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let id = problem.declare_predicate(
        "P",
        vec![
            array_sort.clone(),
            ChcSort::Int,
            ChcSort::Real,
            ChcSort::Bool,
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            id,
            vec![
                ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
                ChcExpr::Int(0),
                ChcExpr::Real(1, 2),
                ChcExpr::Bool(true),
            ],
        ),
    ));
    let array = variable("array", array_sort);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            id,
            vec![
                array.clone(),
                variable("integer", ChcSort::Int),
                variable("real", ChcSort::Real),
                variable("boolean", ChcSort::Bool),
            ],
        )],
        Some(ChcExpr::ne(
            ChcExpr::select(array.clone(), ChcExpr::Int(0)),
            ChcExpr::select(array, ChcExpr::Int(1)),
        )),
    )));
    problem
}

pub(super) fn collision_source() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32)));
    let id = problem.declare_predicate(
        "P",
        vec![array_sort.clone(), ChcSort::BitVec(64), ChcSort::BitVec(64)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            id,
            vec![
                ChcExpr::const_array(ChcSort::BitVec(64), bv(5, 32)),
                bv(0, 64),
                bv(1, 64),
            ],
        ),
    ));
    let array = variable("array", array_sort);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            id,
            vec![
                array.clone(),
                variable("left", ChcSort::BitVec(64)),
                variable("right", ChcSort::BitVec(64)),
            ],
        )],
        Some(ChcExpr::ne(
            ChcExpr::select(array.clone(), bv(1, 64)),
            ChcExpr::select(array, bv(2, 64)),
        )),
    )));
    problem
}
