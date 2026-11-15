// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_sat::{Literal, SatResult, Solver};

#[test]
fn removing_actual_congruence_admits_alias_contradiction_but_duplicate_decode_refuses() {
    let a = array("a", ChcSort::BitVec(2), ChcSort::Bool);
    let i = var("i", ChcSort::BitVec(2));
    let j = var("j", ChcSort::BitVec(2));
    let source = op(
        ChcOp::And,
        vec![
            eq(i.clone(), j.clone()),
            select(a.clone(), i),
            op(ChcOp::Not, vec![select(a, j)]),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let mut oracle = Solver::new(encoding.num_vars() as usize);
            for row in encoding.rows() {
                if !matches!(row.origin(), RowOrigin::ArrayRead(_)) {
                    oracle.add_clause(
                        row.literals()
                            .iter()
                            .copied()
                            .map(Literal::from_dimacs)
                            .collect(),
                    );
                }
            }
            let SatResult::Sat(wrong) = oracle.solve().into_inner() else {
                panic!("the actual omitted congruence must matter");
            };
            assert!(matches!(
                encoding.check_scalar_candidate(&wrong),
                Err(Error::InvalidCandidate)
            ));
            assert!(matches!(
                Model::decode(encoding, &wrong),
                Err(Error::InvalidCandidate)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn every_boolean_array_has_an_actual_sat_model_and_full_domain_replay() {
    for table in 0..4 {
        let a = array("a", ChcSort::Bool, ChcSort::Bool);
        let source = op(
            ChcOp::And,
            (0..2)
                .map(|key| {
                    eq(
                        select(a.clone(), ChcExpr::Bool(key != 0)),
                        ChcExpr::Bool(table & (1 << key) != 0),
                    )
                })
                .collect(),
        );
        let original = ample();
        let mut built = convert(&source, &original).unwrap();
        built
            .with_scalar_encoding(|encoding| {
                let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
                assert_eq!(candidate.arrays.arrays.len(), 1);
                assert!(candidate.values().is_empty());
                for key in 0..2 {
                    assert_eq!(
                        candidate
                            .arrays
                            .read(0, ScalarValue::Bool(key != 0), &original)?,
                        ScalarValue::Bool(table & (1 << key) != 0)
                    );
                }
                encoding.replay_scalar_candidate(&candidate)
            })
            .unwrap();
        built.finish().unwrap();
    }
}

#[test]
fn bitvector_128_observations_and_unobserved_tail_keep_full_width() {
    let a = array("a", ChcSort::BitVec(128), ChcSort::BitVec(128));
    let source = op(
        ChcOp::And,
        vec![
            eq(
                select(a.clone(), ChcExpr::BitVec(1, 128)),
                ChcExpr::BitVec(1u128 << 127, 128),
            ),
            eq(
                select(a, ChcExpr::BitVec(u128::MAX, 128)),
                ChcExpr::BitVec(u128::MAX, 128),
            ),
        ],
    );
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
            for (key, expected) in [
                (0, 0),
                (1, 1u128 << 127),
                (1u128 << 127, 0),
                (u128::MAX - 1, 0),
                (u128::MAX, u128::MAX),
            ] {
                assert_eq!(
                    candidate
                        .arrays
                        .read(0, ScalarValue::BitVec(key, 128), &original)?,
                    ScalarValue::BitVec(expected, 128)
                );
            }
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn exact_free_root_and_typed_identity_separate_same_name_arrays() {
    let source = op(
        ChcOp::And,
        vec![
            select(
                array("same", ChcSort::Bool, ChcSort::Bool),
                ChcExpr::Bool(false),
            ),
            eq(
                select(
                    array("same", ChcSort::BitVec(2), ChcSort::Bool),
                    ChcExpr::BitVec(0, 2),
                ),
                ChcExpr::Bool(false),
            ),
            eq(
                select(
                    array("other", ChcSort::Bool, ChcSort::Bool),
                    ChcExpr::Bool(false),
                ),
                ChcExpr::Bool(false),
            ),
        ],
    );
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
            assert_eq!(candidate.arrays.arrays.len(), 3);
            let roots: std::collections::BTreeSet<_> =
                candidate.arrays.arrays.iter().map(|a| a.term).collect();
            assert_eq!(roots.len(), 3);
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn read_valued_indices_and_both_free_ite_store_branches_replay_original_dag() {
    for condition in [false, true] {
        let a = array("a", ChcSort::BitVec(2), ChcSort::BitVec(2));
        let b = array("b", ChcSort::BitVec(2), ChcSort::BitVec(2));
        let key = select(b.clone(), ChcExpr::BitVec(0, 2));
        let first = op(
            ChcOp::Store,
            vec![a.clone(), ChcExpr::BitVec(1, 2), ChcExpr::BitVec(1, 2)],
        );
        let shadowed = op(
            ChcOp::Store,
            vec![first, ChcExpr::BitVec(1, 2), ChcExpr::BitVec(2, 2)],
        );
        let branch = op(
            ChcOp::Ite,
            vec![var("c", ChcSort::Bool), shadowed, a.clone()],
        );
        let source = op(
            ChcOp::And,
            vec![
                eq(var("c", ChcSort::Bool), ChcExpr::Bool(condition)),
                eq(key.clone(), ChcExpr::BitVec(1, 2)),
                eq(
                    select(a.clone(), ChcExpr::BitVec(1, 2)),
                    ChcExpr::BitVec(3, 2),
                ),
                eq(
                    select(a.clone(), ChcExpr::BitVec(0, 2)),
                    ChcExpr::BitVec(1, 2),
                ),
                eq(
                    select(branch.clone(), key),
                    ChcExpr::BitVec(if condition { 2 } else { 3 }, 2),
                ),
                eq(select(branch, ChcExpr::BitVec(0, 2)), ChcExpr::BitVec(1, 2)),
            ],
        );
        sequence(&source, &ample()).unwrap();
    }
}

#[test]
fn distinct_symbolic_indices_with_same_concrete_key_share_one_override() {
    let a = array("a", ChcSort::BitVec(2), ChcSort::Bool);
    let i = var("i", ChcSort::BitVec(2));
    let j = var("j", ChcSort::BitVec(2));
    let source = op(
        ChcOp::And,
        vec![eq(i.clone(), j.clone()), select(a.clone(), i), select(a, j)],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
            assert_eq!(candidate.arrays.observations().len(), 2);
            assert_eq!(candidate.arrays.arrays[0].cells.len(), 1);
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}
