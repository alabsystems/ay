// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_arrays::counted_reads::{Derivation, Unresolved};

mod resources;

fn constant(index: ChcSort, value: ChcExpr) -> ChcExpr {
    ChcExpr::ConstArray(index, Arc::new(value))
}

fn select(array: ChcExpr, index: ChcExpr) -> ChcExpr {
    op(ChcOp::Select, vec![array, index])
}

fn store(array: ChcExpr, index: ChcExpr, value: ChcExpr) -> ChcExpr {
    op(ChcOp::Store, vec![array, index, value])
}

fn full_domain() -> ChcExpr {
    let base = constant(ChcSort::BitVec(128), var("fill", ChcSort::BitVec(128)));
    let array = store(
        base,
        ChcExpr::BitVec(1, 128),
        var("written", ChcSort::BitVec(128)),
    );
    op(
        ChcOp::And,
        vec![
            op(
                ChcOp::Eq,
                vec![
                    var("fill", ChcSort::BitVec(128)),
                    ChcExpr::BitVec(u128::MAX, 128),
                ],
            ),
            op(
                ChcOp::Eq,
                vec![
                    var("written", ChcSort::BitVec(128)),
                    ChcExpr::BitVec(17, 128),
                ],
            ),
            op(
                ChcOp::Eq,
                vec![
                    select(array.clone(), ChcExpr::BitVec(1, 128)),
                    ChcExpr::BitVec(17, 128),
                ],
            ),
            op(
                ChcOp::Eq,
                vec![
                    select(array, ChcExpr::BitVec(u128::MAX, 128)),
                    ChcExpr::BitVec(u128::MAX, 128),
                ],
            ),
        ],
    )
}

#[test]
fn full_domain_closed_array_replay_preserves_128_bit_indices_elements_and_fill() {
    let source = full_domain();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let closure = encoding.array_read_obligations().unwrap();
            assert_eq!(closure.roots(), encoding.cnf.roots());
            assert!(closure.unresolved().is_empty());
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            encoding.replay_scalar_candidate(&candidate)?;
            let before = original.usage()?.work_admitted;
            closure.admission().admit(7, 0)?;
            assert_eq!(original.usage()?.work_admitted, before + 7);
            let mut array_rows = 0;
            for row in encoding.rows() {
                if let RowOrigin::ArrayRead(index) = row.origin() {
                    array_rows += 1;
                    let expected: Vec<_> = closure.steps()[index]
                        .literals()
                        .iter()
                        .map(|term| {
                            attachment::shifted(
                                encoding.bv.literal(*term).unwrap(),
                                encoding.offset,
                            )
                            .unwrap()
                        })
                        .collect();
                    assert_eq!(row.literals(), expected);
                }
            }
            assert_eq!(array_rows, closure.steps().len());
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn raw_store_hit_miss_and_shadowing_have_unique_actual_sat_values() {
    for index in 0..4 {
        for expected in 0..4 {
            let base = constant(ChcSort::BitVec(2), ChcExpr::BitVec(0, 2));
            let first = store(base, ChcExpr::BitVec(1, 2), ChcExpr::BitVec(1, 2));
            let last = store(first, ChcExpr::BitVec(1, 2), ChcExpr::BitVec(2, 2));
            let source = op(
                ChcOp::Eq,
                vec![
                    select(last, ChcExpr::BitVec(index, 2)),
                    ChcExpr::BitVec(expected, 2),
                ],
            );
            let mut built = convert(&source, &ample()).unwrap();
            built
                .with_scalar_encoding(|encoding| {
                    let actual = if index == 1 { 2 } else { 0 };
                    if expected == actual {
                        let candidate = encoding.check_scalar_candidate(&model(encoding))?;
                        encoding.replay_scalar_candidate(&candidate)?;
                    } else {
                        assert!(matches!(
                            solve(encoding, OracleRows::Attached),
                            SatResult::Unsat(_)
                        ));
                    }
                    Ok(())
                })
                .unwrap();
            built.finish().unwrap();
        }
    }
}

#[test]
fn boolean_array_ite_retains_projection_and_congruence_premises() {
    for condition in [false, true] {
        let array = op(
            ChcOp::Ite,
            vec![
                var("condition", ChcSort::Bool),
                constant(ChcSort::Bool, ChcExpr::Bool(true)),
                constant(ChcSort::Bool, ChcExpr::Bool(false)),
            ],
        );
        let source = op(
            ChcOp::And,
            vec![
                op(
                    ChcOp::Eq,
                    vec![var("condition", ChcSort::Bool), ChcExpr::Bool(condition)],
                ),
                op(
                    ChcOp::Eq,
                    vec![
                        select(array, ChcExpr::Bool(false)),
                        ChcExpr::Bool(condition),
                    ],
                ),
            ],
        );
        let mut built = convert(&source, &ample()).unwrap();
        built
            .with_scalar_encoding(|encoding| {
                let closure = encoding.array_read_obligations().unwrap();
                assert!(closure
                    .steps()
                    .iter()
                    .any(|step| matches!(step.derivation(), Derivation::IteThen { .. })));
                assert!(closure
                    .steps()
                    .iter()
                    .any(|step| matches!(step.derivation(), Derivation::IteElse { .. })));
                let candidate = encoding.check_scalar_candidate(&model(encoding))?;
                encoding.replay_scalar_candidate(&candidate)
            })
            .unwrap();
        built.finish().unwrap();
    }
}

#[test]
fn omitting_the_derived_const_row_admits_wrong_reads_but_never_a_candidate() {
    let source = op(
        ChcOp::Eq,
        vec![
            select(
                constant(ChcSort::BitVec(2), ChcExpr::BitVec(1, 2)),
                ChcExpr::BitVec(3, 2),
            ),
            ChcExpr::BitVec(2, 2),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            assert!(matches!(
                solve(encoding, OracleRows::Attached),
                SatResult::Unsat(_)
            ));
            let mut oracle = Solver::new(encoding.num_vars() as usize);
            for row in encoding
                .rows()
                .iter()
                .filter(|row| !matches!(row.origin(), RowOrigin::ArrayRead(_)))
            {
                oracle.add_clause(
                    row.literals()
                        .iter()
                        .copied()
                        .map(Literal::from_dimacs)
                        .collect(),
                );
            }
            let SatResult::Sat(wrong) = oracle.solve().into_inner() else {
                panic!("omitted premise must matter");
            };
            assert!(matches!(
                encoding.check_scalar_candidate(&wrong),
                Err(Error::InvalidCandidate)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn free_read_aliasing_is_constrained_by_real_congruence_with_model_obligations_retained() {
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::BitVec(2)));
    let source = op(
        ChcOp::And,
        vec![
            op(
                ChcOp::Eq,
                vec![var("i", ChcSort::BitVec(2)), var("j", ChcSort::BitVec(2))],
            ),
            op(
                ChcOp::Ne,
                vec![
                    select(var("a", sort.clone()), var("i", ChcSort::BitVec(2))),
                    select(var("a", sort), var("j", ChcSort::BitVec(2))),
                ],
            ),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let closure = encoding.array_read_obligations().unwrap();
            assert_eq!(closure.unresolved().len(), 2);
            assert!(closure
                .unresolved()
                .iter()
                .all(|entry| matches!(entry, Unresolved::FreeRead { .. })));
            assert!(closure
                .steps()
                .iter()
                .any(|step| matches!(step.derivation(), Derivation::FreeReadCongruence { .. })));
            assert!(matches!(
                solve(encoding, OracleRows::Attached),
                SatResult::Unsat(_)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn array_relations_in_dead_arms_still_decline_before_attachment() {
    let sort = ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool));
    let source = op(
        ChcOp::Or,
        vec![
            ChcExpr::Bool(true),
            op(ChcOp::Eq, vec![var("a", sort.clone()), var("b", sort)]),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    let mut reached = false;
    assert_eq!(
        built.with_scalar_encoding(|_| {
            reached = true;
            Ok(())
        }),
        Err(Error::Unsupported)
    );
    assert!(!reached);
    built.finish().unwrap();
}

#[test]
fn closed_array_candidates_cannot_cross_equal_numeric_encodings() {
    let source = full_domain();
    let mut left = convert(&source, &ample()).unwrap();
    let mut right = convert(&source, &ample()).unwrap();
    left.with_scalar_encoding(|a| {
        right.with_scalar_encoding(|b| {
            assert_eq!(a.num_vars(), b.num_vars());
            let candidate = a.check_scalar_candidate(&model(a))?;
            assert_eq!(
                b.replay_scalar_candidate(&candidate),
                Err(Error::InvalidCandidate)
            );
            a.replay_scalar_candidate(&candidate)
        })
    })
    .unwrap();
    left.finish().unwrap();
    right.finish().unwrap();
}
