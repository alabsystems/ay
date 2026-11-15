// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn malformed_typed_witnesses_and_observation_corruption_never_replay() {
    let source = boolean_source();
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let assignment = sat_model(encoding);
            for change in 0..10 {
                let mut candidate = encoding.check_scalar_candidate(&assignment)?;
                match change {
                    0 => candidate.arrays.arrays[0].term = TermId(u32::MAX),
                    1 => candidate.arrays.arrays[0].default = ScalarValue::BitVec(0, 1),
                    2 => candidate.arrays.arrays[0].cells[0].index = ScalarValue::BitVec(0, 1),
                    3 => candidate.arrays.arrays[0].cells[0].value = ScalarValue::BitVec(1, 1),
                    4 => {
                        candidate.arrays.arrays.pop();
                    }
                    5 => {
                        candidate.arrays.reads.pop();
                    }
                    6 => {
                        let cell = candidate.arrays.arrays[0].cells[0];
                        candidate.arrays.arrays[0].cells.push(cell);
                    }
                    7 => {
                        let mut cell = candidate.arrays.arrays[0].cells[0];
                        let ScalarValue::Bool(value) = cell.value else {
                            unreachable!()
                        };
                        cell.value = ScalarValue::Bool(!value);
                        candidate.arrays.arrays[0].cells.push(cell);
                    }
                    8 => {
                        let ScalarValue::Bool(key) = candidate.arrays.reads[0].index else {
                            unreachable!()
                        };
                        candidate.arrays.reads[0].index = ScalarValue::Bool(!key);
                    }
                    9 => {
                        let ScalarValue::Bool(value) = candidate.arrays.reads[0].value else {
                            unreachable!()
                        };
                        candidate.arrays.reads[0].value = ScalarValue::Bool(!value);
                    }
                    _ => unreachable!(),
                }
                assert_eq!(
                    encoding.replay_scalar_candidate(&candidate),
                    Err(Error::InvalidCandidate),
                    "mutation {change}"
                );
            }
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn generated_base_read_is_replayed_even_when_the_original_store_hit_is_true() {
    let a = array("a", ChcSort::Bool, ChcSort::Bool);
    let stored = op(
        ChcOp::Store,
        vec![a, ChcExpr::Bool(false), ChcExpr::Bool(true)],
    );
    let source = select(stored, ChcExpr::Bool(false));
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let mut candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
            let closure = encoding.array_read_obligations().unwrap();
            let Unresolved::FreeRead { read } = closure.unresolved()[0] else {
                unreachable!()
            };
            let ScalarValue::Bool(value) = candidate.arrays.reads[read].value else {
                unreachable!()
            };
            candidate.arrays.reads[read].value = ScalarValue::Bool(!value);
            // Shape/type validation still passes. The unchanged full witness still
            // makes the original hit true; only the independent closure replay
            // detects this corrupted generated base observation.
            candidate.arrays.validate(encoding)?;
            assert_eq!(
                encoding.replay_scalar_candidate(&candidate),
                Err(Error::InvalidCandidate)
            );
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn numeric_model_and_source_equality_cannot_transfer_an_encoding_credential() {
    let source = boolean_source();
    let mut first = convert(&source, &ample()).unwrap();
    let mut second = convert(&source, &ample()).unwrap();
    first
        .with_scalar_encoding(|left| {
            let candidate = left.check_scalar_candidate(&sat_model(left))?;
            second.with_scalar_encoding(|right| {
                assert_eq!(
                    right.replay_scalar_candidate(&candidate),
                    Err(Error::InvalidCandidate)
                );
                Ok(())
            })?;
            left.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    first.finish().unwrap();
    second.finish().unwrap();
}

#[test]
fn wide_noncanonical_model_cells_are_not_silently_truncated() {
    let original = ample();
    let mut array = Array::empty(TermId(3), ScalarSort::BitVec(2), ScalarSort::BitVec(2));
    for cell in [
        ReadValue {
            index: ScalarValue::BitVec(4, 2),
            value: ScalarValue::BitVec(0, 2),
        },
        ReadValue {
            index: ScalarValue::BitVec(0, 2),
            value: ScalarValue::BitVec(4, 2),
        },
        ReadValue {
            index: ScalarValue::BitVec(0, 128),
            value: ScalarValue::BitVec(0, 2),
        },
    ] {
        assert_eq!(
            decode::insert(&mut array, cell, &original),
            Err(Error::InvalidCandidate)
        );
        assert!(array.cells.is_empty());
    }
}
