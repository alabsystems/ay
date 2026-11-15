// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{ChildSpec, Guard, NodeLabel};

fn bv(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

fn constant(default: bool, width: u32) -> ChcExpr {
    ChcExpr::const_array(ChcSort::BitVec(width), ChcExpr::Bool(default))
}

fn store(array: ChcExpr, index: ChcExpr, value: ChcExpr) -> ChcExpr {
    op(ChcOp::Store, vec![array, index, value])
}

fn captured_identity() -> ChcExpr {
    let inner = store(constant(true, 32), bv(66, 32), ChcExpr::Bool(false));
    ChcExpr::eq(store(inner.clone(), bv(67, 32), ChcExpr::Bool(true)), inner)
}

#[test]
fn captured_realloc_constant_array_writes_preserve_their_exact_bases() {
    let original = constant(true, 32);
    let no_change = store(original.clone(), bv(66, 32), ChcExpr::Bool(true));
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(no_change, original)),
        Ok(true)
    );
    assert_eq!(prove(&ChcExpr::Bool(true), &captured_identity()), Ok(true));
}

#[test]
fn all_two_cell_store_pairs_agree_with_their_actual_read_values() {
    for default in [false, true] {
        for first_index in 0..2 {
            for second_index in 0..2 {
                for first_value in [false, true] {
                    for second_value in [false, true] {
                        let base = store(
                            constant(default, 1),
                            bv(first_index, 1),
                            ChcExpr::Bool(first_value),
                        );
                        let updated = store(
                            base.clone(),
                            bv(second_index, 1),
                            ChcExpr::Bool(second_value),
                        );
                        let old_value = if first_index == second_index {
                            first_value
                        } else {
                            default
                        };
                        assert_eq!(
                            prove(&ChcExpr::Bool(true), &ChcExpr::eq(updated, base)),
                            Ok(old_value == second_value),
                            "default={default}, first=({first_index},{first_value}), second=({second_index},{second_value})"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn unknown_index_overlap_does_not_prove_a_store_redundant() {
    let i = variable("i", ChcSort::BitVec(2));
    let j = variable("j", ChcSort::BitVec(2));
    let base = store(constant(true, 2), j, ChcExpr::Bool(false));
    let updated = store(base.clone(), i, ChcExpr::Bool(true));
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(updated, base)),
        Ok(false)
    );
}

#[test]
fn proved_index_and_value_aliases_allow_the_same_value_write() {
    let i = variable("i", ChcSort::BitVec(2));
    let j = variable("j", ChcSort::BitVec(2));
    let value = variable("value", ChcSort::Bool);
    let body = op(
        ChcOp::And,
        vec![
            ChcExpr::eq(i.clone(), j.clone()),
            ChcExpr::eq(value.clone(), ChcExpr::Bool(false)),
        ],
    );
    let base = store(constant(true, 2), i, ChcExpr::Bool(false));
    let updated = store(base.clone(), j, value);
    assert_eq!(prove(&body, &ChcExpr::eq(updated, base)), Ok(true));
}

#[test]
fn a_dead_store_does_not_hide_malformed_index_or_value_sorts() {
    for inner in [
        store(constant(true, 2), bv(0, 3), ChcExpr::Bool(false)),
        store(constant(true, 2), bv(0, 2), bv(0, 1)),
    ] {
        let updated = store(inner.clone(), bv(1, 2), ChcExpr::Bool(true));
        let dead = op(
            ChcOp::Ite,
            vec![ChcExpr::Bool(false), updated, constant(true, 2)],
        );
        assert_eq!(
            prove(&ChcExpr::Bool(false), &ChcExpr::eq(dead, inner)),
            Ok(false)
        );
    }
}

#[test]
fn nested_store_walk_shares_the_original_work_allowance() {
    let head = captured_identity();
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let entered = generous.enter();
    assert_eq!(prove(&ChcExpr::Bool(true), &head), Ok(true));
    let used = generous.ticks();
    assert!(used > 1);
    drop(entered);

    let exact = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used + 1)));
    let entered = exact.enter();
    assert_eq!(prove(&ChcExpr::Bool(true), &head), Ok(true));
    assert_eq!(exact.ticks(), used);
    drop(entered);

    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let entered = short.enter();
    let mut owner = Owner::capture().unwrap();
    assert_eq!(
        entails(&ChcExpr::Bool(true), &head, &mut owner),
        Err(Error::Resource)
    );
    drop(entered);
    let replacement =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let _replacement = replacement.enter();
    assert_eq!(
        entails(&ChcExpr::Bool(true), &head, &mut owner),
        Err(Error::Resource)
    );
    assert_eq!(replacement.ticks(), 0);
}
