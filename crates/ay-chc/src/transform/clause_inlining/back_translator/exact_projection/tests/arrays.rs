// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod negative;
mod oracle;
mod resources;

fn array(name: &str, key: ChcSort, value: ChcSort) -> ChcVar {
    ChcVar::new(name, ChcSort::Array(Box::new(key), Box::new(value)))
}

fn constant(key: ChcSort, value: ChcExpr) -> ChcExpr {
    ChcExpr::ConstArray(key, Arc::new(value))
}

fn select(base: ChcExpr, key: ChcExpr) -> ChcExpr {
    op(ChcOp::Select, vec![base, key])
}

fn store(base: ChcExpr, key: ChcExpr, value: ChcExpr) -> ChcExpr {
    op(ChcOp::Store, vec![base, key, value])
}

#[test]
fn unused_array_formals_do_not_prevent_scalar_exact_projection() {
    let a = var("a", 2);
    let x = var("x", 2);
    let memory = array("memory", ChcSort::BitVec(32), ChcSort::Bool);
    let projected = closed(&eq(expr(&a), quotient(&x, 2)), &[a, memory]);
    for value in 0..4 {
        assert_eq!(oracle::truth(&projected, &[("a", value)]), value < 2);
    }
}

#[test]
fn closed_array_atoms_and_scalar_images_match_complete_finite_tables() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::Bool);
    let a = var("a", 2);
    let x = var("x", 2);
    let formula = op(
        ChcOp::And,
        vec![
            select(expr(&memory), ChcExpr::BitVec(0, 1)),
            eq(expr(&a), quotient(&x, 2)),
        ],
    );
    let projected = closed(&formula, &[memory, a]);
    for memory in 0..4 {
        for a in 0..4 {
            let expected =
                (0..4).any(|x| oracle::truth(&formula, &[("memory", memory), ("a", a), ("x", x)]));
            assert_eq!(
                oracle::truth(&projected, &[("memory", memory), ("a", a)]),
                expected
            );
        }
    }
}

#[test]
fn typed_array_alias_and_store_definitions_preserve_all_observations() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let local = array("local", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let alias = array("alias", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let index = var("index", 1);
    let result = var("result", 2);
    let formula = op(
        ChcOp::And,
        vec![
            eq(
                expr(&local),
                store(expr(&memory), expr(&index), ChcExpr::BitVec(3, 2)),
            ),
            eq(expr(&alias), expr(&local)),
            eq(expr(&result), select(expr(&alias), ChcExpr::BitVec(0, 1))),
        ],
    );
    let projected = closed(&formula, &[memory, index, result]);
    for memory in 0..16 {
        for index in 0..2 {
            for result in 0..4 {
                let expected = (0..16).any(|local| {
                    (0..16).any(|alias| {
                        oracle::truth(
                            &formula,
                            &[
                                ("memory", memory),
                                ("index", index),
                                ("result", result),
                                ("local", local),
                                ("alias", alias),
                            ],
                        )
                    })
                });
                assert_eq!(
                    oracle::truth(
                        &projected,
                        &[("memory", memory), ("index", index), ("result", result)]
                    ),
                    expected
                );
            }
        }
    }
}

#[test]
fn constant_array_default_is_rewritten_after_its_scalar_alias_closes() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let local = var("local", 2);
    let a = var("a", 2);
    let formula = op(
        ChcOp::And,
        vec![
            eq(expr(&local), expr(&a)),
            eq(expr(&memory), constant(ChcSort::BitVec(1), expr(&local))),
        ],
    );
    let projected = closed(&formula, &[memory, a]);
    for memory in 0..16 {
        for a in 0..4 {
            let expected = (0..4).any(|local| {
                oracle::truth(&formula, &[("memory", memory), ("a", a), ("local", local)])
            });
            assert_eq!(
                oracle::truth(&projected, &[("memory", memory), ("a", a)]),
                expected
            );
        }
    }
}

#[test]
fn boolean_index_and_array_ite_retain_exact_extensional_equality() {
    let memory = array("memory", ChcSort::Bool, ChcSort::Bool);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let choice = op(
        ChcOp::Ite,
        vec![
            expr(&flag),
            store(expr(&memory), ChcExpr::Bool(false), ChcExpr::Bool(true)),
            constant(ChcSort::Bool, ChcExpr::Bool(false)),
        ],
    );
    let formula = eq(choice, expr(&memory));
    let projected = closed(&formula, &[memory, flag]);
    for memory in 0..4 {
        for flag in 0..2 {
            let values = [("memory", memory), ("flag", flag)];
            assert_eq!(
                oracle::truth(&projected, &values),
                oracle::truth(&formula, &values)
            );
        }
    }
}

#[test]
fn branch_local_array_definitions_preserve_common_and_alternative_correlation() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::Bool);
    let local = array("local", ChcSort::BitVec(1), ChcSort::Bool);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let left = op(
        ChcOp::And,
        vec![
            eq(expr(&local), expr(&memory)),
            select(expr(&local), ChcExpr::BitVec(0, 1)),
        ],
    );
    let right = op(
        ChcOp::And,
        vec![
            eq(
                expr(&local),
                constant(ChcSort::BitVec(1), ChcExpr::Bool(false)),
            ),
            op(
                ChcOp::Not,
                vec![select(expr(&memory), ChcExpr::BitVec(1, 1))],
            ),
        ],
    );
    let formula = op(
        ChcOp::And,
        vec![expr(&flag), op(ChcOp::Or, vec![left, right])],
    );
    let projected = closed(&formula, &[memory, flag]);
    for memory in 0..4 {
        for flag in 0..2 {
            let expected = (0..4).any(|local| {
                oracle::truth(
                    &formula,
                    &[("memory", memory), ("flag", flag), ("local", local)],
                )
            });
            assert_eq!(
                oracle::truth(&projected, &[("memory", memory), ("flag", flag)]),
                expected
            );
        }
    }
}

#[test]
fn four_cell_array_reads_with_branch_local_index_aliases_match_full_tables() {
    let memory = array("memory", ChcSort::BitVec(2), ChcSort::Bool);
    let index = var("index", 2);
    let formula = op(
        ChcOp::Or,
        vec![
            op(
                ChcOp::And,
                vec![
                    eq(expr(&index), ChcExpr::BitVec(0, 2)),
                    select(expr(&memory), expr(&index)),
                ],
            ),
            op(
                ChcOp::And,
                vec![
                    eq(expr(&index), ChcExpr::BitVec(3, 2)),
                    op(ChcOp::Not, vec![select(expr(&memory), expr(&index))]),
                ],
            ),
        ],
    );
    let projected = closed(&formula, &[memory]);
    for memory in 0..16 {
        let expected =
            (0..4).any(|index| oracle::truth(&formula, &[("memory", memory), ("index", index)]));
        assert_eq!(oracle::truth(&projected, &[("memory", memory)]), expected);
    }
}

#[test]
fn pure_array_alias_cycles_have_an_exact_inhabited_witness() {
    let a = array("a", ChcSort::BitVec(1), ChcSort::Bool);
    let b = array("b", ChcSort::BitVec(1), ChcSort::Bool);
    let formula = op(
        ChcOp::And,
        vec![eq(expr(&a), expr(&b)), eq(expr(&b), expr(&a))],
    );
    let projected = closed(&formula, &[]);
    let expected = (0..4).any(|a| (0..4).any(|b| oracle::truth(&formula, &[("a", a), ("b", b)])));
    assert_eq!(oracle::truth(&projected, &[]), expected);
}
