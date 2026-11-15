// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Alpha-renamed checked subtraction/product definitions from the original
//! MODEL_CHECKER_CONSUMER `arithunsafe.main.smt2`, lines154-159/174-179, retained under
//! the development design notes (source SHA-256
//! 930169683f90ac1df75953659eb8da9f42b91dc9384733f0c0a04418856304b1).
//! These are source-shaped finite oracles, not a claim about whole-input replay.

use super::*;

#[derive(Clone, Copy)]
enum Conditional {
    Value,
    Boolean,
}

#[derive(Clone, Copy)]
enum Guard {
    Canonical,
    DoubleNegated,
}

fn formals(arithmetic: Arithmetic, width: u32) -> Vec<ChcVar> {
    let (count, bools, fields): (usize, &[usize], &[(usize, &str)]) = match arithmetic {
        Arithmetic::Difference => (
            19,
            &[0, 3, 4, 8, 12, 14, 17],
            &[
                (0, "previous_valid"),
                (1, "previous_checked"),
                (2, "previous_result"),
                (4, "valid"),
                (5, "checked"),
                (7, "result"),
                (8, "flag"),
            ],
        ),
        Arithmetic::Product => (
            14,
            &[0, 3, 4, 7, 8, 12],
            &[
                (0, "previous_valid"),
                (1, "previous_checked"),
                (2, "previous_result"),
                (4, "prior_valid"),
                (5, "prior_checked"),
                (6, "prior_result"),
                (8, "valid"),
                (9, "checked"),
                (11, "result"),
                (12, "flag"),
            ],
        ),
    };
    (0..count)
        .map(|index| {
            let name = fields.iter().find(|(slot, _)| *slot == index).map_or_else(
                || format!("unused_{index}"),
                |(_, name)| (*name).to_string(),
            );
            ChcVar::new(
                name,
                if bools.contains(&index) {
                    ChcSort::Bool
                } else {
                    ChcSort::BitVec(width)
                },
            )
        })
        .collect()
}

fn source(
    arithmetic: Arithmetic,
    width: u32,
    conditional: Conditional,
    guard: Guard,
) -> (ChcExpr, Vec<ChcVar>) {
    let keep = formals(arithmetic, width);
    let x = var("x", width);
    let y = var("y", width);
    let result = low(arithmetic, &x, &y);
    let observed = observation(arithmetic, &x, &y, width);
    let (good, error) = match arithmetic {
        Arithmetic::Difference => (op(ChcOp::Not, vec![observed.clone()]), observed),
        Arithmetic::Product => (observed.clone(), op(ChcOp::Not, vec![observed])),
    };
    let good = match guard {
        Guard::Canonical => good,
        Guard::DoubleNegated => op(ChcOp::Not, vec![op(ChcOp::Not, vec![good])]),
    };
    let checked = expr(&var("checked", width));
    let zero = ChcExpr::BitVec(0, width);
    let conditional = match conditional {
        Conditional::Value => eq(
            checked,
            op(ChcOp::Ite, vec![good.clone(), result.clone(), zero]),
        ),
        Conditional::Boolean => op(
            ChcOp::Ite,
            vec![
                good.clone(),
                eq(checked.clone(), result.clone()),
                eq(checked, zero),
            ],
        ),
    };
    let valid = expr(&ChcVar::new("valid", ChcSort::Bool));
    let mut atoms = vec![
        expr(&ChcVar::new("previous_valid", ChcSort::Bool)),
        eq(
            expr(&var("previous_checked", width)),
            expr(&var("previous_result", width)),
        ),
        eq(expr(&var("result", width)), result),
        eq(expr(&ChcVar::new("flag", ChcSort::Bool)), error),
        good.clone(),
        eq(valid.clone(), good),
        conditional,
        valid,
    ];
    if matches!(arithmetic, Arithmetic::Product) {
        atoms.extend([
            expr(&ChcVar::new("prior_valid", ChcSort::Bool)),
            eq(
                expr(&var("prior_checked", width)),
                expr(&var("prior_result", width)),
            ),
        ]);
    }
    (op(ChcOp::And, atoms), keep)
}

fn context() -> Vec<(&'static str, u128)> {
    vec![
        ("previous_valid", 1),
        ("previous_checked", 1),
        ("previous_result", 1),
        ("prior_valid", 1),
        ("prior_checked", 0),
        ("prior_result", 0),
    ]
}

#[test]
fn exact_source_shapes_preserve_conditional_result_correlations() {
    for (arithmetic, boolean_nodes, value_nodes, arity) in [
        (Arithmetic::Difference, 39, 37, 19),
        (Arithmetic::Product, 61, 59, 14),
    ] {
        assert_eq!(
            source(arithmetic, 8, Conditional::Boolean, Guard::Canonical)
                .0
                .node_count(1000),
            boolean_nodes
        );
        assert_eq!(
            source(arithmetic, 8, Conditional::Value, Guard::Canonical)
                .0
                .node_count(1000),
            value_nodes
        );
        for width in 1..=3 {
            let size = 1u128 << width;
            for conditional in [Conditional::Value, Conditional::Boolean] {
                for guard in [Guard::Canonical, Guard::DoubleNegated] {
                    let (formula, keep) = source(arithmetic, width, conditional, guard);
                    assert_eq!(keep.len(), arity);
                    let projected = closed(&formula, &keep);
                    for result in 0..size {
                        for checked in 0..size {
                            for valid in 0..2 {
                                for error in 0..2 {
                                    let mut values = context();
                                    values.extend([
                                        ("result", result),
                                        ("checked", checked),
                                        ("valid", valid),
                                        ("flag", error),
                                    ]);
                                    let exists = (0..size).any(|x| {
                                        (0..size).any(|y| {
                                            let mut local_values = values.clone();
                                            local_values.extend([("x", x), ("y", y)]);
                                            oracle::truth(&formula, &local_values)
                                        })
                                    });
                                    assert_eq!(oracle::truth(&projected, &values), exists);
                                    assert_eq!(
                                        exists,
                                        valid == 1 && error == 0 && checked == result
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn inherited_guards_and_both_checked_result_equalities_remain_required() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        for conditional in [Conditional::Value, Conditional::Boolean] {
            let (formula, keep) = source(arithmetic, 8, conditional, Guard::Canonical);
            let projected = closed(&formula, &keep);
            let mut values = context();
            values.extend([("result", 255), ("checked", 255), ("valid", 1), ("flag", 0)]);
            assert!(oracle::truth(&projected, &values));
            let mut mutations = vec![
                ("previous_valid", 0),
                ("previous_result", 0),
                ("checked", 127),
            ];
            if matches!(arithmetic, Arithmetic::Product) {
                mutations.extend([("prior_valid", 0), ("prior_result", 1)]);
            }
            for (name, replacement) in mutations {
                let mut changed = values.clone();
                changed.iter_mut().find(|(key, _)| *key == name).unwrap().1 = replacement;
                assert!(!oracle::truth(&projected, &changed), "lost {name}");
            }
        }
    }
}

#[test]
fn operand_alias_chains_are_eliminated_before_joint_observation_matching() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (formula, keep) = source(arithmetic, 2, Conditional::Boolean, Guard::DoubleNegated);
        let mut atoms = vec![formula];
        for name in ["x", "y"] {
            let mut previous = var(name, 2);
            for index in 0..12 {
                let next = var(&format!("{name}_alias_{index}"), 2);
                atoms.push(eq(expr(&previous), expr(&next)));
                previous = next;
            }
        }
        let projected = closed(&op(ChcOp::And, atoms), &keep);
        for result in 0..4 {
            for checked in 0..4 {
                let mut values = context();
                values.extend([
                    ("result", result),
                    ("checked", checked),
                    ("valid", 1),
                    ("flag", 0),
                ]);
                assert_eq!(oracle::truth(&projected, &values), result == checked);
            }
        }
    }
}
