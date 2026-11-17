// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use crate::{Expr, ExprValue, Sort};
use num_traits::ToPrimitive;
use std::sync::Arc;

#[derive(Clone, Copy)]
struct Model {
    data: u8,
    fresh: u8,
    fill: bool,
    index: u8,
}

fn bit(array: u8, index: u8) -> bool {
    array & (1 << index) != 0
}

fn bits(expr: &Expr, model: Model) -> u8 {
    match expr.value() {
        ExprValue::Var { name } if name == "i" => model.index,
        ExprValue::BitVecConst { value, width: 2 } => value.to_u8().unwrap(),
        other => panic!("unexpected BV2 oracle node: {other:?}"),
    }
}

fn truth(expr: &Expr, model: Model) -> bool {
    match expr.value() {
        ExprValue::BoolConst(value) => *value,
        ExprValue::Var { name } if name == "fill" => model.fill,
        ExprValue::And(args) => args.iter().all(|arg| truth(arg, model)),
        ExprValue::Or(args) => args.iter().any(|arg| truth(arg, model)),
        ExprValue::Not(arg) => !truth(arg, model),
        ExprValue::Implies(left, right) => !truth(left, model) || truth(right, model),
        ExprValue::Eq(left, right) => {
            if left.sort().is_bool() {
                truth(left, model) == truth(right, model)
            } else {
                bits(left, model) == bits(right, model)
            }
        }
        ExprValue::BvULt(left, right) => bits(left, model) < bits(right, model),
        ExprValue::BvULe(left, right) => bits(left, model) <= bits(right, model),
        ExprValue::BvUGt(left, right) => bits(left, model) > bits(right, model),
        ExprValue::BvUGe(left, right) => bits(left, model) >= bits(right, model),
        ExprValue::Select { array, index } => {
            let ExprValue::Var { name } = array.value() else {
                panic!("oracle requires a source array variable")
            };
            let array = match name.as_str() {
                "data" => model.data,
                "fresh" => model.fresh,
                _ => panic!("unknown source array"),
            };
            bit(array, bits(index, model))
        }
        ExprValue::Forall {
            vars,
            body,
            triggers,
        } => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "i");
            assert_eq!(vars[0].1.bitvec_width(), Some(2));
            assert_eq!(triggers.as_slice(), &[] as &[Vec<Expr>]);
            (0..4).all(|index| truth(body, Model { index, ..model }))
        }
        other => panic!("unexpected Boolean oracle node: {other:?}"),
    }
}

fn source_array(name: &str) -> Expr {
    Expr::var(name, Sort::array(Sort::bitvec(2), Sort::bool()))
}

fn index() -> Expr {
    Expr::var("i", Sort::bitvec(2))
}

fn assert_full_table(body: Expr, expected: impl Fn(Model) -> bool) {
    let vars = vec![("i".to_owned(), Sort::bitvec(2))];
    // Deliberately bypass every quantifier constructor for the original. The
    // reference must not accidentally normalize using the code under test.
    let original = Expr {
        sort: Sort::bool(),
        value: Arc::new(ExprValue::Forall {
            vars: vars.clone(),
            body: body.clone(),
            triggers: Vec::new(),
        }),
    };
    let rewritten = Expr::forall(vars, body);
    assert!(!matches!(rewritten.value(), ExprValue::Forall { .. }));
    for data in 0..16 {
        for fresh in 0..16 {
            for fill in [false, true] {
                let model = Model {
                    data,
                    fresh,
                    fill,
                    index: 0,
                };
                let expected = expected(model);
                assert_eq!(
                    truth(&original, model),
                    expected,
                    "raw: {data}/{fresh}/{fill}"
                );
                assert_eq!(
                    truth(&rewritten, model),
                    expected,
                    "new: {data}/{fresh}/{fill}"
                );
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Fill {
    Missing,
    Literal(bool),
    Variable,
}

impl Fill {
    fn value(self, model: Model) -> Option<bool> {
        match self {
            Self::Missing => None,
            Self::Literal(value) => Some(value),
            Self::Variable => Some(model.fill),
        }
    }
}

fn resize_body(old: u8, new: u8, fill: Fill) -> Expr {
    let read = source_array("fresh").select(index());
    let prefix = index()
        .bvult(Expr::bitvec_const(old, 2))
        .implies(read.clone().eq(source_array("data").select(index())));
    let value = match fill {
        Fill::Missing => return prefix,
        Fill::Literal(value) => Expr::bool_const(value),
        Fill::Variable => Expr::var("fill", Sort::bool()),
    };
    let appended = Expr::and_many(vec![
        Expr::bitvec_const(old, 2).bvule(index()),
        index().bvult(Expr::bitvec_const(new, 2)),
    ])
    .implies(read.eq(value));
    Expr::and_many(vec![prefix, appended])
}

#[test]
fn resize_and_missing_fill_match_raw_forall_for_every_small_array_and_bound() {
    for old in 0..4 {
        for new in 0..4 {
            for fill in [
                Fill::Missing,
                Fill::Literal(false),
                Fill::Literal(true),
                Fill::Variable,
            ] {
                assert_full_table(resize_body(old, new, fill), |model| {
                    (0..4).all(|index| {
                        let actual = bit(model.fresh, index);
                        (index >= old || actual == bit(model.data, index))
                            && match fill.value(model) {
                                Some(value) if old <= index && index < new => actual == value,
                                _ => true,
                            }
                    })
                });
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Comparison {
    Lt,
    Le,
    Gt,
    Ge,
}

impl Comparison {
    fn expression(self, left: Expr, right: Expr) -> Expr {
        match self {
            Self::Lt => left.bvult(right),
            Self::Le => left.bvule(right),
            Self::Gt => left.bvugt(right),
            Self::Ge => left.bvuge(right),
        }
    }

    fn holds(self, left: u8, right: u8) -> bool {
        match self {
            Self::Lt => left < right,
            Self::Le => left <= right,
            Self::Gt => left > right,
            Self::Ge => left >= right,
        }
    }
}

#[test]
fn unsigned_guards_in_both_orientations_preserve_zero_and_maximum_endpoints() {
    for comparison in [
        Comparison::Lt,
        Comparison::Le,
        Comparison::Gt,
        Comparison::Ge,
    ] {
        for reversed in [false, true] {
            for bound in 0..4 {
                let constant = Expr::bitvec_const(bound, 2);
                let guard = if reversed {
                    comparison.expression(constant, index())
                } else {
                    comparison.expression(index(), constant)
                };
                let body = guard.implies(
                    source_array("fresh")
                        .select(index())
                        .eq(source_array("data").select(index())),
                );
                assert_full_table(body, |model| {
                    (0..4).all(|index| {
                        let guarded = if reversed {
                            comparison.holds(bound, index)
                        } else {
                            comparison.holds(index, bound)
                        };
                        !guarded || bit(model.fresh, index) == bit(model.data, index)
                    })
                });
            }
        }
    }
}
