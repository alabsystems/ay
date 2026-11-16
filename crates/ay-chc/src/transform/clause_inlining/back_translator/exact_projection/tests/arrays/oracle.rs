// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent complete tables for tiny finite arrays. This evaluator calls
//! neither projection, the production array evaluator nor an SMT solver.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scalar {
    Bool,
    Bv(u32),
}

impl Scalar {
    fn read(sort: &ChcSort) -> Self {
        match sort {
            ChcSort::Bool => Self::Bool,
            ChcSort::BitVec(width @ 1..=128) => Self::Bv(*width),
            _ => panic!("unsupported tiny oracle sort"),
        }
    }

    fn bits(self) -> u32 {
        match self {
            Self::Bool => 1,
            Self::Bv(width) => width,
        }
    }

    fn domain(self) -> usize {
        match self {
            Self::Bool => 2,
            Self::Bv(width @ 1..=2) => 1 << width,
            _ => panic!("tiny array index domain exceeds four cells"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Table {
    index: Scalar,
    element: Scalar,
    cells: [u128; 4],
}

impl Table {
    fn packed(key: &ChcSort, element: &ChcSort, packed: u128) -> Self {
        let (index, element) = (Scalar::read(key), Scalar::read(element));
        assert!(element.bits() <= 8, "tiny packed element domain");
        let mut cells = [0; 4];
        for (position, cell) in cells.iter_mut().take(index.domain()).enumerate() {
            *cell = (packed >> (position as u32 * element.bits())) & mask(element.bits());
        }
        Self {
            index,
            element,
            cells,
        }
    }

    fn constant(key: &ChcSort, value: Value) -> Self {
        let (element, raw) = value.scalar();
        let index = Scalar::read(key);
        let mut cells = [0; 4];
        for cell in cells.iter_mut().take(index.domain()) {
            *cell = raw;
        }
        Self {
            index,
            element,
            cells,
        }
    }

    fn position(self, value: Value) -> usize {
        let (sort, raw) = value.scalar();
        assert_eq!(sort, self.index);
        let position = usize::try_from(raw).expect("tiny index fits usize");
        assert!(position < self.index.domain());
        position
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u128, u32),
    Array(Table),
}

impl Value {
    fn scalar(self) -> (Scalar, u128) {
        match self {
            Self::Bool(value) => (Scalar::Bool, u128::from(value)),
            Self::Bv(value, width) => (Scalar::Bv(width), value),
            Self::Array(_) => panic!("expected scalar"),
        }
    }

    fn boolean(self) -> bool {
        let Self::Bool(value) = self else {
            panic!("expected Boolean")
        };
        value
    }
}

fn mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1 << width) - 1
    }
}

pub(super) fn truth(expr: &ChcExpr, values: &[(&str, u128)]) -> bool {
    evaluate(expr, values).boolean()
}

fn evaluate(expr: &ChcExpr, values: &[(&str, u128)]) -> Value {
    match expr {
        ChcExpr::Bool(value) => Value::Bool(*value),
        ChcExpr::BitVec(value, width) => Value::Bv(*value, *width),
        ChcExpr::Var(var) => {
            let raw = values
                .iter()
                .find(|(name, _)| *name == var.name)
                .expect("bound oracle variable")
                .1;
            match &var.sort {
                ChcSort::Bool => Value::Bool(raw != 0),
                ChcSort::BitVec(width) => Value::Bv(raw & mask(*width), *width),
                ChcSort::Array(key, value) => Value::Array(Table::packed(key, value, raw)),
                _ => panic!("unsupported fixture variable"),
            }
        }
        ChcExpr::ConstArray(key, value) => {
            Value::Array(Table::constant(key, evaluate(value, values)))
        }
        ChcExpr::Op(operation, args) => {
            let args: Vec<_> = args.iter().map(|arg| evaluate(arg, values)).collect();
            operation_value(*operation, &args)
        }
        _ => panic!("unsupported fixture expression"),
    }
}

fn operation_value(operation: ChcOp, args: &[Value]) -> Value {
    match operation {
        ChcOp::And => Value::Bool(args.iter().all(|value| value.boolean())),
        ChcOp::Or => Value::Bool(args.iter().any(|value| value.boolean())),
        ChcOp::Not => Value::Bool(!args[0].boolean()),
        ChcOp::Eq => Value::Bool(args[0] == args[1]),
        ChcOp::Ne => Value::Bool(args[0] != args[1]),
        ChcOp::Ite => {
            if args[0].boolean() {
                args[1]
            } else {
                args[2]
            }
        }
        ChcOp::Select | ChcOp::Store => {
            let Value::Array(mut table) = args[0] else {
                panic!("expected table")
            };
            let position = table.position(args[1]);
            if operation == ChcOp::Store {
                let (element, raw) = args[2].scalar();
                assert_eq!(element, table.element);
                table.cells[position] = raw;
                Value::Array(table)
            } else {
                match table.element {
                    Scalar::Bool => Value::Bool(table.cells[position] != 0),
                    Scalar::Bv(width) => Value::Bv(table.cells[position], width),
                }
            }
        }
        ChcOp::BvUDiv | ChcOp::BvAdd | ChcOp::BvULe => {
            let (left_sort, left) = args[0].scalar();
            let (right_sort, right) = args[1].scalar();
            assert_eq!(left_sort, right_sort);
            let Scalar::Bv(width) = left_sort else {
                panic!("expected bitvector")
            };
            match operation {
                ChcOp::BvUDiv => Value::Bv(
                    match left.checked_div(right) {
                        Some(quotient) => quotient,
                        None => mask(width),
                    },
                    width,
                ),
                ChcOp::BvAdd => Value::Bv(left.wrapping_add(right) & mask(width), width),
                ChcOp::BvULe => Value::Bool(left <= right),
                _ => unreachable!(),
            }
        }
        _ => panic!("unsupported fixture operation"),
    }
}

#[test]
fn bvudiv_oracle_matches_smt_zero_and_nonzero_semantics() {
    let expected = [[3, 0, 0, 0], [3, 1, 0, 0], [3, 2, 1, 0], [3, 3, 1, 1]];
    for left in 0..4 {
        for right in 0..4 {
            assert_eq!(
                operation_value(ChcOp::BvUDiv, &[Value::Bv(left, 2), Value::Bv(right, 2)]),
                Value::Bv(expected[left as usize][right as usize], 2),
                "left={left} right={right}"
            );
        }
    }
}
