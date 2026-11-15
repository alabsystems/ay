// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::{index::ReadIndex, Budget, Expr, ExprValue, ScalarSort, VariableSort};
use crate::sort::Sort;
use num_bigint::{BigInt, Sign};
use std::sync::Arc;

enum Value<'a> {
    Read {
        array: &'a Expr,
        sort: &'a Sort,
        index: ReadIndex<'a>,
    },
    Scalar(&'a Expr),
}

impl<'a> Value<'a> {
    fn parse(
        node: &'a Expr,
        binder: &str,
        width: u32,
        budget: &mut Budget<'a>,
    ) -> Option<(Self, ScalarSort)> {
        budget.work(1)?;
        let result_sort = ScalarSort::from_sort(node.sort())?;
        match node.value() {
            ExprValue::Select { array, index } => {
                budget.work(2)?;
                let index = ReadIndex::parse(index, binder, width, budget)?;
                let ExprValue::Var { name } = array.value() else {
                    return None;
                };
                let array_sort = array.sort().array_sort()?;
                if name == binder
                    || array_sort.index_sort.bitvec_width() != Some(width)
                    || ScalarSort::from_sort(&array_sort.element_sort)? != result_sort
                {
                    return None;
                }
                budget.variable(
                    name,
                    VariableSort::Array {
                        index: width,
                        element: result_sort,
                    },
                )?;
                Some((
                    Self::Read {
                        array,
                        sort: &array_sort.element_sort,
                        index,
                    },
                    result_sort,
                ))
            }
            ExprValue::Var { name } => {
                if name == binder {
                    return None;
                }
                budget.variable(name, VariableSort::Scalar(result_sort))?;
                Some((Self::Scalar(node), result_sort))
            }
            ExprValue::BoolConst(_) if result_sort == ScalarSort::Bool => {
                Some((Self::Scalar(node), result_sort))
            }
            ExprValue::BitVecConst { value, width } => {
                if result_sort != ScalarSort::BitVec(*width)
                    || value.sign() == Sign::Minus
                    || value.bits() > u64::from(*width)
                {
                    return None;
                }
                // No magnitude-sized arithmetic or cloning: preserve the
                // original canonical BigInt behind the shared ExprValue Arc.
                Some((Self::Scalar(node), result_sort))
            }
            _ => None,
        }
    }

    fn extra_output_cost(&self) -> usize {
        match self {
            Self::Read { index, .. } => index.extra_output_cost(),
            Self::Scalar(_) => 0,
        }
    }

    fn instantiate(&self, ground_index: &Expr) -> Expr {
        match self {
            Self::Read { array, sort, index } => Expr {
                sort: (*sort).clone(),
                value: Arc::new(ExprValue::Select {
                    array: (*array).clone(),
                    index: index.instantiate(ground_index),
                }),
            },
            Self::Scalar(value) => (*value).clone(),
        }
    }
}

pub(super) struct Equality<'a> {
    left: Value<'a>,
    right: Value<'a>,
}

impl<'a> Equality<'a> {
    pub(super) fn parse(
        node: &'a Expr,
        binder: &str,
        width: u32,
        budget: &mut Budget<'a>,
    ) -> Option<Self> {
        budget.work(1)?;
        if !node.sort().is_bool() {
            return None;
        }
        let ExprValue::Eq(left, right) = node.value() else {
            return None;
        };
        let (left, left_sort) = Value::parse(left, binder, width, budget)?;
        let (right, right_sort) = Value::parse(right, binder, width, budget)?;
        if left_sort != right_sort
            || !matches!(
                (&left, &right),
                (Value::Read { .. }, _) | (_, Value::Read { .. })
            )
        {
            return None;
        }
        Some(Self { left, right })
    }

    pub(super) fn output_cost(&self) -> Option<usize> {
        // Conservative allocation/edge units: one index, equality, output slot,
        // two operands, and up to two three-cell reads. Scalars/arrays are shared.
        // A translated read additionally emits its operation and two edges.
        11usize
            .checked_add(self.left.extra_output_cost())?
            .checked_add(self.right.extra_output_cost())
    }

    pub(super) fn instantiate(&self, index: u128, width: u32) -> Expr {
        // The guard authenticated index < 2^width and width <= 64. Construct
        // that bounded literal directly, without a width-sized modulus.
        let index = Expr {
            sort: Sort::bitvec(width),
            value: Arc::new(ExprValue::BitVecConst {
                value: BigInt::from(index),
                width,
            }),
        };
        Expr {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Eq(
                self.left.instantiate(&index),
                self.right.instantiate(&index),
            )),
        }
    }
}
