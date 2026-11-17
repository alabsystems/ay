// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact borrowed Expr whitelist; no renderer parsing or fallback terms.

mod bitvectors;
mod floating;

use ay_bindings::{Expr, ExprValue, SortInner};
use ay_chc::ChcSort;

use super::FpAdapterError;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Scalar {
    Bool,
    Bv(u32),
    Fp(u32, u32),
}

impl Scalar {
    pub(super) fn core(self) -> ay_core::Sort {
        match self {
            Self::Bool => ay_core::Sort::Bool,
            Self::Bv(w) => ay_core::Sort::bitvec(w),
            Self::Fp(e, s) => ay_core::Sort::FloatingPoint(e, s),
        }
    }
    pub(super) fn binding(self, target: &ChcSort) -> bool {
        match (self, target) {
            (Self::Bool, ChcSort::Bool) => true,
            (Self::Bv(w), ChcSort::BitVec(t)) => w == *t,
            (Self::Fp(e, s), ChcSort::BitVec(t)) => e + s == *t,
            _ => false,
        }
    }
}

pub(super) fn scalar(expr: &Expr) -> Result<Scalar, FpAdapterError> {
    match expr.sort().inner() {
        SortInner::Bool => Ok(Scalar::Bool),
        SortInner::BitVec(bits) if (1..=64).contains(&bits.width) => Ok(Scalar::Bv(bits.width)),
        SortInner::FloatingPoint(8, 24) => Ok(Scalar::Fp(8, 24)),
        SortInner::FloatingPoint(11, 53) => Ok(Scalar::Fp(11, 53)),
        _ => Err(FpAdapterError::Unsupported("typed scalar format")),
    }
}

#[derive(Clone)]
pub(super) enum Children<'a> {
    Slice(std::slice::Iter<'a, Expr>),
    Fixed(std::array::IntoIter<Option<&'a Expr>, 3>),
}
impl<'a> Iterator for Children<'a> {
    type Item = &'a Expr;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Slice(iter) => iter.next(),
            Self::Fixed(iter) => iter.find_map(|v| v),
        }
    }
}
fn fixed<'a>(a: Option<&'a Expr>, b: Option<&'a Expr>, c: Option<&'a Expr>) -> Children<'a> {
    Children::Fixed([a, b, c].into_iter())
}

pub(super) enum Operator {
    Bool(bool),
    Bv,
    Var,
    Not,
    Ite,
    Apply(&'static str, Option<usize>),
    Special(&'static str, u32, u32),
    Numeric(&'static str, u32, u32),
    Extract(u32, u32),
}
pub(super) struct Shape<'a> {
    pub op: Operator,
    pub children: Children<'a>,
}

pub(super) fn describe(expr: &Expr) -> Result<Shape<'_>, FpAdapterError> {
    let kind = scalar(expr)?;
    match expr.value() {
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::Var { .. }
        | ExprValue::Not(_) => leaf(expr, kind),
        ExprValue::Ite {
            cond,
            then_expr,
            else_expr,
        } => selection(kind, cond, then_expr, else_expr),
        ExprValue::BvExtract {
            expr: word,
            high,
            low,
        } => raw_extract(kind, word, *high, *low),
        ExprValue::And(_)
        | ExprValue::Or(_)
        | ExprValue::Xor(_, _)
        | ExprValue::Implies(_, _)
        | ExprValue::Eq(_, _)
        | ExprValue::Distinct(_) => boolean(expr, kind),
        ExprValue::BvULt(..)
        | ExprValue::BvULe(..)
        | ExprValue::BvUGt(..)
        | ExprValue::BvUGe(..)
        | ExprValue::BvSLt(..)
        | ExprValue::BvSLe(..)
        | ExprValue::BvSGt(..)
        | ExprValue::BvSGe(..) => bitvectors::describe(expr),
        _ => floating::describe(expr, kind),
    }
}

fn leaf(expr: &Expr, kind: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    let (op, children) = match expr.value() {
        ExprValue::BoolConst(v) if kind == Scalar::Bool => {
            (Operator::Bool(*v), fixed(None, None, None))
        }
        ExprValue::BitVecConst { value, width } => {
            if kind != Scalar::Bv(*width) || value.bits() > u64::from(*width) {
                return Err(FpAdapterError::Invalid("typed BV constant"));
            }
            // Magnitude is bounded before this <=9-byte signed copy.
            if value
                .to_signed_bytes_le()
                .last()
                .is_some_and(|b| b & 128 != 0)
            {
                return Err(FpAdapterError::Invalid("negative typed BV constant"));
            }
            (Operator::Bv, fixed(None, None, None))
        }
        ExprValue::Var { .. } => (Operator::Var, fixed(None, None, None)),
        ExprValue::Not(a) if kind == Scalar::Bool && scalar(a)? == Scalar::Bool => {
            (Operator::Not, fixed(Some(a), None, None))
        }
        _ => return Err(FpAdapterError::Invalid("typed leaf sort")),
    };
    Ok(Shape { op, children })
}

fn selection<'a>(
    kind: Scalar,
    cond: &'a Expr,
    left: &'a Expr,
    right: &'a Expr,
) -> Result<Shape<'a>, FpAdapterError> {
    if !matches!(kind, Scalar::Bool | Scalar::Fp(_, _))
        || scalar(cond)? != Scalar::Bool
        || scalar(left)? != kind
        || scalar(right)? != kind
    {
        return Err(FpAdapterError::Invalid("typed selection sorts"));
    }
    Ok(Shape {
        op: Operator::Ite,
        children: fixed(Some(cond), Some(left), Some(right)),
    })
}

fn raw_extract(
    kind: Scalar,
    word: &Expr,
    high: u32,
    low: u32,
) -> Result<Shape<'_>, FpAdapterError> {
    let width = match scalar(word)? {
        Scalar::Bv(w @ (32 | 64)) => w,
        _ => return Err(FpAdapterError::Unsupported("typed raw extract word width")),
    };
    if !matches!(
        word.value(),
        ExprValue::Var { .. } | ExprValue::BitVecConst { .. }
    ) {
        return Err(FpAdapterError::Unsupported(
            "typed compound raw extract operand",
        ));
    }
    if low > high || high >= width || kind != Scalar::Bv(high - low + 1) {
        return Err(FpAdapterError::Invalid("typed raw extract result/range"));
    }
    Ok(Shape {
        op: Operator::Extract(high, low),
        children: fixed(Some(word), None, None),
    })
}

fn both(a: &Expr, b: &Expr, kind: Scalar) -> Result<(), FpAdapterError> {
    if scalar(a)? == kind && scalar(b)? == kind {
        Ok(())
    } else {
        Err(FpAdapterError::Invalid("typed operand sorts"))
    }
}

fn boolean(expr: &Expr, kind: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    if kind != Scalar::Bool {
        return Err(FpAdapterError::Invalid("typed Boolean result"));
    }
    let (name, children) = match expr.value() {
        ExprValue::And(args) | ExprValue::Or(args) => {
            if args.len() > 64 || args.iter().any(|a| scalar(a) != Ok(Scalar::Bool)) {
                return Err(FpAdapterError::Invalid("typed Boolean arity/sorts"));
            }
            let name = if matches!(expr.value(), ExprValue::And(_)) {
                "and"
            } else {
                "or"
            };
            (name, Children::Slice(args.iter()))
        }
        ExprValue::Xor(a, b) | ExprValue::Implies(a, b) => {
            both(a, b, Scalar::Bool)?;
            let name = if matches!(expr.value(), ExprValue::Xor(..)) {
                "xor"
            } else {
                "=>"
            };
            (name, fixed(Some(a), Some(b), None))
        }
        ExprValue::Eq(a, b) => {
            let input = scalar(a)?;
            if !matches!(input, Scalar::Bool | Scalar::Fp(_, _) | Scalar::Bv(_)) {
                return Err(FpAdapterError::Unsupported("typed equality format"));
            }
            both(a, b, input)?;
            ("=", fixed(Some(a), Some(b), None))
        }
        ExprValue::Distinct(args) => {
            if args.len() != 2 {
                return Err(FpAdapterError::Unsupported("typed distinct arity"));
            }
            let input = scalar(&args[0])?;
            if !matches!(input, Scalar::Bool | Scalar::Bv(_)) {
                return Err(FpAdapterError::Unsupported("typed distinct format"));
            }
            both(&args[0], &args[1], input)?;
            ("distinct", Children::Slice(args.iter()))
        }
        _ => return Err(FpAdapterError::Unsupported("typed Boolean source")),
    };
    Ok(Shape {
        op: Operator::Apply(name, None),
        children,
    })
}
