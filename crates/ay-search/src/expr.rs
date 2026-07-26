// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::ops::{Add, Mul, Neg, Sub};

/// A model-scoped finite-domain integer variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IntVar {
    pub(crate) model_id: u64,
    pub(crate) index: u32,
}

/// A model-scoped Boolean variable. Its integer representation is exactly 0/1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoolVar(pub(crate) IntVar);

impl BoolVar {
    /// Use this Boolean as the integer value 0/1 in a linear expression.
    pub fn as_int(self) -> IntVar {
        self.0
    }
}

/// A normalized affine integer expression.
///
/// Expressions can be assembled with `+`, `-`, unary `-`, and multiplication
/// by an integer constant. Arithmetic overflow is remembered and reported as a
/// typed error when the expression is added to a model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearExpr {
    pub(crate) terms: BTreeMap<IntVar, i128>,
    pub(crate) constant: i128,
    pub(crate) overflowed: bool,
}

impl LinearExpr {
    /// The constant zero expression.
    pub fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
            constant: 0,
            overflowed: false,
        }
    }

    /// Whether this expression contains no variable terms.
    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    pub(crate) fn add_expr(mut self, rhs: Self, subtract: bool) -> Self {
        self.overflowed |= rhs.overflowed;
        let sign = if subtract { -1 } else { 1 };
        let Some(signed_constant) = rhs.constant.checked_mul(sign) else {
            self.overflowed = true;
            return self;
        };
        match self.constant.checked_add(signed_constant) {
            Some(value) => self.constant = value,
            None => self.overflowed = true,
        }
        for (var, coefficient) in rhs.terms {
            let Some(signed_coefficient) = coefficient.checked_mul(sign) else {
                self.overflowed = true;
                continue;
            };
            let previous = self.terms.get(&var).copied().unwrap_or(0);
            match previous.checked_add(signed_coefficient) {
                Some(0) => {
                    self.terms.remove(&var);
                }
                Some(value) => {
                    self.terms.insert(var, value);
                }
                None => self.overflowed = true,
            }
        }
        self
    }

    pub(crate) fn scaled(mut self, factor: i128) -> Self {
        match self.constant.checked_mul(factor) {
            Some(value) => self.constant = value,
            None => self.overflowed = true,
        }
        for coefficient in self.terms.values_mut() {
            match coefficient.checked_mul(factor) {
                Some(value) => *coefficient = value,
                None => self.overflowed = true,
            }
        }
        self.terms.retain(|_, coefficient| *coefficient != 0);
        self
    }

    pub(crate) fn constant_value(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.constant)
    }
}

impl Default for LinearExpr {
    fn default() -> Self {
        Self::zero()
    }
}

impl From<IntVar> for LinearExpr {
    fn from(value: IntVar) -> Self {
        Self {
            terms: BTreeMap::from([(value, 1)]),
            constant: 0,
            overflowed: false,
        }
    }
}

impl From<BoolVar> for LinearExpr {
    fn from(value: BoolVar) -> Self {
        value.as_int().into()
    }
}

impl From<i64> for LinearExpr {
    fn from(value: i64) -> Self {
        Self {
            terms: BTreeMap::new(),
            constant: i128::from(value),
            overflowed: false,
        }
    }
}

impl From<i32> for LinearExpr {
    fn from(value: i32) -> Self {
        i64::from(value).into()
    }
}

impl Add for LinearExpr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add_expr(rhs, false)
    }
}

impl Sub for LinearExpr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.add_expr(rhs, true)
    }
}

impl Neg for LinearExpr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.scaled(-1)
    }
}

macro_rules! impl_expr_ops {
    ($rhs:ty) => {
        impl Add<$rhs> for LinearExpr {
            type Output = LinearExpr;
            fn add(self, rhs: $rhs) -> Self::Output {
                self + LinearExpr::from(rhs)
            }
        }
        impl Sub<$rhs> for LinearExpr {
            type Output = LinearExpr;
            fn sub(self, rhs: $rhs) -> Self::Output {
                self - LinearExpr::from(rhs)
            }
        }
        impl Add<LinearExpr> for $rhs {
            type Output = LinearExpr;
            fn add(self, rhs: LinearExpr) -> Self::Output {
                LinearExpr::from(self) + rhs
            }
        }
        impl Sub<LinearExpr> for $rhs {
            type Output = LinearExpr;
            fn sub(self, rhs: LinearExpr) -> Self::Output {
                LinearExpr::from(self) - rhs
            }
        }
    };
}

impl_expr_ops!(IntVar);
impl_expr_ops!(BoolVar);
impl_expr_ops!(i64);
impl_expr_ops!(i32);

impl Add<IntVar> for IntVar {
    type Output = LinearExpr;
    fn add(self, rhs: IntVar) -> Self::Output {
        LinearExpr::from(self) + rhs
    }
}

impl Sub<IntVar> for IntVar {
    type Output = LinearExpr;
    fn sub(self, rhs: IntVar) -> Self::Output {
        LinearExpr::from(self) - rhs
    }
}

impl Add<BoolVar> for BoolVar {
    type Output = LinearExpr;
    fn add(self, rhs: BoolVar) -> Self::Output {
        LinearExpr::from(self) + rhs
    }
}

impl Sub<BoolVar> for BoolVar {
    type Output = LinearExpr;
    fn sub(self, rhs: BoolVar) -> Self::Output {
        LinearExpr::from(self) - rhs
    }
}

impl Add<BoolVar> for IntVar {
    type Output = LinearExpr;
    fn add(self, rhs: BoolVar) -> Self::Output {
        LinearExpr::from(self) + rhs
    }
}

impl Sub<BoolVar> for IntVar {
    type Output = LinearExpr;
    fn sub(self, rhs: BoolVar) -> Self::Output {
        LinearExpr::from(self) - rhs
    }
}

impl Add<IntVar> for BoolVar {
    type Output = LinearExpr;
    fn add(self, rhs: IntVar) -> Self::Output {
        LinearExpr::from(self) + rhs
    }
}

impl Sub<IntVar> for BoolVar {
    type Output = LinearExpr;
    fn sub(self, rhs: IntVar) -> Self::Output {
        LinearExpr::from(self) - rhs
    }
}

impl Neg for IntVar {
    type Output = LinearExpr;
    fn neg(self) -> Self::Output {
        -LinearExpr::from(self)
    }
}

impl Neg for BoolVar {
    type Output = LinearExpr;
    fn neg(self) -> Self::Output {
        -LinearExpr::from(self)
    }
}

macro_rules! impl_constant_multiplication {
    ($constant:ty) => {
        impl Mul<$constant> for LinearExpr {
            type Output = LinearExpr;
            fn mul(self, rhs: $constant) -> Self::Output {
                self.scaled(i128::from(rhs))
            }
        }
        impl Mul<LinearExpr> for $constant {
            type Output = LinearExpr;
            fn mul(self, rhs: LinearExpr) -> Self::Output {
                rhs.scaled(i128::from(self))
            }
        }
        impl Mul<$constant> for IntVar {
            type Output = LinearExpr;
            fn mul(self, rhs: $constant) -> Self::Output {
                LinearExpr::from(self).scaled(i128::from(rhs))
            }
        }
        impl Mul<IntVar> for $constant {
            type Output = LinearExpr;
            fn mul(self, rhs: IntVar) -> Self::Output {
                LinearExpr::from(rhs).scaled(i128::from(self))
            }
        }
        impl Mul<$constant> for BoolVar {
            type Output = LinearExpr;
            fn mul(self, rhs: $constant) -> Self::Output {
                LinearExpr::from(self).scaled(i128::from(rhs))
            }
        }
        impl Mul<BoolVar> for $constant {
            type Output = LinearExpr;
            fn mul(self, rhs: BoolVar) -> Self::Output {
                LinearExpr::from(rhs).scaled(i128::from(self))
            }
        }
    };
}

impl_constant_multiplication!(i64);
impl_constant_multiplication!(i32);
