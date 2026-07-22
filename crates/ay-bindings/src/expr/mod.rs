// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! AY Expression AST.
//!
//! Expressions represent symbolic values that can be reasoned about by AY.
//! Every expression has a sort (type) and a value.
//!
//! ## Expression Categories
//!
//! - **Constants**: Literal values (true, 42, #x0F)
//! - **Variables**: Symbolic values (declare-const x Int)
//! - **Operations**: Function applications (bvadd, and, ite)
//! - **Quantifiers**: forall, exists
//!
//! ## SMT-LIB2 Mapping
//!
//! | AYExpr | SMT-LIB2 |
//! |--------|----------|
//! | BoolConst(true) | true |
//! | BitVecConst(42, 32) | #x0000002a |
//! | Var("x", Int) | x (after declare-const) |
//! | BvAdd(a, b) | (bvadd a b) |
//! | Ite(c, t, e) | (ite c t e) |

#[macro_use]
mod macros;
mod arrays;
mod bool;
mod bv;
mod display;
mod drop;
mod dt;
mod fp;
mod fp_predict;
mod int;
mod overflow;
mod real;
mod seq;
mod share;
mod string;

pub mod fold;

#[cfg(test)]
mod tests;

use crate::sort::Sort;
use num_bigint::BigInt;
use num_traits::Signed;
use std::sync::Arc;

// ===== Helper Functions =====

pub(crate) fn normalize_bitvec_value(value: BigInt, width: u32) -> BigInt {
    assert!(width > 0, "BitVec width must be > 0");
    let modulus = BigInt::from(1u8) << (width as usize);
    let mut normalized = value % &modulus;
    if normalized.is_negative() {
        normalized += modulus;
    }
    normalized
}

/// Generate an SMT-LIB2 bitvector literal with all bits set to 1 for the given bit width.
///
/// For widths that are multiples of 4, uses hex format (#xFFFF).
/// For other widths, uses binary format (#b111...) to get exact bit width.
/// For widths > 128, computes the value directly.
pub(crate) fn all_ones_literal(width: u32) -> String {
    if width.is_multiple_of(4) {
        // Safe to use hex - each hex digit is exactly 4 bits
        let hex_digits = (width as usize) / 4;
        if width <= 128 {
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            format!("#x{mask:0>hex_digits$x}")
        } else {
            // For widths > 128 that are multiples of 4
            let mut result = String::with_capacity(hex_digits + 2);
            result.push_str("#x");
            for _ in 0..hex_digits {
                result.push('f');
            }
            result
        }
    } else {
        let mut result = String::with_capacity(2 + width as usize);
        result.push_str("#b");
        for _ in 0..width {
            result.push('1');
        }
        result
    }
}

/// Generate an SMT-LIB2 bitvector literal for INT_MIN (sign bit = 1, all others = 0).
///
/// For a w-bit signed integer, INT_MIN = 2^(w-1) = 0x80...0
/// For widths that are multiples of 4, uses hex format.
/// For other widths, uses binary format (#b1000...) to get exact bit width.
pub(crate) fn int_min_literal(width: u32) -> String {
    if width.is_multiple_of(4) {
        // Safe to use hex - each hex digit is exactly 4 bits
        let hex_digits = (width as usize) / 4;
        if width <= 128 {
            let int_min = 1u128 << (width - 1);
            format!("#x{int_min:0>hex_digits$x}")
        } else {
            // For widths > 128 that are multiples of 4
            let mut result = String::with_capacity(hex_digits + 2);
            result.push_str("#x8");
            for _ in 1..hex_digits {
                result.push('0');
            }
            result
        }
    } else {
        let mut result = String::with_capacity(2 + width as usize);
        result.push_str("#b");
        result.push('1');
        for _ in 1..width {
            result.push('0');
        }
        result
    }
}

/// Generate an SMT-LIB2 bitvector literal with value zero for the given bit width.
///
/// For widths that are multiples of 4, uses hex format (#x0000).
/// For other widths, uses binary format (#b000...) to get exact bit width.
pub(crate) fn zero_literal(width: u32) -> String {
    if width.is_multiple_of(4) {
        // Safe to use hex - each hex digit is exactly 4 bits
        let hex_digits = (width as usize) / 4;
        format!("#x{:0>w$}", 0, w = hex_digits)
    } else {
        let mut result = String::with_capacity(2 + width as usize);
        result.push_str("#b");
        for _ in 0..width {
            result.push('0');
        }
        result
    }
}

/// IEEE 754 rounding mode for floating-point operations.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RoundingMode {
    /// Round to nearest, ties to even (default).
    #[default]
    RNE,
    /// Round to nearest, ties away from zero.
    RNA,
    /// Round toward positive infinity.
    RTP,
    /// Round toward negative infinity.
    RTN,
    /// Round toward zero.
    RTZ,
}

impl RoundingMode {
    /// SMT-LIB2 name for this rounding mode.
    #[must_use]
    pub(crate) fn smt_name(self) -> &'static str {
        match self {
            Self::RNE => "RNE",
            Self::RNA => "RNA",
            Self::RTP => "RTP",
            Self::RTN => "RTN",
            Self::RTZ => "RTZ",
        }
    }
}

/// AY Expression - a symbolic value with a sort.
///
/// Expressions are immutable and use `Arc` for efficient sharing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    /// The sort (type) of this expression.
    pub(crate) sort: Sort,
    /// The value of this expression.
    pub(crate) value: Arc<ExprValue>,
}

mod expr_value;
mod expr_value_iter;
pub use expr_value::ExprValue;

impl Expr {
    /// Returns an iterator over the child expressions of this node.
    ///
    /// Convenience wrapper around [`ExprValue::children`].
    pub fn children(&self) -> impl Iterator<Item = &Self> {
        self.value.children()
    }
}

impl Expr {
    /// Get the sort of this expression.
    #[must_use]
    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    /// Get the value of this expression.
    #[must_use]
    pub fn value(&self) -> &ExprValue {
        &self.value
    }

    // ===== Constants =====

    /// Create a boolean constant.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn bool_const(value: bool) -> Self {
        Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::BoolConst(value)),
        }
    }

    /// Create a true constant.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn true_() -> Self {
        Self::bool_const(true)
    }

    /// Create a false constant.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn false_() -> Self {
        Self::bool_const(false)
    }

    /// Create a bitvector constant.
    #[must_use]
    #[cfg_attr(kani, kani::requires(width > 0))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    pub fn bitvec_const(value: impl Into<BigInt>, width: u32) -> Self {
        assert!(width > 0, "BitVec width must be > 0");
        Self {
            sort: Sort::bitvec(width),
            value: Arc::new(ExprValue::BitVecConst {
                value: normalize_bitvec_value(value.into(), width),
                width,
            }),
        }
    }

    /// Create an integer constant.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_int()))]
    pub fn int_const(value: impl Into<BigInt>) -> Self {
        Self {
            sort: Sort::int(),
            value: Arc::new(ExprValue::IntConst(value.into())),
        }
    }

    /// Create an integer constant (shorthand).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_int()))]
    pub fn int(value: impl Into<BigInt>) -> Self {
        Self::int_const(value)
    }

    /// Create a real constant.
    ///
    /// Creates a real-sorted constant from an integer value. This is more
    /// ergonomic than `Expr::int_const(n).int_to_real()` for simple cases.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::Expr;
    ///
    /// // Direct real constant
    /// let r = Expr::real_const(42);
    /// assert!(r.sort().is_real());
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_real()))]
    pub fn real_const(value: impl Into<BigInt>) -> Self {
        Self {
            sort: Sort::real(),
            value: Arc::new(ExprValue::RealConst(value.into())),
        }
    }

    /// Create a real constant (shorthand).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_real()))]
    pub fn real(value: impl Into<BigInt>) -> Self {
        Self::real_const(value)
    }

    // ===== Variables =====

    /// Create a symbolic variable.
    ///
    /// # ENSURES
    /// - Result sort equals the provided sort
    #[must_use]
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Self {
            sort,
            value: Arc::new(ExprValue::Var { name: name.into() }),
        }
    }

    // ===== Function Application =====

    /// Create an uninterpreted function application.
    ///
    /// Used for CHC relation applications and uninterpreted functions.
    /// The result sort is Bool by default (for CHC relations).
    ///
    /// # ENSURES
    /// - Result sort is Bool
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort};
    ///
    /// // Relation application: state(x, y)
    /// let x = Expr::var("x", Sort::int());
    /// let y = Expr::var("y", Sort::int());
    /// let state_xy = Expr::func_app("state", vec![x, y]);
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn func_app(name: impl Into<String>, args: Vec<Self>) -> Self {
        Self {
            sort: Sort::bool(), // CHC relations return Bool
            value: Arc::new(ExprValue::FuncApp {
                name: name.into(),
                args,
            }),
        }
    }

    /// Create an uninterpreted function application with explicit result sort.
    ///
    /// Use this when the function returns a non-Bool sort.
    ///
    /// # ENSURES
    /// - Result sort equals the provided result_sort
    #[must_use]
    pub fn func_app_with_sort(name: impl Into<String>, args: Vec<Self>, result_sort: Sort) -> Self {
        Self {
            sort: result_sort,
            value: Arc::new(ExprValue::FuncApp {
                name: name.into(),
                args,
            }),
        }
    }

    // ===== Quantifiers =====

    /// Universal quantifier.
    #[must_use]
    #[cfg_attr(kani, kani::requires(body.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn forall(vars: Vec<(String, Sort)>, body: Self) -> Self {
        Self::forall_with_triggers(vars, body, Vec::new())
    }

    /// Universal quantifier with trigger patterns for E-matching.
    #[must_use]
    #[cfg_attr(kani, kani::requires(body.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn forall_with_triggers(
        vars: Vec<(String, Sort)>,
        body: Self,
        triggers: Vec<Vec<Self>>,
    ) -> Self {
        Self::try_forall_with_triggers(vars, body, triggers).expect("forall body must be Bool")
    }

    /// Existential quantifier.
    #[must_use]
    #[cfg_attr(kani, kani::requires(body.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn exists(vars: Vec<(String, Sort)>, body: Self) -> Self {
        Self::exists_with_triggers(vars, body, Vec::new())
    }

    /// Existential quantifier with trigger patterns for E-matching.
    #[must_use]
    #[cfg_attr(kani, kani::requires(body.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    pub fn exists_with_triggers(
        vars: Vec<(String, Sort)>,
        body: Self,
        triggers: Vec<Vec<Self>>,
    ) -> Self {
        Self::try_exists_with_triggers(vars, body, triggers).expect("exists body must be Bool")
    }

    // ===== Quantifier try_* variants (#5818) =====

    /// Fallible universal quantifier — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_forall(vars: Vec<(String, Sort)>, body: Self) -> Result<Self, crate::SortError> {
        Self::try_forall_with_triggers(vars, body, Vec::new())
    }

    /// Fallible universal quantifier with triggers — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_forall_with_triggers(
        vars: Vec<(String, Sort)>,
        body: Self,
        triggers: Vec<Vec<Self>>,
    ) -> Result<Self, crate::SortError> {
        if !body.sort.is_bool() {
            return Err(crate::SortError::unary("forall", "Bool body", &body.sort));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Forall {
                vars,
                body,
                triggers,
            }),
        })
    }

    /// Fallible existential quantifier — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_exists(vars: Vec<(String, Sort)>, body: Self) -> Result<Self, crate::SortError> {
        Self::try_exists_with_triggers(vars, body, Vec::new())
    }

    /// Fallible existential quantifier with triggers — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_exists_with_triggers(
        vars: Vec<(String, Sort)>,
        body: Self,
        triggers: Vec<Vec<Self>>,
    ) -> Result<Self, crate::SortError> {
        if !body.sort.is_bool() {
            return Err(crate::SortError::unary("exists", "Bool body", &body.sort));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Exists {
                vars,
                body,
                triggers,
            }),
        })
    }
}
