// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`BvExpr`]'s public construction API: the named constructors downstream
//! consumers build expressions with, and the operator conveniences.

use super::BvExpr;

impl BvExpr {
    /// Convenience: a named leaf.
    #[must_use]
    pub fn leaf(name: &str, width: u32) -> Self {
        Self::Leaf {
            name: name.to_string(),
            width,
        }
    }
    /// Convenience: `bvadd(lhs, rhs)`. Restored after the workspace-quality
    /// audit removed it as workspace-unused: downstream consumers (proof-replay-consumer's
    /// pcay reconstruction, trust-router's ay_certify, external-codegen-bridge's
    /// verify_output) construct these shapes at many call sites — the boxed
    /// variant spelling is an implementation detail, not the API.
    #[must_use]
    #[expect(
        clippy::should_implement_trait,
        reason = "this downstream constructor API uses the SMT operator name and has no receiver"
    )]
    pub fn add(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvsub(lhs, rhs)`.
    #[must_use]
    #[expect(
        clippy::should_implement_trait,
        reason = "this downstream constructor API uses the SMT operator name and has no receiver"
    )]
    pub fn sub(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Sub(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvmul(lhs, rhs)`.
    #[must_use]
    #[expect(
        clippy::should_implement_trait,
        reason = "this downstream constructor API uses the SMT operator name and has no receiver"
    )]
    pub fn mul(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: `bvshl(value, amount)`.
    #[must_use]
    #[expect(
        clippy::should_implement_trait,
        reason = "this downstream constructor API uses the SMT operator name and has no receiver"
    )]
    pub fn shl(value: BvExpr, amount: BvExpr) -> Self {
        Self::Shl(Box::new(value), Box::new(amount))
    }
    /// Convenience: `bvnot(inner)`.
    #[must_use]
    #[expect(
        clippy::should_implement_trait,
        reason = "this downstream constructor API uses the SMT operator name and has no receiver"
    )]
    pub fn not(inner: BvExpr) -> Self {
        Self::Not(Box::new(inner))
    }
    /// Convenience: `(_ zero_extend added)`.
    #[must_use]
    pub fn zero_ext(inner: BvExpr, added: u32) -> Self {
        Self::ZeroExt(Box::new(inner), added)
    }
    /// Convenience: `(_ extract high low)`.
    #[must_use]
    pub fn extract(inner: BvExpr, high: u32, low: u32) -> Self {
        Self::Extract {
            inner: Box::new(inner),
            high,
            low,
        }
    }
    /// Convenience: `bvor`.
    #[must_use]
    pub fn or(l: BvExpr, r: BvExpr) -> Self {
        Self::Or(Box::new(l), Box::new(r))
    }
    /// Convenience: `bvand`.
    #[must_use]
    pub fn and(l: BvExpr, r: BvExpr) -> Self {
        Self::And(Box::new(l), Box::new(r))
    }
    /// Convenience: `bvxor`.
    #[must_use]
    pub fn xor(l: BvExpr, r: BvExpr) -> Self {
        Self::Xor(Box::new(l), Box::new(r))
    }
    /// Convenience: a fixed bit-vector constant of the given width.
    #[must_use]
    pub fn const_val(value: u128, width: u32) -> Self {
        Self::Const { value, width }
    }
    /// Convenience: `(_ sign_extend added)`.
    #[must_use]
    pub fn sign_ext(inner: BvExpr, added: u32) -> Self {
        Self::SignExt(Box::new(inner), added)
    }
    /// Convenience: `bvlshr`.
    #[must_use]
    pub fn lshr(value: BvExpr, amount: BvExpr) -> Self {
        Self::Lshr(Box::new(value), Box::new(amount))
    }
    /// Convenience: `bvashr`.
    #[must_use]
    pub fn ashr(value: BvExpr, amount: BvExpr) -> Self {
        Self::Ashr(Box::new(value), Box::new(amount))
    }
    /// Convenience: bit-vector equality (`= lhs rhs`) reduced to a 1-bit predicate.
    #[must_use]
    pub fn eq(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::Eq(Box::new(lhs), Box::new(rhs))
    }
    /// Convenience: carry-out of the ripple-carry add (`is_sub == false`).
    #[must_use]
    pub fn carry_out_add(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::CarryOut {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            is_sub: false,
        }
    }
    /// Convenience: carry-out of the ripple-carry subtract (`a + ~b + 1`).
    /// `bvudiv(lhs, rhs)`.
    #[must_use]
    pub fn udiv(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::UDiv(Box::new(lhs), Box::new(rhs))
    }
    /// `bvurem(lhs, rhs)`.
    #[must_use]
    pub fn urem(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::URem(Box::new(lhs), Box::new(rhs))
    }
    /// `unsigned_lt(a, b) = NOT(carry_out_sub(a, b))`.
    #[must_use]
    pub fn carry_out_sub(lhs: BvExpr, rhs: BvExpr) -> Self {
        Self::CarryOut {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            is_sub: true,
        }
    }
}

/// Convenience: `bvadd` (also callable as `BvExpr::add(l, r)`).
impl std::ops::Add for BvExpr {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::Add(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvsub` (also callable as `BvExpr::sub(l, r)`).
impl std::ops::Sub for BvExpr {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self::Sub(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvmul` (also callable as `BvExpr::mul(l, r)`).
impl std::ops::Mul for BvExpr {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::Mul(Box::new(self), Box::new(rhs))
    }
}

/// Convenience: `bvshl` (also callable as `BvExpr::shl(value, amount)`).
impl std::ops::Shl for BvExpr {
    type Output = Self;
    fn shl(self, amount: Self) -> Self {
        Self::Shl(Box::new(self), Box::new(amount))
    }
}

/// Convenience: `bvnot`, per-bit NOT (also callable as `BvExpr::not(inner)`).
impl std::ops::Not for BvExpr {
    type Output = Self;
    fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}
