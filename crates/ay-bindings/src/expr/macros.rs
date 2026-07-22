// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Macros for generating panicking + fallible (`try_*`) expression operation
//! pairs in the ay-bindings `Expr` API.
//!
//! These macros eliminate ~2,300 lines of boilerplate across bv.rs, fp.rs,
//! int.rs, real.rs, bool.rs, and overflow.rs by generating both the panicking
//! and `try_*` variants from a single declaration.
//!
//! Part of #5864: bindings expr macro dedup.
//! Unblocks #5843: verification-consumer Result-based API.
//! Fixes #5818: error inconsistency (missing try_* variants).

/// Binary operation: both operands must satisfy a sort predicate, result sort
/// is the same as `self.sort`.
///
/// Generates:
/// - `pub fn $name(self, other: Self) -> Self` (panicking)
/// - `pub fn $try_name(self, other: Self) -> Result<Self, SortError>` (fallible)
macro_rules! binop_same_sort {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self, other: Self) -> Self {
            assert!($check(&self, &other), $assert_msg);
            let sort = self.sort.clone();
            Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self, other)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self, other: Self) -> Result<Self, $crate::SortError> {
            if !$check(&self, &other) {
                return Err($crate::SortError::binary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                    &other.sort,
                ));
            }
            let sort = self.sort.clone();
            Ok(Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self, other)),
            })
        }
    };
}

/// Binary operation: both operands must satisfy a sort predicate, result sort
/// is `Sort::bool()`.
///
/// Generates:
/// - `pub fn $name(self, other: Self) -> Self` (panicking)
/// - `pub fn $try_name(self, other: Self) -> Result<Self, SortError>` (fallible)
macro_rules! binop_to_bool {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self, other: Self) -> Self {
            assert!($check(&self, &other), $assert_msg);
            Self {
                sort: $crate::sort::Sort::bool(),
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self, other)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self, other: Self) -> Result<Self, $crate::SortError> {
            if !$check(&self, &other) {
                return Err($crate::SortError::binary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                    &other.sort,
                ));
            }
            Ok(Self {
                sort: $crate::sort::Sort::bool(),
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self, other)),
            })
        }
    };
}

/// Unary operation: operand must satisfy a sort predicate, result sort is the
/// same as `self.sort`.
///
/// Generates:
/// - `pub fn $name(self) -> Self` (panicking)
/// - `pub fn $try_name(self) -> Result<Self, SortError>` (fallible)
macro_rules! unop_same_sort {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self) -> Self {
            assert!($check(&self), $assert_msg);
            let sort = self.sort.clone();
            Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self) -> Result<Self, $crate::SortError> {
            if !$check(&self) {
                return Err($crate::SortError::unary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                ));
            }
            let sort = self.sort.clone();
            Ok(Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            })
        }
    };
}

/// Unary operation: operand must satisfy a sort predicate, result sort is
/// `Sort::bool()`.
///
/// Generates:
/// - `pub fn $name(self) -> Self` (panicking)
/// - `pub fn $try_name(self) -> Result<Self, SortError>` (fallible)
macro_rules! unop_to_bool {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self) -> Self {
            assert!($check(&self), $assert_msg);
            Self {
                sort: $crate::sort::Sort::bool(),
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self) -> Result<Self, $crate::SortError> {
            if !$check(&self) {
                return Err($crate::SortError::unary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                ));
            }
            Ok(Self {
                sort: $crate::sort::Sort::bool(),
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            })
        }
    };
}

/// Unary operation: operand must satisfy a sort predicate, result sort is a
/// specified fixed sort.
///
/// Generates:
/// - `pub fn $name(self) -> Self` (panicking)
/// - `pub fn $try_name(self) -> Result<Self, SortError>` (fallible)
macro_rules! unop_to_sort {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        result_sort: $result_sort:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self) -> Self {
            assert!($check(&self), $assert_msg);
            Self {
                sort: $result_sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self) -> Result<Self, $crate::SortError> {
            if !$check(&self) {
                return Err($crate::SortError::unary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                ));
            }
            Ok(Self {
                sort: $result_sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(self)),
            })
        }
    };
}

/// Binary operation with a `RoundingMode` parameter: both operands must satisfy
/// a sort predicate, result sort is the same as `self.sort`.
///
/// Variant layout: `Variant(RoundingMode, Expr, Expr)`.
///
/// Generates:
/// - `pub fn $name(self, rm: RoundingMode, other: Self) -> Self` (panicking)
/// - `pub fn $try_name(self, rm: RoundingMode, other: Self) -> Result<Self, SortError>` (fallible)
macro_rules! binop_rm_same_sort {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self, rm: $crate::expr::RoundingMode, other: Self) -> Self {
            assert!($check(&self, &other), $assert_msg);
            let sort = self.sort.clone();
            Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(rm, self, other)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self, rm: $crate::expr::RoundingMode, other: Self) -> Result<Self, $crate::SortError> {
            if !$check(&self, &other) {
                return Err($crate::SortError::binary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                    &other.sort,
                ));
            }
            let sort = self.sort.clone();
            Ok(Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(rm, self, other)),
            })
        }
    };
}

/// Unary operation with a `RoundingMode` parameter: operand must satisfy a sort
/// predicate, result sort is the same as `self.sort`.
///
/// Variant layout: `Variant(RoundingMode, Expr)`.
///
/// Generates:
/// - `pub fn $name(self, rm: RoundingMode) -> Self` (panicking)
/// - `pub fn $try_name(self, rm: RoundingMode) -> Result<Self, SortError>` (fallible)
macro_rules! unop_rm_same_sort {
    (
        $(#[doc = $doc:expr])*
        $(#[kani_requires($kani_req:expr)])?
        $(#[kani_ensures($kani_ens:expr)])?
        fn $name:ident / $try_name:ident,
        check: $check:expr,
        assert_msg: $assert_msg:expr,
        error_expected: $error_expected:expr,
        variant: $variant:ident
    ) => {
        $(#[doc = $doc])*
        #[must_use = "expression operations return a new Expr"]
        $(#[cfg_attr(kani, kani::requires($kani_req))])?
        $(#[cfg_attr(kani, kani::ensures($kani_ens))])?
        pub fn $name(self, rm: $crate::expr::RoundingMode) -> Self {
            assert!($check(&self), $assert_msg);
            let sort = self.sort.clone();
            Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(rm, self)),
            }
        }

        #[doc = concat!("Fallible version of [`Expr::", stringify!($name), "`].")]
        #[must_use = "try_* methods return a Result that must be used"]
        pub fn $try_name(self, rm: $crate::expr::RoundingMode) -> Result<Self, $crate::SortError> {
            if !$check(&self) {
                return Err($crate::SortError::unary(
                    stringify!($name),
                    $error_expected,
                    &self.sort,
                ));
            }
            let sort = self.sort.clone();
            Ok(Self {
                sort,
                value: ::std::sync::Arc::new($crate::expr::ExprValue::$variant(rm, self)),
            })
        }
    };
}

// Macros are available to sibling modules via `#[macro_use]` on the module
// declaration in mod.rs. No explicit re-exports needed.
