// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! String and regex operations for AY expressions.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

/// Predicate: both operands are String sorts.
fn str_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_string() && b.sort.is_string()
}

/// Predicate: operand is a String sort.
fn is_str(a: &Expr) -> bool {
    a.sort.is_string()
}

/// Predicate: both operands are RegLan sorts.
fn re_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_reglan() && b.sort.is_reglan()
}

/// Predicate: operand is a RegLan sort.
fn is_re(a: &Expr) -> bool {
    a.sort.is_reglan()
}

impl Expr {
    // ===== String Constants =====

    /// Create a string constant.
    #[must_use = "expression operations return a new Expr"]
    pub fn string_const(value: impl Into<String>) -> Self {
        Self {
            sort: Sort::string(),
            value: Arc::new(ExprValue::Var {
                name: format!("\"{}\"", value.into()),
            }),
        }
    }

    // ===== String Concatenation =====

    binop_same_sort! {
        /// String concatenation (str.++ s1 s2).
        /// REQUIRES: `self` and `other` are String sorts.
        /// ENSURES: result sort is String.
        fn str_concat / try_str_concat,
        check: str_same,
        assert_msg: "str_concat requires String sorts",
        error_expected: "String sorts",
        variant: StrConcat
    }

    // ===== String Length =====

    unop_to_sort! {
        /// String length (str.len s), returns Int.
        /// REQUIRES: `self` is a String sort.
        /// ENSURES: result sort is Int.
        fn str_len / try_str_len,
        check: is_str,
        assert_msg: "str_len requires String sort",
        error_expected: "String",
        result_sort: Sort::int(),
        variant: StrLen
    }

    // ===== String Character Access =====

    /// Character at index (str.at s i), returning a length-1 String.
    ///
    /// # Panics
    /// Panics if `self` is not String or `index` is not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_at(self, index: Self) -> Self {
        self.try_str_at(index)
            .expect("str_at requires String and Int sorts")
    }

    /// Fallible version of [`Expr::str_at`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_at(self, index: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !index.sort.is_int() {
            return Err(crate::SortError::binary(
                "str_at",
                "String and Int",
                &self.sort,
                &index.sort,
            ));
        }
        Ok(Self {
            sort: Sort::string(),
            value: Arc::new(ExprValue::StrAt(self, index)),
        })
    }

    // ===== String Substring =====

    /// Substring extraction (str.substr s offset len), returning String.
    ///
    /// # Panics
    /// Panics if `self` is not String or `offset`/`len` are not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_substr(self, offset: Self, len: Self) -> Self {
        self.try_str_substr(offset, len)
            .expect("str_substr requires String, Int, Int sorts")
    }

    /// Fallible version of [`Expr::str_substr`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_substr(self, offset: Self, len: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !offset.sort.is_int() || !len.sort.is_int() {
            return Err(crate::SortError::Mismatch {
                operation: "str_substr",
                expected: "String, Int, Int",
                actual: format!("{}, {}, {}", self.sort, offset.sort, len.sort),
            });
        }
        Ok(Self {
            sort: Sort::string(),
            value: Arc::new(ExprValue::StrSubstr(self, offset, len)),
        })
    }

    // ===== String Predicates =====

    binop_to_bool! {
        /// String containment test (str.contains s t), returns Bool.
        /// REQUIRES: `self` and `other` are String sorts.
        /// ENSURES: result sort is Bool.
        fn str_contains / try_str_contains,
        check: str_same,
        assert_msg: "str_contains requires String sorts",
        error_expected: "String sorts",
        variant: StrContains
    }

    binop_to_bool! {
        /// String prefix test (str.prefixof pre s), returns Bool.
        /// REQUIRES: `self` and `other` are String sorts.
        /// ENSURES: result sort is Bool.
        fn str_prefixof / try_str_prefixof,
        check: str_same,
        assert_msg: "str_prefixof requires String sorts",
        error_expected: "String sorts",
        variant: StrPrefixOf
    }

    binop_to_bool! {
        /// String suffix test (str.suffixof suf s), returns Bool.
        /// REQUIRES: `self` and `other` are String sorts.
        /// ENSURES: result sort is Bool.
        fn str_suffixof / try_str_suffixof,
        check: str_same,
        assert_msg: "str_suffixof requires String sorts",
        error_expected: "String sorts",
        variant: StrSuffixOf
    }

    // ===== String Search =====

    /// String index-of (str.indexof s t i), returns Int.
    /// Returns -1 if `t` is not found in `s` starting at position `i`.
    ///
    /// # Panics
    /// Panics if `self`/`t` are not String or `start` is not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_indexof(self, t: Self, start: Self) -> Self {
        self.try_str_indexof(t, start)
            .expect("str_indexof requires String, String, Int sorts")
    }

    /// Fallible version of [`Expr::str_indexof`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_indexof(self, t: Self, start: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !t.sort.is_string() || !start.sort.is_int() {
            return Err(crate::SortError::Mismatch {
                operation: "str_indexof",
                expected: "String, String, Int",
                actual: format!("{}, {}, {}", self.sort, t.sort, start.sort),
            });
        }
        Ok(Self {
            sort: Sort::int(),
            value: Arc::new(ExprValue::StrIndexOf(self, t, start)),
        })
    }

    // ===== String Replacement =====

    /// String replace first occurrence (str.replace s from to), returns String.
    ///
    /// # Panics
    /// Panics if any argument is not a String sort.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_replace(self, from: Self, to: Self) -> Self {
        self.try_str_replace(from, to)
            .expect("str_replace requires String sorts")
    }

    /// Fallible version of [`Expr::str_replace`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_replace(self, from: Self, to: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !from.sort.is_string() || !to.sort.is_string() {
            return Err(crate::SortError::Mismatch {
                operation: "str_replace",
                expected: "String, String, String",
                actual: format!("{}, {}, {}", self.sort, from.sort, to.sort),
            });
        }
        Ok(Self {
            sort: Sort::string(),
            value: Arc::new(ExprValue::StrReplace(self, from, to)),
        })
    }

    /// String replace all occurrences (str.replace_all s from to), returns String.
    ///
    /// # Panics
    /// Panics if any argument is not a String sort.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_replace_all(self, from: Self, to: Self) -> Self {
        self.try_str_replace_all(from, to)
            .expect("str_replace_all requires String sorts")
    }

    /// Fallible version of [`Expr::str_replace_all`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_replace_all(self, from: Self, to: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !from.sort.is_string() || !to.sort.is_string() {
            return Err(crate::SortError::Mismatch {
                operation: "str_replace_all",
                expected: "String, String, String",
                actual: format!("{}, {}, {}", self.sort, from.sort, to.sort),
            });
        }
        Ok(Self {
            sort: Sort::string(),
            value: Arc::new(ExprValue::StrReplaceAll(self, from, to)),
        })
    }

    // ===== String/Int Conversions =====

    unop_to_sort! {
        /// String to integer conversion (str.to_int s), returns Int.
        /// REQUIRES: `self` is a String sort.
        /// ENSURES: result sort is Int.
        fn str_to_int / try_str_to_int,
        check: is_str,
        assert_msg: "str_to_int requires String sort",
        error_expected: "String",
        result_sort: Sort::int(),
        variant: StrToInt
    }

    unop_to_sort! {
        /// Integer to string conversion (str.from_int i), returns String.
        /// REQUIRES: `self` is an Int sort.
        /// ENSURES: result sort is String.
        fn str_from_int / try_str_from_int,
        check: |a: &Expr| a.sort.is_int(),
        assert_msg: "str_from_int requires Int sort",
        error_expected: "Int",
        result_sort: Sort::string(),
        variant: StrFromInt
    }

    // ===== String/Regex Operations =====

    unop_to_sort! {
        /// String to regex conversion (str.to_re s), returns RegLan.
        /// REQUIRES: `self` is a String sort.
        /// ENSURES: result sort is RegLan.
        fn str_to_re / try_str_to_re,
        check: is_str,
        assert_msg: "str_to_re requires String sort",
        error_expected: "String",
        result_sort: Sort::reglan(),
        variant: StrToRe
    }

    /// Regex membership test (str.in_re s re), returns Bool.
    ///
    /// # Panics
    /// Panics if `self` is not String or `re` is not RegLan.
    #[must_use = "expression operations return a new Expr"]
    pub fn str_in_re(self, re: Self) -> Self {
        self.try_str_in_re(re)
            .expect("str_in_re requires String and RegLan sorts")
    }

    /// Fallible version of [`Expr::str_in_re`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_str_in_re(self, re: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_string() || !re.sort.is_reglan() {
            return Err(crate::SortError::binary(
                "str_in_re",
                "String and RegLan",
                &self.sort,
                &re.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::StrInRe(self, re)),
        })
    }

    // ===== Regex Operations =====

    unop_same_sort! {
        /// Regex Kleene star (re.* re).
        /// REQUIRES: `self` is a RegLan sort.
        /// ENSURES: result sort is RegLan.
        fn re_star / try_re_star,
        check: is_re,
        assert_msg: "re_star requires RegLan sort",
        error_expected: "RegLan",
        variant: ReStar
    }

    unop_same_sort! {
        /// Regex Kleene plus (re.+ re).
        /// REQUIRES: `self` is a RegLan sort.
        /// ENSURES: result sort is RegLan.
        fn re_plus / try_re_plus,
        check: is_re,
        assert_msg: "re_plus requires RegLan sort",
        error_expected: "RegLan",
        variant: RePlus
    }

    binop_same_sort! {
        /// Regex union (re.union re1 re2).
        /// REQUIRES: `self` and `other` are RegLan sorts.
        /// ENSURES: result sort is RegLan.
        fn re_union / try_re_union,
        check: re_same,
        assert_msg: "re_union requires RegLan sorts",
        error_expected: "RegLan sorts",
        variant: ReUnion
    }

    binop_same_sort! {
        /// Regex concatenation (re.++ re1 re2).
        /// REQUIRES: `self` and `other` are RegLan sorts.
        /// ENSURES: result sort is RegLan.
        fn re_concat / try_re_concat,
        check: re_same,
        assert_msg: "re_concat requires RegLan sorts",
        error_expected: "RegLan sorts",
        variant: ReConcat
    }
}
