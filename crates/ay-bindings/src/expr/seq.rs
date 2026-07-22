// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Sequence operations for AY expressions.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

/// Predicate: both operands are Seq sorts with the same element sort.
fn seq_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_seq() && b.sort.is_seq() && a.sort == b.sort
}

/// Predicate: operand is a Seq sort.
fn is_seq(a: &Expr) -> bool {
    a.sort.is_seq()
}

impl Expr {
    // ===== Sequence Construction =====

    /// Create an empty sequence of the given element sort.
    ///
    /// In SMT-LIB: `(as seq.empty (Seq T))`.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_empty(element_sort: Sort) -> Self {
        let seq_sort = Sort::seq(element_sort.clone());
        Self {
            sort: seq_sort,
            value: Arc::new(ExprValue::SeqEmpty(element_sort)),
        }
    }

    /// Create a unit sequence containing a single element.
    ///
    /// In SMT-LIB: `(seq.unit elem)`.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_unit(self) -> Self {
        let seq_sort = Sort::seq(self.sort.clone());
        Self {
            sort: seq_sort,
            value: Arc::new(ExprValue::SeqUnit(self)),
        }
    }

    // ===== Sequence Concatenation =====

    binop_same_sort! {
        /// Sequence concatenation (seq.++ s t).
        /// REQUIRES: `self` and `other` are Seq sorts with the same element sort.
        /// ENSURES: result sort is the same Seq sort.
        fn seq_concat / try_seq_concat,
        check: seq_same,
        assert_msg: "seq_concat requires matching Seq sorts",
        error_expected: "matching Seq sorts",
        variant: SeqConcat
    }

    // ===== Sequence Length =====

    unop_to_sort! {
        /// Sequence length (seq.len s), returns Int.
        /// REQUIRES: `self` is a Seq sort.
        /// ENSURES: result sort is Int.
        fn seq_len / try_seq_len,
        check: is_seq,
        assert_msg: "seq_len requires Seq sort",
        error_expected: "Seq",
        result_sort: Sort::int(),
        variant: SeqLen
    }

    // ===== Element Access =====

    /// Element at index (seq.nth s i), returning the element sort.
    ///
    /// # Panics
    /// Panics if `self` is not a Seq sort or `index` is not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_nth(self, index: Self) -> Self {
        self.try_seq_nth(index)
            .expect("seq_nth requires Seq and Int sorts")
    }

    /// Fallible version of [`Expr::seq_nth`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_seq_nth(self, index: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_seq() || !index.sort.is_int() {
            return Err(crate::SortError::binary(
                "seq_nth",
                "Seq and Int",
                &self.sort,
                &index.sort,
            ));
        }
        let elem_sort = self.sort.seq_element().expect("checked is_seq").clone();
        Ok(Self {
            sort: elem_sort,
            value: Arc::new(ExprValue::SeqNth(self, index)),
        })
    }

    // ===== Subsequence Extraction =====

    /// Subsequence extraction (seq.extract s offset len), returning the same Seq sort.
    ///
    /// # Panics
    /// Panics if `self` is not a Seq sort or `offset`/`len` are not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_extract(self, offset: Self, len: Self) -> Self {
        self.try_seq_extract(offset, len)
            .expect("seq_extract requires Seq, Int, Int sorts")
    }

    /// Fallible version of [`Expr::seq_extract`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_seq_extract(self, offset: Self, len: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_seq() || !offset.sort.is_int() || !len.sort.is_int() {
            return Err(crate::SortError::Mismatch {
                operation: "seq_extract",
                expected: "Seq, Int, Int",
                actual: format!("{}, {}, {}", self.sort, offset.sort, len.sort),
            });
        }
        let sort = self.sort.clone();
        Ok(Self {
            sort,
            value: Arc::new(ExprValue::SeqExtract(self, offset, len)),
        })
    }

    // ===== Sequence Predicates =====

    binop_to_bool! {
        /// Sequence containment test (seq.contains s t), returns Bool.
        /// REQUIRES: `self` and `other` are Seq sorts with the same element sort.
        /// ENSURES: result sort is Bool.
        fn seq_contains / try_seq_contains,
        check: seq_same,
        assert_msg: "seq_contains requires matching Seq sorts",
        error_expected: "matching Seq sorts",
        variant: SeqContains
    }

    binop_to_bool! {
        /// Sequence prefix test (seq.prefixof pre s), returns Bool.
        /// REQUIRES: `self` and `other` are Seq sorts with the same element sort.
        /// ENSURES: result sort is Bool.
        fn seq_prefixof / try_seq_prefixof,
        check: seq_same,
        assert_msg: "seq_prefixof requires matching Seq sorts",
        error_expected: "matching Seq sorts",
        variant: SeqPrefixOf
    }

    binop_to_bool! {
        /// Sequence suffix test (seq.suffixof suf s), returns Bool.
        /// REQUIRES: `self` and `other` are Seq sorts with the same element sort.
        /// ENSURES: result sort is Bool.
        fn seq_suffixof / try_seq_suffixof,
        check: seq_same,
        assert_msg: "seq_suffixof requires matching Seq sorts",
        error_expected: "matching Seq sorts",
        variant: SeqSuffixOf
    }

    // ===== Sequence Search =====

    /// Sequence index-of (seq.indexof s t i), returns Int.
    /// Returns -1 if `t` is not found in `s` starting at position `i`.
    ///
    /// # Panics
    /// Panics if `self`/`t` are not matching Seq sorts or `start` is not Int.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_indexof(self, t: Self, start: Self) -> Self {
        self.try_seq_indexof(t, start)
            .expect("seq_indexof requires matching Seq sorts and Int")
    }

    /// Fallible version of [`Expr::seq_indexof`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_seq_indexof(self, t: Self, start: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_seq() || !t.sort.is_seq() || self.sort != t.sort || !start.sort.is_int() {
            return Err(crate::SortError::Mismatch {
                operation: "seq_indexof",
                expected: "Seq(T), Seq(T), Int",
                actual: format!("{}, {}, {}", self.sort, t.sort, start.sort),
            });
        }
        Ok(Self {
            sort: Sort::int(),
            value: Arc::new(ExprValue::SeqIndexOf(self, t, start)),
        })
    }

    // ===== Sequence Replacement =====

    /// Sequence replace first occurrence (seq.replace s from to).
    ///
    /// # Panics
    /// Panics if any argument is not a matching Seq sort.
    #[must_use = "expression operations return a new Expr"]
    pub fn seq_replace(self, from: Self, to: Self) -> Self {
        self.try_seq_replace(from, to)
            .expect("seq_replace requires matching Seq sorts")
    }

    /// Fallible version of [`Expr::seq_replace`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_seq_replace(self, from: Self, to: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_seq()
            || !from.sort.is_seq()
            || !to.sort.is_seq()
            || self.sort != from.sort
            || self.sort != to.sort
        {
            return Err(crate::SortError::Mismatch {
                operation: "seq_replace",
                expected: "Seq(T), Seq(T), Seq(T)",
                actual: format!("{}, {}, {}", self.sort, from.sort, to.sort),
            });
        }
        let sort = self.sort.clone();
        Ok(Self {
            sort,
            value: Arc::new(ExprValue::SeqReplace(self, from, to)),
        })
    }
}
