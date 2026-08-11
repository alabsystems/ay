// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Elaboration of SMT-LIB multiset (bag) operators over the count carrier.
//!
//! Multisets are carried as `Array(T -> Int)`. The count and the
//! array-decidable constructors are reduced to `select` / `store` here so the
//! array solver decides them soundly with no quantifier instantiation:
//!
//! - `(multiset.count e m)`     → `(select m e)`                          : Int
//! - `(multiset.singleton e)`   → `(store (const0) e 1)`
//! - `(multiset.insert e m)`    → `(store m e (+ (select m e) 1))`
//! - `(multiset.remove e m)`    → `(store m e (ite (> (select m e) 0)
//!                                                  (- (select m e) 1) 0))`
//!
//! The `remove` clamp at 0 keeps counts non-negative (a multiset never holds a
//! negative multiplicity). Subset stays as an opaque application decided by the
//! native multiset theory (`ay-multiset`) plus executor-injected ground axioms:
//!
//! - `(multiset.subset m n)`    : Bool   (opaque; `count>=0` and the
//!   subset↔count witness obligations are injected by the executor)
//!
//! The pointwise combinators `multiset.union` / `multiset.inter` /
//! `multiset.diff` (and the higher-order image ops) are emitted as opaque
//! multiset-sorted applications. The executor's fail-closed guard then returns
//! `Unknown` for any formula that references them, because their count
//! semantics (`count(union(m,n),e) = max(count(m,e),count(n,e))`, etc.) need a
//! comprehension over the element domain the carrier does not yet provide.
//! Emitting them as opaque apps (rather than erroring) lets well-formed
//! formulas parse and be soundly classified `Unknown` instead of crashing.

use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;

use super::super::{Context, ElaborateError, Result};

impl Context {
    /// Try to elaborate a `multiset.*` application. Returns `Ok(None)` when
    /// `name` is not a multiset operator (so other dispatchers get a chance).
    pub(super) fn try_elaborate_multiset_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        // Record multiset usage so logic detection routes to the dedicated
        // QF_MSLIA solver (which enforces `count >= 0`) even under
        // `(set-logic ALL)`, where the erased Array(T->Int) carrier would
        // otherwise be solved by the generic array/LIA path (#multiset-routing).
        if name.starts_with("multiset.") {
            self.mark_uses_multiset();
        }
        match name {
            // count(e, m) == select(m, e). SMT-LIB order is (multiset.count elem ms).
            "multiset.count" => {
                self.expect_exact_arity("multiset.count", arg_ids, 2)?;
                let elem = arg_ids[0];
                let multiset = arg_ids[1];
                self.check_multiset_carrier("multiset.count", multiset, elem)?;
                Ok(Some(self.terms.mk_select(multiset, elem)))
            }
            // singleton(e) == store(const-0, e, 1).
            "multiset.singleton" => {
                self.expect_exact_arity("multiset.singleton", arg_ids, 1)?;
                let elem = arg_ids[0];
                let elem_sort = self.terms.sort(elem).clone();
                let zero = self.terms.mk_int(BigInt::from(0));
                let empty = self.terms.mk_const_array(elem_sort, zero);
                let one = self.terms.mk_int(BigInt::from(1));
                Ok(Some(self.terms.mk_store(empty, elem, one)))
            }
            // insert(e, m) == store(m, e, count(m,e) + 1).
            "multiset.insert" => {
                self.expect_exact_arity("multiset.insert", arg_ids, 2)?;
                let elem = arg_ids[0];
                let multiset = arg_ids[1];
                self.check_multiset_carrier("multiset.insert", multiset, elem)?;
                let count = self.terms.mk_select(multiset, elem);
                let one = self.terms.mk_int(BigInt::from(1));
                let inc = self.terms.mk_add(vec![count, one]);
                Ok(Some(self.terms.mk_store(multiset, elem, inc)))
            }
            // remove(e, m) == store(m, e, max(count(m,e) - 1, 0)) — clamped at 0.
            "multiset.remove" => {
                self.expect_exact_arity("multiset.remove", arg_ids, 2)?;
                let elem = arg_ids[0];
                let multiset = arg_ids[1];
                self.check_multiset_carrier("multiset.remove", multiset, elem)?;
                let count = self.terms.mk_select(multiset, elem);
                let one = self.terms.mk_int(BigInt::from(1));
                let zero = self.terms.mk_int(BigInt::from(0));
                let dec = self.terms.mk_sub(vec![count, one]);
                // ite(count > 0, count - 1, 0): clamp so multiplicity stays >= 0.
                let positive = self.terms.mk_gt(count, zero);
                let clamped = self.terms.mk_ite(positive, dec, zero);
                Ok(Some(self.terms.mk_store(multiset, elem, clamped)))
            }
            // subset(m, n) : Bool — opaque, decided natively + injected axioms.
            "multiset.subset" => {
                self.expect_exact_arity("multiset.subset", arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("multiset.subset"),
                    arg_ids,
                    Sort::Bool,
                )))
            }
            // Pointwise / higher-order ops: emit opaque multiset-sorted apps. The
            // executor fail-closes (Unknown) on any formula referencing these.
            // `map`/`filter` take a function/predicate first arg; their result
            // multiset sort is the last argument's multiset sort.
            "multiset.union"
            | "multiset.inter"
            | "multiset.diff"
            | "multiset.map"
            | "multiset.filter"
            | "multiset.fold"
            | "multiset.comprehension"
            | "multiset.sum"
            | "multiset.choose" => {
                // Use the last argument's sort as the result sort when it is a
                // multiset carrier (`map`/`filter` carry a function/predicate in
                // arg 0); otherwise the first argument's sort. The executor
                // fail-closes regardless, so this only needs to type-check.
                let Some(&last) = arg_ids.last() else {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 1 argument"
                    )));
                };
                let result_sort = if self.terms.sort(last).is_array() {
                    self.terms.sort(last).clone()
                } else {
                    self.terms.sort(arg_ids[0]).clone()
                };
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            _ => Ok(None),
        }
    }

    /// Validate that `multiset` is carried as `Array(_ -> Int)` and `elem`
    /// matches its index sort. Returns a sort-mismatch error otherwise.
    fn check_multiset_carrier(&self, op: &str, multiset: TermId, elem: TermId) -> Result<()> {
        if let Sort::Array(arr) = self.terms.sort(multiset).clone() {
            let elem_sort = self.terms.sort(elem).clone();
            if elem_sort != arr.index_sort {
                return Err(ElaborateError::SortMismatch {
                    expected: arr.index_sort.to_string(),
                    actual: elem_sort.to_string(),
                });
            }
            Ok(())
        } else {
            Err(ElaborateError::SortMismatch {
                expected: format!("(Multiset _) carried as Array for {op}"),
                actual: self.terms.sort(multiset).to_string(),
            })
        }
    }
}
