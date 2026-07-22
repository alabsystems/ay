// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Elaboration of SMT-LIB finite-set operators over the membership carrier.
//!
//! Sets are carried as `Array(T -> Bool)`. Membership and the
//! array-decidable constructors are reduced to `select` / `store` here so the
//! array solver decides them soundly with no quantifier instantiation:
//!
//! - `(set.member e s)`    → `(select s e)`           : Bool
//! - `(set.singleton e)`   → `(store (constfalse) e true)`
//! - `(set.insert e s)`    → `(store s e true)`
//! - `(set.remove e s)`    → `(store s e false)`
//!
//! Cardinality and subset stay as opaque applications decided by the native
//! set theory (`ay-set`) plus executor-injected ground axioms:
//!
//! - `(set.card s)`        : Int    (opaque; `card >= 0`, `card(empty)=0` injected)
//! - `(set.subset s t)`    : Bool   (opaque; refuted by ground witness saturation)
//!
//! The pointwise combinators `set.union` / `set.inter` / `set.minus` (and the
//! higher-order image ops) are emitted as opaque set-sorted applications. The
//! executor's fail-closed guard then returns `Unknown` for any formula that
//! references them, because their membership semantics need a comprehension
//! over the element domain that the carrier does not yet provide. Emitting them
//! as opaque apps (rather than erroring) lets well-formed formulas parse and be
//! soundly classified `Unknown` instead of crashing.

use ay_core::{Sort, Symbol, TermId};

use super::super::{Context, ElaborateError, Result};

impl Context {
    /// Try to elaborate a `set.*` application. Returns `Ok(None)` when `name` is
    /// not a set operator (so other dispatchers get a chance).
    pub(super) fn try_elaborate_set_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        // Record set usage so logic detection routes to the dedicated QF_SETLIA
        // solver (which enforces card>=0 / card(empty)=0 / subset<->membership)
        // even under a mismatched declared logic, where the erased Array(T->Bool)
        // carrier would otherwise be solved by the generic array path
        // (#set-routing).
        if name.starts_with("set.") {
            self.mark_uses_set();
        }
        match name {
            // member(e, s) == select(s, e). SMT-LIB order is (set.member elem set).
            "set.member" => {
                self.expect_exact_arity("set.member", arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier("set.member", set, elem)?;
                Ok(Some(self.terms.mk_select(set, elem)))
            }
            // singleton(e) == store(const-false, e, true).
            "set.singleton" => {
                self.expect_exact_arity("set.singleton", arg_ids, 1)?;
                let elem = arg_ids[0];
                let elem_sort = self.terms.sort(elem).clone();
                let false_t = self.terms.false_term();
                let empty = self.terms.mk_const_array(elem_sort, false_t);
                let true_t = self.terms.true_term();
                Ok(Some(self.terms.mk_store(empty, elem, true_t)))
            }
            // insert(e, s) == store(s, e, true).
            "set.insert" => {
                self.expect_exact_arity("set.insert", arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier("set.insert", set, elem)?;
                let true_t = self.terms.true_term();
                Ok(Some(self.terms.mk_store(set, elem, true_t)))
            }
            // remove(e, s) == store(s, e, false).
            "set.remove" => {
                self.expect_exact_arity("set.remove", arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier("set.remove", set, elem)?;
                let false_t = self.terms.false_term();
                Ok(Some(self.terms.mk_store(set, elem, false_t)))
            }
            // card(s) : Int — opaque, decided by native set theory + LIA.
            "set.card" => {
                self.expect_exact_arity("set.card", arg_ids, 1)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("set.card"),
                    arg_ids,
                    Sort::Int,
                )))
            }
            // subset(s, t) : Bool — opaque, refuted by ground-witness saturation.
            "set.subset" => {
                self.expect_exact_arity("set.subset", arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("set.subset"),
                    arg_ids,
                    Sort::Bool,
                )))
            }
            // Pointwise / higher-order ops: emit opaque set-sorted apps. The
            // executor fail-closes (Unknown) on any formula referencing these.
            "set.union" | "set.inter" | "set.minus" | "set.complement" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 1 argument"
                    )));
                }
                let set_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    set_sort,
                )))
            }
            _ => Ok(None),
        }
    }

    /// Validate that `set` is carried as `Array(_ -> Bool)` and `elem` matches
    /// its index sort. Returns a sort-mismatch error otherwise.
    fn check_set_carrier(&self, op: &str, set: TermId, elem: TermId) -> Result<()> {
        if let Sort::Array(arr) = self.terms.sort(set).clone() {
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
                expected: format!("(Set _) carried as Array for {op}"),
                actual: self.terms.sort(set).to_string(),
            })
        }
    }
}
