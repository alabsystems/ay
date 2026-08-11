// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Elaboration of SMT-LIB and Z3 5.0.0 finite-set operators over the
//! membership carrier.
//!
//! Sets are carried as `Array(T -> Bool)`. Membership and the
//! array-decidable constructors are reduced to `select` / `store` here so the
//! array solver decides them soundly with no quantifier instantiation:
//!
//! - `(set.member e s)` / `(set.in e s)` → `(select s e)` : Bool
//! - `(set.singleton e)` → `(store (constfalse) e true)`
//! - `(set.insert e s)` → `(store s e true)`
//! - `(set.remove e s)` → `(store s e false)`
//!
//! Cardinality and symbolic subset stay as opaque applications decided by the
//! native set theory (`ay-set`) plus executor-injected ground axioms; an
//! empty-rooted ground subset is decided exactly during elaboration:
//!
//! - `(set.card s)` / `(set.size s)` : Int
//! - `(set.subset s t)` : Bool
//!
//! Z3 5.0.0's pointwise union/intersection/difference/complement constructors
//! are represented exactly as characteristic-array lambdas. Map/filter/range
//! constructors are reduced to covered store chains when their finite support
//! is explicitly known. This makes the ground constructor laws exact,
//! including cardinality. A general symbolic image or range remains an opaque
//! `set.*` application; the executor's fail-closed guard returns `Unknown` for
//! it instead of treating the operation as an uninterpreted function and
//! guessing a verdict.

use std::collections::BTreeSet;

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::super::{Context, ElaborateError, Result};

/// Bound one textual range expansion so a compact pair of endpoints cannot
/// amplify into an unbounded term DAG. Larger or symbolic ranges stay as the
/// real `set.range` operation and are rejected as incomplete by the set solver.
const MAX_EXPLICIT_RANGE_ELEMENTS: usize = 4096;

impl Context {
    /// Try to elaborate a `set.*` application. Returns `Ok(None)` when `name` is
    /// not a set operator (so other dispatchers get a chance).
    pub(super) fn try_elaborate_set_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        // Z3's array plugin exposes these legacy set spellings only in the
        // null logic, HORN, and ALL signatures. A user declaration is resolved
        // before this dispatcher, so it still shadows the builtin exactly as
        // it does in Z3. Canonicalize them to AY's `set.*` operators so both
        // vocabularies share one sound implementation.
        let legacy_aliases_enabled = self
            .logic
            .as_deref()
            .is_none_or(|logic| matches!(logic, "HORN" | "ALL"));
        let canonical_name = if legacy_aliases_enabled {
            match name {
                "union" => "set.union",
                "intersection" => "set.intersect",
                "setminus" => "set.difference",
                "complement" => "set.complement",
                "subset" => "set.subset",
                _ => name,
            }
        } else {
            name
        };

        // Record set usage so logic detection routes to the dedicated QF_SETLIA
        // solver (which enforces card>=0 / card(empty)=0 / subset<->membership)
        // even under a mismatched declared logic, where the erased Array(T->Bool)
        // carrier would otherwise be solved by the generic array path
        // (#set-routing).
        if canonical_name.starts_with("set.") {
            self.mark_uses_set();
        }
        match canonical_name {
            // Z3 5.0.0 calls membership `set.in`; AY's existing Set spelling is
            // `set.member`. Both use element-first argument order.
            "set.member" | "set.in" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier(name, set, elem)?;
                Ok(Some(self.terms.mk_select(set, elem)))
            }
            // singleton(e) == store(const-false, e, true).
            "set.singleton" => {
                self.expect_exact_arity("set.singleton", arg_ids, 1)?;
                let elem = arg_ids[0];
                let elem_sort = self.terms.sort(elem).clone();
                let false_term = self.terms.false_term();
                let empty = self.terms.mk_const_array(elem_sort, false_term);
                let true_term = self.terms.true_term();
                Ok(Some(self.terms.mk_store(empty, elem, true_term)))
            }
            // insert(e, s) == store(s, e, true).
            "set.insert" => {
                self.expect_exact_arity("set.insert", arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier("set.insert", set, elem)?;
                let true_term = self.terms.true_term();
                Ok(Some(self.terms.mk_store(set, elem, true_term)))
            }
            // remove(e, s) == store(s, e, false).
            "set.remove" => {
                self.expect_exact_arity("set.remove", arg_ids, 2)?;
                let elem = arg_ids[0];
                let set = arg_ids[1];
                self.check_set_carrier("set.remove", set, elem)?;
                let false_term = self.terms.false_term();
                Ok(Some(self.terms.mk_store(set, elem, false_term)))
            }
            // Z3 5.0.0 calls cardinality `set.size`; AY's native set theory
            // consumes the canonical `set.card` node.
            "set.card" | "set.size" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.set_carrier_basis(name, arg_ids[0])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("set.card"),
                    arg_ids,
                    Sort::Int,
                )))
            }
            // subset(s, t) : Bool.  Empty-rooted ground store chains have an
            // exact finite representation, so decide them here.  Symbolic
            // sets remain opaque for the native set solver and its
            // ground-witness saturation.
            "set.subset" => {
                self.expect_exact_arity("set.subset", arg_ids, 2)?;
                self.check_matching_set_carriers("set.subset", arg_ids)?;
                if let (Some(left), Some(right)) = (
                    self.concrete_ground_set(arg_ids[0]),
                    self.concrete_ground_set(arg_ids[1]),
                ) {
                    return Ok(Some(if left.is_subset(&right) {
                        self.terms.true_term()
                    } else {
                        self.terms.false_term()
                    }));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("set.subset"),
                    arg_ids,
                    Sort::Bool,
                )))
            }

            // Z3 5.0.0 marks union/intersection associative, so its textual
            // parser accepts two or more operands. When every operand is a
            // ground, empty-rooted store chain, compute the exact finite support
            // and return another covered chain. Otherwise retain the real
            // operator so the executor fails closed.
            "set.union" | "set.intersect" => {
                self.expect_min_arity(name, arg_ids, 2)?;
                let basis = self.check_matching_set_carriers(name, arg_ids)?;
                let concrete = arg_ids
                    .iter()
                    .map(|&set| self.concrete_ground_set(set))
                    .collect::<Option<Vec<_>>>();
                if let Some(mut sets) = concrete {
                    let mut elements = sets.remove(0);
                    for next in sets {
                        if canonical_name == "set.union" {
                            elements.extend(next);
                        } else {
                            elements = elements
                                .intersection(&next)
                                .copied()
                                .collect::<BTreeSet<_>>();
                        }
                    }
                    return Ok(Some(self.mk_explicit_set(basis, elements)));
                }
                let index = self.terms.mk_fresh_var("__ay_set_index", basis);
                let members = arg_ids
                    .iter()
                    .map(|&set| self.terms.mk_select(set, index))
                    .collect::<Vec<_>>();
                let membership = if canonical_name == "set.union" {
                    self.terms.mk_or(members)
                } else {
                    self.terms.mk_and(members)
                };
                Ok(Some(self.terms.mk_lambda_array(index, membership)))
            }

            // Difference is binary in Z3 5.0.0. The legacy AY spelling
            // `set.minus` shares the same exact ground reduction.
            "set.difference" | "set.minus" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let basis = self.check_matching_set_carriers(name, arg_ids)?;
                if let (Some(left), Some(right)) = (
                    self.concrete_ground_set(arg_ids[0]),
                    self.concrete_ground_set(arg_ids[1]),
                ) {
                    let elements: BTreeSet<TermId> = left.difference(&right).copied().collect();
                    return Ok(Some(self.mk_explicit_set(basis, elements)));
                }
                let index = self.terms.mk_fresh_var("__ay_set_index", basis);
                let left = self.terms.mk_select(arg_ids[0], index);
                let right = self.terms.mk_select(arg_ids[1], index);
                let not_right = self.terms.mk_not(right);
                let membership = self.terms.mk_and(vec![left, not_right]);
                Ok(Some(self.terms.mk_lambda_array(index, membership)))
            }

            // The legacy pointwise intersection shares the characteristic-
            // array lambda encoding. Unlike Z3's `intersection`, this AY
            // spelling historically accepts one operand as the identity.
            "set.inter" => {
                self.expect_min_arity(name, arg_ids, 1)?;
                let basis = self.check_matching_set_carriers(name, arg_ids)?;
                let index = self.terms.mk_fresh_var("__ay_set_index", basis);
                let members = arg_ids
                    .iter()
                    .map(|&set| self.terms.mk_select(set, index))
                    .collect::<Vec<_>>();
                let membership = self.terms.mk_and(members);
                Ok(Some(self.terms.mk_lambda_array(index, membership)))
            }
            "set.complement" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                let basis = self.set_carrier_basis(name, arg_ids[0])?;
                let index = self.terms.mk_fresh_var("__ay_set_index", basis);
                let member = self.terms.mk_select(arg_ids[0], index);
                let membership = self.terms.mk_not(member);
                Ok(Some(self.terms.mk_lambda_array(index, membership)))
            }

            // Image under an array-encoded unary function. An explicitly known
            // finite source has an exact store-chain image, even when individual
            // image terms remain symbolic. A free source requires existential
            // image reasoning and stays fail-closed.
            "set.map" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let (domain, image) = self.array_signature(name, arg_ids[0])?;
                let basis = self.set_carrier_basis(name, arg_ids[1])?;
                if domain != basis {
                    return Err(ElaborateError::SortMismatch {
                        expected: basis.to_string(),
                        actual: domain.to_string(),
                    });
                }
                let result_sort = Sort::array(image.clone(), Sort::Bool);
                if let Some(source) = self.concrete_ground_set(arg_ids[1]) {
                    let images: BTreeSet<TermId> = source
                        .into_iter()
                        .map(|element| self.terms.mk_select(arg_ids[0], element))
                        .collect();
                    return Ok(Some(self.mk_explicit_set(image, images)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }

            // Filtering an explicitly known source is the exact characteristic
            // store chain `store(..., e, predicate[e])`. The general case stays
            // as a guarded out-of-fragment operator.
            "set.filter" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let (domain, predicate_range) = self.array_signature(name, arg_ids[0])?;
                if predicate_range != Sort::Bool {
                    return Err(ElaborateError::SortMismatch {
                        expected: Sort::Bool.to_string(),
                        actual: predicate_range.to_string(),
                    });
                }
                let basis = self.set_carrier_basis(name, arg_ids[1])?;
                if domain != basis {
                    return Err(ElaborateError::SortMismatch {
                        expected: basis.to_string(),
                        actual: domain.to_string(),
                    });
                }
                if let Some(source) = self.concrete_ground_set(arg_ids[1]) {
                    let false_term = self.terms.false_term();
                    let mut result = self.terms.mk_const_array(basis.clone(), false_term);
                    for element in source {
                        let accepted = self.terms.mk_select(arg_ids[0], element);
                        result = self.terms.mk_store(result, element, accepted);
                    }
                    return Ok(Some(result));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    Sort::array(basis, Sort::Bool),
                )))
            }

            // Inclusive integer range. Small literal endpoints become a covered
            // store chain, giving exact empty/singleton/cardinality behavior.
            // Symbolic or deliberately non-expanded large ranges retain their
            // true operator and therefore return Unknown at solve time.
            "set.range" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                for &endpoint in arg_ids {
                    let actual = self.terms.sort(endpoint);
                    if actual != &Sort::Int {
                        return Err(ElaborateError::SortMismatch {
                            expected: Sort::Int.to_string(),
                            actual: actual.to_string(),
                        });
                    }
                }
                if let Some(elements) = self.explicit_integer_range(arg_ids[0], arg_ids[1]) {
                    return Ok(Some(self.mk_explicit_set(Sort::Int, elements)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    Sort::array(Sort::Int, Sort::Bool),
                )))
            }
            _ => Ok(None),
        }
    }

    /// Return the element sort of an `Array(T, Bool)` finite-set carrier.
    fn set_carrier_basis(&self, op: &str, set: TermId) -> Result<Sort> {
        match self.terms.sort(set) {
            Sort::Array(array) if array.element_sort == Sort::Bool => Ok(array.index_sort.clone()),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("(FiniteSet _) carried as (Array _ Bool) for {op}"),
                actual: actual.to_string(),
            }),
        }
    }

    /// Validate a non-empty list of same-basis finite-set carriers.
    fn check_matching_set_carriers(&self, op: &str, sets: &[TermId]) -> Result<Sort> {
        let Some(&first) = sets.first() else {
            return Err(ElaborateError::InvalidConstant(format!(
                "{op} requires at least one finite-set argument"
            )));
        };
        let basis = self.set_carrier_basis(op, first)?;
        for &set in &sets[1..] {
            let actual = self.set_carrier_basis(op, set)?;
            if actual != basis {
                return Err(ElaborateError::SortMismatch {
                    expected: basis.to_string(),
                    actual: actual.to_string(),
                });
            }
        }
        Ok(basis)
    }

    /// Domain/range of an array-encoded unary function.
    fn array_signature(&self, op: &str, function: TermId) -> Result<(Sort, Sort)> {
        match self.terms.sort(function) {
            Sort::Array(array) => Ok((array.index_sort.clone(), array.element_sort.clone())),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("(Array _ _) function argument for {op}"),
                actual: actual.to_string(),
            }),
        }
    }

    /// Recover an explicitly represented finite set.
    ///
    /// Only ground element constants are admitted. Statically applying a
    /// `store(..., x, false)` update when `x` is symbolic would be unsound
    /// because two syntactically different indices may be equal in a model.
    fn concrete_ground_set(&self, set: TermId) -> Option<BTreeSet<TermId>> {
        let mut updates = Vec::new();
        let mut current = set;
        loop {
            match self.terms.get(current) {
                TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                    if !matches!(self.terms.get(args[1]), TermData::Const(_)) {
                        return None;
                    }
                    let present = if self.terms.is_true(args[2]) {
                        true
                    } else if self.terms.is_false(args[2]) {
                        false
                    } else {
                        return None;
                    };
                    updates.push((args[1], present));
                    current = args[0];
                }
                _ => {
                    let default = self.terms.get_const_array(current)?;
                    if !self.terms.is_false(default) {
                        return None;
                    }
                    break;
                }
            }
        }

        let mut elements = BTreeSet::new();
        for (element, present) in updates.into_iter().rev() {
            if present {
                elements.insert(element);
            } else {
                elements.remove(&element);
            }
        }
        Some(elements)
    }

    /// Build a covered, empty-rooted characteristic-array store chain.
    fn mk_explicit_set(
        &mut self,
        basis: Sort,
        elements: impl IntoIterator<Item = TermId>,
    ) -> TermId {
        let false_term = self.terms.false_term();
        let true_term = self.terms.true_term();
        let mut result = self.terms.mk_const_array(basis, false_term);
        for element in elements {
            result = self.terms.mk_store(result, element, true_term);
        }
        result
    }

    /// Expand a small inclusive literal range, returning `None` for symbolic or
    /// intentionally non-expanded large endpoints.
    fn explicit_integer_range(&mut self, low: TermId, high: TermId) -> Option<BTreeSet<TermId>> {
        let (TermData::Const(Constant::Int(low)), TermData::Const(Constant::Int(high))) =
            (self.terms.get(low), self.terms.get(high))
        else {
            return None;
        };
        let low = low.clone();
        let high = high.clone();
        if low > high {
            return Some(BTreeSet::new());
        }
        let width = (&high - &low + BigInt::from(1u8)).to_usize()?;
        if width > MAX_EXPLICIT_RANGE_ELEMENTS {
            return None;
        }
        Some(
            (0..width)
                .map(|offset| self.terms.mk_int(&low + BigInt::from(offset)))
                .collect::<BTreeSet<_>>(),
        )
    }

    /// Validate that `set` is carried as `Array(_ -> Bool)` and `elem` matches
    /// its index sort. Returns a sort-mismatch error otherwise.
    fn check_set_carrier(&self, op: &str, set: TermId, elem: TermId) -> Result<()> {
        let basis = self.set_carrier_basis(op, set)?;
        let elem_sort = self.terms.sort(elem).clone();
        if elem_sort != basis {
            return Err(ElaborateError::SortMismatch {
                expected: basis.to_string(),
                actual: elem_sort.to_string(),
            });
        }
        Ok(())
    }
}
