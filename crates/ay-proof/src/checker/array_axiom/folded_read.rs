// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The independent re-derivation of a FOLDED array read: the work-bounded
//! matcher `recognize_folded_array_extensionality` uses, and the ground
//! index-disequality test the row-chain walk uses.
//!
//! Both answer the same question from the McCarthy axioms alone — what does
//! this term denote as `select(array, index)`? — and neither confers any
//! authority: a folded extensionality clause is licensed by its witness's
//! provenance (`super::ExtDiffRegistry`), never by shape.

use super::*;

/// Memoized, work-bounded structural matcher for folded witness reads.
///
/// Array terms are DAGs. In particular, proof-shape-preserving raw ITEs may
/// retain identical branches, so naive recursion would revisit one shared
/// child exponentially many times. The `(array, index, candidate, depth)` memo
/// makes matching linear in the reachable product DAG. The hard state ceiling
/// also makes an adversarial non-shared depth-64 tree fail closed instead of
/// consuming unbounded checker work.
pub(super) struct FoldedReadMatcher<'terms, 'budget, 'counter> {
    terms: &'terms TermStore,
    memo: DetHashMap<(TermId, TermId, FoldTarget, usize), bool>,
    budget: &'budget mut FoldedReadWorkBudget<'counter>,
}

/// What one point of the fold has to denote: an exact term of the clause, or
/// one of the two Boolean constants a `mk_ite` fold ERASED.
///
/// `mk_ite` does not always leave an `Ite` node behind. At element sort `Bool`
/// it rewrites the node into propositional structure, and the two rewrites the
/// measured population needs erase a `true`/`false` branch outright:
///
/// ```text
/// (ite c true false) = c          (ite c false true) = (not c)
/// ```
///
/// The erased branch has no `TermId` in the clause and the strict checker holds
/// an IMMUTABLE [`TermStore`], so it cannot intern `true`/`false` to compare.
/// It is carried as a constant instead and decoded against a candidate term.
/// This is the same device — and the same two identities — that
/// `ArrayRowChain` sub-schema (K) (`super::ite_eval::FoldedValue`) uses.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum FoldTarget {
    Node(TermId),
    BoolConst(bool),
}

impl FoldTarget {
    /// Whether this denotation IS the exact term `term`.
    fn denotes(self, terms: &TermStore, term: TermId) -> bool {
        match self {
            Self::Node(id) => id == term,
            Self::BoolConst(value) => {
                matches!(terms.get(term), TermData::Const(ay_core::Constant::Bool(b)) if *b == value)
            }
        }
    }

    /// Whether this denotation is well sorted at an array's element sort.
    fn well_sorted(self, terms: &TermStore, element_sort: &Sort) -> bool {
        match self {
            Self::Node(id) => terms.sort(id) == element_sort,
            Self::BoolConst(_) => element_sort == &Sort::Bool,
        }
    }
}

impl<'terms, 'budget, 'counter> FoldedReadMatcher<'terms, 'budget, 'counter> {
    const FOLD_BOUND: usize = 64;

    pub(super) fn new(
        terms: &'terms TermStore,
        budget: &'budget mut FoldedReadWorkBudget<'counter>,
    ) -> Self {
        Self {
            terms,
            memo: DetHashMap::default(),
            budget,
        }
    }

    /// Independently match the proof-shape-preserving fold of `select(array,
    /// index)` against an already-interned `candidate` term.
    pub(super) fn matches(
        &mut self,
        array: TermId,
        index: TermId,
        candidate: TermId,
        depth: usize,
    ) -> bool {
        self.matches_target(array, index, FoldTarget::Node(candidate), depth)
    }

    fn matches_target(
        &mut self,
        array: TermId,
        index: TermId,
        target: FoldTarget,
        depth: usize,
    ) -> bool {
        let key = (array, index, target, depth);
        if let Some(&cached) = self.memo.get(&key) {
            return cached;
        }
        if !self.budget.consume() {
            return false;
        }

        let result = self.matches_uncached(array, index, target, depth);
        self.memo.insert(key, result);
        result
    }

    fn matches_uncached(
        &mut self,
        array: TermId,
        index: TermId,
        target: FoldTarget,
        depth: usize,
    ) -> bool {
        let Sort::Array(array_sort) = self.terms.sort(array) else {
            return false;
        };
        let index_sort = array_sort.index_sort.clone();
        let element_sort = array_sort.element_sort.clone();
        if self.terms.sort(index) != &index_sort || !target.well_sorted(self.terms, &element_sort) {
            return false;
        }
        let FoldTarget::Node(candidate) = target else {
            // An ERASED Boolean branch is a constant, so nothing below can read
            // it as a raw select or as further `ite` structure. Only the two
            // arms that compare a constant directly — the const-array fill and
            // a write AT the read index — can discharge it; everything else
            // fails closed.
            return self.matches_erased_bool(array, index, target, &element_sort, &index_sort);
        };
        if depth >= Self::FOLD_BOUND {
            return is_exact_well_sorted_select(self.terms, candidate, array, index);
        }

        if let Some(fill) = self.terms.get_const_array(array) {
            return self.terms.sort(fill) == &element_sort && candidate == fill;
        }

        match self.terms.get(array).clone() {
            TermData::App(Symbol::Named(symbol), args) if symbol == "store" && args.len() == 3 => {
                let (base, store_index, value) = (args[0], args[1], args[2]);
                if self.terms.sort(base) != self.terms.sort(array)
                    || self.terms.sort(store_index) != &index_sort
                    || self.terms.sort(value) != &element_sort
                {
                    return false;
                }
                if store_index == index {
                    return candidate == value;
                }
                if matches!(self.terms.get(index), TermData::Const(_))
                    && matches!(self.terms.get(store_index), TermData::Const(_))
                {
                    return self.matches(base, index, candidate, depth + 1);
                }

                let Some((condition, then_target, else_target)) =
                    self.decode_store_fold(candidate, index, store_index, &element_sort)
                else {
                    return false;
                };
                self.terms.sort(condition) == &Sort::Bool
                    && matches_equality_pair(self.terms, condition, index, store_index)
                    && then_target.denotes(self.terms, value)
                    && self.matches_target(base, index, else_target, depth + 1)
            }
            TermData::Ite(guard, then_array, else_array) => {
                if self.terms.sort(guard) != &Sort::Bool
                    || self.terms.sort(then_array) != self.terms.sort(array)
                    || self.terms.sort(else_array) != self.terms.sort(array)
                {
                    return false;
                }
                let TermData::Ite(candidate_guard, then_value, else_value) =
                    self.terms.get(candidate).clone()
                else {
                    return false;
                };
                candidate_guard == guard
                    && self.terms.sort(then_value) == &element_sort
                    && self.terms.sort(else_value) == &element_sort
                    && self.matches(then_array, index, then_value, depth + 1)
                    && self.matches(else_array, index, else_value, depth + 1)
            }
            _ => is_exact_well_sorted_select(self.terms, candidate, array, index),
        }
    }

    /// Discharge an ERASED Boolean branch: the only readings are a const-array
    /// whose fill IS that constant, and a store AT the read index whose value
    /// IS that constant. Everything else — a deeper store, an array `ite`, an
    /// opaque root — fails closed, because a constant cannot be a raw select
    /// and the further `mk_ite` Bool rewrites (`(or c x)`, `(and c x)`) are
    /// deliberately not decoded here.
    fn matches_erased_bool(
        &mut self,
        array: TermId,
        index: TermId,
        target: FoldTarget,
        element_sort: &Sort,
        index_sort: &Sort,
    ) -> bool {
        if let Some(fill) = self.terms.get_const_array(array) {
            return self.terms.sort(fill) == element_sort && target.denotes(self.terms, fill);
        }
        match self.terms.get(array).clone() {
            TermData::App(Symbol::Named(symbol), args) if symbol == "store" && args.len() == 3 => {
                let (store_index, value) = (args[1], args[2]);
                self.terms.sort(store_index) == index_sort
                    && self.terms.sort(value) == element_sort
                    && store_index == index
                    && target.denotes(self.terms, value)
            }
            _ => false,
        }
    }

    /// Decode `candidate` as `ite((= index store_index), then, else)` under the
    /// folds `mk_ite` performs, returning the guard and the two branches.
    ///
    /// DETERMINISTIC: at most one reading is returned and no alternative is
    /// retried, because the three arms are mutually exclusive by term head
    /// (`Ite`, `=`, `not`). The two Bool arms are only offered at element sort
    /// `Bool` — at any other sort `mk_ite` leaves the `Ite` node alone, so
    /// offering them would be reading structure that no fold could have
    /// produced.
    fn decode_store_fold(
        &self,
        candidate: TermId,
        index: TermId,
        store_index: TermId,
        element_sort: &Sort,
    ) -> Option<(TermId, FoldTarget, FoldTarget)> {
        if let TermData::Ite(condition, then_value, else_value) = self.terms.get(candidate) {
            let (condition, then_value, else_value) = (*condition, *then_value, *else_value);
            if self.terms.sort(then_value) != element_sort
                || self.terms.sort(else_value) != element_sort
            {
                return None;
            }
            return Some((
                condition,
                FoldTarget::Node(then_value),
                FoldTarget::Node(else_value),
            ));
        }
        if element_sort != &Sort::Bool {
            return None;
        }
        // `(ite c true false) = c`
        if matches_equality_pair(self.terms, candidate, index, store_index) {
            return Some((
                candidate,
                FoldTarget::BoolConst(true),
                FoldTarget::BoolConst(false),
            ));
        }
        // `(ite c false true) = (not c)`
        if let TermData::Not(inner) = self.terms.get(candidate) {
            let inner = *inner;
            if matches_equality_pair(self.terms, inner, index, store_index) {
                return Some((
                    inner,
                    FoldTarget::BoolConst(false),
                    FoldTarget::BoolConst(true),
                ));
            }
        }
        None
    }
}

/// Whether `left` and `right` are interpreted constants of the SAME kind whose
/// values differ, so `left != right` holds in every model with no case analysis
/// and no clause literal to discharge it.
///
/// Deliberately restricted to the two constant families
/// `TermStore::mk_select`'s own read-over-write fold consults (`Int` and a
/// same-WIDTH `BitVec`). A `Bool`, `Rational` or `String` index would be sound
/// too, but nothing in the measured population produces one and each extra
/// family is one more spelling to get wrong; they fail closed.
pub(crate) fn distinct_interpreted_indices(terms: &TermStore, left: TermId, right: TermId) -> bool {
    let (TermData::Const(left), TermData::Const(right)) = (terms.get(left), terms.get(right))
    else {
        return false;
    };
    match (left, right) {
        (ay_core::Constant::Int(a), ay_core::Constant::Int(b)) => a != b,
        (
            ay_core::Constant::BitVec {
                value: a,
                width: wa,
            },
            ay_core::Constant::BitVec {
                value: b,
                width: wb,
            },
        ) => wa == wb && a != b,
        _ => false,
    }
}

#[cfg(test)]
#[path = "../array_ext_bool_fold_tests.rs"]
mod bool_fold_tests;
