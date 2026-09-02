// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean/logical term constructors: not, and, or, implies, xor.
//!
//! Equality, ITE, and distinct constructors are in `boolean_eq`.

use super::*;
use crate::kani_compat::det_hash_set_with_capacity;

impl TermStore {
    /// Create negation
    pub fn mk_not(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Bool,
            "BUG: mk_not expects Bool, got {:?}",
            self.sort(arg)
        );
        // Memoize: `mk_not` recursively pushes De Morgan / ITE-negation down, so
        // without a cache a shared (let-bound) subterm reached through many
        // negation contexts is re-normalized once per occurrence — the
        // DAG-unfolded-to-tree blow-up that makes a 100k-`let` state-machine VC
        // take minutes to elaborate. The recursion below calls back through this
        // cached entry point, so each distinct arg is normalized at most once.
        // SOUND: `mk_not` is pure; speculative rollback prunes every cache
        // entry that mentions its discarded suffix before those IDs are reused.
        // (#mk-not-memo)
        if let Some(&cached) = self.not_cache.get(&arg) {
            return cached;
        }
        let result = self.mk_not_uncached(arg);
        self.not_cache.insert(arg, result);
        result
    }

    fn mk_not_uncached(&mut self, arg: TermId) -> TermId {
        // Check for double negation
        if let TermData::Not(inner) = self.get(arg) {
            return *inner;
        }
        // Check for constant
        if let TermData::Const(Constant::Bool(b)) = self.get(arg) {
            return self.mk_bool(!*b);
        }

        // De Morgan normalization for boolean connectives
        // (not (and a b ...)) -> (or (not a) (not b) ...)
        // (not (or a b ...))  -> (and (not a) (not b) ...)
        let de_morgan: Option<(bool, Vec<TermId>)> = match self.get(arg) {
            TermData::App(Symbol::Named(name), args) if name == "and" => Some((true, args.clone())),
            TermData::App(Symbol::Named(name), args) if name == "or" => Some((false, args.clone())),
            _ => None,
        };
        if let Some((is_and, args)) = de_morgan {
            let negated_args: Vec<TermId> = args.into_iter().map(|t| self.mk_not(t)).collect();
            return if is_and {
                self.mk_or(negated_args)
            } else {
                self.mk_and(negated_args)
            };
        }

        // ITE negation normalization (for Boolean ITE only)
        // (not (ite c a b)) -> (ite c (not a) (not b))
        // This pushes negation down and enables further simplifications in mk_ite
        if let TermData::Ite(cond, then_term, else_term) = self.get(arg) {
            let cond = *cond;
            let then_term = *then_term;
            let else_term = *else_term;
            // Only apply to Boolean ITE (which is the case since we're in mk_not)
            if self.sort(then_term) == &Sort::Bool {
                let not_then = self.mk_not(then_term);
                let not_else = self.mk_not(else_term);
                return self.mk_ite(cond, not_then, not_else);
            }
        }

        self.intern(TermData::Not(arg), Sort::Bool)
    }

    /// Create a raw negation term without simplification.
    ///
    /// This preserves an explicit `Not` wrapper (no De Morgan rewrite), which is
    /// required when constructing proof literals that must remain syntactically
    /// complementary for proof checking.
    pub fn mk_not_raw(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Bool,
            "BUG: mk_not_raw expects Bool, got {:?}",
            self.sort(arg)
        );
        self.intern(TermData::Not(arg), Sort::Bool)
    }

    /// Create conjunction (and)
    ///
    /// Flattens nested and terms: (and a (and b c)) -> (and a b c)
    /// Detects complements: (and x (not x)) -> false
    /// Absorption: (and x (or x y)) -> x
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_and(&mut self, args: Vec<TermId>) -> TermId {
        debug_assert!(
            args.iter().all(|&a| self.sort(a) == &Sort::Bool),
            "BUG: mk_and expects all Bool args"
        );
        if args.is_empty() {
            return self.true_term();
        }
        if let &[only] = args.as_slice() {
            return only;
        }

        if self.has_flatten_hidden_complement_pair(&args, "and") {
            return self.false_term();
        }

        // Flatten nested ands, filter out true constants, check for false
        let mut filtered = Vec::new();
        for &arg in &args {
            match self.get(arg) {
                TermData::Const(Constant::Bool(false)) => return self.false_term(),
                TermData::Const(Constant::Bool(true)) => {} // skip
                TermData::App(Symbol::Named(name), nested_args) if name == "and" => {
                    // Flatten: extract nested and arguments
                    let nested = nested_args.clone();
                    filtered.extend(nested);
                }
                _ => filtered.push(arg),
            }
        }

        if filtered.is_empty() {
            return self.true_term();
        }
        if let &[only] = filtered.as_slice() {
            return only;
        }

        // Sort for canonical form
        filtered.sort();
        filtered.dedup();

        // Complement detection AFTER flattening:
        // This catches (and x (not x)) and (and a (and b (not b)))
        // filtered is sorted, so use binary_search for O(n log n) total.
        for &arg in &filtered {
            if let TermData::Not(inner) = self.get(arg) {
                if filtered.binary_search(inner).is_ok() {
                    return self.false_term();
                }
            }
        }

        if let &[only] = filtered.as_slice() {
            return only;
        }

        // Absorption: (and x (or x y)) -> x
        // If any arg is an Or containing another arg of the And, remove that Or
        // filtered is sorted, so use binary_search for O(n × m × log n) instead of O(n × m × n).
        let mut absorbed = Vec::new();
        for &arg in &filtered {
            let mut absorb_this = false;
            if let TermData::App(Symbol::Named(name), or_args) = self.get(arg) {
                if name == "or" {
                    for &or_elem in or_args {
                        if filtered.binary_search(&or_elem).is_ok() && or_elem != arg {
                            absorb_this = true;
                            break;
                        }
                    }
                }
            }
            if !absorb_this {
                absorbed.push(arg);
            }
        }

        if absorbed.is_empty() {
            return self.true_term();
        }
        if let &[only] = absorbed.as_slice() {
            return only;
        }

        // Negation-through absorption: (and x (or (not x) y z)) -> (and x (or y z))
        // For each literal x in the conjunction, remove (not x) from any inner or's
        // absorbed preserves sorted order from filtered, so binary_search works.
        let mut neg_absorbed = Vec::new();
        for &arg in &absorbed {
            if let TermData::App(Symbol::Named(name), or_args) = self.get(arg) {
                if name == "or" {
                    let mut new_or_args: Vec<TermId> = Vec::new();
                    let or_args_clone = or_args.clone();
                    for &or_elem in &or_args_clone {
                        let mut is_negated_sibling = false;
                        if let TermData::Not(inner) = self.get(or_elem) {
                            if absorbed.binary_search(inner).is_ok() && *inner != arg {
                                is_negated_sibling = true;
                            }
                        }
                        if !is_negated_sibling {
                            new_or_args.push(or_elem);
                        }
                    }
                    // Rebuild the or if we removed anything
                    if new_or_args.len() < or_args_clone.len() {
                        let new_or = self.mk_or(new_or_args);
                        neg_absorbed.push(new_or);
                        continue;
                    }
                }
            }
            neg_absorbed.push(arg);
        }

        // Re-run simplifications on the result since we may have changed inner terms
        if neg_absorbed.len() != absorbed.len()
            || neg_absorbed.iter().zip(&absorbed).any(|(a, b)| a != b)
        {
            return self.mk_and(neg_absorbed);
        }

        self.intern(
            TermData::App(Symbol::named("and"), neg_absorbed),
            Sort::Bool,
        )
    }

    /// Create disjunction (or)
    ///
    /// Flattens nested or terms: (or a (or b c)) -> (or a b c)
    /// Detects complements: (or x (not x)) -> true
    /// Absorption: (or x (and x y)) -> x
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_or(&mut self, args: Vec<TermId>) -> TermId {
        debug_assert!(
            args.iter().all(|&a| self.sort(a) == &Sort::Bool),
            "BUG: mk_or expects all Bool args"
        );
        if args.is_empty() {
            return self.false_term();
        }
        if let &[only] = args.as_slice() {
            return only;
        }

        if self.has_flatten_hidden_complement_pair(&args, "or") {
            return self.true_term();
        }

        // Flatten nested ors, filter out false constants, check for true
        let mut filtered = Vec::new();
        for &arg in &args {
            match self.get(arg) {
                TermData::Const(Constant::Bool(true)) => return self.true_term(),
                TermData::Const(Constant::Bool(false)) => {} // skip
                TermData::App(Symbol::Named(name), nested_args) if name == "or" => {
                    // Flatten: extract nested or arguments
                    let nested = nested_args.clone();
                    filtered.extend(nested);
                }
                _ => filtered.push(arg),
            }
        }

        if filtered.is_empty() {
            return self.false_term();
        }
        if let &[only] = filtered.as_slice() {
            return only;
        }

        // Sort for canonical form
        filtered.sort();
        filtered.dedup();

        // Complement detection AFTER flattening:
        // This catches (or x (not x)) and (or a (or b (not b)))
        // filtered is sorted, so use binary_search for O(n log n) total.
        for &arg in &filtered {
            if let TermData::Not(inner) = self.get(arg) {
                if filtered.binary_search(inner).is_ok() {
                    return self.true_term();
                }
            }
        }

        if let &[only] = filtered.as_slice() {
            return only;
        }

        // Absorption: (or x (and x y)) -> x
        // If any arg is an And containing another arg of the Or, remove that And
        // filtered is sorted, so use binary_search.
        let mut absorbed = Vec::new();
        for &arg in &filtered {
            let mut absorb_this = false;
            if let TermData::App(Symbol::Named(name), and_args) = self.get(arg) {
                if name == "and" {
                    for &and_elem in and_args {
                        if filtered.binary_search(&and_elem).is_ok() && and_elem != arg {
                            absorb_this = true;
                            break;
                        }
                    }
                }
            }
            if !absorb_this {
                absorbed.push(arg);
            }
        }

        if absorbed.is_empty() {
            return self.false_term();
        }
        if let &[only] = absorbed.as_slice() {
            return only;
        }

        // Negation-through absorption: (or x (and (not x) y z)) -> (or x (and y z))
        // For each literal x in the disjunction, remove (not x) from any inner and's
        // absorbed preserves sorted order from filtered, so binary_search works.
        let mut neg_absorbed = Vec::new();
        for &arg in &absorbed {
            if let TermData::App(Symbol::Named(name), and_args) = self.get(arg) {
                if name == "and" {
                    let mut new_and_args: Vec<TermId> = Vec::new();
                    let and_args_clone = and_args.clone();
                    for &and_elem in &and_args_clone {
                        let mut is_negated_sibling = false;
                        if let TermData::Not(inner) = self.get(and_elem) {
                            if absorbed.binary_search(inner).is_ok() && *inner != arg {
                                is_negated_sibling = true;
                            }
                        }
                        if !is_negated_sibling {
                            new_and_args.push(and_elem);
                        }
                    }
                    // Rebuild the and if we removed anything
                    if new_and_args.len() < and_args_clone.len() {
                        let new_and = self.mk_and(new_and_args);
                        neg_absorbed.push(new_and);
                        continue;
                    }
                }
            }
            neg_absorbed.push(arg);
        }

        // Re-run simplifications on the result since we may have changed inner terms
        if neg_absorbed.len() != absorbed.len()
            || neg_absorbed.iter().zip(&absorbed).any(|(a, b)| a != b)
        {
            return self.mk_or(neg_absorbed);
        }

        self.intern(TermData::App(Symbol::named("or"), neg_absorbed), Sort::Bool)
    }

    /// Create implication
    pub fn mk_implies(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            self.sort(lhs) == &Sort::Bool && self.sort(rhs) == &Sort::Bool,
            "BUG: mk_implies expects Bool args, got {:?} => {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // a => b is equivalent to (not a) or b
        let not_lhs = self.mk_not(lhs);
        self.mk_or(vec![not_lhs, rhs])
    }

    /// Create exclusive or (XOR) with simplifications
    ///
    /// Simplifications:
    /// - (xor a a) = false
    /// - (xor a true) = (not a)
    /// - (xor a false) = a
    /// - (xor a (not a)) = true
    /// - (xor (not a) (not b)) = (xor a b) (double negation lifting)
    pub fn mk_xor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            self.sort(lhs) == &Sort::Bool && self.sort(rhs) == &Sort::Bool,
            "BUG: mk_xor expects Bool args, got {:?} xor {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        let true_term = self.true_term();
        let false_term = self.false_term();

        // (xor a a) = false
        if lhs == rhs {
            return false_term;
        }

        // (xor a true) = (not a), (xor true a) = (not a)
        if rhs == true_term {
            return self.mk_not(lhs);
        }
        if lhs == true_term {
            return self.mk_not(rhs);
        }

        // (xor a false) = a, (xor false a) = a
        if rhs == false_term {
            return lhs;
        }
        if lhs == false_term {
            return rhs;
        }

        // (xor a (not a)) = true, (xor (not a) a) = true
        if let Some(inner) = self.get_not_inner(lhs) {
            if inner == rhs {
                return true_term;
            }
        }
        if let Some(inner) = self.get_not_inner(rhs) {
            if inner == lhs {
                return true_term;
            }
        }

        // (xor (not a) (not b)) = (xor a b)
        if let (Some(lhs_inner), Some(rhs_inner)) =
            (self.get_not_inner(lhs), self.get_not_inner(rhs))
        {
            return self.mk_xor(lhs_inner, rhs_inner);
        }

        // Canonical ordering
        let (a, b) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
        self.intern(TermData::App(Symbol::named("xor"), vec![a, b]), Sort::Bool)
    }

    // =======================================================================
    // Boolean helpers
    // =======================================================================

    /// Helper: extract the inner term from a (not x) term
    pub(crate) fn get_not_inner(&self, id: TermId) -> Option<TermId> {
        match self.get(id) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        }
    }

    fn has_flatten_hidden_complement_pair(&self, args: &[TermId], flattened_name: &str) -> bool {
        let has_flattenable_not = args.iter().any(|&arg| {
            matches!(
                self.get(arg),
                TermData::Not(inner)
                    if matches!(
                        self.get(*inner),
                        TermData::App(Symbol::Named(name), _) if name == flattened_name
                    )
            )
        });
        if !has_flattenable_not {
            return false;
        }

        let mut arg_set = det_hash_set_with_capacity(args.len());
        for &arg in args {
            arg_set.insert(arg);
        }

        args.iter().any(|&arg| {
            matches!(
                self.get(arg),
                TermData::Not(inner) if arg_set.contains(inner)
            )
        })
    }
}
