// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural keys for the persistent BV bit-blast cache.
//!
//! `SmtContext::reset` replaces the `TermStore`, so a `TermId` means nothing
//! to the next query. The cache names a term by its structure instead: a
//! [`BvCacheKey`] is interned from the term's node (its sort, its operator
//! with any indices, constant, or canonical CHC variable, and the keys of its
//! children) in the [`BvCacheKeys`] table stored inside the cache it indexes.
//!
//! * Exact: two terms get the same key iff their nodes are equal after
//!   replacing each child by its key, so equal keys mean the same term over
//!   the same variables. That is the property `restore_cached_bv_state`
//!   relies on when it hands a cached bit vector or literal to a new term.
//! * DAG-linear: [`SmtContext::bv_cache_key`] keys each distinct `TermId`
//!   once per pass (the caller's memo) with O(arity) work, on an explicit
//!   stack.
//!
//! The previous key printed `term_to_chc_expr(term)` with the tree printer
//! `InvariantModel::expr_to_smtlib`, once for every keyed term: exponential
//! in the nesting of shared sub-terms. On bist_cell a 170-atom signature
//! over 254 distinct terms prints 1.9e9 tree nodes, and a single
//! `check_sat` grew past 6 GB. It also named variables without their sort
//! below the root, so `x <= y` over BV8 and over BV16 shared one key and a
//! reused cache refuted a satisfiable query.
//!
//! Admission (which terms get a key) keeps the old grammar: the terms the
//! old key could print, i.e. constants and canonical CHC variables closed
//! under the operators `term_to_chc_expr` decodes. Extract, extensions,
//! rotations and uninterpreted functions stay outside, as the cache's reuse
//! protocol (and `full_adder_cache_tests`) expects. One deliberate narrowing:
//! a `Let` node is not keyed (the old key read it as its body, which would
//! give two different nodes one key; the CHC layer never mints `Let`).
//! Admission only decides what is cached; exactness alone makes a restored
//! entry right.

use crate::smt::context::SmtContext;
use crate::smt::SmtValue;
use crate::term_bridge::sort::{core_sort_decodes_strict, core_sort_to_chc_strict};
use crate::{ChcExpr, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_traits::ToPrimitive;

/// Structural identity of a cacheable term, valid for the [`BvCacheKeys`]
/// table that minted it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(in crate::smt) struct BvCacheKey(u32);

#[cfg(test)]
impl BvCacheKey {
    /// A key for cache-container tests that never consult a key table.
    pub(in crate::smt) fn from_raw_for_tests(raw: u32) -> Self {
        Self(raw)
    }
}

/// Per-pass memo: `TermId` -> key (`None`: outside the cacheable grammar).
/// Valid for one `TermStore` state and one [`BvCacheKeys`] table.
pub(in crate::smt) type BvKeyMemo = FxHashMap<TermId, Option<BvCacheKey>>;

/// One term node with its children replaced by their keys.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum KeyNode {
    Const(Constant),
    /// A canonical CHC variable, by its sort-qualified term name.
    Var(String),
    Not(BvCacheKey),
    Ite(BvCacheKey, BvCacheKey, BvCacheKey),
    App(Symbol, Vec<BvCacheKey>),
}

/// Interning table for [`BvCacheKey`]s. It lives in the `PersistentBvCache`
/// whose maps it keys and is cleared with them.
#[derive(Debug, Default)]
pub(in crate::smt) struct BvCacheKeys {
    ids: FxHashMap<(KeyNode, Sort), BvCacheKey>,
}

impl BvCacheKeys {
    /// Number of interned nodes.
    pub(in crate::smt) fn len(&self) -> usize {
        self.ids.len()
    }

    pub(in crate::smt) fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    pub(in crate::smt) fn clear(&mut self) {
        self.ids.clear();
    }

    fn intern(&mut self, node: KeyNode, sort: Sort) -> Option<BvCacheKey> {
        let fresh = BvCacheKey(u32::try_from(self.ids.len()).ok()?);
        Some(*self.ids.entry((node, sort)).or_insert(fresh))
    }
}

/// Operators `term_to_chc_expr` decodes, with the arity it requires.
fn decoded_operator_arity_ok(symbol: &Symbol, arity: usize) -> Option<bool> {
    let ok = match symbol.name() {
        "and" | "or" | "+" | "-" => arity >= 1,
        "neg" | "bvnot" | "bvneg" | "bv2nat" | "bv2int" => arity == 1,
        "int2bv" => {
            arity == 1 && matches!(symbol, Symbol::Indexed(_, indices) if !indices.is_empty())
        }
        "store" => arity == 3,
        "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">=" | "*" | "div" | "intdiv" | "mod"
        | "select" | "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
        | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl"
        | "bvlshr" | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle"
        | "bvsgt" | "bvsge" | "concat" => arity == 2,
        _ => return None,
    };
    Some(ok)
}

/// Constants `term_to_chc_expr` decodes.
fn constant_decodes(constant: &Constant) -> bool {
    match constant {
        Constant::Bool(_) | Constant::Int(_) => true,
        Constant::Rational(r) => {
            r.0.numer().to_i64().is_some() && r.0.denom().to_i64().is_some_and(|d| d != 0)
        }
        Constant::BitVec { value, width } => SmtValue::bitvec_from_bigint(value.clone(), *width)
            .bitvec_to_chc_expr()
            .is_some(),
        _ => false,
    }
}

impl SmtContext {
    /// Structural key of `term`, or `None` when it is outside the cacheable
    /// grammar. Linear in the terms not yet in `memo`.
    pub(in crate::smt) fn bv_cache_key(
        &self,
        keys: &mut BvCacheKeys,
        term: TermId,
        memo: &mut BvKeyMemo,
    ) -> Option<BvCacheKey> {
        if let Some(&key) = memo.get(&term) {
            return key;
        }
        let mut stack = vec![(term, false)];
        while let Some((node, children_keyed)) = stack.pop() {
            if memo.contains_key(&node) {
                continue;
            }
            if children_keyed {
                let key = self.bv_cache_node_key(keys, node, memo);
                memo.insert(node, key);
                continue;
            }
            stack.push((node, true));
            match self.terms.get(node) {
                TermData::Not(inner) => stack.push((*inner, false)),
                TermData::Ite(c, t, e) => stack.extend([(*c, false), (*t, false), (*e, false)]),
                TermData::App(_, args) => stack.extend(args.iter().map(|&arg| (arg, false))),
                _ => {}
            }
        }
        memo.get(&term).copied().flatten()
    }

    /// Sorted, deduplicated keys of the cacheable `terms`: equal signatures
    /// mean equal sets of cacheable atoms.
    pub(in crate::smt) fn bv_cache_signature(
        &self,
        keys: &mut BvCacheKeys,
        terms: impl IntoIterator<Item = TermId>,
        memo: &mut BvKeyMemo,
    ) -> Vec<BvCacheKey> {
        let mut signature: Vec<BvCacheKey> = terms
            .into_iter()
            .filter_map(|term| self.bv_cache_key(keys, term, memo))
            .collect();
        signature.sort_unstable();
        signature.dedup();
        signature
    }

    /// Key of one node whose children are already in `memo`.
    fn bv_cache_node_key(
        &self,
        keys: &mut BvCacheKeys,
        term: TermId,
        memo: &BvKeyMemo,
    ) -> Option<BvCacheKey> {
        let child = |t: &TermId| memo.get(t).copied().flatten();
        let sort = self.terms.sort(term);
        let node = match self.terms.get(term) {
            TermData::Const(constant) if constant_decodes(constant) => {
                KeyNode::Const(constant.clone())
            }
            // Only the variable `get_or_create_var` minted for this
            // sort-qualified name denotes the same CHC variable in every
            // query. Any other term-store variable (an auxiliary minted
            // directly, such as an `_ite_*` or predicate-application
            // stand-in) is not keyed.
            TermData::Var(name, _)
                if self.var_map.get(name.as_str()) == Some(&term)
                    && core_sort_decodes_strict(sort) =>
            {
                KeyNode::Var(name.clone())
            }
            TermData::Not(inner) => KeyNode::Not(child(inner)?),
            TermData::Ite(c, t, e) => KeyNode::Ite(child(c)?, child(t)?, child(e)?),
            TermData::App(symbol, args) => {
                let arg_keys = args.iter().map(child).collect::<Option<Vec<_>>>()?;
                if !self.bv_cache_app_decodes(symbol, args, sort) {
                    return None;
                }
                KeyNode::App(symbol.clone(), arg_keys)
            }
            _ => return None,
        };
        keys.intern(node, sort.clone())
    }

    /// Whether `term_to_chc_expr` decodes an application of `symbol` to
    /// decodable `args`.
    fn bv_cache_app_decodes(&self, symbol: &Symbol, args: &[TermId], sort: &Sort) -> bool {
        if let Some(ok) = decoded_operator_arity_ok(symbol, args.len()) {
            return ok;
        }
        // Datatype constructors, selectors and testers: the decoder checks
        // names and sorts only, so sort-faithful stand-ins give its verdict.
        self.try_dt_app_to_chc_expr(symbol.name(), args, sort, |arg| {
            core_sort_to_chc_strict(self.terms.sort(arg))
                .map(|sort| ChcExpr::Var(ChcVar::new(String::new(), sort)))
        })
        .is_some()
    }
}

#[cfg(test)]
#[path = "key_tests.rs"]
mod tests;
