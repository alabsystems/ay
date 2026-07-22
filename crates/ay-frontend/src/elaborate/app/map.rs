// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Elaboration of SMT-LIB finite-map (dictionary) operators over the
//! (value carrier + domain carrier) model.
//!
//! A `Map(K, V)` is carried as **two** parallel arrays:
//!
//! - the **value** carrier `Array(K -> V)` — the Map-sorted term itself; and
//! - the **domain** carrier `dom = Array(K -> Bool)` — reached via the
//!   `(map.dom m)` projection.
//!
//! The constructors stay as **opaque Map-sorted apps** (`map.insert`,
//! `map.remove`) so the readers can push through them and update both carriers
//! in lockstep via `store`/`select` read-through. The empty map is the
//! constant-false-domain pair (its value carrier is an unconstrained const
//! array; reads are gated by the false domain).
//!
//! - `(map.get m k)` : V — value read pushed through the constructors of `m`
//!   (insert -> `ite(k=k', v', get(m', k))`, remove -> `get(m', k)`, var/empty
//!   -> `(select m k)`).
//! - `(map.dom m)` : Array(K, Bool) — domain array pushed through the
//!   constructors (empty -> const-false, insert -> `store(dom m') k' true`,
//!   remove -> `store(dom m') k' false`, var -> opaque `(map.dom m)`).
//! - `(map.contains_key m k)` : Bool -> `(select (map.dom m) k)`.
//! - `(map.subset m n)` : Bool — opaque; reflexivity decided natively, the
//!   subset<->key obligations injected by the executor.
//!
//! The polymorphic / higher-order ops (`map.values` / `map.entries` /
//! `map.filter_keys` / `map.fold` / `map.comprehension` / `map.map_values` /
//! `map.choose`) are emitted as opaque map-sorted apps. The executor's
//! fail-closed guard then returns `Unknown` for any formula that references
//! them, because their semantics need a comprehension over the key domain the
//! carriers do not yet provide. Emitting them as opaque apps (rather than
//! erroring) lets well-formed formulas parse and be soundly classified
//! `Unknown` instead of crashing.

use ay_core::term::TermData;
use ay_core::{Sort, Symbol, TermId};

use super::super::{Context, ElaborateError, Result};

/// Out-of-fragment / higher-order map operators emitted as opaque apps.
const MAP_OPAQUE_OPS: &[&str] = &[
    "map.values",
    "map.entries",
    "map.filter_keys",
    "map.fold",
    "map.comprehension",
    "map.map_values",
    "map.choose",
];

impl Context {
    /// Try to elaborate a `map.*` application. Returns `Ok(None)` when `name` is
    /// not a map operator (so other dispatchers get a chance).
    pub(super) fn try_elaborate_map_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        match name {
            // get(m, k): value read, gated by the domain, pushed through the
            // constructors of `m`.
            "map.get" => {
                self.expect_exact_arity("map.get", arg_ids, 2)?;
                let map = arg_ids[0];
                let key = arg_ids[1];
                self.check_map_value_carrier("map.get", map, key)?;
                Ok(Some(self.elaborate_map_get(map, key)))
            }
            // contains_key(m, k) == select(dom(m), k).
            "map.contains_key" => {
                self.expect_exact_arity("map.contains_key", arg_ids, 2)?;
                let map = arg_ids[0];
                let key = arg_ids[1];
                self.check_map_value_carrier("map.contains_key", map, key)?;
                let dom = self.elaborate_map_dom(map);
                Ok(Some(self.terms.mk_select(dom, key)))
            }
            // dom(m): the domain array `Array(K -> Bool)`, pushed through the
            // constructors of `m`.
            "map.dom" => {
                self.expect_exact_arity("map.dom", arg_ids, 1)?;
                let map = arg_ids[0];
                Ok(Some(self.elaborate_map_dom(map)))
            }
            // insert(m, k, v): opaque Map-sorted app over the value carrier so
            // readers can push through it. Sort is the map's value-carrier sort.
            "map.insert" => {
                self.expect_exact_arity("map.insert", arg_ids, 3)?;
                let map = arg_ids[0];
                let key = arg_ids[1];
                let value = arg_ids[2];
                self.check_map_value_carrier("map.insert", map, key)?;
                self.check_map_value_sort("map.insert", map, value)?;
                let result_sort = self.terms.sort(map).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("map.insert"),
                    vec![map, key, value],
                    result_sort,
                )))
            }
            // remove(m, k): opaque Map-sorted app over the value carrier.
            "map.remove" => {
                self.expect_exact_arity("map.remove", arg_ids, 2)?;
                let map = arg_ids[0];
                let key = arg_ids[1];
                self.check_map_value_carrier("map.remove", map, key)?;
                let result_sort = self.terms.sort(map).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("map.remove"),
                    vec![map, key],
                    result_sort,
                )))
            }
            // subset(m, n) : Bool — opaque, decided natively + injected axioms.
            "map.subset" => {
                self.expect_exact_arity("map.subset", arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("map.subset"),
                    arg_ids,
                    Sort::Bool,
                )))
            }
            // Higher-order / image ops: emit opaque apps. The executor
            // fail-closes (Unknown) on any formula referencing these.
            other if MAP_OPAQUE_OPS.contains(&other) => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 1 argument"
                    )));
                }
                // Use the last map-sorted argument's sort as the result sort
                // when present; otherwise the first argument's sort. The
                // executor fail-closes regardless, so this only needs to
                // type-check.
                let result_sort = arg_ids
                    .iter()
                    .rev()
                    .map(|&a| self.terms.sort(a))
                    .find(|s| s.is_array())
                    .unwrap_or_else(|| self.terms.sort(arg_ids[0]))
                    .clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            _ => Ok(None),
        }
    }

    /// Elaborate `get(map, key)` by pushing the read through the constructors of
    /// `map` (read-over-write). Bottoms out at a `select` over the value carrier
    /// for variables / empty / opaque maps.
    fn elaborate_map_get(&mut self, map: TermId, key: TermId) -> TermId {
        match self.terms.get(map).clone() {
            TermData::App(sym, args) if sym.name() == "map.insert" && args.len() == 3 => {
                let inner = args[0];
                let k_prime = args[1];
                let v_prime = args[2];
                let cond = self.terms.mk_eq(key, k_prime);
                let else_branch = self.elaborate_map_get(inner, key);
                self.terms.mk_ite(cond, v_prime, else_branch)
            }
            TermData::App(sym, args) if sym.name() == "map.remove" && args.len() == 2 => {
                // remove does not change values of other keys; the value at a
                // removed key is unconstrained but gated false by the domain, so
                // reading through the inner map is sound.
                let inner = args[0];
                self.elaborate_map_get(inner, key)
            }
            // Variable / empty / opaque map: read the value carrier directly.
            _ => self.terms.mk_select(map, key),
        }
    }

    /// Elaborate `dom(map)` by pushing the domain array through the constructors
    /// of `map`. Bottoms out at the const-false array for empty maps and an
    /// opaque `(map.dom m)` projection for variables / opaque maps.
    fn elaborate_map_dom(&mut self, map: TermId) -> TermId {
        match self.terms.get(map).clone() {
            TermData::App(sym, args) if sym.name() == "map.insert" && args.len() == 3 => {
                let inner = args[0];
                let k_prime = args[1];
                let inner_dom = self.elaborate_map_dom(inner);
                let true_t = self.terms.true_term();
                self.terms.mk_store(inner_dom, k_prime, true_t)
            }
            TermData::App(sym, args) if sym.name() == "map.remove" && args.len() == 2 => {
                let inner = args[0];
                let k_prime = args[1];
                let inner_dom = self.elaborate_map_dom(inner);
                let false_t = self.terms.false_term();
                self.terms.mk_store(inner_dom, k_prime, false_t)
            }
            // Empty map: the constant-false domain.
            TermData::App(sym, _) if sym.name() == "const-array" && self.is_empty_map(map) => {
                let key_sort = self.map_key_sort(map);
                let false_t = self.terms.false_term();
                self.terms.mk_const_array(key_sort, false_t)
            }
            // Variable / opaque map: the opaque domain projection.
            _ => {
                let key_sort = self.map_key_sort(map);
                let dom_sort = Sort::array(key_sort, Sort::Bool);
                self.terms
                    .mk_app(Symbol::named("map.dom"), vec![map], dom_sort)
            }
        }
    }

    /// Whether `map` is an empty-map value carrier: a const array whose default
    /// value carries the empty-map marker. We treat any const-array value
    /// carrier as having an empty (all-false) domain — a const-array Map term is
    /// only produced by `(as map.empty (Map K V))`.
    fn is_empty_map(&self, map: TermId) -> bool {
        matches!(self.terms.get(map), TermData::App(sym, _) if sym.name() == "const-array")
    }

    /// The key (index) sort of a Map value carrier `Array(K -> V)`.
    fn map_key_sort(&self, map: TermId) -> Sort {
        self.terms
            .sort(map)
            .array_index()
            .cloned()
            .unwrap_or(Sort::Int)
    }

    /// Validate that `map` is carried as `Array(K -> V)` and `key` matches its
    /// index sort. Returns a sort-mismatch error otherwise.
    fn check_map_value_carrier(&self, op: &str, map: TermId, key: TermId) -> Result<()> {
        if let Sort::Array(arr) = self.terms.sort(map).clone() {
            let key_sort = self.terms.sort(key).clone();
            if key_sort != arr.index_sort {
                return Err(ElaborateError::SortMismatch {
                    expected: arr.index_sort.to_string(),
                    actual: key_sort.to_string(),
                });
            }
            Ok(())
        } else {
            Err(ElaborateError::SortMismatch {
                expected: format!("(Map K V) carried as Array for {op}"),
                actual: self.terms.sort(map).to_string(),
            })
        }
    }

    /// Validate that `value` matches the Map's value (element) sort.
    fn check_map_value_sort(&self, op: &str, map: TermId, value: TermId) -> Result<()> {
        if let Sort::Array(arr) = self.terms.sort(map).clone() {
            let value_sort = self.terms.sort(value).clone();
            if value_sort != arr.element_sort {
                return Err(ElaborateError::SortMismatch {
                    expected: arr.element_sort.to_string(),
                    actual: value_sort.to_string(),
                });
            }
            Ok(())
        } else {
            Err(ElaborateError::SortMismatch {
                expected: format!("(Map K V) carried as Array for {op}"),
                actual: self.terms.sort(map).to_string(),
            })
        }
    }
}
