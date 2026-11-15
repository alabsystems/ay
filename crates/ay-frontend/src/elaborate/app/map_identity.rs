// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Which terms are maps, and which one is the empty map (#map-value-semantics).
//!
//! `(Map K V)` is erased to its value array `Array(K -> V)`, so nothing in a
//! term's sort says it is a map. These are the facts the frontend alone can
//! supply to the SAT funnel's native-map gate (`ay-dpll`,
//! `executor/model/native_map_gate.rs`): the one empty map per sort, the
//! operator spellings the map theory decides, whether a sort can hold a map,
//! whether a map term is a declared constant, and whether a sort as written
//! is a map.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::super::{Context, DeclarationKind, SymbolInfo};
use super::map::MAP_OPAQUE_OPS;
use crate::command;
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

/// Name prefix of a map sort's empty-map value array. Recognition goes by the
/// memoized term ([`Context::is_native_empty_map`]), never by this name. It is
/// deliberately NOT in the reserved `__ay_` namespace: model validation skips
/// assertions over `__ay_` symbols as internal, which would withhold a genuine
/// `sat` such as `(= 5 (map.get (as map.empty (Map Int Int)) 1))`.
const MAP_EMPTY_VALUES_PREFIX: &str = "map_empty_values";

/// The native map operator spellings besides [`MAP_OPAQUE_OPS`]. A USER
/// declaration of one of these names (`map.dom`, `map.subset` — deductive-checks's
/// activation route) builds an application the map theory reads as its own
/// operator, so it marks the problem as a map problem just like the builtin.
const NATIVE_MAP_OPS: &[&str] = &[
    "map.get",
    "map.contains_key",
    "map.dom",
    "map.insert",
    "map.remove",
    "map.subset",
];

impl Context {
    /// The empty map of `map_sort` (the lowered `Array(K -> V)`): one fresh,
    /// unconstrained value array per sort, minted on first use. `map.empty`
    /// is a constant, so all its occurrences are one term; `map.dom` gives it
    /// the constant-false domain (`elaborate_map_dom` in `map.rs`).
    pub(in crate::elaborate) fn native_empty_map(&mut self, map_sort: Sort) -> TermId {
        if let Some(&existing) = self.map_empty_values.get(&map_sort) {
            return existing;
        }
        let values = self
            .terms
            .mk_fresh_var(MAP_EMPTY_VALUES_PREFIX, map_sort.clone());
        self.map_empty_values.insert(map_sort, values);
        values
    }

    /// Whether `term` is the empty map of its sort, as
    /// [`Self::native_empty_map`] minted it.
    pub fn is_native_empty_map(&self, term: TermId) -> bool {
        self.map_empty_values.get(self.terms.sort(term)) == Some(&term)
    }

    /// Whether `name` spells a native map operator (see [`NATIVE_MAP_OPS`]).
    pub(in crate::elaborate) fn is_native_map_op_name(name: &str) -> bool {
        NATIVE_MAP_OPS.contains(&name) || MAP_OPAQUE_OPS.contains(&name)
    }

    /// Whether a value of `sort` can be or contain a map. A `(Map K V)` is
    /// erased to `Array(K -> V)`, so this is any array sort, reached directly
    /// or through a sequence or a datatype field. A structural
    /// `Sort::Datatype`, which this frontend does not mint, counts as one.
    pub fn sort_may_hold_map(&self, sort: &Sort) -> bool {
        let mut seen_datatypes = HashSet::default();
        self.sort_may_hold_map_in(sort, &mut seen_datatypes)
    }

    fn sort_may_hold_map_in(&self, sort: &Sort, seen_datatypes: &mut HashSet<String>) -> bool {
        match sort {
            Sort::Seq(element) => self.sort_may_hold_map_in(element, seen_datatypes),
            Sort::Array(_) | Sort::Datatype(_) => true,
            // Datatypes elaborate to named sorts; their fields live in the
            // selector table. A recursive datatype is visited once.
            Sort::Uninterpreted(name) => {
                seen_datatypes.insert(name.clone())
                    && self.datatypes.get(name).is_some_and(|constructors| {
                        constructors.iter().any(|constructor| {
                            self.ctor_selector_info
                                .get(constructor)
                                .is_some_and(|selectors| {
                                    selectors.iter().any(|(_, field)| {
                                        self.sort_may_hold_map_in(field, seen_datatypes)
                                    })
                                })
                        })
                    })
            }
            _ => false,
        }
    }

    /// Whether `map` is a declared nullary map constant — the only map term a
    /// domain carrier faithfully stands for. A quantifier-bound or `define-fun`
    /// parameter is a fresh variable that no symbol binds, so it is not one.
    pub(super) fn is_declared_map_constant(&self, map: TermId) -> bool {
        let TermData::Var(name, _) = self.terms.get(map) else {
            return false;
        };
        let binds = |info: &SymbolInfo| {
            info.term == Some(map)
                && info.arg_sorts.is_empty()
                && info.declaration_kind() == DeclarationKind::Uninterpreted
        };
        // A redeclared or overloaded surface name binds its term under its
        // surface key, not the term's internal name: fall back to a scan.
        self.symbols.get(name).is_some_and(binds) || self.symbols.values().any(binds)
    }

    /// Whether `sort`, as written, is a `(Map K V)`: directly, through a
    /// monomorphic `define-sort` synonym, or through a parametric one whose
    /// body is a map once its parameters are bound. Elaboration erases a map
    /// sort to its value array, so only the written sort tells
    /// `((as const (Map K V)) v)` from a constant array. Called on a sort that
    /// already elaborated, so synonyms are acyclic.
    pub(in crate::elaborate) fn parsed_sort_is_map(&self, sort: &command::Sort) -> bool {
        self.parsed_sort_is_map_in(sort, &HashMap::default())
    }

    fn parsed_sort_is_map_in(&self, sort: &command::Sort, bound: &HashMap<&str, bool>) -> bool {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match sort {
            // Elaboration matches `Map` before any synonym, so it is the map sort.
            command::Sort::Parameterized(name, _) if name == "Map" => true,
            command::Sort::Simple(name) => bound
                .get(name.as_str())
                .copied()
                .unwrap_or_else(|| self.map_sort_synonyms.contains(name)),
            command::Sort::Parameterized(name, arguments) => {
                let Some((parameters, body)) = self.parametric_sort_defs.get(name) else {
                    return false;
                };
                let inner: HashMap<&str, bool> = parameters
                    .iter()
                    .map(String::as_str)
                    .zip(
                        arguments
                            .iter()
                            .map(|argument| self.parsed_sort_is_map_in(argument, bound)),
                    )
                    .collect();
                self.parsed_sort_is_map_in(body, &inner)
            }
            command::Sort::Indexed(_, _) => false,
        })
    }

    /// Record whether the monomorphic synonym `name` now names a map sort.
    pub(in crate::elaborate) fn record_sort_synonym(&mut self, name: &str, body: &command::Sort) {
        if self.parsed_sort_is_map(body) {
            self.map_sort_synonyms.insert(name.to_string());
        } else {
            self.map_sort_synonyms.remove(name);
        }
    }

    /// Forget a monomorphic synonym its scope popped.
    pub(in crate::elaborate) fn forget_sort_synonym(&mut self, name: &str) {
        self.map_sort_synonyms.remove(name);
    }
}
