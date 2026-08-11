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
//!   remove -> `store(dom m') k' false`, var -> a REGISTERED domain-carrier
//!   constant, never an application, so `(get-model)` publishes the domain and
//!   the model gate can evaluate a membership read — see
//!   [`Context::map_domain_carrier`], which also explains the `ite` chain that
//!   keeps `m = n ⇒ dom(m) = dom(n)` once the application is gone).
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

use super::super::{Context, ElaborateError, PublicSort, Result, SymbolInfo};

/// Registered name of a map's PUBLISHED domain carrier: the constant a
/// `(get-model)` witness prints so the model pins `map.dom` / `map.contains_key`.
const DOMAIN_CARRIER_PREFIX: &str = "__ay_map_dom!";

/// Registered name of the free array behind a domain carrier. Suppressed from
/// `(get-model)`: it is an encoding artifact, and the carrier above already
/// prints the domain it stands for.
const DOMAIN_FREE_PREFIX: &str = "__ay_map_dom_free!";

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
            // Variable / opaque map: the published domain carrier.
            _ => self.map_domain_carrier(map),
        }
    }

    /// The domain carrier of an opaque map term: a REGISTERED array constant,
    /// not an application, so a `sat` witness actually pins the domain.
    ///
    /// ## The defect this closes
    ///
    /// `(map.dom m)` used to be emitted as an application. `(get-model)` prints
    /// `define-fun` entries for declared symbols, so a `(Map K V)` witness
    /// published only its value array — the domain appeared nowhere — and the
    /// independent model gate, asked to evaluate `(select (map.dom m) k)`,
    /// correctly refused: *"model commits no value for this application of
    /// `map.dom`"*. Every domain-touching `sat` was therefore published as
    /// `unknown`; measured at HEAD, `(assert (map.contains_key m 5))` alone was
    /// `unknown`, as was the `subset_consistent_with_witness_is_sat` test. That
    /// is the "solver right, MODEL absent, gate correctly refuses" class, so the
    /// fix belongs in the witness and never in the gate.
    ///
    /// The limitation is not map-specific: `(select (f m) k)` for a declared
    /// `f : (Array Int Int) -> (Array Int Bool)` is `unknown` in QF_AUFLIA for
    /// exactly the same reason. The map lane sidesteps it by not needing an
    /// array-returning application at all — a registered constant is an ordinary
    /// model leaf, which both the printer and the gate's evaluator handle.
    ///
    /// ## Why a bare fresh constant would be WRONG
    ///
    /// Carrying `dom` as an application bought EUF congruence for free:
    /// `m = n ⇒ dom(m) = dom(n)`. That is load-bearing, because `(= m n)` at Map
    /// sort is value-carrier equality, and
    ///
    /// ```smt2
    /// (assert (= m n)) (assert (map.contains_key m 1))
    /// (assert (not (map.contains_key n 1)))
    /// ```
    ///
    /// is `unsat` at HEAD *because* of it. Independent carriers alone make that
    /// `sat` — a wrong answer bought with a better-looking model. So the carrier
    /// is not a bare constant but that congruence, spelled out structurally: an
    /// `ite` chain testing `m` against every map that already owns a carrier,
    ///
    /// ```smt2
    /// (ite (= m m1) c1 (ite (= m m2) c2 ... free))
    /// ```
    ///
    /// which resolves to the carrier of the FIRST map `m` equals, and to its own
    /// free array otherwise. Each chain is built once and registered, so a later
    /// map extends the relation by testing against the earlier ones rather than
    /// by rewriting their chains — every pair is still covered, from the later
    /// side. Equal maps therefore pick the same first match and share a carrier,
    /// while distinct maps stay independent: congruence, no over-constraint.
    ///
    /// Doing this structurally rather than as injected axioms is what keeps it
    /// honest. `has_map_ops` fires only on `map.`-prefixed APPLICATION symbols,
    /// so once these projections are gone a `contains_key`-only query no longer
    /// routes to QF_MAPLIA — an axiom injected by the map theory solver would
    /// simply not run, and the wrong `sat` above would escape. The `ite` chain is
    /// part of the term, so it binds under every logic and every solver, and the
    /// gate can check it: it is `ite`, array equality, and constants.
    fn map_domain_carrier(&mut self, map: TermId) -> TermId {
        let key_sort = self.map_key_sort(map);
        let dom_sort = Sort::array(key_sort, Sort::Bool);

        // A user `(declare-fun map.dom ((Array K V)) (Array K Bool))` is the
        // documented activation route for the native map solver, and it makes
        // `(map.dom m)` a symbol with the USER's meaning. Leave that spelling
        // untouched — giving the direct application and the `contains_key`
        // reduction different carriers would let them disagree.
        if self.has_symbol_binding("map.dom") {
            return self
                .terms
                .mk_app(Symbol::named("map.dom"), vec![map], dom_sort);
        }

        let carrier_name = Self::domain_carrier_name(DOMAIN_CARRIER_PREFIX, &self.terms, map);
        // One carrier per map term, for every occurrence: the chain below grows
        // as later maps appear, so rebuilding it would hand two occurrences of
        // `(map.dom m)` two unrelated domains.
        if let Some(existing) = self.symbols.get(&carrier_name).and_then(|info| info.term) {
            return existing;
        }

        // The free array this map falls back to when it equals no earlier map.
        // Registered so the model pins it (the chain reads through it), and
        // suppressed from `(get-model)` because the carrier prints the domain.
        let free_name = Self::domain_carrier_name(DOMAIN_FREE_PREFIX, &self.terms, map);
        let free = self
            .terms
            .mk_fresh_named_var(free_name.clone(), dom_sort.clone());
        self.register_domain_symbol(free_name.clone(), free, &dom_sort);
        self.internal_symbols.insert(free_name);

        // Earlier carriers, oldest first, restricted to maps of the SAME sort —
        // `(= m n)` is well-sorted only then, so any other pair is congruence
        // that can never fire.
        let map_sort = self.terms.sort(map).clone();
        let mut earlier: Vec<(TermId, TermId)> = self
            .symbols
            .iter()
            .filter_map(|(name, info)| {
                let suffix = name.strip_prefix(DOMAIN_CARRIER_PREFIX)?;
                let id: u32 = suffix.rsplit_once('!')?.1.parse().ok()?;
                let earlier_map = TermId(id);
                (*self.terms.sort(earlier_map) == map_sort)
                    .then(|| info.term.map(|carrier| (earlier_map, carrier)))?
            })
            .collect();
        earlier.sort_unstable();

        // Fold from the back so the FIRST (oldest) match wins: equal maps agree
        // on which one that is, which is what makes the relation transitive.
        let mut carrier = free;
        for (earlier_map, earlier_carrier) in earlier.into_iter().rev() {
            let same_map = self.terms.mk_eq(map, earlier_map);
            carrier = self.terms.mk_ite(same_map, earlier_carrier, carrier);
        }

        self.register_domain_symbol(carrier_name, carrier, &dom_sort);
        carrier
    }

    /// Register one solver-minted domain symbol as a nullary constant, so it is
    /// collected as a solvable variable, resolves in `get-value`, and is
    /// published by `(get-model)` unless separately suppressed.
    fn register_domain_symbol(&mut self, name: String, term: TermId, sort: &Sort) {
        self.track_scoped_symbol(&name);
        self.symbols.insert(
            name,
            SymbolInfo::fresh(
                Some(term),
                sort.clone(),
                vec![],
                PublicSort::from_engine(sort),
                vec![],
                None,
                super::super::DeclarationKind::SolverInternal,
            ),
        );
    }

    /// Name of a minted domain symbol for `map`: `<prefix><label>!<term id>`.
    ///
    /// The `__ay_` prefix is rejected by `is_reserved_symbol`, so no user
    /// declaration can occupy one of these or be clobbered by one. The term id
    /// is always the LAST `!`-separated segment, because the congruence chain
    /// recovers the map it belongs to by parsing it back — a name that omitted
    /// it made every non-`Var` map (an `ite` over two maps, say) invisible to
    /// later chains, and `(map.contains_key (ite c m n) 1)` with `c` true and
    /// `(not (map.contains_key m 1))` answered `sat` instead of `unsat`. The
    /// id also keeps two declarations of one surface name — distinct `Var`s
    /// sharing that name — from sharing a domain. The label rides along so the
    /// published witness reads as the domain OF something.
    fn domain_carrier_name(prefix: &str, terms: &ay_core::TermStore, map: TermId) -> String {
        match terms.get(map) {
            TermData::Var(name, _) => format!("{prefix}{name}!{}", map.0),
            _ => format!("{prefix}term!{}", map.0),
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
