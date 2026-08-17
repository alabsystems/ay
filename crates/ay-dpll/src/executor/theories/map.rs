// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native finite-map theory solving (QF_MAP / QF_MAPLIA).
//!
//! Maps are modelled on the value carrier `Map(K, V) = Array(K → V)` plus the
//! domain carrier `dom = (map.dom m) : Array(K → Bool)`. The array solver
//! decides both carriers (`select`/`store` read-through) and map equality
//! (extensionality); the native [`ay_map::MapSolver`] adds subset reflexivity
//! reasoning; LIA decides any integer arithmetic over Int-valued value reads.
//!
//! ## Subset-axiom injection (the set.card / multiset.count pattern)
//!
//! Because a `TheorySolver` only holds an immutable `&TermStore` during
//! `check()`, the ground subset↔key obligations are injected here (where
//! `&mut TermStore` is available) before solving, exactly as `set.card` /
//! `multiset.count` axioms are injected for QF_SETLIA / QF_MSLIA:
//!
//! - `subset(m, n) ⇒ (contains_key(m, k) ⇒ contains_key(n, k))` and
//! - `subset(m, n) ⇒ (contains_key(m, k) ⇒ get(m, k) = get(n, k))`
//!
//! for every present `map.subset` atom and every ground key `k` whose domain /
//! value reads are present for both operands (sound *implications* restricted to
//! present witnesses — never asserts subset positively).
//!
//! The get/dom read-through equations (`get(insert(m,k,v),k)=v`,
//! `dom(insert(m,k,v))[k]=true`, `dom(remove(m,k))[k]=false`,
//! `dom(empty)=const-false`) are decided directly by the array solver via
//! `store`/const-array read-through — the frontend pushes the readers through
//! the constructors, so no separate axiom is needed for them.
//!
//! ## Fail-closed contract
//!
//! Out-of-fragment map operators (polymorphic / higher-order image:
//! `map.values`, `map.entries`, `map.filter_keys`, `map.fold`,
//! `map.comprehension`, `map.map_values`, `map.choose`) are **not** decided.
//! Their presence yields `Unknown` (incomplete) rather than a guessed SAT/UNSAT
//! verdict.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::UfMapLiaSolver;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use ay_core::term::{Symbol, TermData, TermId};
use ay_core::Sort;
use ay_map::{OP_DOM, OP_SUBSET, OUT_OF_FRAGMENT_OPS};

/// Registered-name prefixes of a published map domain carrier and of the free
/// array behind it. Must match the minting site in `ay-frontend`'s
/// `elaborate/app/map.rs`.
const MAP_DOMAIN_CARRIER_PREFIX: &str = "__ay_map_dom!";
const MAP_DOMAIN_FREE_PREFIX: &str = "__ay_map_dom_free!";

impl Executor {
    /// Solve the native map theory (QF_MAP / QF_MAPLIA).
    ///
    /// Injects ground subset↔key axioms, then solves with [`UfMapLiaSolver`].
    /// Returns `Unknown` (fail-closed) when any out-of-fragment map operator is
    /// present.
    pub(in crate::executor) fn solve_map_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Fail-closed guard: out-of-fragment map operators are not decided.
        if self.assertions_contain_out_of_fragment_map_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Inject ground subset↔key axioms (subset -> dom/get implications).
        let subset_axioms = self.collect_map_subset_axioms();
        if !subset_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                subset_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Map value/domain carriers are arrays; close any finite-index
        // equalities exposed by the route-local subset axioms before solving.
        let _ = self.add_finite_index_array_closure();

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        solve_incremental_split_loop_pipeline!(self,
            tag: "MapLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: UfMapLiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, array_model, lia_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    array: Some(array_model),
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |_theory| {
                let (lc, hc) = _theory.take_learned_state();
                let ds = _theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                    || solve_deadline.expired()
            }
        )
    }

    /// Solve QF_MAP / QF_MAPLIA with check-sat-assuming.
    ///
    /// Mirrors [`solve_map_lia`](Self::solve_map_lia) but temporarily adds
    /// assumptions to the assertion set under an isolated incremental scope.
    pub(in crate::executor) fn solve_map_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result =
            self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_map_lia);

        match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    /// Whether any assertion references an out-of-fragment map operator.
    ///
    /// These polymorphic / higher-order image operators fall outside the sound
    /// saturatable fragment; their presence forces a fail-closed `Unknown`.
    fn assertions_contain_out_of_fragment_map_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if OUT_OF_FRAGMENT_OPS.contains(&name.as_str()) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// Collect ground subset↔key axioms for the map theory.
    ///
    /// For every present `map.subset(m, n)` atom and every ground key `k` whose
    /// domain reads (`(select (map.dom m) k)` / `(select (map.dom n) k)`) are
    /// present for both operands, inject:
    ///
    /// - `subset(m, n) ⇒ (contains_key(m, k) ⇒ contains_key(n, k))`
    /// - `subset(m, n) ⇒ (contains_key(m, k) ⇒ get(m, k) = get(n, k))`
    ///   (only when value reads `(select m k)` / `(select n k)` are present for
    ///   both operands).
    ///
    /// Sound implications restricted to present witnesses — never asserts subset
    /// positively, never quantifies over an unbounded key domain.
    fn collect_map_subset_axioms(&mut self) -> Vec<TermId> {
        // Every array term that is part of some map's published domain, mapped
        // to that map. The frontend no longer emits `(map.dom m)` as an
        // application — it publishes a REGISTERED CONSTANT so a `sat` witness
        // pins the domain (see `elaborate/app/map.rs`) — so a domain read is not
        // recognisable from its shape any more, and this table is the only link
        // back. Without it the obligations below found no `contains_key` reads
        // and `subset(m,n) ∧ contains_key(m,k) ∧ ¬contains_key(n,k)` regressed
        // from `unsat` to `unknown`.
        let (carrier_of, domain_arrays) = self.map_domain_carriers();

        // Discover subset atoms, domain reads, and value reads.
        let mut subset_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        // (map, key, walked select) whose `contains_key` read is present.
        let mut dom_read_keys: Vec<(TermId, TermId, TermId)> = Vec::new();
        // (map, key, get_term) for `(select map key)` over a value carrier.
        let mut value_reads: Vec<(TermId, TermId, TermId)> = Vec::new();

        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == OP_SUBSET && args.len() == 2 {
                        subset_atoms.push((term, args[0], args[1]));
                    } else if name == "select" && args.len() == 2 {
                        let array = args[0];
                        let key = args[1];
                        if let Some(map) = domain_arrays
                            .get(&array)
                            .copied()
                            .or_else(|| self.dom_carrier_map(array))
                        {
                            dom_read_keys.push((map, key, term));
                        } else if self.is_value_carrier(array) {
                            // get(map, key) = (select map key).
                            value_reads.push((array, key, term));
                        }
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }

        if subset_atoms.is_empty() {
            return Vec::new();
        }

        // Rebuild `contains_key(map, key)` from the map's carrier rather than
        // reusing the `select` the walk happened to land on. A carrier can be an
        // `ite` chain (the domain-congruence encoding), and `mk_select` lifts a
        // select through an `ite` — so the walk sees the BRANCH reads,
        // `(select free_n k)` and `(select carrier_m k)`, and never the whole
        // membership term. Reconstructing through `mk_select` is hash-consed to
        // the exact term the frontend built for `(map.contains_key map key)`,
        // branches and all; pairing an obligation with a bare branch instead
        // would constrain the wrong array.
        let mut dom_reads: Vec<(TermId, TermId, TermId)> = Vec::new();
        dom_read_keys.sort_unstable();
        dom_read_keys.dedup();
        for (map, key, walked) in dom_read_keys {
            // A user-declared `map.dom` keeps the application shape, which the
            // walk already landed on whole: use it unchanged.
            let contains = match carrier_of.get(&map) {
                Some(&carrier) => self.ctx.terms.mk_select(carrier, key),
                None => walked,
            };
            dom_reads.push((map, key, contains));
        }

        let mut axioms = Vec::new();
        for (subset_atom, sub, sup) in &subset_atoms {
            // Range over present keys with domain reads on BOTH operands.
            for (m, k, contains_m) in &dom_reads {
                if *m != *sub {
                    continue;
                }
                let Some(contains_n) = dom_reads
                    .iter()
                    .find(|(n, k2, _)| *n == *sup && *k2 == *k)
                    .map(|(_, _, c)| *c)
                else {
                    continue;
                };

                // subset(m,n) => (contains_key(m,k) => contains_key(n,k)).
                let dom_impl = self.ctx.terms.mk_implies(*contains_m, contains_n);
                let ax1 = self.ctx.terms.mk_implies(*subset_atom, dom_impl);
                axioms.push(ax1);

                // subset(m,n) => (contains_key(m,k) => get(m,k) = get(n,k))
                // when value reads are present for both operands at this key.
                let get_m = value_reads
                    .iter()
                    .find(|(vm, vk, _)| *vm == *sub && *vk == *k)
                    .map(|(_, _, g)| *g);
                let get_n = value_reads
                    .iter()
                    .find(|(vn, vk, _)| *vn == *sup && *vk == *k)
                    .map(|(_, _, g)| *g);
                if let (Some(gm), Some(gn)) = (get_m, get_n) {
                    let val_eq = self.ctx.terms.mk_eq(gm, gn);
                    let val_impl = self.ctx.terms.mk_implies(*contains_m, val_eq);
                    let ax2 = self.ctx.terms.mk_implies(*subset_atom, val_impl);
                    axioms.push(ax2);
                }
            }
        }

        axioms
    }

    /// The published map domain carriers, as `(map -> carrier, domain array ->
    /// map)`.
    ///
    /// The frontend registers each carrier under `__ay_map_dom!<label>!<map term
    /// id>` and the free array behind it under `__ay_map_dom_free!<label>!<map
    /// term id>` (see `elaborate/app/map.rs`); those names are the only
    /// surviving link once the `(map.dom m)` application is gone. The `__ay_`
    /// prefix is rejected for user declarations, so every name matched here was
    /// minted by that code, and the map's term id is always the last `!`
    /// segment.
    ///
    /// The second map covers the free arrays as well as the carriers, because a
    /// carrier that is an `ite` chain never appears under a `select` — the
    /// select is lifted into the branches, and the branch a read lands on may be
    /// the free array. Recognising it is what tells us which map that read
    /// belongs to.
    fn map_domain_carriers(&self) -> (HashMap<TermId, TermId>, HashMap<TermId, TermId>) {
        let mut carrier_of = HashMap::default();
        let mut domain_arrays = HashMap::default();
        for (name, info) in self.ctx.symbol_iter() {
            let Some(term) = info.term else {
                continue;
            };
            let carrier = if let Some(suffix) = name.strip_prefix(MAP_DOMAIN_CARRIER_PREFIX) {
                Some((suffix, true))
            } else {
                name.strip_prefix(MAP_DOMAIN_FREE_PREFIX)
                    .map(|suffix| (suffix, false))
            };
            let Some((suffix, is_carrier)) = carrier else {
                continue;
            };
            let Some(id) = suffix.rsplit_once('!').and_then(|(_, id)| id.parse().ok()) else {
                continue;
            };
            let map = TermId(id);
            if is_carrier {
                carrier_of.insert(map, term);
            }
            domain_arrays.insert(term, map);
        }
        (carrier_of, domain_arrays)
    }

    /// The map argument of a domain carrier `(map.dom m)`, if `array` is one.
    ///
    /// Only a USER-declared `map.dom` still takes this shape; the builtin
    /// projection is published as a constant and resolved through
    /// [`Self::map_domain_carriers`].
    fn dom_carrier_map(&self, array: TermId) -> Option<TermId> {
        match self.ctx.terms.get(array) {
            TermData::App(Symbol::Named(name), args) if name == OP_DOM && args.len() == 1 => {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// Whether `term` is a Map value carrier, i.e. an `Array(_ → V)` whose
    /// element sort is not Bool. (A Bool element sort is the domain carrier.)
    fn is_value_carrier(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.sort(term), Sort::Array(arr) if !matches!(arr.element_sort, Sort::Bool))
    }
}
