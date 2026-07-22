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
use ay_core::kani_compat::DetHashSet as HashSet;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::UfMapLiaSolver;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use ay_core::term::{Symbol, TermData, TermId};
use ay_core::Sort;
use ay_map::{OP_DOM, OP_SUBSET, OUT_OF_FRAGMENT_OPS};

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
        // Discover subset atoms, domain reads, and value reads.
        let mut subset_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        // (map, key, contains_term) for `(select (map.dom map) key)`.
        let mut dom_reads: Vec<(TermId, TermId, TermId)> = Vec::new();
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
                        if let Some(map) = self.dom_carrier_map(array) {
                            // contains_key(map, key) = (select (map.dom map) key).
                            dom_reads.push((map, key, term));
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

    /// The map argument of a domain carrier `(map.dom m)`, if `array` is one.
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
