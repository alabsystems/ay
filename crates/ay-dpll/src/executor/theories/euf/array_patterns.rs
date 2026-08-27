// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array extensionality and store-base decomposition axiom generation.
//!
//! Congruence axioms are in `array_congruence`. ROW/ROW2b axioms are in `array_row`.

use super::super::super::Executor;
use super::super::{
    array_extensionality_witness, deep_array_extensionality_witness, ArrayExtWitnessBinding,
};
use super::pigeonhole_core::EnumDiseqEdges;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId};

const SINGLETON_CLOSURE_RESOURCE_POLL_INTERVAL: usize = 1024;

pub(in crate::executor) mod finite_array_closure;

/// Whether singleton-sort closure finished emitting its complete spanning set.
///
/// Callers must not dispatch a solver after `Aborted`: equalities emitted before
/// the resource checkpoint are sound, but they may be only a prefix of the
/// closure required for EUF congruence completeness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[must_use]
pub(in crate::executor) enum SingletonSortClosureStatus {
    Complete,
    Aborted,
}

impl SingletonSortClosureStatus {
    #[must_use]
    pub(in crate::executor) const fn is_complete(self) -> bool {
        matches!(self, Self::Complete)
    }
}

/// Boolean polarity of a sub-term occurrence, for soundly deciding whether a
/// pointwise-forall holds as a PREMISE. `Positive` = under an even number of
/// negations / conjunctive-premise position; `Negative` = under an odd number;
/// `Unknown` = under a polarity-mixing operator (`=`/`distinct`/`xor`/ite
/// condition) where the occurrence is effectively at both polarities. `Unknown`
/// is absorbing: flipping it stays `Unknown`, so nothing beneath a mixing
/// operator is ever treated as a positive premise.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Polarity {
    Positive,
    Negative,
    Unknown,
}

impl Polarity {
    fn flip(self) -> Polarity {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Unknown => Polarity::Unknown,
        }
    }
}

impl Executor {
    /// Sound under-approximation of "this sort has exactly one inhabitant",
    /// resolving `Uninterpreted(name)` references against declared datatypes.
    ///
    /// Returns `true` ONLY when provably a singleton; returns `false` whenever
    /// the cardinality is > 1, infinite, or cannot be determined (genuinely
    /// uninterpreted sorts, recursive datatypes). This conservatism keeps the
    /// caller sound: it asserts a forced array equality only on a `true` result.
    ///
    /// - `Array(_, elem)`: singleton iff `elem` is a singleton (the only
    ///   function into a singleton codomain is the constant function).
    /// - `Uninterpreted(name)` naming a declared datatype: singleton iff that
    ///   datatype has exactly one constructor whose field sorts are ALL
    ///   singletons (recursively). A recursive datatype is treated as
    ///   non-singleton (fail closed).
    /// - Everything else (Bool, Int, Real, BitVec, String, RegLan, genuinely
    ///   uninterpreted sorts): `false`.
    pub(in crate::executor) fn sort_cardinality_is_one(&self, sort: &Sort) -> bool {
        self.sort_cardinality_is_one_inner(sort, &mut Vec::new())
    }

    fn sort_cardinality_is_one_inner(&self, sort: &Sort, in_progress: &mut Vec<String>) -> bool {
        match sort {
            Sort::FiniteDomain(_, size) => *size == 1,
            Sort::Array(arr) => self.sort_cardinality_is_one_inner(&arr.element_sort, in_progress),
            Sort::Datatype(dt) => self.datatype_constructors_card_one(
                &dt.name,
                || {
                    if dt.constructors.len() == 1 {
                        Some(
                            dt.constructors[0]
                                .fields
                                .iter()
                                .map(|f| f.sort.clone())
                                .collect(),
                        )
                    } else {
                        None
                    }
                },
                in_progress,
            ),
            Sort::Uninterpreted(name) => {
                // Resolve against the declared-datatype registry. A name that is
                // not a declared datatype is genuinely uninterpreted: cardinality
                // is unknown (could be >= 2), so it is NOT a provable singleton.
                let ctors: Vec<&str> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt_name, _)| dt_name == name)
                    .map(|(_, ctors)| ctors.iter().map(String::as_str).collect())
                    .unwrap_or_default();
                if ctors.len() != 1 {
                    return false;
                }
                let ctor = ctors[0].to_string();
                self.datatype_constructors_card_one(
                    name,
                    || {
                        // `ctor` IS the datatype's single constructor (from
                        // datatype_iter). A NULLARY constructor has no selectors, so
                        // `constructor_selector_info` returns `None` — that means
                        // ZERO fields (an empty product = cardinality 1), NOT
                        // "unknown". Treating `None` as unknown wrongly classified a
                        // singleton enum like `D8 = {c9}` as non-singleton, so
                        // `(Array Int D8)` array equalities / store no-ops were
                        // missed (wrong-sat). Default to empty fields.
                        Some(
                            self.ctx
                                .constructor_selector_info(&ctor)
                                .map(|fields| {
                                    fields.iter().map(|(_, s)| s.clone()).collect::<Vec<Sort>>()
                                })
                                .unwrap_or_default(),
                        )
                    },
                    in_progress,
                )
            }
            _ => false,
        }
    }

    /// Shared singleton check for a datatype with exactly one constructor.
    /// `field_sorts` lazily produces the single constructor's field sorts (or
    /// `None` if the datatype does not have exactly one constructor). Guards
    /// against recursive datatypes via `in_progress`.
    fn datatype_constructors_card_one<F>(
        &self,
        dt_name: &str,
        field_sorts: F,
        in_progress: &mut Vec<String>,
    ) -> bool
    where
        F: FnOnce() -> Option<Vec<Sort>>,
    {
        if in_progress.iter().any(|n| n == dt_name) {
            return false; // recursive datatype: fail closed
        }
        let Some(fields) = field_sorts() else {
            return false;
        };
        in_progress.push(dt_name.to_string());
        let result = fields
            .iter()
            .all(|s| self.sort_cardinality_is_one_inner(s, in_progress));
        in_progress.pop();
        result
    }

    /// Upper bound on a sort cardinality we are willing to compute exactly. A
    /// finite-domain pigeonhole conflict needs at most `k + 1` pairwise-distinct
    /// terms in the assertions, and the bounded clique search caps the node count
    /// far below this; so any `k` at or above this bound can never be exceeded by
    /// a real clique and is treated as "effectively unbounded" (return `None`),
    /// which both prevents `usize` overflow in the product/power computations and
    /// keeps the pass cheap. Conservative: returning `None` only loses a
    /// (practically unreachable) conflict, never asserts a wrong bound.
    const FINITE_CARDINALITY_CAP: usize = 1 << 20;

    /// Sound EXACT cardinality of a PROVABLY-FINITE sort, for the finite-domain
    /// pigeonhole conflict. Returns `Some(n)` ONLY when the sort has exactly `n`
    /// inhabitants and `n < FINITE_CARDINALITY_CAP`; returns `None` whenever the
    /// sort is infinite, recursive, genuinely uninterpreted, or its cardinality
    /// cannot be proven finite (or would exceed the cap). This direction of
    /// conservatism is REQUIRED for soundness: the pigeonhole pass asserts `false`
    /// when a disequality clique EXCEEDS `k`, so `k` must never UNDER-estimate the
    /// true cardinality (an under-estimate would refute a satisfiable problem).
    /// `None` (skip) only costs completeness.
    ///
    /// Cardinality algebra:
    ///   - `Bool` = 2.
    ///   - `BitVec(w)` = `2^w` (capped).
    ///   - `Array(idx, elem)` = `|elem| ^ |idx|` (the function space; finite iff
    ///     both index and element sorts are finite).
    ///   - `Datatype` / `Uninterpreted`-naming-a-datatype = `sum over constructors
    ///     of (product over fields of |field sort|)` — an empty product (nullary
    ///     constructor) contributes 1. Recursive datatypes are caught by
    ///     `in_progress` and treated as infinite (`None`).
    ///   - Everything else (`Int`, `Real`, `String`, `RegLan`, `FloatingPoint`,
    ///     `Seq`, genuinely uninterpreted sorts) = `None` (infinite or
    ///     conservatively unknown — `FloatingPoint` is finite but large and never
    ///     needed here, so it is fail-closed).
    pub(in crate::executor) fn sort_finite_cardinality(&self, sort: &Sort) -> Option<usize> {
        self.sort_finite_cardinality_inner(sort, &mut Vec::new())
    }

    fn sort_finite_cardinality_inner(
        &self,
        sort: &Sort,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        match sort {
            Sort::Bool => Some(2),
            Sort::FiniteDomain(_, size) => {
                let size = usize::try_from(*size).ok()?;
                (size < Self::FINITE_CARDINALITY_CAP).then_some(size)
            }
            Sort::BitVec(bv) => {
                // 2^w, capped. Widths past the cap are "effectively unbounded".
                if (bv.width as usize) >= (Self::FINITE_CARDINALITY_CAP.trailing_zeros() as usize) {
                    return None;
                }
                Some(1usize << bv.width)
            }
            Sort::Array(arr) => {
                // |Array I E| = |E| ^ |I|, so the ELEMENT sort must be resolved
                // first. A one-element element sort collapses the whole array
                // sort to a single inhabitant no matter what the index sort is --
                // INCLUDING an infinite one.
                //
                // Resolving the index first and bailing on it (the previous
                // order) therefore reported `None` for a carrier that is not just
                // finite but a singleton. `(Array Int E)` with `|E| = 1` has
                // exactly one inhabitant, yet `Int` made the index lookup return
                // `None`, the caller fell through to the "large or unknown
                // carrier" arm, and AY ASSERTED `default(store(a,i,v)) =
                // default(a)` -- which is false on a singleton carrier, where the
                // store replaces the array's only element. Z3 5.0.0 refutes that
                // axiom standalone:
                //
                //   (declare-datatypes ((E 0)) (((C))))
                //   (declare-const i (Array Int E))
                //   (define-fun a () (Array (Array Int E) Int)
                //     ((as const (Array (Array Int E) Int)) 5))
                //   (assert (= (default (store a i 9)) (default a)))   => unsat
                //   (assert (= (default (store a i 9)) 9))
                //   (assert (= (default a) 5))                         => sat
                //
                // Reachable in QF_AUFDT with no quantifiers.
                let elem = self.sort_finite_cardinality_inner(&arr.element_sort, in_progress)?;
                if elem <= 1 {
                    // |E| = 1 => exactly one total function I -> E for any I.
                    // (|E| = 0 cannot occur: SMT-LIB sorts are non-empty.)
                    return Some(1);
                }
                // |E| >= 2 with an unknown-or-infinite index is unbounded, so the
                // `?` below is the correct bail.
                let idx = self.sort_finite_cardinality_inner(&arr.index_sort, in_progress)?;
                // Bail (None) on any overflow / cap breach.
                let mut acc: usize = 1;
                for _ in 0..idx {
                    acc = acc.checked_mul(elem)?;
                    if acc >= Self::FINITE_CARDINALITY_CAP {
                        return None;
                    }
                }
                Some(acc)
            }
            Sort::Datatype(dt) => {
                let ctor_field_sorts: Vec<Vec<Sort>> = dt
                    .constructors
                    .iter()
                    .map(|c| c.fields.iter().map(|f| f.sort.clone()).collect())
                    .collect();
                self.datatype_finite_cardinality(&dt.name, ctor_field_sorts, in_progress)
            }
            Sort::Uninterpreted(name) => {
                // Resolve against the declared-datatype registry. A name that is
                // not a declared datatype is genuinely uninterpreted: cardinality
                // is unknown (could be infinite), so `None`.
                let ctors: Vec<String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt_name, _)| dt_name == name)
                    .map(|(_, cs)| cs.iter().map(String::clone).collect())
                    .unwrap_or_default();
                if ctors.is_empty() {
                    return None;
                }
                let ctor_field_sorts: Vec<Vec<Sort>> = ctors
                    .iter()
                    .map(|c| {
                        self.ctx
                            .constructor_selector_info(c)
                            .map(|fields| fields.iter().map(|(_, s)| s.clone()).collect())
                            .unwrap_or_default()
                    })
                    .collect();
                self.datatype_finite_cardinality(name, ctor_field_sorts, in_progress)
            }
            // Infinite, or conservatively unknown / never needed.
            _ => None,
        }
    }

    /// Exact cardinality of a datatype given the field sorts of each of its
    /// constructors: `sum_ctor (product_field |field sort|)`. Returns `None` if
    /// the datatype is recursive (caught by `in_progress`), has no constructors,
    /// any field sort is not provably finite, or the running total exceeds the
    /// cap. An empty constructor (nullary) contributes a product of 1.
    fn datatype_finite_cardinality(
        &self,
        dt_name: &str,
        ctor_field_sorts: Vec<Vec<Sort>>,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        if in_progress.iter().any(|n| n == dt_name) {
            return None; // recursive datatype: infinite, fail closed
        }
        if ctor_field_sorts.is_empty() {
            return None; // an empty (no-constructor) datatype is uninhabited/odd
        }
        in_progress.push(dt_name.to_string());
        let mut total: usize = 0;
        let mut ok = true;
        for fields in &ctor_field_sorts {
            // Product over this constructor's fields (empty product = 1).
            let mut prod: usize = 1;
            for fs in fields {
                let Some(c) = self.sort_finite_cardinality_inner(fs, in_progress) else {
                    ok = false;
                    break;
                };
                match prod.checked_mul(c) {
                    Some(p) if p < Self::FINITE_CARDINALITY_CAP => prod = p,
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                break;
            }
            match total.checked_add(prod) {
                Some(t) if t < Self::FINITE_CARDINALITY_CAP => total = t,
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        in_progress.pop();
        if ok {
            Some(total)
        } else {
            None
        }
    }

    /// Soundness pass: two const-arrays `(as const T) d1` and `(as const T) d2`
    /// with provably-distinct defaults `d1 != d2` are EXTENSIONALLY distinct
    /// (they differ at every index), so assert `(not (= c1 c2))` for each such
    /// pair reachable from the assertions.
    ///
    /// Without this, model-based theory combination can propose the interface
    /// equality `(= c1 c2)` (two const-arrays look equal under an incomplete
    /// array model) and the SAT solver may decide it true; the array theory then
    /// merges the two const-arrays into one equivalence class — directly, or
    /// transitively via store-over-const aliases it cannot refute (the folded
    /// const-array selects leave it without a witness) — and the distinct-default
    /// conflict fires a lemma that, combined with the forced interface
    /// equalities, yields a spurious UNSAT (a false theorem). Telling the solver
    /// up front that the const-arrays are distinct keeps that merge from ever
    /// happening. Sound: the disequality holds in every model. (#arr_lia561)
    pub(in crate::executor) fn add_distinct_const_array_disequalities(&mut self) {
        // (const-array term, default-value term), deduped by const-array term.
        let mut const_arrays: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            self.collect_const_array_terms(assertion, &mut const_arrays, &mut seen);
        }
        const_arrays.sort_unstable_by_key(|&(c, _)| c.0);
        const_arrays.dedup_by_key(|&mut (c, _)| c);
        // Bound the O(n^2) pairing on pathological inputs.
        const MAX_CONST_ARRAYS: usize = 64;
        if const_arrays.len() < 2 || const_arrays.len() > MAX_CONST_ARRAYS {
            return;
        }

        let mut diseqs: Vec<(TermId, TermId)> = Vec::new();
        for i in 0..const_arrays.len() {
            for j in (i + 1)..const_arrays.len() {
                let (ci, vi) = const_arrays[i];
                let (cj, vj) = const_arrays[j];
                // Same array sort (else they could never be equated anyway), and
                // provably-distinct default constants.
                if self.ctx.terms.sort(ci) == self.ctx.terms.sort(cj)
                    && self.are_terms_distinct_constants(vi, vj)
                {
                    diseqs.push((ci, cj));
                }
            }
        }
        for (ci, cj) in diseqs {
            let eq = self.ctx.terms.mk_eq(ci, cj);
            let neq = self.ctx.terms.mk_not(eq);
            self.push_array_axiom_assertion_site(neq, "distinct_const_array");
        }
    }

    /// Collect `(const-array d)` terms (with their default-value term `d`)
    /// reachable from `term`, recursing through all structure.
    fn collect_const_array_terms(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, TermId)>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                if sym.name() == "const-array" && args.len() == 1 {
                    out.push((term, args[0]));
                }
                for arg in args {
                    self.collect_const_array_terms(arg, out, seen);
                }
            }
            TermData::Not(inner) => self.collect_const_array_terms(inner, out, seen),
            TermData::Ite(c, t, e) => {
                self.collect_const_array_terms(c, out, seen);
                self.collect_const_array_terms(t, out, seen);
                self.collect_const_array_terms(e, out, seen);
            }
            _ => {}
        }
    }

    /// Soundness pass: ASSERT a linear spanning set of equalities between every
    /// GROUND term of each provably-singleton sort reachable from `roots`.
    ///
    /// A singleton sort has exactly one inhabitant, so every emitted equality
    /// holds in every model and removes no models. Emitting `n - 1` equalities
    /// from one representative (rather than all `n²` pairs) is sufficient for
    /// EUF congruence and keeps the pass linear after term discovery.
    ///
    /// This must collect terms regardless of their surrounding syntax. Looking
    /// only for existing equality atoms misses a singleton-sorted term used
    /// exclusively as a UF argument: `a` and `b` may be the only arrays of sort
    /// `(Array Int D1)`, with `D1 = {c}`, while `(distinct (f a) (f b))`
    /// requires `a = b` to reach the UF congruence conflict.
    ///
    /// CRITICAL: it ASSERTS the equality rather than REWRITING the atom to
    /// `true`. Rewriting would also delete the atom from any DEFINITIONAL role —
    /// e.g. the `(= sk c0)` enum-skolem-coverage fact that links a Skolem
    /// constant to the sole constructor — and the EUF core (which does not
    /// independently know the sort is a singleton) would then float the Skolem
    /// free, producing a spurious SAT (#bug10 regression). Asserting adds facts
    /// without removing any structure.
    ///
    /// Quantifier and let bodies are deliberately opaque. Their variables are
    /// locally scoped; hoisting an equality containing one into the ground
    /// assertion set would be invalid. Quantifier preprocessing may separately
    /// produce ground instances, which are ordinary roots and are covered.
    ///
    /// Sound: `sort_cardinality_is_one` is a conservative under-approximation,
    /// and an unknown/non-singleton sort emits nothing.
    pub(in crate::executor) fn add_ground_singleton_sort_equalities(
        &mut self,
        roots: &[TermId],
    ) -> SingletonSortClosureStatus {
        if self.should_abort_theory_loop() {
            return SingletonSortClosureStatus::Aborted;
        }

        let mut by_sort: HashMap<Sort, Vec<TermId>> = HashMap::default();
        let mut cardinality_cache: HashMap<Sort, bool> = HashMap::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        let mut work_since_poll = 0usize;

        while let Some(term) = stack.pop() {
            work_since_poll += 1;
            if work_since_poll >= SINGLETON_CLOSURE_RESOURCE_POLL_INTERVAL {
                work_since_poll = 0;
                if self.should_abort_theory_loop() {
                    return SingletonSortClosureStatus::Aborted;
                }
            }
            if !seen.insert(term) {
                continue;
            }

            let data = self.ctx.terms.get(term).clone();
            // Never lift a term whose meaning depends on a local binder.
            if matches!(
                data,
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..)
            ) {
                continue;
            }

            let sort = self.ctx.terms.sort(term).clone();
            let singleton = if let Some(&cached) = cardinality_cache.get(&sort) {
                cached
            } else {
                let proved = self.sort_cardinality_is_one(&sort);
                cardinality_cache.insert(sort.clone(), proved);
                proved
            };
            if singleton {
                by_sort.entry(sort).or_default().push(term);
            }

            match data {
                TermData::Const(_) | TermData::Var(..) => {}
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                    unreachable!("binder terms are filtered above")
                }
                TermData::App(_, args) => {
                    for arg in args.into_iter().rev() {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, t, e) => {
                    stack.push(e);
                    stack.push(t);
                    stack.push(c);
                }
                // `TermData` is non-exhaustive. Unknown future structure stays
                // opaque so this ground-only pass cannot cross a new binder.
                _ => {}
            }
        }

        let mut forced_equalities = Vec::new();
        work_since_poll = 0;
        for terms in by_sort.values_mut() {
            terms.sort_unstable_by_key(|term| term.0);
            if self.should_abort_theory_loop() {
                return SingletonSortClosureStatus::Aborted;
            }
            terms.dedup();
            if let Some((&representative, rest)) = terms.split_first() {
                for &other in rest {
                    work_since_poll += 1;
                    if work_since_poll >= SINGLETON_CLOSURE_RESOURCE_POLL_INTERVAL {
                        work_since_poll = 0;
                        if self.should_abort_theory_loop() {
                            return SingletonSortClosureStatus::Aborted;
                        }
                    }
                    if other != representative {
                        forced_equalities.push((representative, other));
                    }
                }
            }
        }
        if self.should_abort_theory_loop() {
            return SingletonSortClosureStatus::Aborted;
        }
        forced_equalities.sort_unstable_by_key(|&(lhs, rhs)| (lhs.0, rhs.0));
        if self.should_abort_theory_loop() {
            return SingletonSortClosureStatus::Aborted;
        }

        let mut already_present: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        already_present.extend(roots.iter().copied());
        work_since_poll = 0;
        for (lhs, rhs) in forced_equalities {
            work_since_poll += 1;
            if work_since_poll >= SINGLETON_CLOSURE_RESOURCE_POLL_INTERVAL {
                work_since_poll = 0;
                if self.should_abort_theory_loop() {
                    return SingletonSortClosureStatus::Aborted;
                }
            }
            // Keep the equality STRUCTURAL. `TermStore::mk_eq` soundly rewrites
            // `(= (store a i v) a)` to `(= (select a i) v)`, but that equivalent
            // atom no longer merges the original array terms in EUF. This pass
            // exists specifically to expose those congruence merges.
            let (lhs, rhs) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);
            if already_present.insert(eq) {
                self.push_array_axiom_assertion_site(eq, "singleton_sort_eq_fact");
            }
        }

        if self.should_abort_theory_loop() {
            SingletonSortClosureStatus::Aborted
        } else {
            SingletonSortClosureStatus::Complete
        }
    }

    /// Soundness pass (#qarr-ext-quant wrong-SAT): a universally-quantified
    /// pointwise array equality `(forall ((i S)) (= (select a i) (select b i)))`
    /// asserted as a TOP-LEVEL CONJUNCT forces `a = b` by array extensionality
    /// (two arrays equal at every index are equal). The bounded E-matching /
    /// MBQI quantifier path only instantiates `i` at ground indices already in
    /// the problem, so it can satisfy a finite set of pointwise constraints while
    /// leaving the extensionality witness forced by a sibling `(not (= a b))`
    /// uninstantiated — yielding a wrong SAT. Asserting the extensional `(= a b)`
    /// eagerly lets the ground array solver refute `a = b /\ a != b` directly.
    ///
    /// Also handles the guarded form
    /// `(forall ((i S)) (=> (distinct i c) (= (select a i) (select b i))))`
    /// when a TOP-LEVEL ground conjunct `(= (select a c) (select b c))` patches
    /// the excluded index `c`: the guard covers every `i != c` and the patch
    /// covers `i = c`, so `a` and `b` again agree at every index.
    ///
    /// SOUNDNESS — two distinct moves, each model-preserving:
    ///
    /// (1) Plain form `(forall ((i S)) (= (select a i) (select b i)))` is
    ///     LOGICALLY EQUIVALENT to `(= a b)` in every model (array extensionality
    ///     gives `⟹`, congruence gives `⟸`). So this forall sub-term is REWRITTEN
    ///     to `(= a b)` wherever it occurs (any polarity / position) via
    ///     `substitute_terms`. The forall is a closed term, so the replacement is
    ///     capture-free. This both refutes a sibling `(not (= a b))` (wrong SAT
    ///     fix) AND keeps the genuinely-SAT variant SAT (no quantifier remains to
    ///     trip the unsafe-binder gate — `a = b` is decided in the ground array
    ///     theory). Equisatisfiable, so it can never flip a verdict wrongly.
    ///
    /// (2) Guarded form `(forall ((i S)) (=> (distinct i c) (= (select a i)
    ///     (select b i))))` is NOT equivalent to `(= a b)` on its own (it permits
    ///     `a`, `b` to differ at `c`). Only when a TOP-LEVEL ground conjunct
    ///     `(= (select a c) (select b c))` also holds do `a`, `b` agree at every
    ///     index, forcing `a = b`. So `(= a b)` is ADDED as a CONSEQUENCE (the
    ///     forall is left in place) and ONLY when both the forall and the patch
    ///     are top-level conjunctive premises. Adding a logical consequence
    ///     removes no models.
    ///
    /// The guard `c` and the array operands must be binder-INDEPENDENT.
    ///
    /// IMPLEMENTATION NOTE — add-only, never rewrite the forall away. An earlier
    /// version REPLACED a matched plain pointwise forall with `(= a b)` via
    /// `substitute_terms`. That rewrite is logically equisatisfiable, but routing
    /// the residual problem (other foralls still present) fully through the ground
    /// array path exposed a latent array+quantifier unsoundness that returned
    /// wrong-UNSAT on multi-forall problems (qarr_gen3 seeds 76/133/193/441/555 —
    /// sound `unknown` on baseline became `unsat`). Instead we only ADD `(= a b)`
    /// as a logical CONSEQUENCE and keep the forall: a consequence holds in every
    /// model of its premise, so it can NEVER turn a SAT problem UNSAT. It still
    /// fixes the wrong-SAT target, because a sibling `(not (= a b))` makes
    /// `(= a b)` and its negation complementary literals — a propositional
    /// conflict the SAT layer refutes directly, no quantifier reasoning needed.
    pub(in crate::executor) fn add_quantified_array_extensionality_equalities(&mut self) {
        let assertions = self.ctx.assertions.clone();

        // Top-level conjunctive premises (the disequalities / patch the matchers
        // consult).
        let mut conjuncts: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &a in &assertions {
            self.collect_top_level_conjuncts(a, &mut conjuncts, &mut seen);
        }
        let conjunct_set: HashSet<TermId> = conjuncts.iter().copied().collect();

        // We collect TWO kinds of action, keyed by whether the extensional
        // equality `(= a b)` a forall forces is DIRECTLY contradicted by a
        // top-level `(not (= a b))` / `(distinct a b)`:
        //
        //  * CONTRADICTED -> the forall premise + that disequality are jointly
        //    UNSAT. REWRITE the forall to `(= a b)` so the contradiction becomes
        //    a GROUND pair of complementary literals the solver refutes (the
        //    quantifier path otherwise masks an added `false` / consequence). This
        //    rewrite is only taken when the problem is genuinely UNSAT, so even if
        //    it routes through the ground array path, `unsat` is the CORRECT
        //    answer — it can never manufacture a wrong-UNSAT on a SAT problem.
        //
        //  * NOT CONTRADICTED -> only ADD `(= a b)` as a logical CONSEQUENCE
        //    (extensionality), never rewriting the forall away. A consequence
        //    holds in every model of its premise, so it can never turn SAT into
        //    UNSAT; it merely lets model validation reject a bogus finite model
        //    (degrading a former wrong-SAT to a sound `unknown`). This is what
        //    keeps multi-forall SAT problems (e.g. `a2 = store(a1,4,v)` with only
        //    `a2 != a1` asserted — no direct clash) sound: an unconditional
        //    rewrite there exposed a latent array+quantifier unsoundness and
        //    returned wrong-UNSAT.
        let mut substitution: HashMap<TermId, TermId> = ay_core::kani_compat::det_hash_map_new();
        let mut consequences: Vec<TermId> = Vec::new();
        let mut added: HashSet<TermId> = HashSet::default();

        // (1) Plain pointwise foralls reachable in POSITIVE polarity.
        // `(forall i. a[i]=b[i])` is LOGICALLY EQUIVALENT to `(= a b)`
        // (extensionality + congruence). The downstream moves below treat such a
        // forall as a PREMISE — they either rewrite it to `(= a b)` or add `(= a
        // b)` as a top-level consequence. Both are sound ONLY when the forall is
        // asserted positively. Under an odd number of negations the assertion
        // really says `(not (= a b))` (the arrays DIFFER), so adding `(= a b)`
        // would manufacture a wrong UNSAT (ALIA `(not (forall i. b[i]=cc[i]))`,
        // genuinely SAT — z3 sat, ay was wrong-unsat). Collect only positive
        // occurrences; a negated pointwise forall is left for the normal
        // quantifier pipeline (Skolemized to a ground disequality → SAT).
        let mut rewrite: HashMap<TermId, TermId> = ay_core::kani_compat::det_hash_map_new();
        let mut seen_all: HashSet<(TermId, Polarity, bool)> = HashSet::default();
        for &a in &assertions {
            self.collect_plain_pointwise_foralls(a, true, &mut rewrite, &mut seen_all);
        }
        let mut plain: Vec<(TermId, TermId)> = rewrite.iter().map(|(&f, &e)| (f, e)).collect();
        plain.sort_unstable_by_key(|(f, _)| f.0);
        for (forall_term, eq) in plain {
            if self.array_equality_negation_asserted(eq, &conjunct_set) {
                substitution.insert(forall_term, eq);
            } else if conjunct_set.contains(&forall_term) && added.insert(eq) {
                // SOUNDNESS (#alia-quant-ext-polarity): only add `(= a b)` as a
                // free top-level CONSEQUENCE when the `forall i. a[i]=b[i]` is
                // itself asserted at positive top-level position (a top-level
                // conjunct). `collect_plain_pointwise_foralls` descends through
                // `not`/`or` without tracking polarity, so it also surfaces
                // foralls under negation — e.g. `(not (forall i. b[i]=cc[i]))`,
                // which is `(exists i. b[i]!=cc[i])` and is SAT for arbitrary
                // arrays. Forcing `(= b cc)` there fabricated a wrong-UNSAT. The
                // equivalence-preserving substitution above (genuine
                // biconditional) still applies at any polarity when the eq is
                // directly contradicted; this consequence add does not.
                consequences.push(eq);
            }
        }

        // (2) Guarded form `(forall i. i!=c => a[i]=b[i])` completed by a
        // top-level ground patch `(= (select a c) (select b c))`. Here
        // `F ∧ patch ⟺ (= a b)`, so a slot-replace of the forall (which keeps the
        // patch) is sound ONLY at a direct top-level conjunctive position. When
        // contradicted and the forall is a direct assertion, slot-replace it with
        // `(= a b)`; otherwise add the consequence.
        let mut forced: Vec<(TermId, TermId, TermId)> = Vec::new();
        for &conj in &conjuncts {
            if let Some((a, b)) = self.guarded_pointwise_array_eq_forces(conj, &conjunct_set) {
                forced.push((conj, a, b));
            }
        }
        forced.sort_unstable_by_key(|(c, _, _)| c.0);
        let mut slot_replacements: Vec<(TermId, TermId)> = Vec::new();
        for (forall_conj, a, b) in forced {
            if a == b {
                continue;
            }
            let eq = self.ctx.terms.mk_eq(a, b);
            let contradicted = self.array_equality_negation_asserted(eq, &conjunct_set);
            let is_direct = self.ctx.assertions.iter().any(|&x| x == forall_conj);
            if contradicted && is_direct {
                slot_replacements.push((forall_conj, eq));
            } else if added.insert(eq) {
                consequences.push(eq);
            }
        }

        // Apply the equivalence-preserving substitutions for contradicted plain
        // foralls (sound everywhere — genuine equivalence).
        if !substitution.is_empty() {
            let rewritten: Vec<TermId> = self
                .ctx
                .assertions
                .iter()
                .map(|&a| self.ctx.terms.substitute_terms(a, &substitution))
                .collect();
            self.ctx.assertions = rewritten;
        }
        // Slot-replace contradicted direct-assertion guarded foralls.
        for (forall_conj, eq) in slot_replacements {
            if let Some(slot) = self.ctx.assertions.iter().position(|&x| x == forall_conj) {
                self.ctx.assertions[slot] = eq;
            }
        }
        // Add the remaining (non-contradicted) extensional consequences.
        for eq in consequences {
            self.push_array_axiom_assertion_site(eq, "quantified_array_extensionality");
        }
    }

    /// True iff a top-level conjunct directly negates the equality `eq` (i.e.
    /// `(= a b)`): either `(not (= a b))` or `(distinct a b)` / `(distinct b a)`.
    /// Used to turn an extensional consequence into a ground UNSAT certificate.
    fn array_equality_negation_asserted(&self, eq: TermId, conjunct_set: &HashSet<TermId>) -> bool {
        let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(eq) else {
            return false;
        };
        if eq_sym.name() != "=" || eq_args.len() != 2 {
            return false;
        }
        let (a, b) = (eq_args[0], eq_args[1]);
        for &conj in conjunct_set {
            match self.ctx.terms.get(conj) {
                // `(not (= a b))` — the inner equality is hash-consed to `eq`.
                TermData::Not(inner) if *inner == eq => return true,
                // `(distinct a b)` / `(distinct b a)`.
                TermData::App(sym, args)
                    if sym.name() == "distinct"
                        && args.len() == 2
                        && ((args[0] == a && args[1] == b) || (args[0] == b && args[1] == a)) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// Walk the assertion DAG and record, for each `(forall ((i S)) (= (select a
    /// i) (select b i)))` sub-term encountered AT POSITIVE POLARITY, a
    /// `forall -> (= a b)` rewrite. Descends through all structure; does NOT
    /// descend into the matched forall's body (the rewrite replaces the whole
    /// forall).
    ///
    /// POLARITY + DISJUNCTION (#alia-arrayext-neg-polarity wrong-UNSAT AND
    /// #arrayext-or-positive-over-injection wrong-UNSAT): a pointwise forall is
    /// LOGICALLY EQUIVALENT to `(= a b)` ONLY as a fact it CONTRIBUTES. The caller
    /// uses each recorded forall in two ways — (i) ADD `(= a b)` as a consequence,
    /// or (ii) rewrite the forall slot to `(= a b)`. Move (i) is only sound when
    /// the forall holds as an ASSERTED PREMISE — i.e. it is a TOP-LEVEL CONJUNCT,
    /// reached from the assertion root through `and`/positive only and NEVER under
    /// a disjunction.
    ///
    /// Two unsoundness traps this guards against:
    ///   * NEGATIVE polarity: under a `not` the asserted fact is `¬(forall…)` ≡
    ///     `(a ≠ b)`, whose consequence is `(not (= a b))`, never `(= a b)` —
    ///     adding `(= a b)` there manufactures a wrong-UNSAT
    ///     (`(assert (not (forall i. b[i]=cc[i])))` is SAT, ay reported UNSAT).
    ///   * POSITIVE polarity but UNDER A DISJUNCTION: in `(or (forall i. a[i]=b[i])
    ///     p)` the forall is NNF-positive yet is NOT an asserted premise — the
    ///     disjunction may be satisfied by `p` alone with `a ≠ b`. Adding `(= a b)`
    ///     as a top-level fact there is unsound: with a sibling `(not (= (select a
    ///     k) (select b k)))` it forces `(select a k) = (select b k)` by congruence
    ///     → spurious UNSAT (z3=cvc5=sat). The `=>` consequent is the same trap
    ///     (`(=> A B) ≡ (or (not A) B)`), so `B` is treated as under a disjunction.
    ///
    /// We therefore only collect a forall encountered at POSITIVE polarity AND
    /// NOT under any disjunction (`pol == Positive && !under_disj`). Polarity flips
    /// on `Not` and on the antecedent of `=>`, and becomes UNKNOWN (collect nowhere
    /// beneath) under `=`/`distinct`/`xor`/`ite` branches that mix polarity. The
    /// `under_disj` flag latches `true` when descending into any `or` argument or
    /// the consequent of `=>`, and never clears. Restricting to positive
    /// top-level-conjunct occurrences is completeness-only: it never adds an
    /// unentailed fact. (The equivalence-preserving REWRITE path (ii) would be
    /// sound at any position, but gating collection wholesale is the safe
    /// over-approximation — it only forgoes a rewrite, never a verdict.)
    fn collect_plain_pointwise_foralls(
        &mut self,
        term: TermId,
        _positive: bool,
        rewrite: &mut HashMap<TermId, TermId>,
        seen: &mut HashSet<(TermId, Polarity, bool)>,
    ) {
        self.collect_plain_pointwise_foralls_pol(term, Polarity::Positive, false, rewrite, seen);
    }

    fn collect_plain_pointwise_foralls_pol(
        &mut self,
        term: TermId,
        pol: Polarity,
        under_disj: bool,
        rewrite: &mut HashMap<TermId, TermId>,
        seen: &mut HashSet<(TermId, Polarity, bool)>,
    ) {
        if !seen.insert((term, pol, under_disj)) {
            return;
        }
        if pol == Polarity::Positive && !under_disj {
            if let TermData::Forall(vars, body, _) = self.ctx.terms.get(term).clone() {
                if vars.len() == 1 {
                    let binder = vars[0].0.clone();
                    let bound = [binder.clone()];
                    if let Some((a, b)) = self.select_eq_at_binder(body, &binder, &bound) {
                        let eq = self.ctx.terms.mk_eq(a, b);
                        rewrite.insert(term, eq);
                        return;
                    }
                }
            }
        }
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => match sym.name() {
                // `and` preserves polarity AND the premise (conjunct) status, so a
                // forall directly under top-level `and` is still a premise.
                "and" => {
                    for arg in args {
                        self.collect_plain_pointwise_foralls_pol(
                            arg, pol, under_disj, rewrite, seen,
                        );
                    }
                }
                // `or` preserves polarity but DESTROYS premise status: a positive
                // forall under `or` is merely a disjunct, not an asserted fact.
                // Latch `under_disj`.
                "or" => {
                    for arg in args {
                        self.collect_plain_pointwise_foralls_pol(arg, pol, true, rewrite, seen);
                    }
                }
                // `(=> A B)`: the antecedent `A` is negated; the consequent `B`
                // keeps polarity but, since `(=> A B) ≡ (or (not A) B)`, `B` is
                // under a disjunction — it is not an asserted premise on its own.
                "=>" if args.len() == 2 => {
                    self.collect_plain_pointwise_foralls_pol(
                        args[0],
                        pol.flip(),
                        true,
                        rewrite,
                        seen,
                    );
                    self.collect_plain_pointwise_foralls_pol(args[1], pol, true, rewrite, seen);
                }
                // `=` / `distinct` / `xor` / atoms: Boolean operands sit at MIXED
                // (iff) polarity — neither premise nor negated-premise — so visit
                // at UNKNOWN. Unknown is absorbing (a `not` under it stays
                // unknown), so no sub-forall there is ever recorded as a positive
                // premise.
                _ => {
                    for arg in args {
                        self.collect_plain_pointwise_foralls_pol(
                            arg,
                            Polarity::Unknown,
                            under_disj,
                            rewrite,
                            seen,
                        );
                    }
                }
            },
            TermData::Not(inner) => self.collect_plain_pointwise_foralls_pol(
                inner,
                pol.flip(),
                under_disj,
                rewrite,
                seen,
            ),
            TermData::Ite(c, t, e) => {
                // The condition appears at both polarities (unknown); the branches
                // keep the parent polarity but are guarded by the condition, so they
                // are not unconditional premises — treat them as under a disjunction
                // (`(ite c t e) ≡ (or (and c t) (and (not c) e))`).
                self.collect_plain_pointwise_foralls_pol(
                    c,
                    Polarity::Unknown,
                    under_disj,
                    rewrite,
                    seen,
                );
                self.collect_plain_pointwise_foralls_pol(t, pol, true, rewrite, seen);
                self.collect_plain_pointwise_foralls_pol(e, pol, true, rewrite, seen);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    self.collect_plain_pointwise_foralls_pol(
                        v,
                        Polarity::Unknown,
                        under_disj,
                        rewrite,
                        seen,
                    );
                }
                self.collect_plain_pointwise_foralls_pol(b, pol, under_disj, rewrite, seen);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => {
                self.collect_plain_pointwise_foralls_pol(b, pol, under_disj, rewrite, seen);
            }
            _ => {}
        }
    }

    /// Collect the top-level conjuncts of `term` (descending only through
    /// positive `(and ...)`). Each assertion is itself a conjunct; an `(and ...)`
    /// contributes its arguments. Anything else (a forall, disjunction, equality,
    /// negation, ...) is a single conjunct and is NOT descended into — the goal
    /// is exactly the set of premises that must hold in every model.
    fn collect_top_level_conjuncts(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if sym.name() == "and" {
                let args = args.clone();
                for arg in args {
                    self.collect_top_level_conjuncts(arg, out, seen);
                }
                return;
            }
        }
        out.push(term);
    }

    /// If `conj` is a GUARDED pointwise forall `(forall ((i S)) (=> (distinct i
    /// c) (= (select a i) (select b i))))` (or `(=> (not (= i c)) ...)`) whose
    /// excluded index `c` is patched by a top-level ground conjunct
    /// `(= (select a c) (select b c))` present in `conjunct_set`, return the
    /// forced `(a, b)`. The plain unguarded form is handled separately by a
    /// term rewrite, not here. The array operands and guard constant must be
    /// binder-independent.
    fn guarded_pointwise_array_eq_forces(
        &self,
        conj: TermId,
        conjunct_set: &HashSet<TermId>,
    ) -> Option<(TermId, TermId)> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(conj).clone() else {
            return None;
        };
        if vars.len() != 1 {
            return None;
        }
        let binder = vars[0].0.clone();
        let bound = [binder.clone()];

        // The body is the NNF of `(=> (distinct i c) (= (select a i) (select b
        // i)))`, which the elaborator normalises to a disjunction
        //   `(or (= i c) (= (select a i) (select b i)))`
        // (since `(not (distinct i c))` ≡ `(= i c)`). Match exactly that shape:
        // one disjunct excludes a single binder-independent index `c` and the
        // other is the pointwise select equality. Both the explicit `(=> ...)`
        // form and the normalised `or` form are accepted.
        let (excluded_c, consequent) = self.split_guarded_body(body, &binder, &bound)?;
        let (a, b) = self.select_eq_at_binder(consequent, &binder, &bound)?;
        if self.ground_patch_present(a, b, excluded_c, conjunct_set) {
            return Some((a, b));
        }
        None
    }

    /// Decompose a guarded-pointwise forall body into `(excluded_index_c,
    /// consequent)`, where the forall says "for all `i` other than `c`, the
    /// consequent holds". Accepts:
    ///   - the explicit `(=> guard consequent)` form with `guard` = `(distinct i
    ///     c)` / `(not (= i c))`; and
    ///   - the elaborator-normalised `(or (= i c) consequent)` form
    ///     (NNF of the above, since `¬(distinct i c)` ≡ `(= i c)`).
    /// `c` must be binder-independent and the OTHER operand the bound variable.
    fn split_guarded_body(
        &self,
        body: TermId,
        binder: &str,
        bound: &[String],
    ) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(body) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        match sym.name() {
            "=>" => {
                let c = self.guard_excluded_index(args[0], binder, bound)?;
                Some((c, args[1]))
            }
            "or" => {
                // One disjunct is `(= i c)` (the excluded index); the other is the
                // consequent. Try both orders.
                if let Some(c) = self.binder_eq_const_index(args[0], binder, bound) {
                    return Some((c, args[1]));
                }
                if let Some(c) = self.binder_eq_const_index(args[1], binder, bound) {
                    return Some((c, args[0]));
                }
                None
            }
            _ => None,
        }
    }

    /// If `term` is a POSITIVE equality `(= i c)` / `(= c i)` with `i` the bound
    /// variable and `c` binder-independent, return `c`.
    fn binder_eq_const_index(
        &self,
        term: TermId,
        binder: &str,
        bound: &[String],
    ) -> Option<TermId> {
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if sym.name() == "=" && args.len() == 2 {
                return self.binder_vs_const(args[0], args[1], binder, bound);
            }
        }
        None
    }

    /// Match `(= (select X i) (select Y i))` where the index of BOTH selects is
    /// exactly the bound variable `binder` and the arrays `X`, `Y` are
    /// binder-independent terms of the same array sort. Returns `(X, Y)`.
    pub(in crate::executor) fn select_eq_at_binder(
        &self,
        term: TermId,
        binder: &str,
        bound: &[String],
    ) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (l, r) = (args[0], args[1]);
        let (xa, xi) = self.select_args(l)?;
        let (ya, yi) = self.select_args(r)?;
        // Both indices are exactly the bound variable.
        if !self.is_exactly_binder(xi, binder) || !self.is_exactly_binder(yi, binder) {
            return None;
        }
        // Array operands must NOT mention the binder (else `a`/`b` are not fixed
        // arrays and extensionality does not collapse to a single `a = b`).
        if self.term_mentions_binder(xa, bound) || self.term_mentions_binder(ya, bound) {
            return None;
        }
        if self.ctx.terms.sort(xa) != self.ctx.terms.sort(ya) {
            return None;
        }
        Some((xa, ya))
    }

    /// Return `(array, index)` if `term` is `(select array index)`.
    fn select_args(&self, term: TermId) -> Option<(TermId, TermId)> {
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if sym.name() == "select" && args.len() == 2 {
                return Some((args[0], args[1]));
            }
        }
        None
    }

    /// `true` iff `term` is exactly the bound variable named `binder`.
    fn is_exactly_binder(&self, term: TermId, binder: &str) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Var(n, _) if n == binder)
    }

    /// If `guard` excludes exactly one binder-independent index `c` — i.e. it is
    /// `(distinct i c)` / `(distinct c i)` / `(not (= i c))` / `(not (= c i))`
    /// with `i` the bound variable and `c` binder-independent — return `c`.
    fn guard_excluded_index(
        &self,
        guard: TermId,
        binder: &str,
        bound: &[String],
    ) -> Option<TermId> {
        // `(distinct i c)`
        if let TermData::App(sym, args) = self.ctx.terms.get(guard) {
            if sym.name() == "distinct" && args.len() == 2 {
                return self.binder_vs_const(args[0], args[1], binder, bound);
            }
        }
        // `(not (= i c))`
        if let TermData::Not(inner) = self.ctx.terms.get(guard) {
            if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                if sym.name() == "=" && args.len() == 2 {
                    return self.binder_vs_const(args[0], args[1], binder, bound);
                }
            }
        }
        None
    }

    /// Given the two operands of a (dis)equality, return the binder-independent
    /// one when the OTHER is exactly the bound variable.
    fn binder_vs_const(
        &self,
        x: TermId,
        y: TermId,
        binder: &str,
        bound: &[String],
    ) -> Option<TermId> {
        let x_is_binder = self.is_exactly_binder(x, binder);
        let y_is_binder = self.is_exactly_binder(y, binder);
        if x_is_binder && !y_is_binder && !self.term_mentions_binder(y, bound) {
            return Some(y);
        }
        if y_is_binder && !x_is_binder && !self.term_mentions_binder(x, bound) {
            return Some(x);
        }
        None
    }

    /// `true` if `term` structurally contains any of the `bound` variable names.
    /// Name-based / scope-insensitive: over-approximation only costs a missed
    /// rewrite (the pass declines), never soundness.
    fn term_mentions_binder(&self, term: TermId, bound: &[String]) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(name, _) if bound.iter().any(|b| b == name) => return true,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    /// `true` iff top-level ground conjuncts force `(select a c) = (select b c)`,
    /// patching the index `c` the guard excludes. Two shapes (both unconditional,
    /// so each is a genuine premise):
    ///   - DIRECT: `(= (select a c) (select b c))` (either operand order); or
    ///   - TRANSITIVE: `(= (select a c) K)` and `(= (select b c) K)` for a common
    ///     term `K` — then `(select a c) = K = (select b c)`.
    fn ground_patch_present(
        &self,
        a: TermId,
        b: TermId,
        c: TermId,
        conjunct_set: &HashSet<TermId>,
    ) -> bool {
        // Terms each select-at-`c` is equated to by a top-level conjunct.
        let mut eq_a: HashSet<TermId> = HashSet::default();
        let mut eq_b: HashSet<TermId> = HashSet::default();
        for &conj in conjunct_set {
            let TermData::App(sym, args) = self.ctx.terms.get(conj) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (l, r) = (args[0], args[1]);
            let l_sel = self.select_args(l);
            let r_sel = self.select_args(r);
            // DIRECT: both sides are selects at `c` over {a, b}.
            if let (Some((la, li)), Some((ra, ri))) = (l_sel, r_sel) {
                if li == c && ri == c && ((la == a && ra == b) || (la == b && ra == a)) {
                    return true;
                }
            }
            // TRANSITIVE collection: record what `(select a c)` / `(select b c)`
            // are equated to.
            if let Some((la, li)) = l_sel {
                if li == c {
                    if la == a {
                        eq_a.insert(r);
                    }
                    if la == b {
                        eq_b.insert(r);
                    }
                }
            }
            if let Some((ra, ri)) = r_sel {
                if ri == c {
                    if ra == a {
                        eq_a.insert(l);
                    }
                    if ra == b {
                        eq_b.insert(l);
                    }
                }
            }
        }
        // TRANSITIVE: `(select a c) = K` and `(select b c) = K` for a common `K`.
        eq_a.iter().any(|k| eq_b.contains(k))
    }

    /// Maximum number of constructors of an enum datatype whose array index
    /// domain is enumerated eagerly for finite-index extensionality.
    const FINITE_ENUM_INDEX_MAX_CTORS: usize = 16;

    /// When `sort` is an ALL-NULLARY (enum) datatype with `1..=CAP`
    /// constructors, return its constructor names — the complete (finite) set
    /// of inhabitants. Otherwise `None`. Used as an array index domain for exact
    /// finite-index extensionality (`add_finite_index_array_closure`).
    /// Resolves both the inline `Sort::Datatype` form and a bare
    /// `Sort::Uninterpreted(name)` against the declared-datatype registry.
    fn finite_enum_datatype_ctors(&self, sort: &Sort) -> Option<Vec<String>> {
        match sort {
            Sort::Datatype(dt) => {
                if dt.constructors.is_empty()
                    || dt.constructors.len() > Self::FINITE_ENUM_INDEX_MAX_CTORS
                    || !dt.constructors.iter().all(|c| c.fields.is_empty())
                {
                    return None;
                }
                Some(dt.constructors.iter().map(|c| c.name.clone()).collect())
            }
            Sort::Uninterpreted(name) => {
                let ctors: Vec<String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt_name, _)| dt_name == name)
                    .map(|(_, cs)| cs.iter().map(String::clone).collect())
                    .unwrap_or_default();
                if ctors.is_empty() || ctors.len() > Self::FINITE_ENUM_INDEX_MAX_CTORS {
                    return None;
                }
                // All constructors must be nullary (no selectors): an enum.
                let all_nullary = ctors.iter().all(|c| {
                    self.ctx
                        .constructor_selector_info(c)
                        .map_or(true, |f| f.is_empty())
                });
                if all_nullary {
                    Some(ctors)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Cardinality `k` to use for the finite-domain PIGEONHOLE conflict over a
    /// DATATYPE-sorted `distinct`/disequality clique. Returns `Some(k)` ONLY when
    /// `sort` is a datatype (inline `Sort::Datatype` or a `Sort::Uninterpreted`
    /// naming a declared datatype) that is PROVABLY FINITE — covering both the
    /// all-nullary enum case (`k = #constructors`) and the FIELD-BEARING finite
    /// case (e.g. a single-constructor `C(b:Bool)` has `k = 2`, a multi-ctor
    /// type's `k = sum over ctors of product of field cardinalities`). Returns
    /// `None` for any non-datatype sort, a recursive (infinite) datatype, or one
    /// with a not-provably-finite field (e.g. an `Int` field), so the pass stays
    /// SOUND: `k` is the EXACT cardinality, never an under-estimate, and a `None`
    /// merely skips the conflict (incompleteness).
    ///
    /// Restricting to DATATYPE sorts (rather than every finite sort via
    /// `sort_finite_cardinality`) keeps this pass focused: `Bool`/`BitVec`
    /// `distinct`s are already decided exactly by their own theories, so the
    /// pigeonhole graph machinery only needs to cover the datatype domains that
    /// EUF otherwise floats free.
    pub(in crate::executor) fn pigeonhole_datatype_cardinality(
        &self,
        sort: &Sort,
    ) -> Option<usize> {
        let is_datatype = match sort {
            Sort::Datatype(_) => true,
            Sort::Uninterpreted(name) => self
                .ctx
                .datatype_iter()
                .any(|(dt_name, _)| dt_name == *name),
            _ => false,
        };
        if !is_datatype {
            return None;
        }
        self.sort_finite_cardinality(sort)
    }

    /// Maximum number of distinct enum-sorted terms (graph nodes) over which the
    /// finite-enum pigeonhole conflict check runs a clique search. Beyond this we
    /// skip the check (staying SOUND — it never fires a false conflict, just may
    /// miss one). Real coloring-style instances (SMT-LIB 20210312-Bouvier) reach
    /// ~1026 nodes; 4096 covers them with headroom while the adjacency bitsets
    /// stay tiny (4096 nodes = 64 u64 words/row = 2 MiB total). Runaway search
    /// cost is bounded by `FINITE_ENUM_PIGEONHOLE_WORK_BUDGET`, not by this cap.
    pub(in crate::executor) const FINITE_ENUM_PIGEONHOLE_MAX_NODES: usize = 4096;

    /// Work budget for the clique search, in u64 bitset-word operations, shared
    /// by the greedy pre-pass and the exact Bron–Kerbosch search. Exhaustion
    /// returns "no clique found" — a SOUND skip (the pass just stays silent),
    /// never a wrong answer. ~300M word-ops is well under a second; the Bouvier
    /// witnesses are found in a few milliseconds, so this only bounds the
    /// pathological worst case (clique EXISTENCE refutation is exponential).
    pub(in crate::executor) const FINITE_ENUM_PIGEONHOLE_WORK_BUDGET: u64 = 300_000_000;

    /// Restarts of the greedy clique pre-pass (one per highest-degree seed).
    /// Greedy finds the witness on dense instances where exact Bron–Kerbosch
    /// would exhaust its budget first; 50 seeds is ample in practice and its
    /// cost is charged against `FINITE_ENUM_PIGEONHOLE_WORK_BUDGET` anyway.
    pub(in crate::executor) const FINITE_ENUM_PIGEONHOLE_GREEDY_RESTARTS: usize = 50;

    /// Soundness pass (finite-enum CARDINALITY / pigeonhole): a datatype sort
    /// whose constructors are ALL NULLARY has exactly `k` inhabitants (its `k`
    /// constructor constants). If the assertions force more than `k` values of
    /// that sort to be pairwise distinct, no model exists — UNSAT.
    ///
    /// AY otherwise reports SAT here by inventing fresh enum representatives
    /// (`@Col!0/1/2`), ignoring that an all-nullary datatype is a FINITE domain.
    /// (`add_ground_singleton_sort_equalities` handles only the `k == 1`
    /// singleton case.)
    ///
    /// Method: collect the disequality edges that hold UNCONDITIONALLY (top-level
    /// asserted `(not (= a b))`, `(distinct ...)`, and conjuncts of a top-level
    /// `(and ...)` — which is how an n-ary `distinct` over >=3 terms is encoded).
    /// Restrict to a single finite-enum sort, build the disequality graph, and
    /// search for a clique of size `> k`. If one exists, `k` holes cannot seat
    /// `> k` pairwise-distinct pigeons, so assert `false`.
    ///
    /// Sound: every edge is an unconditional fact, the enum cardinality is EXACT
    /// (all-nullary => inhabitants are precisely the constructor constants), and a
    /// reported clique is a genuine clique (we only assert `false` on a real one).
    /// Conservative: bounded node count, bounded clique enumeration; a missed
    /// conflict merely leaves the prior (possibly incomplete) behaviour, never a
    /// wrong answer. Only finite-enum (all-nullary) sorts are bounded; datatypes
    /// with any field (recursive or wide) are infinite/large and untouched.
    ///
    /// Returns `true` iff the conflict fired (a re-verified clique of size `> k`
    /// was found and `false` was asserted) so the caller can conclude UNSAT
    /// without dispatching the (now trivially unsatisfiable) ground solve.
    pub(in crate::executor) fn add_finite_enum_pigeonhole_conflict(&mut self) -> bool {
        // A failed scan must never leave a clique from a prior attempt eligible
        // for proof reconstruction.
        self.clear_finite_enum_proof_state();
        // sort-key -> cardinality k + disequality edges with source-assertion
        // provenance (the provenance also feeds the named unsat-core fast
        // path, see `pigeonhole_core`).
        let mut by_sort: HashMap<Sort, EnumDiseqEdges> = HashMap::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            self.collect_finite_enum_diseq_edges(assertion, assertion, &mut by_sort);
        }
        // Recover the disequality edges contributed by DT-sorted `ite` operands
        // of a `distinct`, which preprocessing has Shannon-lifted + CNF'd into
        // complementary guarded clauses (see `collect_guarded_ite_diseq_edges`).
        for &assertion in &assertions {
            self.collect_guarded_ite_diseq_edges(assertion, assertion, &mut by_sort);
        }

        let debug_pigeonhole = ay_core::misc_cli_flags().debug_pigeonhole;
        for (_sort, info) in by_sort {
            let k = info.k;
            let edges: HashSet<(TermId, TermId)> = info.edges.keys().copied().collect();
            if debug_pigeonhole {
                eprintln!(
                    "c pigeonhole-debug sort={:?} k={} edges={}",
                    _sort,
                    k,
                    edges.len()
                );
            }
            let found = self.disequality_graph_clique_exceeding(&edges, k);
            if debug_pigeonhole {
                eprintln!(
                    "c pigeonhole-debug clique={:?}",
                    found.as_ref().map(|c| c.len())
                );
            }
            let Some(clique) = found else {
                continue;
            };
            // Never assert a clique the pass did not re-verify: every member
            // pair must be one of the collected unconditional disequality
            // edges. The search only constructs genuine cliques, so this check
            // cannot fail — but `false` is the strongest possible assertion,
            // so guard it defensively (a failure is a sound skip, never a
            // wrong answer).
            let verified = clique.len() > k
                && clique.iter().enumerate().all(|(i, &a)| {
                    clique[i + 1..]
                        .iter()
                        .all(|&b| edges.contains(&(a, b)) || edges.contains(&(b, a)))
                });
            if debug_pigeonhole {
                eprintln!("c pigeonhole-debug verified={verified}");
            }
            debug_assert!(
                verified,
                "finite-enum pigeonhole search returned an unverified clique"
            );
            if !verified {
                continue;
            }
            // Record the ARGUMENT before asserting the conclusion
            // (#dt-enum-pigeonhole). Pushing bare `false` makes the verdict
            // plumbing work but throws the reasoning away: `[false]` is not a
            // tautology and carries no premises, so strict certification must
            // reject it and every discharge lane fails. Keeping the clique lets
            // the proof layer emit a checkable lemma instead.
            let members: Vec<TermId> = clique.iter().copied().take(k + 1).collect();
            let mut edge_sources: HashMap<(TermId, TermId), TermId> = HashMap::default();
            for (i, &a) in members.iter().enumerate() {
                for &b in &members[i + 1..] {
                    let key = if a.0 < b.0 { (a, b) } else { (b, a) };
                    if let Some(&src) = info.edges.get(&(a, b)).or_else(|| info.edges.get(&(b, a)))
                    {
                        edge_sources.insert(key, src);
                    }
                }
            }
            let Some((pigeonhole, equalities)) = self.finite_enum_pigeonhole_disjunction(&members)
            else {
                continue;
            };
            self.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
                k,
                members,
                edge_sources,
            });
            self.push_finite_enum_pigeonhole_axiom(pigeonhole, equalities);
            // The clique is refuted; no need to scan the remaining sorts.
            return true;
        }
        false
    }

    /// The finite-enum PIGEONHOLE TAUTOLOGY over one re-verified clique:
    /// `(or (= m_i m_j) : i < j)` for `k + 1` members of a sort with exactly
    /// `k` inhabitants. Two of them must be equal, so the disjunction holds in
    /// EVERY model.
    ///
    /// #dt-enum-pigeonhole-false-lemma. The caller used to conclude by pushing
    /// the Bool constant `false`, which `record_array_axiom_proof` recorded as
    /// `TheoryLemma { kind: Generic, clause: [false] }` — a maximal trust
    /// admission wearing a theory lemma's label, since `(cl false)` is valid in
    /// no model at all. The disjunction is what the argument actually
    /// establishes; combined with the problem's own disequality edges it
    /// refutes the query, and the caller's `true` return (never the `false`
    /// assertion) is what carries that to the solve. Asserting a VALID clause
    /// removes no models, so the solver is no weaker.
    ///
    /// FAILS CLOSED: `mk_eq`/`mk_or` fold, so a degenerate clique could in
    /// principle collapse an edge — or the whole disjunction — to a Bool
    /// constant. `false` is the very step this exists to abolish and `true`
    /// would leave the UNSAT claim with no recorded justification, so `None`
    /// refuses the conflict outright and the caller routes to the ordinary
    /// solver. Returns the asserted disjunction AND its disjuncts.
    fn finite_enum_pigeonhole_disjunction(
        &mut self,
        members: &[TermId],
    ) -> Option<(TermId, Vec<TermId>)> {
        let (true_term, false_term) = (self.ctx.terms.true_term(), self.ctx.terms.false_term());
        let mut equalities: Vec<TermId> = Vec::new();
        for (index, &left) in members.iter().enumerate() {
            for &right in &members[index + 1..] {
                let equality = self.ctx.terms.mk_eq(left, right);
                if equality == true_term || equality == false_term {
                    return None;
                }
                equalities.push(equality);
            }
        }
        let pigeonhole = self.ctx.terms.mk_or(equalities.clone());
        (pigeonhole != false_term && pigeonhole != true_term).then_some((pigeonhole, equalities))
    }

    /// Assert the pigeonhole tautology and record it as a theory lemma whose
    /// clause is the COMPLETE EQUALITY GRAPH, not the packed `(or ..)` term.
    ///
    /// `push_array_axiom_assertion_site` records `[axiom]` — one literal, the
    /// whole disjunction. `proof::rebuild_finite_enum_pigeonhole_refutation`
    /// matches this conflict's recorded stub literal BY LITERAL against the
    /// member pairs it independently re-authenticated, so the packed form would
    /// silently disable the strict-checkable `DatatypeEnumPigeonhole` rebuild
    /// that authored-disequality cliques already receive (measured: the
    /// four-member QF_DT clique of `api::tests::test_proof_artifact` loses its
    /// `unsat` outright). Recording the disjuncts states exactly the same
    /// clause and keeps that rebuild reachable.
    fn push_finite_enum_pigeonhole_axiom(&mut self, axiom: TermId, equalities: Vec<TermId>) {
        self.trace_array_axiom_assertion_site(axiom, "finite_enum_pigeonhole");
        self.ctx.assertions.push(axiom);
        if self.produce_proofs_enabled() {
            let _ = self.proof_tracker.add_explicit_trust_lemma(equalities);
        }
    }

    /// Maximum number of enum-sorted terms for which finite-domain coverage
    /// disjunctions are asserted. Each adds one `(or (= t c0) … (= t c_{k-1}))`
    /// clause; bounding this keeps the pass cheap and skipping merely leaves the
    /// prior (possibly incomplete) behaviour — never a wrong answer.
    ///
    /// Deliberately NOT raised alongside `FINITE_ENUM_PIGEONHOLE_MAX_NODES`:
    /// lifting it would be sound (the clauses are valid), but on the huge
    /// coloring-style instances (e.g. Bouvier `vlsat3_b80`, 735 enum terms ×
    /// k = 84 constructors ≈ 62k extra equality atoms) the resulting CDCL
    /// refutation embeds a pigeonhole proof — exponentially hard for resolution
    /// — so the extra clauses cost CNF/search time on SAT instances without
    /// making the UNSAT ones tractable. Those are exactly the instances the
    /// (budgeted) pigeonhole clique pass above now refutes directly.
    const FINITE_ENUM_COVERAGE_MAX_TERMS: usize = 256;

    /// Soundness pass (finite-enum DOMAIN COVERAGE): every term `t` of an
    /// all-nullary (enum) datatype sort `D = {c0..c_{k-1}}` necessarily equals
    /// ONE of `D`'s constructor constants — that is the EXACT, FINITE inhabitant
    /// set of `D`. EUF on its own does not know this: it treats an enum-sorted
    /// FUNCTION-APPLICATION term such as `(f a)` as a fresh, unconstrained value
    /// and so can satisfy a finite-domain-impossible constraint by inventing an
    /// out-of-domain representative.
    ///
    /// Concretely `(distinct (f a) (f (f (f a))))` over `E = {c0, c1}`,
    /// `f : E → E`, is UNSAT (over a 2-element domain no `f` makes those two
    /// applications differ once `a` is pinned through the image), but ay reported
    /// SAT because `(f a)`, `(f (f a))`, `(f^3 a)` floated free of `{c0, c1}`.
    /// (`add_finite_enum_pigeonhole_conflict` only refutes a disequality CLIQUE
    /// of size `> k`; here the single edge `(f a) ≠ (f^3 a)` is a 2-clique that
    /// never exceeds `k = 2`, so it cannot fire. The real obligation is a
    /// FUNCTIONAL pigeonhole that needs each application term constrained to the
    /// finite domain.)
    ///
    /// Method: collect every ground sub-term `t` whose OWN sort is a finite-enum
    /// datatype and that is NOT itself a constructor constant (those trivially
    /// satisfy coverage) nor a bound variable, then assert the coverage
    /// disjunction `(or (= t c0) … (= t c_{k-1}))`. The SAT layer then case-splits
    /// the finite domain and EUF congruence refutes the genuinely-UNSAT cases.
    ///
    /// SOUNDNESS: each `(or (= t c0) … (= t c_{k-1}))` is VALID in every model,
    /// because an all-nullary datatype's domain is EXACTLY its `k` constructor
    /// constants, so any term of that sort equals one of them. Adding logically
    /// valid clauses removes no models — it can NEVER turn SAT into UNSAT. It only
    /// blocks EUF from satisfying the formula with a fresh out-of-domain value,
    /// recovering the genuine UNSAT. Bounded by a term budget (skip => prior
    /// behaviour, never a wrong answer); only finite-enum (all-nullary) sorts are
    /// touched.
    pub(in crate::executor) fn add_finite_enum_domain_coverage(&mut self) {
        // Distinct enum-sorted terms needing coverage, in deterministic order,
        // each paired with its constructor-name list.
        let mut terms: Vec<(TermId, Vec<String>)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut ctor_cache: HashMap<Sort, Option<Vec<String>>> = HashMap::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            if terms.len() >= Self::FINITE_ENUM_COVERAGE_MAX_TERMS {
                break;
            }
            self.collect_finite_enum_coverage_terms(
                assertion,
                &mut terms,
                &mut seen,
                &mut ctor_cache,
            );
        }
        if terms.len() > Self::FINITE_ENUM_COVERAGE_MAX_TERMS {
            return; // over budget: skip entirely (sound — just incomplete)
        }

        for (t, ctors) in terms {
            let sort = self.ctx.terms.sort(t).clone();
            let eqs: Vec<TermId> = ctors
                .iter()
                .map(|c| {
                    // A nullary datatype constructor reference elaborates to
                    // `mk_var(name, sort)` (frontend `elaborate/term.rs` registers
                    // it as `mk_fresh_named_var`), so build the constructor constant
                    // the SAME way — a fresh `App(Symbol::named(c), [])` would be a
                    // DISTINCT term that EUF never merges with the real constructor,
                    // leaving the coverage disjunction theory-inert (the SAT layer
                    // satisfies it propositionally while EUF floats `t` to a fresh
                    // value, degrading the correct UNSAT to `unknown`).
                    let ct = self.ctx.terms.mk_var(c.clone(), sort.clone());
                    self.ctx.terms.mk_eq(t, ct)
                })
                .collect();
            if eqs.is_empty() {
                continue;
            }
            let cov = self.ctx.terms.mk_or(eqs);
            self.push_array_axiom_assertion_site(cov, "finite_enum_domain_coverage");
        }
    }

    /// Collect ground sub-terms of `term` whose OWN sort is a finite-enum
    /// (all-nullary) datatype and that are NOT already a constructor constant of
    /// that sort (nor a bound variable). Each is recorded with its constructor
    /// names so the caller can assert the coverage disjunction. Descends through
    /// all structure; does NOT descend into quantifier bodies (those terms may
    /// mention bound variables and are not yet ground).
    fn collect_finite_enum_coverage_terms(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, Vec<String>)>,
        seen: &mut HashSet<TermId>,
        ctor_cache: &mut HashMap<Sort, Option<Vec<String>>>,
    ) {
        if !seen.insert(term) {
            return;
        }
        // Collect THIS term when it is an enum-sorted COMPOUND term (a function
        // application / select / store etc.). We skip `Var` terms entirely: a
        // nullary datatype constructor constant (`c0`) elaborates to
        // `TermData::Var("c0", sort)` (frontend `elaborate/datatypes.rs`
        // `mk_fresh_named_var`) and trivially satisfies its own coverage, and a
        // plain declared variable's coverage is not needed to close the functional
        // pigeonhole (the application terms carry the constraint). Skipping Vars
        // keeps the pass minimal and avoids vacuous `(or (= c0 c0) …)` clauses.
        let sort = self.ctx.terms.sort(term).clone();
        let ctors = ctor_cache
            .entry(sort.clone())
            .or_insert_with(|| self.finite_enum_datatype_ctors(&sort))
            .clone();
        if let Some(ctors) = ctors {
            if !matches!(self.ctx.terms.get(term), TermData::Var(..)) {
                out.push((term, ctors));
            }
        }
        // Recurse into children (but never into quantifier bodies).
        match self.ctx.terms.get(term).clone() {
            TermData::App(_, args) => {
                for arg in args {
                    self.collect_finite_enum_coverage_terms(arg, out, seen, ctor_cache);
                }
            }
            TermData::Not(inner) => {
                self.collect_finite_enum_coverage_terms(inner, out, seen, ctor_cache)
            }
            TermData::Ite(c, t, e) => {
                self.collect_finite_enum_coverage_terms(c, out, seen, ctor_cache);
                self.collect_finite_enum_coverage_terms(t, out, seen, ctor_cache);
                self.collect_finite_enum_coverage_terms(e, out, seen, ctor_cache);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    self.collect_finite_enum_coverage_terms(v, out, seen, ctor_cache);
                }
                self.collect_finite_enum_coverage_terms(b, out, seen, ctor_cache);
            }
            // Do NOT descend into Forall/Exists bodies: those terms can mention
            // bound variables and are not ground; coverage there is unsound to
            // assert at the top level.
            _ => {}
        }
    }

    /// Walk `term` collecting UNCONDITIONAL disequality edges between terms of a
    /// finite-enum sort, grouped by that sort (recording the sort's cardinality).
    /// Recurses only through top-level `and` conjuncts — disequalities buried
    /// under `or`/`ite`/`=>`/`not` are NOT unconditional and must be ignored
    /// (including them could fabricate a false clique => wrong-unsat).
    ///
    /// `source` is the TOP-LEVEL assertion being walked; every recorded edge
    /// carries it as provenance (first-recorded source defines the graph;
    /// further distinct sources per pair are kept in `extra_sources` for the
    /// edge-closure core assembly) so the named unsat-core fast path can map
    /// clique edges back to `:named` assertions (named ids equal the bare
    /// inner assertion TermIds).
    pub(in crate::executor) fn collect_finite_enum_diseq_edges(
        &self,
        term: TermId,
        source: TermId,
        by_sort: &mut HashMap<Sort, EnumDiseqEdges>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_finite_enum_diseq_edges(arg, source, by_sort);
                }
            }
            // `(distinct a b ...)` over a provably-finite datatype sort (enum OR
            // field-bearing): each pair is an edge, `k` the exact cardinality.
            TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                let args = args.clone();
                let sort = self.ctx.terms.sort(args[0]).clone();
                let Some(k) = self.pigeonhole_datatype_cardinality(&sort) else {
                    return;
                };
                let entry = by_sort
                    .entry(sort)
                    .or_insert_with(|| EnumDiseqEdges::new(k));
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        if args[i] != args[j] {
                            entry.record(Self::ordered_term_pair(args[i], args[j]), source);
                        }
                    }
                }
            }
            // `(not (= a b))` over a provably-finite datatype sort: a single edge.
            TermData::Not(inner) => {
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    return;
                };
                if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                    let (lhs, rhs) = (args[0], args[1]);
                    let sort = self.ctx.terms.sort(lhs).clone();
                    if let Some(k) = self.pigeonhole_datatype_cardinality(&sort) {
                        let entry = by_sort
                            .entry(sort)
                            .or_insert_with(|| EnumDiseqEdges::new(k));
                        entry.record(Self::ordered_term_pair(lhs, rhs), source);
                    }
                }
                // `(not (distinct ...))` is a positive constraint, not a
                // disequality — nothing to collect.
            }
            _ => {}
        }
    }

    /// Maximum number of guarded disequality clauses scanned for ite-operand
    /// edge recovery. The matcher is O(n^2) so this bounds it; pigeonhole
    /// problems are tiny, and skipping merely leaves the prior (incomplete)
    /// behaviour — never a wrong answer.
    const FINITE_ENUM_GUARDED_CLAUSE_MAX: usize = 256;

    /// Recover the disequality edge contributed by a DT-sorted `ite` operand of a
    /// `distinct`. `(not (= (ite g u v) X))` is eagerly Shannon-lifted by `mk_eq`
    /// to `(not (ite g (= X u) (= X v)))` and then CNF'd into the complementary
    /// guarded pair
    ///   `(or (not (= u X)) (not g))`   and   `(or g (not (= v X)))`.
    /// Each pair means `X != (ite g u v)` UNCONDITIONALLY: under `g` it forces
    /// `X != u` (= the then-value), under `!g` it forces `X != v` (= the
    /// else-value). The plain-`(not (= ..))` collector never sees this, so the
    /// finite-enum pigeonhole would undercount the clique and miss a real
    /// cardinality conflict — e.g. `(distinct (ite p v1 v2) (f a) a b)` over a
    /// 3-inhabitant enum (#dt-enum-pigeonhole-ite false-SAT).
    ///
    /// Soundness: each recovered edge is genuinely entailed by two ASSERTED
    /// top-level clauses, regardless of whether they originated from the same
    /// `ite` (the entailment `X != ite(g,u,v)` holds for any complementary pair
    /// sharing guard `g` and operand `X`). A missed pair only leaves a conflict
    /// undetected (incompleteness), never a false one — the clique check still
    /// only fires on a genuine clique of real disequalities over real enum-sorted
    /// terms.
    ///
    /// `source` is the TOP-LEVEL assertion being walked (both complementary
    /// clauses of a recovered edge live in the same assertion — the matcher
    /// only pairs clauses gathered from this one walk), recorded as the
    /// edge's provenance for the named unsat-core fast path.
    pub(in crate::executor) fn collect_guarded_ite_diseq_edges(
        &mut self,
        term: TermId,
        source: TermId,
        by_sort: &mut HashMap<Sort, EnumDiseqEdges>,
    ) {
        // (guard term, guard polarity, eq operand a, eq operand b)
        let mut clauses: Vec<(TermId, bool, TermId, TermId)> = Vec::new();
        self.gather_guarded_diseq_clauses(term, &mut clauses);
        if clauses.len() > Self::FINITE_ENUM_GUARDED_CLAUSE_MAX {
            return; // bound the O(n^2) match (sound: just skip)
        }
        // Match a negative-guard clause `(or (not g) (not (= u X)))` with a
        // positive-guard clause `(or g (not (= v X)))` over the same guard.
        let mut pending: Vec<(TermId, TermId, TermId, TermId)> = Vec::new(); // (X, g, u, v)
        for i in 0..clauses.len() {
            let (gi, posi, ai, bi) = clauses[i];
            if posi {
                continue; // i must be the NEGATIVE-guard (then) clause
            }
            for &(gj, posj, aj, bj) in &clauses {
                if !posj || gj != gi {
                    continue; // j must be the POSITIVE-guard (else) clause, same guard
                }
                if let Some((x, u, v)) = Self::shared_operand_split(ai, bi, aj, bj) {
                    pending.push((x, gi, u, v));
                }
            }
        }
        for (x, g, u, v) in pending {
            let sort = self.ctx.terms.sort(x).clone();
            if let Some(k) = self.pigeonhole_datatype_cardinality(&sort) {
                let iteop = self.ctx.terms.mk_ite(g, u, v);
                if iteop != x {
                    let entry = by_sort
                        .entry(sort)
                        .or_insert_with(|| EnumDiseqEdges::new(k));
                    entry.record(Self::ordered_term_pair(x, iteop), source);
                }
            }
        }
    }

    /// Walk top-level `and` conjuncts collecting binary `or` clauses that pair a
    /// guard literal with a disequality literal: `(or <guard> (not (= a b)))`.
    /// Records `(guard_term, guard_is_positive, a, b)`.
    fn gather_guarded_diseq_clauses(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, bool, TermId, TermId)>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.gather_guarded_diseq_clauses(arg, out);
                }
            }
            TermData::App(sym, args) if sym.name() == "or" && args.len() == 2 => {
                let (l, r) = (args[0], args[1]);
                for (diseq_lit, guard_lit) in [(l, r), (r, l)] {
                    if let Some((a, b)) = self.neg_eq_operands(diseq_lit) {
                        if let Some((guard, pos)) = self.guard_literal(guard_lit) {
                            out.push((guard, pos, a, b));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// `(not (= a b))` with `a != b` → `Some((a, b))`, else `None`.
    fn neg_eq_operands(&self, t: TermId) -> Option<(TermId, TermId)> {
        let TermData::Not(inner) = self.ctx.terms.get(t) else {
            return None;
        };
        match self.ctx.terms.get(*inner) {
            TermData::App(sym, args)
                if sym.name() == "=" && args.len() == 2 && args[0] != args[1] =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// A guard literal: `(not g)` → `Some((g, false))`, or a Bool-sorted atom
    /// `g` that is not an (dis)equality → `Some((g, true))`. Equalities are
    /// excluded so the disequality disjunct is never mistaken for the guard.
    fn guard_literal(&self, t: TermId) -> Option<(TermId, bool)> {
        if let TermData::Not(inner) = self.ctx.terms.get(t) {
            let inner = *inner;
            return if self.is_equality_app(inner) {
                None
            } else {
                Some((inner, false))
            };
        }
        if *self.ctx.terms.sort(t) == Sort::Bool && !self.is_equality_app(t) {
            Some((t, true))
        } else {
            None
        }
    }

    fn is_equality_app(&self, t: TermId) -> bool {
        matches!(self.ctx.terms.get(t), TermData::App(sym, _) if matches!(sym.name(), "=" | "distinct"))
    }

    /// Given two disequality operand pairs `(ai,bi)` (the then/neg-guard clause)
    /// and `(aj,bj)` (the else/pos-guard clause), find the single SHARED operand
    /// `X` and the distinct branch values `u` (from i) and `v` (from j). Returns
    /// `(X, u, v)` or `None` if there is no unique shared operand or `u == v`.
    fn shared_operand_split(
        ai: TermId,
        bi: TermId,
        aj: TermId,
        bj: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        for &x in &[ai, bi] {
            if x == aj || x == bj {
                let u = if ai == x { bi } else { ai };
                let v = if aj == x { bj } else { aj };
                if u != v {
                    return Some((x, u, v));
                }
            }
        }
        None
    }

    /// Finds a clique of size strictly greater than `k` in the undirected
    /// disequality graph (given as a set of ordered term pairs), returning its
    /// members. Sound: returns `Some` only for a real clique of size `> k`
    /// (which the caller re-verifies edge-by-edge anyway); bounded so it never
    /// blows up — node-count cap plus a work budget shared by a greedy pre-pass
    /// and the exact Bron–Kerbosch search, whose exhaustion returns `None`
    /// (skip — a missed conflict is only ever incompleteness).
    pub(in crate::executor) fn disequality_graph_clique_exceeding(
        &self,
        edges: &HashSet<(TermId, TermId)>,
        k: usize,
    ) -> Option<Vec<TermId>> {
        if edges.is_empty() {
            return None;
        }
        // Collect and index the distinct nodes.
        let mut nodes: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &(a, b) in edges {
            if seen.insert(a) {
                nodes.push(a);
            }
            if seen.insert(b) {
                nodes.push(b);
            }
        }
        let n = nodes.len();
        // A clique of size `> k` needs at least `k + 1` nodes.
        if n <= k {
            return None;
        }
        if n > Self::FINITE_ENUM_PIGEONHOLE_MAX_NODES {
            return None; // too large: skip (sound — no false conflict)
        }
        let index: HashMap<TermId, usize> =
            nodes.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        // Adjacency bitsets, one row of `words` u64s per node.
        let words = n.div_ceil(64);
        let mut adj = vec![0u64; n * words];
        let set_bit = |adj: &mut [u64], row: usize, col: usize| {
            adj[row * words + col / 64] |= 1u64 << (col % 64);
        };
        for &(a, b) in edges {
            let (ia, ib) = (index[&a], index[&b]);
            if ia != ib {
                set_bit(&mut adj, ia, ib);
                set_bit(&mut adj, ib, ia);
            }
        }
        // Degree (k-core) prune: any node in a clique of size `k + 1` needs
        // degree `>= k` among the survivors. Worklist peel — O(V + E) with
        // popcount degrees — so the prune itself never becomes the bottleneck.
        let mut deg: Vec<usize> = (0..n)
            .map(|v| {
                adj[v * words..(v + 1) * words]
                    .iter()
                    .map(|w| w.count_ones() as usize)
                    .sum()
            })
            .collect();
        let mut alive = vec![true; n];
        let mut kill: Vec<usize> = (0..n).filter(|&v| deg[v] < k).collect();
        while let Some(v) = kill.pop() {
            if !alive[v] {
                continue;
            }
            alive[v] = false;
            for w in 0..words {
                let mut bits = adj[v * words + w];
                while bits != 0 {
                    let u = w * 64 + bits.trailing_zeros() as usize;
                    bits &= bits - 1;
                    if alive[u] {
                        deg[u] -= 1;
                        if deg[u] + 1 == k {
                            kill.push(u); // just dropped below k
                        }
                    }
                }
            }
        }
        let mut alive_bits = vec![0u64; words];
        let mut alive_count = 0usize;
        for v in 0..n {
            if alive[v] {
                alive_bits[v / 64] |= 1u64 << (v % 64);
                alive_count += 1;
            }
        }
        if alive_count <= k {
            return None;
        }
        // Restrict adjacency to the survivors so every step below sees the
        // pruned graph (dead rows are zeroed, live rows masked).
        for (v, &v_alive) in alive.iter().enumerate() {
            let row = v * words;
            if v_alive {
                for (w, &mask) in alive_bits.iter().enumerate() {
                    adj[row + w] &= mask;
                }
            } else {
                adj[row..row + words].fill(0);
            }
        }
        let target = k + 1;
        let mut budget = Self::FINITE_ENUM_PIGEONHOLE_WORK_BUDGET;
        // Greedy pre-pass: cheap, and on dense graphs (where exact search is
        // at its worst) it routinely finds the witness directly.
        if let Some(clique) = Self::greedy_clique_reaches(target, &adj, words, &alive, &mut budget)
        {
            return Some(clique.into_iter().map(|v| nodes[v]).collect());
        }
        // Exact (budgeted) Bron–Kerbosch over the pruned node set; stops as
        // soon as a clique of size `k + 1` is reached (existence only).
        let mut r: Vec<usize> = Vec::new();
        let mut p = alive_bits;
        let mut x = vec![0u64; words];
        Self::bron_kerbosch_reaches(target, &mut r, &mut p, &mut x, &adj, words, &mut budget)
            .map(|clique| clique.into_iter().map(|v| nodes[v]).collect())
    }

    /// Greedy clique search: from each of the `FINITE_ENUM_PIGEONHOLE_GREEDY_RESTARTS`
    /// highest-degree seeds, repeatedly add the candidate with the largest
    /// common neighbourhood inside the remaining candidate set. Every grown set
    /// is a genuine clique by construction (candidates are the intersection of
    /// all members' neighbourhoods). Returns `Some(clique)` on reaching
    /// `target` vertices; `None` on failure or budget exhaustion (sound skip).
    fn greedy_clique_reaches(
        target: usize,
        adj: &[u64],
        words: usize,
        alive: &[bool],
        budget: &mut u64,
    ) -> Option<Vec<usize>> {
        let n = alive.len();
        let row = |v: usize| &adj[v * words..(v + 1) * words];
        let deg = |v: usize| {
            row(v)
                .iter()
                .map(|w| w.count_ones() as usize)
                .sum::<usize>()
        };
        *budget = budget.saturating_sub((n * words) as u64);
        let mut seeds: Vec<usize> = (0..n).filter(|&v| alive[v]).collect();
        seeds.sort_by_key(|&v| std::cmp::Reverse(deg(v)));
        seeds.truncate(Self::FINITE_ENUM_PIGEONHOLE_GREEDY_RESTARTS);
        for &seed in &seeds {
            let mut clique = vec![seed];
            let mut cand: Vec<u64> = row(seed).to_vec();
            loop {
                // Pick the candidate maximizing |N(u) ∩ cand|.
                let mut best: Option<(usize, usize)> = None;
                for w in 0..words {
                    let mut bits = cand[w];
                    while bits != 0 {
                        let u = w * 64 + bits.trailing_zeros() as usize;
                        bits &= bits - 1;
                        if *budget < words as u64 {
                            return None; // budget exhausted: sound skip
                        }
                        *budget -= words as u64;
                        let common: usize = (0..words)
                            .map(|i| (adj[u * words + i] & cand[i]).count_ones() as usize)
                            .sum();
                        if best.is_none_or(|(_, c)| common > c) {
                            best = Some((u, common));
                        }
                    }
                }
                let Some((u, _)) = best else { break };
                clique.push(u);
                if clique.len() >= target {
                    return Some(clique);
                }
                for i in 0..words {
                    cand[i] &= adj[u * words + i];
                }
            }
        }
        None
    }

    /// Bron–Kerbosch (with Tomita pivoting) over bitset-encoded `P`/`X` that
    /// returns the clique as soon as `R` reaches `target` size. Existence-only:
    /// it does not enumerate all maximal cliques, it short-circuits. `budget`
    /// is decremented by the (approximate) number of u64 word operations; on
    /// exhaustion the search bails out with `None` — a sound "not found".
    fn bron_kerbosch_reaches(
        target: usize,
        r: &mut Vec<usize>,
        p: &mut [u64],
        x: &mut [u64],
        adj: &[u64],
        words: usize,
        budget: &mut u64,
    ) -> Option<Vec<usize>> {
        if r.len() >= target {
            return Some(r.clone());
        }
        let popcount = |bs: &[u64]| bs.iter().map(|w| w.count_ones() as usize).sum::<usize>();
        let p_count = popcount(p);
        if p_count == 0 {
            return None;
        }
        // An upper bound: even adding every remaining candidate cannot reach the
        // target, so prune.
        if r.len() + p_count < target {
            return None;
        }
        // Charge this call's dominant cost (the pivot scan) up front.
        let cost = ((p_count + popcount(x) + 2) * words) as u64;
        if *budget < cost {
            *budget = 0;
            return None; // budget exhausted: sound skip
        }
        *budget -= cost;
        // Choose a pivot from P ∪ X maximizing neighbours in P.
        let mut pivot = usize::MAX;
        let mut pivot_nb = 0usize;
        for w in 0..words {
            let mut bits = p[w] | x[w];
            while bits != 0 {
                let u = w * 64 + bits.trailing_zeros() as usize;
                bits &= bits - 1;
                let nb: usize = (0..words)
                    .map(|i| (adj[u * words + i] & p[i]).count_ones() as usize)
                    .sum();
                if pivot == usize::MAX || nb > pivot_nb {
                    pivot = u;
                    pivot_nb = nb;
                }
            }
        }
        // Candidates: P \ N(pivot).
        let mut candidates: Vec<usize> = Vec::new();
        for w in 0..words {
            let mut bits = p[w] & !adj[pivot * words + w];
            while bits != 0 {
                candidates.push(w * 64 + bits.trailing_zeros() as usize);
                bits &= bits - 1;
            }
        }
        for v in candidates {
            if *budget == 0 {
                return None; // exhausted deeper down: unwind without new work
            }
            let mut new_p: Vec<u64> = (0..words).map(|i| p[i] & adj[v * words + i]).collect();
            let mut new_x: Vec<u64> = (0..words).map(|i| x[i] & adj[v * words + i]).collect();
            r.push(v);
            if let Some(clique) =
                Self::bron_kerbosch_reaches(target, r, &mut new_p, &mut new_x, adj, words, budget)
            {
                return Some(clique);
            }
            r.pop();
            // Move v from P to X.
            p[v / 64] &= !(1u64 << (v % 64));
            x[v / 64] |= 1u64 << (v % 64);
        }
        None
    }

    /// (#array-const-store-ext) Restricted extensionality for `const-array = store
    /// chain` over an INFINITE index domain, where
    /// [`add_finite_index_array_closure`](Self::add_finite_index_array_closure)
    /// does not apply and the lazy ArraySolver applies the const=store congruence at
    /// only ONE written index — so `((as const) ed) = (store (store c i0 e3) i1 e0)`
    /// with `i0 != i1`, `e3 != e0` was wrongly SAT (round-3 rank2: it should force
    /// `ed = e3` AND `ed = e0`, hence `e3 = e0`, contradiction).
    ///
    /// For each such equality post the SOUND necessary condition
    /// `(= a b) => (= (select a e) (select b e))` over EVERY store index `e` of the
    /// chain — an IMPLICATION (valid over any index domain, never refutes a real
    /// model). `select(const, e)` folds to the default; `select(chain, e)` is
    /// resolved to the matching stored value by the ROW axioms, forcing the default
    /// to equal each stored value.
    pub(in crate::executor) fn add_const_store_array_extensionality(&mut self) {
        let roots = self.ctx.assertions.clone();
        let mut eqs: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        self.collect_const_store_array_eqs(&roots, &mut eqs, &mut seen);
        for (eq_atom, const_side, chain_side) in eqs {
            let mut idxs: Vec<TermId> = Vec::new();
            self.collect_array_store_indices(chain_side, &mut idxs);
            idxs.sort_unstable();
            idxs.dedup();
            for e in idxs {
                let sel_c = self.ctx.terms.mk_select(const_side, e);
                let sel_s = self.ctx.terms.mk_select(chain_side, e);
                let sel_eq = self.ctx.terms.mk_eq(sel_c, sel_s);
                let imp = self.ctx.terms.mk_implies(eq_atom, sel_eq);
                self.ensure_array_axiom_assertion_site(imp, "const_store_array_ext");
            }
        }
    }

    /// Collect array equalities `(= a b)` where one side is a const-array and the
    /// other a `store(...)` chain. Returns `(eq_atom, const_side, chain_side)`.
    fn collect_const_store_array_eqs(
        &self,
        roots: &[TermId],
        out: &mut Vec<(TermId, TermId, TermId)>,
        seen: &mut HashSet<TermId>,
    ) {
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term).clone() {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        let (a, b) = (args[0], args[1]);
                        if matches!(self.ctx.terms.sort(a), Sort::Array(_)) {
                            let a_const = self.ctx.terms.get_const_array(a).is_some();
                            let b_const = self.ctx.terms.get_const_array(b).is_some();
                            if a_const && self.is_store_chain(b) {
                                out.push((term, a, b));
                            } else if b_const && self.is_store_chain(a) {
                                out.push((term, b, a));
                            }
                        }
                    }
                    for arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, t, e) => {
                    stack.push(c);
                    stack.push(t);
                    stack.push(e);
                }
                _ => {}
            }
        }
    }

    /// True iff `t` is a `store(arr, idx, val)` application.
    fn is_store_chain(&self, t: TermId) -> bool {
        matches!(self.ctx.terms.get(t),
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3)
    }

    /// Collect the store indices along a `store(...)` chain (outermost first),
    /// stopping at the first non-store node.
    fn collect_array_store_indices(&self, t: TermId, out: &mut Vec<TermId>) {
        let mut cur = t;
        for _ in 0..100_000 {
            match self.ctx.terms.get(cur) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    out.push(args[1]);
                    cur = args[0];
                }
                _ => return,
            }
        }
    }

    #[inline]
    pub(in crate::executor) fn ordered_term_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    /// Collect direct top-level disequalities asserted as `(assert (not (= a b)))`.
    pub(super) fn collect_top_level_disequalities(&self) -> HashSet<(TermId, TermId)> {
        let mut disequalities = HashSet::default();
        for &assertion in &self.ctx.assertions {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                disequalities.insert(Self::ordered_term_pair(args[0], args[1]));
            }
        }
        disequalities
    }

    fn are_terms_distinct_constants(&self, lhs: TermId, rhs: TermId) -> bool {
        if lhs == rhs || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return false;
        }
        match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
            (TermData::Const(lhs_const), TermData::Const(rhs_const)) => lhs_const != rhs_const,
            _ => false,
        }
    }

    pub(super) fn are_terms_provably_distinct_from_assertions(
        &self,
        lhs: TermId,
        rhs: TermId,
        disequalities: &HashSet<(TermId, TermId)>,
    ) -> bool {
        lhs != rhs
            && (self.are_terms_distinct_constants(lhs, rhs)
                || disequalities.contains(&Self::ordered_term_pair(lhs, rhs)))
    }

    fn has_explicit_select_disequality_witness(
        &self,
        lhs: TermId,
        rhs: TermId,
        selects_by_array: &HashMap<TermId, HashMap<TermId, TermId>>,
        disequalities: &HashSet<(TermId, TermId)>,
    ) -> bool {
        let Some(lhs_selects) = selects_by_array.get(&lhs) else {
            return false;
        };
        let Some(rhs_selects) = selects_by_array.get(&rhs) else {
            return false;
        };
        let (smaller, larger) = if lhs_selects.len() <= rhs_selects.len() {
            (lhs_selects, rhs_selects)
        } else {
            (rhs_selects, lhs_selects)
        };
        smaller.iter().any(|(&index, &lhs_select)| {
            larger.get(&index).is_some_and(|&rhs_select| {
                self.are_terms_provably_distinct_from_assertions(
                    lhs_select,
                    rhs_select,
                    disequalities,
                )
            })
        })
    }

    /// True iff the OUTER array-extensionality Skolem for a NESTED array pair
    /// `(lhs, rhs)` is redundant because one operand is the BASE of a `store`
    /// that is itself read by a `select` — the
    /// `(select (store OPERAND idx val) k)` nested pattern. In that situation the
    /// inner ROW/congruence decomposition over the nested store already pins the
    /// relevant inner-array index; the additional outer `__ay_ext_diff` Skolem only
    /// injects spurious index equalities that combine with unrelated top-level
    /// index literals into a wrong-UNSAT (#r3-nested-arrayext).
    ///
    /// Conditions (all required):
    ///   - the array sort of `(lhs, rhs)` is NESTED (value/element sort is itself
    ///     an array); and
    ///   - some `(select (store OP ..) ..)` term exists in the problem where
    ///     `OP` is `lhs` or `rhs`.
    ///
    /// SOUNDNESS: with `k` fresh, `(= lhs rhs) ∨ select(lhs,k) != select(rhs,k)`
    /// is a conservative, equisatisfiable extension of the original array
    /// problem — not a tautology for an arbitrary pre-existing `k`. Suppressing
    /// that solver aid leaves the original formula unchanged and can only lose
    /// refutational completeness. The nested ROW/store congruence axioms still
    /// decompose the store-of-array, closing any genuine nested-array UNSAT.
    fn nested_array_outer_ext_redundant(&self, lhs: TermId, rhs: TermId) -> bool {
        // Value (element) sort must itself be an array — the NESTED case.
        let Sort::Array(arr) = self.ctx.terms.sort(lhs).clone() else {
            return false;
        };
        if !matches!(arr.element_sort, Sort::Array(_)) {
            return false;
        }
        // Look for a `(select (store OP ..) ..)` term with OP in {lhs, rhs}.
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            let TermData::App(sym, args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if sym.name() != "select" || args.len() != 2 {
                continue;
            }
            let inner = args[0];
            let TermData::App(s2, a2) = self.ctx.terms.get(inner) else {
                continue;
            };
            if s2.name() == "store" && a2.len() == 3 && (a2[0] == lhs || a2[0] == rhs) {
                return true;
            }
        }
        false
    }

    /// Detect the storeinv_nf extensionality-witness pattern (#6546).
    ///
    /// Returns `true` when the assertion graph contains BOTH:
    ///   1. a top-level array equality between two `store` expressions
    ///      `(= store(_, _, _) store(_, _, _))` — the hallmark of a storeinv
    ///      cross-swap where upward-select propagation is needed, AND
    ///   2. a top-level select-disequality witness
    ///      `(not (= (select A k) (select B k)))` for some array pair.
    ///
    /// This combination matches the QF_AUFLIA storeinv cross-swap `_nf_`
    /// encoding (storeinv_nf_size7/9) where unnamed nested stores require
    /// upward select propagation (ROW2b) to close the proof chain. The
    /// select-disequality witness pins an index where two named arrays must
    /// differ; the store-store equality provides the rewrite rule that ROW2b
    /// must propagate through to reach that witness.
    ///
    /// For benchmarks lacking either condition (the vast majority of QF_AUFLIA),
    /// `eager_row2b` stays off and the runtime ArraySolver handles ROW2b lazily.
    ///
    /// This predicate does NOT trigger the false-UNSAT fence in
    /// `storeinv_invalid_t1_nf_00004_must_not_be_unsat_6546` because that
    /// benchmark lacks a top-level store-store equality (#6546, TL18).
    /// Whether any assertion is a top-level POSITIVE array equality between
    /// two store terms (`(= (store …) (store …))`). This is the storeinv
    /// family signature (PDPAR'05: the two interleaved swap chains asserted
    /// equal, in both the unsat and the `_invalid_` sat variants);
    /// storecomm/swap only assert NEGATED chain equalities plus
    /// variable-defining `(= a (store …))` facts. Scans assertions (not the
    /// term store) so ITE-condition/sub-term equalities do not trigger it.
    /// Used as condition 1 of `has_storeinv_extensionality_witness` and to
    /// scope the BCP-time arrays-lane demotion (#qfax-t3-atom-space, see
    /// `solve_array_euf`).
    pub(in crate::executor) fn has_top_level_positive_store_store_equality(&self) -> bool {
        for &assertion in &self.ctx.assertions {
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    let lhs = args[0];
                    let rhs = args[1];
                    if matches!(self.ctx.terms.sort(lhs), Sort::Array(_))
                        && self.is_store_term(lhs)
                        && self.is_store_term(rhs)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub(in crate::executor) fn has_storeinv_extensionality_witness(&self) -> bool {
        // Condition 1: detect at least one top-level array equality
        // `(= store(_,_,_) store(_,_,_))` that is asserted positively.
        if !self.has_top_level_positive_store_store_equality() {
            return false;
        }

        // Condition 2: detect a top-level select-disequality witness. We
        // collect selects keyed by (array, index) and scan for
        // `(not (= sel_a sel_b))` where sel_a and sel_b are selects on
        // different array-sorted terms.
        //
        // #8804: AUFLIA benchmarks (Armando/Bonacina/Ranise/Schulz PDPAR'05
        // storeinv_t3_*) define `e_33 = (select a1 i_32)` and `e_34 =
        // (select a2 i_32)` as top-level assertions, and assert
        // `(not (= e_33 e_34))` — the disequality is on the *alias
        // variables*, not directly on the select applications. Walk
        // top-level `(= var (select a i))` equalities and canonicalize
        // both the variable and the select to the same key so the
        // disequality lookup sees them as equivalent.
        let mut select_alias: HashMap<TermId, TermId> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    let (var, sel) = match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                        (TermData::Var(_, _), TermData::App(sym2, sargs))
                            if sym2.name() == "select" && sargs.len() == 2 =>
                        {
                            (lhs, rhs)
                        }
                        (TermData::App(sym2, sargs), TermData::Var(_, _))
                            if sym2.name() == "select" && sargs.len() == 2 =>
                        {
                            (rhs, lhs)
                        }
                        _ => continue,
                    };
                    select_alias.entry(var).or_insert(sel);
                }
            }
        }
        let mut selects_by_array: HashMap<TermId, HashMap<TermId, TermId>> = HashMap::default();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select" && args.len() == 2 {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .entry(args[1])
                        .or_insert(term_id);
                }
            }
        }
        let mut top_level_disequalities = self.collect_top_level_disequalities();
        // #8804: Expand disequalities through select-alias defining
        // equalities. If `a != b` and `a = select(A, i)` and
        // `b = select(B, i)`, then `select(A, i) != select(B, i)` is an
        // implied disequality that witnesses extensionality between A and B.
        let base_diseqs: Vec<(TermId, TermId)> = top_level_disequalities.iter().copied().collect();
        for (a, b) in base_diseqs {
            if let (Some(&sel_a), Some(&sel_b)) = (select_alias.get(&a), select_alias.get(&b)) {
                top_level_disequalities.insert(Self::ordered_term_pair(sel_a, sel_b));
            }
            if let Some(&sel_a) = select_alias.get(&a) {
                top_level_disequalities.insert(Self::ordered_term_pair(sel_a, b));
            }
            if let Some(&sel_b) = select_alias.get(&b) {
                top_level_disequalities.insert(Self::ordered_term_pair(a, sel_b));
            }
        }
        // Any two distinct array-sorted terms whose selects at the same index
        // are asserted distinct (via top-level diseq or constant distinctness)
        // satisfy the witness condition.
        let arrays: Vec<TermId> = selects_by_array.keys().copied().collect();
        for i in 0..arrays.len() {
            for j in (i + 1)..arrays.len() {
                if self.has_explicit_select_disequality_witness(
                    arrays[i],
                    arrays[j],
                    &selects_by_array,
                    &top_level_disequalities,
                ) {
                    return true;
                }
            }
        }
        // #qf-ax-negated-swap: a top-level NEGATED ARRAY equality (e.g.
        // `(not (= a1 a2))` in the storeinv `_np_` variants) also supplies the
        // witness — `add_array_extensionality_axioms` fabricates the
        // `__ay_ext_diff` select-disequality Skolem for exactly this atom, and
        // the storeinv refutation then needs the same eager ROW2b/decomposition
        // unroll as the explicit-witness `_sf_` variants. Without this, the
        // two-base `_np_` shape (positive store-store equality + negated base
        // equality) kept a lazy ArraySolver that misses upward select
        // propagation, certifying a witness-less model: false SAT (4 residual
        // conflicts in the 2026-07-02 QF_AX sweep after the same-base fix).
        // OPT-IN research gate (--qfax-neg-eq-witness). Same latent
        // eager-axiom unsoundness as the negated-chain gate above:
        // storeinv_invalid_t3_np_nf_ai_00002_001 (`:status sat`) flips to
        // FALSE UNSAT when this fires. Default OFF until the eager fixpoint
        // derivation is fixed; the storeinv `_np_` wrong-SAT models this was
        // added for are instead degraded fail-closed by the unwitnessed
        // array-disequality guard in model validation.
        if !ay_core::misc_cli_flags().qfax_neg_eq_witness {
            return false;
        }
        for &assertion in &self.ctx.assertions {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() == "="
                && args.len() == 2
                && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
            {
                return true;
            }
        }
        false
    }

    /// Returns `true` if `term` is syntactically a `store` application.
    fn is_store_term(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3
        )
    }

    /// Count the maximum store-nesting depth reachable from any top-level
    /// store-store equality. Used to scale the AUFLIA fixpoint assertion
    /// budget for storeinv cross-swap patterns (#8804).
    ///
    /// An N-deep storeinv chain requires the fixpoint to propagate
    /// extensionality/store-base-decomposition axioms N levels before the
    /// arrays theory can detect the contradiction. A fixed budget of 200
    /// bails out at ~4 levels, which is sufficient for storeinv_*_size7 but
    /// not for sizes 8, 9, or deeper.
    ///
    /// Returns 0 if no top-level store-store equality exists (i.e., not a
    /// storeinv pattern).
    pub(in crate::executor) fn max_top_level_store_store_equality_depth(&self) -> usize {
        let mut max_depth: usize = 0;
        for &assertion in &self.ctx.assertions {
            // #qf-ax-negated-swap: include NEGATED store-store equalities
            // (`(assert (not (= chain1 chain2)))`, the swap/storeinv `_np_`
            // shape) so the eager-ROW2b assertion budget scales with the chain
            // depth the fabricated `__ay_ext_diff` witness has to unroll through.
            let eq_term = match self.ctx.terms.get(assertion) {
                TermData::Not(inner) => *inner,
                _ => assertion,
            };
            if let TermData::App(sym, args) = self.ctx.terms.get(eq_term) {
                if sym.name() == "=" && args.len() == 2 {
                    let lhs = args[0];
                    let rhs = args[1];
                    if matches!(self.ctx.terms.sort(lhs), Sort::Array(_))
                        && self.is_store_term(lhs)
                        && self.is_store_term(rhs)
                    {
                        let d_lhs = self.store_nesting_depth(lhs);
                        let d_rhs = self.store_nesting_depth(rhs);
                        max_depth = max_depth.max(d_lhs.max(d_rhs));
                    }
                }
            }
        }
        max_depth
    }

    /// Detect a top-level NEGATED array equality whose sides are (deep) store
    /// chains: `(assert (not (= (store (store ...)) (store (store ...)))))`.
    ///
    /// This is the SMT-COMP QF_AX swap/storeinv `_np_nf_` shape: the whole
    /// benchmark is one negated equality between two nested store chains, with
    /// NO explicit select-disequality witness anywhere — the only witness is
    /// the `__ay_ext_diff` Skolem fabricated by `add_array_extensionality_axioms`.
    /// Refuting it requires unrolling `select(chain, __ay_ext_diff)` down BOTH
    /// chains (ROW2b upward propagation), which the lazy runtime ArraySolver's
    /// event-driven queues never trigger for unnamed nested stores — leaving a
    /// model that satisfies ROW1/ROW2 locally but violates extensionality
    /// globally, i.e. false SAT (the 2026-07-02 QF_AX sweep found 40 of these).
    /// Firing the same eager-ROW2b rescue as `has_storeinv_extensionality_witness`
    /// closes the gap; the ROW2b budget bounds the cost. Depth >= 2 on at least
    /// one side: single stores are handled exactly by the lazy solver.
    pub(in crate::executor) fn has_negated_deep_store_chain_array_equality(&self) -> bool {
        // OPT-IN research gate (--qfax-neg-chain-gate). Firing eager
        // ROW2b on every negated deep-chain equality exposed a LATENT
        // eager-axiom unsoundness: `:status sat` siblings of the swap `_np_`
        // family (e.g. swap_invalid_t1_np_sf_ai_00002_008) flip to FALSE
        // UNSAT, and the family's solve rate collapses (2026-07-02 postfix
        // sweep: QF_AX 231 -> 95 solved). Until the eager fixpoint derivation
        // is proven sound on these shapes, the sound default is OFF: wrong
        // lazy models are caught fail-closed by the strict-gate array oracle
        // (`store_chain_equality_violated`) and degrade to unknown instead.
        if !ay_core::misc_cli_flags().qfax_neg_chain_gate {
            return false;
        }
        for &assertion in &self.ctx.assertions {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            if !matches!(self.ctx.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            if self
                .store_nesting_depth(lhs)
                .max(self.store_nesting_depth(rhs))
                >= 2
            {
                return true;
            }
        }
        false
    }

    /// Count the `store` nesting depth of a term: the number of chained
    /// `store` applications along its first (array) argument. Bounded by an
    /// internal iteration cap to prevent runaway traversal on pathological
    /// inputs.
    fn store_nesting_depth(&self, term: TermId) -> usize {
        let mut depth: usize = 0;
        let mut cur = term;
        for _ in 0..256_usize {
            match self.ctx.terms.get(cur) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    depth += 1;
                    cur = args[0];
                }
                _ => break,
            }
        }
        depth
    }

    /// Ensure negation terms exist for array equalities appearing inside ITE
    /// conditions. This is necessary for the ABV path where `(ite (= a b) t e)`
    /// contains an array equality `(= a b)` that is never negated elsewhere.
    /// Without the negation in the term store, `add_array_extensionality_axioms`
    /// skips the pair, leaving the array equality unconstrained. The ITE then
    /// becomes a coin flip, causing wrong-SAT or spurious unknown results.
    ///
    /// This function walks the term store for ITE terms whose condition is an
    /// array equality, and creates `(not (= a b))` in the term store. Creating
    /// the negation is semantically harmless (it's just a term, not an assertion)
    /// but enables the extensionality axiom generator to fire.
    pub(in crate::executor) fn ensure_array_eq_ite_negations(&mut self) {
        let mut array_eq_terms: Vec<TermId> = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            let TermData::Ite(cond, _, _) = self.ctx.terms.get(term_id) else {
                continue;
            };
            let cond = *cond;
            // Check if the condition is an array equality
            let TermData::App(sym, args) = self.ctx.terms.get(cond) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            if !matches!(self.ctx.terms.sort(args[0]), Sort::Array(_)) {
                continue;
            }
            array_eq_terms.push(cond);
        }
        // Create negation terms (idempotent via hash-consing in mk_not)
        for eq_term in array_eq_terms {
            let _ = self.ctx.terms.mk_not(eq_term);
        }
    }

    /// Add array-default congruence axioms for array equality atoms.
    ///
    /// For every equality atom `(= a b)` over array-sorted terms, asserts the
    /// theory tautology
    ///
    ///   `¬(= a b) ∨ (= default(a) default(b))`
    ///
    /// i.e. equal arrays have equal defaults. `default` is the array model's
    /// else-value operation. Constant arrays simplify directly; store terms are
    /// handled by [`Self::add_array_default_store_axioms`], because their rule is
    /// carrier-sensitive in Z3 5.0.0.
    ///
    /// This is the principled completion of array extensionality for *positive*
    /// equalities between arrays whose defaults are structurally determined.
    /// The single-Skolem extensionality witness (`add_array_extensionality_*`)
    /// can only force agreement at ONE fresh index `d`, which the solver can
    /// always equate with the store index `k` to dodge the read-over-const /
    /// ROW2 conflict — so it never refutes a positive equality like
    ///   `store((as const C) 0, k, v) = (as const C) 1`.
    /// That formula is UNSAT (the store fixes one index, but the two const
    /// arrays disagree at the infinitely many others), yet the witness-only
    /// machinery returned a spurious SAT.
    ///
    /// On an infinite/large carrier the store-default axiom reduces the store
    /// default to the base default, recovering the same const-default mismatch.
    /// On a small finite carrier it instead links both defaults to selects at a
    /// shared choice point; unconditional store peeling would be unsound there.
    ///
    /// This is independent of (and complementary to) the `select`-over-`ite`
    /// Shannon-lift on the array-EUF route (`lift_arithmetic_ite_all` in
    /// `solve_array_euf`): that lift only rewrites `(select (ite c A B) i)` so
    /// the inner `select`-over-`store` reaches the ROW axioms, and does not
    /// touch a bare positive `(= a b)` between two structurally-different
    /// arrays. Both fixes coexist; neither subsumes the other.
    ///
    /// Soundness: `a = b ⟹ default(a) = default(b)` is a valid array-theory
    /// implication, so adding it (guarded by the equality atom) can never drop a
    /// genuine model — it only adds a *necessary* condition for the equality. On
    /// consistent equalities (e.g. `store(const 0, k, 5) = store(const 0, j, 5)`,
    /// both defaults `0`) the consequent is `true` and nothing is constrained.
    /// Disequalities `(not (= a b))` are unaffected: the antecedent `(= a b)` is
    /// false, so the implication is vacuously satisfied.
    pub(in crate::executor) fn add_array_default_congruence_axioms(&mut self) {
        let should_stop = self.make_should_stop();
        // Record defaults that already occur in the scoped formula before this
        // pass creates any terms.  A dead `default(x)` manufactured while
        // inspecting an unrelated equality must not make that equality relevant
        // on the next fixpoint round.
        let mut arrays_with_default: HashSet<TermId> = HashSet::default();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if self.term_in_array_scope(term_id) {
                if let Some(array) = self.ctx.terms.get_array_default(term_id) {
                    arrays_with_default.insert(array);
                }
            }
        }

        // Collect array-equality atoms once, then materialize axioms, so we do
        // not iterate over the terms we are appending.
        let mut eq_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            let TermData::App(sym, args) = self.ctx.terms.get(term_id) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            if lhs == rhs {
                continue;
            }
            // This pass scans the append-only term history, which can contain
            // malformed/internal equality applications left by a scoped proof
            // replay. Array-default congruence is defined only for two arrays
            // of the SAME sort. Checking just the lhs let `Array = Bool`
            // reach `mk_array_default(rhs)` (a Bool fallback) and then panic
            // while constructing `Int = Bool`. Such a node is not an array
            // theory atom and must contribute no axiom.
            let lhs_sort = self.ctx.terms.sort(lhs);
            if !matches!(lhs_sort, Sort::Array(_)) || self.ctx.terms.sort(rhs) != lhs_sort {
                continue;
            }
            if seen.insert(term_id) {
                eq_atoms.push((term_id, lhs, rhs));
            }
        }

        for (eq_term, lhs, rhs) in eq_atoms {
            if should_stop() {
                return;
            }
            // Preserve the old useful structural case (const/lambda on either
            // side), and additionally propagate an explicitly relevant default
            // through an array equality class.  Z3's add_parent_default does the
            // latter when an array enode class is merged; without it,
            // `(default a)` plus `a = store(b,i,v)` never reaches the store axiom.
            let lhs_resolved = self.ctx.terms.get_const_array(lhs).is_some()
                || self.ctx.terms.get_lambda_array(lhs).is_some();
            let rhs_resolved = self.ctx.terms.get_const_array(rhs).is_some()
                || self.ctx.terms.get_lambda_array(rhs).is_some();
            if !lhs_resolved
                && !rhs_resolved
                && !arrays_with_default.contains(&lhs)
                && !arrays_with_default.contains(&rhs)
            {
                continue;
            }

            let default_lhs = self.ctx.terms.mk_array_default(lhs);
            let default_rhs = self.ctx.terms.mk_array_default(rhs);
            let default_eq = self.ctx.terms.mk_eq(default_lhs, default_rhs);
            // If the consequent already folded to `true`, the implication is a
            // tautology — adding it is pointless. If it folded to `false`, the
            // implication becomes `¬(= a b)`, the unit clause that refutes the
            // equality.
            if default_eq == self.ctx.terms.true_term() {
                continue;
            }
            let not_eq = self.ctx.terms.mk_not(eq_term);
            let clause = self.ctx.terms.mk_or(vec![not_eq, default_eq]);
            self.push_array_axiom_assertion_site(clause, "array_default_congruence");
        }
    }

    /// Z3 5.0.0 array-default axioms for a store whose default is relevant.
    ///
    /// For `A = store(B, i, v)`, Z3's `theory_array_full.cpp` distinguishes:
    ///
    /// - a unit index carrier: `default(A) = v`;
    /// - a finite carrier smaller than 2^14:
    ///   `default(A) = select(A, epsilon)`,
    ///   `default(B) = select(B, epsilon)`, and
    ///   `select(A, diag(i)) = select(B, diag(i))`;
    /// - every infinite, unknown, very large, or >= 2^14 carrier:
    ///   `default(A) = default(B)`.
    ///
    /// `epsilon` and unary `diag` are shared by INDEX SORT, including across
    /// arrays with different element sorts.  Per-store witnesses are weaker and
    /// observably disagree with Z3 (two Bool-indexed stores can force mutually
    /// incompatible choices).
    /// The array-default choice index for `index_sort`, minting it on first use.
    ///
    /// Z3 shares ONE epsilon per INDEX SORT across every array whose default it
    /// resolves that way — stores and lambdas alike, and across arrays with
    /// different element sorts. Measured against z3 4.15.4: with
    /// `a = (lambda ((x Bool)) (ite x 1 0))` and
    /// `b = (store ((as const (Array Bool Int)) 0) false 5)`, asserting
    /// `(= (default a) 1)` (needs epsilon = true) together with
    /// `(= (default b) 5)` (needs epsilon = false) is UNSAT, while moving the
    /// store to index `true` makes it SAT. A per-array witness would call both
    /// SAT and observably disagree.
    pub(in crate::executor) fn array_default_epsilon_for(&mut self, index_sort: &Sort) -> TermId {
        if let Some(&epsilon) = self.array_default_epsilon_by_sort.get(index_sort) {
            return epsilon;
        }
        let name = self.ctx.terms.mk_internal_symbol("array_default_epsilon");
        let epsilon = self.ctx.terms.mk_var(name, index_sort.clone());
        self.array_default_epsilon_by_sort
            .insert(index_sort.clone(), epsilon);
        epsilon
    }

    pub(in crate::executor) fn add_array_default_store_axioms(&mut self) {
        const Z3_LARGE_ARRAY_DOMAIN_SIZE: usize = 1 << 14;

        let should_stop = self.make_should_stop();
        let mut stores = Vec::new();
        let mut seen = HashSet::default();
        let scan_len = self.ctx.terms.len();
        for idx in 0..scan_len {
            let default_term = TermId(idx as u32);
            if !self.term_in_array_scope(default_term) {
                continue;
            }
            let Some(array) = self.ctx.terms.get_array_default(default_term) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(array).clone() else {
                continue;
            };
            if sym.name() != "store" || args.len() != 3 || !seen.insert(array) {
                continue;
            }
            let Sort::Array(array_sort) = self.ctx.terms.sort(array).clone() else {
                continue;
            };
            stores.push((
                default_term,
                array,
                args[0],
                args[1],
                args[2],
                array_sort.index_sort.clone(),
            ));
        }

        for (default_store, store, base, index, value, index_sort) in stores {
            if should_stop() {
                return;
            }
            match self.sort_finite_cardinality(&index_sort) {
                Some(1) => {
                    let axiom = self.ctx.terms.mk_eq(default_store, value);
                    self.push_array_axiom_assertion_site(axiom, "array_default_store_unit");
                }
                Some(size) if size < Z3_LARGE_ARRAY_DOMAIN_SIZE => {
                    let epsilon = self.array_default_epsilon_for(&index_sort);
                    let diag_name =
                        if let Some(name) = self.array_default_diag_by_sort.get(&index_sort) {
                            name.clone()
                        } else {
                            let name = self.ctx.terms.mk_internal_symbol("array_default_diag");
                            self.array_default_diag_by_sort
                                .insert(index_sort.clone(), name.clone());
                            name
                        };

                    let default_base = self.ctx.terms.mk_array_default(base);
                    let store_at_epsilon = self.ctx.terms.mk_select(store, epsilon);
                    let base_at_epsilon = self.ctx.terms.mk_select(base, epsilon);
                    let default_store_axiom = self.ctx.terms.mk_eq(default_store, store_at_epsilon);
                    let default_base_axiom = self.ctx.terms.mk_eq(default_base, base_at_epsilon);
                    self.push_array_axiom_assertion_site(
                        default_store_axiom,
                        "array_default_store_epsilon",
                    );
                    self.push_array_axiom_assertion_site(
                        default_base_axiom,
                        "array_default_base_epsilon",
                    );

                    // Both axioms above are THEORY-INERT on their own. `epsilon`
                    // is a fresh VARIABLE, so `select(A, epsilon)` is an opaque
                    // EUF application: nothing case-splits epsilon over the
                    // carrier, and — because `mk_select` folds a read at a
                    // CONCRETE index through the store chain by ROW — the terms
                    // `select(A, e)` that congruence would need to merge with do
                    // not even exist in the term store. The candidate model
                    // therefore leaves `default(A)` unconstrained, falsifies the
                    // assertion it was meant to decide, and the strict oracle
                    // fail-closes the whole query to `unknown`.
                    //
                    // Materialize the case split for a SMALL, EXACTLY-ENUMERABLE
                    // carrier: `select_case_split_axioms` emits, per inhabitant
                    // `e`, the congruence instance
                    //     (or (not (= epsilon e)) (= (select A epsilon) (select A e)))
                    // where the right-hand `select(A, e)` folds to a real array
                    // value. See that helper for the soundness argument.
                    self.push_finite_epsilon_case_split(
                        store,
                        store_at_epsilon,
                        epsilon,
                        &index_sort,
                    );
                    self.push_finite_epsilon_case_split(
                        base,
                        base_at_epsilon,
                        epsilon,
                        &index_sort,
                    );

                    let diag_index = self.ctx.terms.mk_app(
                        Symbol::named(diag_name),
                        vec![index],
                        index_sort.clone(),
                    );
                    let store_at_diag = self.ctx.terms.mk_select(store, diag_index);
                    let base_at_diag = self.ctx.terms.mk_select(base, diag_index);
                    let diag_axiom = self.ctx.terms.mk_eq(store_at_diag, base_at_diag);
                    self.push_array_axiom_assertion_site(diag_axiom, "array_default_store_diag");
                }
                _ => {
                    let default_base = self.ctx.terms.mk_array_default(base);
                    let axiom = self.ctx.terms.mk_eq(default_store, default_base);
                    self.push_array_axiom_assertion_site(axiom, "array_default_store_large");
                }
            }
        }
    }

    /// Largest index carrier whose inhabitants are enumerated one-by-one for the
    /// array-default epsilon case split.
    ///
    /// Z3's own epsilon rule applies up to 2^14 inhabitants, but ENUMERATING that
    /// many would add ~16k equality atoms per store. The cap keeps the pass cheap;
    /// exceeding it merely leaves the previous behaviour (the epsilon axioms stay
    /// inert and the query can fail closed to `unknown`) — never a wrong answer.
    /// It is deliberately generous enough for the shapes that actually occur:
    /// `Bool` and small enum datatypes.
    const ARRAY_DEFAULT_EPSILON_CASE_SPLIT_MAX: usize = 16;

    /// Exact inhabitant list of a small finite INDEX `sort`, or `None` when the
    /// sort is not one this pass enumerates.
    ///
    /// Returning `Some` is a claim that the returned terms are the WHOLE carrier,
    /// which the caller relies on to assert a domain-coverage disjunction. Only
    /// sorts with a closed, syntactically-known inhabitant set qualify:
    ///
    /// - `Bool` — exactly `{false, true}`;
    /// - an all-nullary (enum) datatype — exactly its constructor constants, per
    ///   the same argument `add_finite_enum_domain_coverage` documents.
    ///
    /// Everything else returns `None`, on one of two grounds.
    ///
    /// NOT ENUMERABLE (soundness): a sort whose CARDINALITY is known while its
    /// inhabitants are not nameable — `FiniteDomain` — must never be enumerated
    /// here, because a coverage disjunction over a guessed inhabitant set would
    /// not be valid and could fabricate an UNSAT. Likewise `Int`/`Real`,
    /// uninterpreted sorts, arrays, and field-bearing or recursive datatypes.
    ///
    /// NOT NEEDED (measured): `BitVec` is deliberately excluded even though its
    /// `2^w` constants are perfectly enumerable. The bare epsilon axioms already
    /// decide the BV-indexed cases on their own — a BV index equality is an atom
    /// the bit-blaster settles, so `select(A, epsilon)` is already pinned — and
    /// the extra clauses are pure redundancy. Measured on
    /// `(Array (_ BitVec 1) Bool)` and `(Array (_ BitVec 2) Bool)` full-carrier
    /// stores, both of which AY refutes WITHOUT this pass and, with BV
    /// enumeration switched on, degraded to `unknown` (the redundant index
    /// equalities steer the search into a conflict whose Alethe lemma is
    /// mis-attributed as `EufCongruentPred`, and mandatory strict certification
    /// then — correctly, fail-closed — rejects the refutation).
    fn small_finite_sort_inhabitants(&mut self, sort: &Sort) -> Option<Vec<TermId>> {
        match sort {
            Sort::Bool => Some(vec![
                self.ctx.terms.false_term(),
                self.ctx.terms.true_term(),
            ]),
            Sort::BitVec(_) => None,
            _ => {
                let ctors = self.finite_enum_datatype_ctors(sort)?;
                if ctors.is_empty() || ctors.len() > Self::ARRAY_DEFAULT_EPSILON_CASE_SPLIT_MAX {
                    return None;
                }
                Some(
                    ctors
                        .iter()
                        // A nullary constructor constant elaborates to
                        // `mk_var(name, sort)`; building it any other way would
                        // make a term EUF never merges with the real constructor,
                        // leaving the case split theory-inert (see the identical
                        // note in `add_finite_enum_domain_coverage`).
                        .map(|c| self.ctx.terms.mk_var(c.clone(), sort.clone()))
                        .collect(),
                )
            }
        }
    }

    /// Make the array-default `epsilon` read decidable by case-splitting it over
    /// a small, exactly-enumerable index carrier.
    ///
    /// For every inhabitant `e` of `index_sort` this asserts the CONGRUENCE
    /// instance
    ///
    /// ```text
    ///   (or (not (= epsilon e)) (= (select array epsilon) (select array e)))
    /// ```
    ///
    /// together with the domain-coverage disjunction
    /// `(or (= epsilon e_1) … (= epsilon e_n))`.
    ///
    /// `array_at_epsilon` is the already-interned `select(array, epsilon)`; the
    /// per-element `select(array, e)` is built here and, because `e` is concrete,
    /// `mk_select` folds it through the store chain by ROW down to an actual
    /// element value. That is what gives the SAT/EUF layers something to merge
    /// `select(array, epsilon)` with.
    ///
    /// SOUNDNESS: both clause families are VALID in every interpretation.
    ///
    /// - Each implication is a plain instance of functional congruence — if
    ///   `epsilon` and `e` denote the same index then the two reads of the SAME
    ///   array denote the same element. This holds whatever `epsilon` is and does
    ///   not depend on the enumeration being complete.
    /// - The coverage disjunction is valid because `small_finite_sort_inhabitants`
    ///   returns `Some` only for sorts whose domain is EXACTLY the returned terms
    ///   (`Bool`, a fully-enumerated `BitVec`, an all-nullary datatype), so every
    ///   value of that sort equals one of them.
    ///
    /// Adding logically valid clauses removes no models, so this can never turn a
    /// SAT query into UNSAT; it only stops the search from satisfying the epsilon
    /// axiom with an out-of-carrier read. A sort we cannot enumerate is skipped
    /// (incompleteness, never unsoundness).
    fn push_finite_epsilon_case_split(
        &mut self,
        array: TermId,
        array_at_epsilon: TermId,
        epsilon: TermId,
        index_sort: &Sort,
    ) {
        let Some(inhabitants) = self.small_finite_sort_inhabitants(index_sort) else {
            return;
        };
        let mut coverage = Vec::with_capacity(inhabitants.len());
        for element in inhabitants {
            let epsilon_is_element = self.ctx.terms.mk_eq(epsilon, element);
            coverage.push(epsilon_is_element);

            let array_at_element = self.ctx.terms.mk_select(array, element);
            let reads_agree = self.ctx.terms.mk_eq(array_at_epsilon, array_at_element);
            let not_epsilon_is_element = self.ctx.terms.mk_not(epsilon_is_element);
            let instance = self
                .ctx
                .terms
                .mk_or(vec![not_epsilon_is_element, reads_agree]);
            self.push_array_axiom_assertion_site(instance, "array_default_epsilon_case_split");
        }
        if coverage.is_empty() {
            return;
        }
        let cover = self.ctx.terms.mk_or(coverage);
        self.push_array_axiom_assertion_site(cover, "array_default_epsilon_coverage");
    }

    /// Add eager extensionality axioms for array equality atoms.
    ///
    /// For every equality atom `(= a b)` in the term store where a, b have
    /// `Sort::Array(...)`, creates:
    ///   - A fresh Skolem variable `__ay_ext_diff_N` with the array's index sort
    ///   - Select terms `(select a __ay_ext_diff_N)` and `(select b __ay_ext_diff_N)`
    ///   - The extensionality clause: `(= a b) ∨ ¬(= (select a k) (select b k))`
    ///
    /// Freshness makes this a conservative, equisatisfiable extension of the
    /// original array problem (it is not a tautology for an arbitrary fixed
    /// `k`). Adding it before Tseitin encoding gives the SAT solver the atoms
    /// needed to enforce extensionality: if `a ≠ b`, the diff witness differs.
    pub(in crate::executor) fn add_array_extensionality_axioms(&mut self) {
        self.add_array_extensionality_axioms_up_to(self.ctx.terms.len());
    }

    pub(in crate::executor) fn add_array_extensionality_axioms_up_to(
        &mut self,
        negation_scan_limit: usize,
    ) {
        // #8615: Check interrupt/deadline so extensionality axiom generation
        // can be cancelled on long-running array formulas.
        let should_stop = self.make_should_stop();

        let mut top_level_disequalities = self.collect_top_level_disequalities();
        let mut top_level_positive_array_equalities: HashSet<TermId> = HashSet::default();
        let mut select_alias: HashMap<TermId, TermId> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            if matches!(self.ctx.terms.sort(lhs), Sort::Array(_)) {
                top_level_positive_array_equalities.insert(assertion);
            }
            let (var, sel) = match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                (TermData::Var(_, _), TermData::App(sel_sym, sel_args))
                    if sel_sym.name() == "select" && sel_args.len() == 2 =>
                {
                    (lhs, rhs)
                }
                (TermData::App(sel_sym, sel_args), TermData::Var(_, _))
                    if sel_sym.name() == "select" && sel_args.len() == 2 =>
                {
                    (rhs, lhs)
                }
                _ => continue,
            };
            select_alias.entry(var).or_insert(sel);
        }

        // Collect array equality atoms and their negations from the term store.
        // Optimization: only generate extensionality axioms for pairs where
        // ¬(= a b) exists in the term store. If the negation never appears,
        // the solver cannot assert a ≠ b, so extensionality is vacuously
        // satisfied and the Skolem witness is unnecessary. Skipping avoids
        // introducing free variables that cause LIA oscillation (#4304).
        let mut negated_terms: HashSet<TermId> = HashSet::default();
        let mut array_eq_pairs: Vec<(TermId, TermId, TermId, Sort)> = Vec::new();
        let mut selects_by_array: HashMap<TermId, HashMap<TermId, TermId>> = HashMap::default();
        let negation_scan_limit = negation_scan_limit.min(self.ctx.terms.len());
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            match self.ctx.terms.get(term_id).clone() {
                TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];
                    if lhs == rhs {
                        continue;
                    }
                    if let Sort::Array(ref arr_sort) = self.ctx.terms.sort(lhs).clone() {
                        // HISTORY (#qf-ax-nested-guard, retired): extensionality used
                        // to be SKIPPED here whenever a side was an array-valued
                        // `select` (the nested `Array I (Array I E)` read-over-write
                        // `(not (= (select (store n i c) j) (store c i e)))`), because
                        // the eager fixpoint fabricated a wrong-UNSAT on that shape.
                        // That was a NEUTRALIZATION, not a root-cause fix; the actual
                        // cause — the redundant OUTER `__ay_ext_diff` Skolem for the
                        // nested `(n1, n2)` pair, whose index equalities unit-forced a
                        // level-0 conflict against an unrelated index disequality — is
                        // fixed by `nested_array_outer_ext_redundant` below.
                        //
                        // Keeping the skip on top of that fix was purely harmful: with
                        // no extensionality Skolem, an asserted array disequality over
                        // such a pair has NO difference witness in the model, so the
                        // fail-closed `arrays-unwitnessed-diseq` strict-gate degraded
                        // the (correct) `sat` to `unknown`. Generating the axiom
                        // restores the witness; the nested wrong-UNSAT stays fixed at
                        // its real source (see the nested/flat `..._store_ext_...`
                        // gates in group_theory_misc).
                        array_eq_pairs.push((term_id, lhs, rhs, arr_sort.index_sort.clone()));
                    }
                }
                TermData::App(ref sym, ref args) if sym.name() == "select" && args.len() == 2 => {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .entry(args[1])
                        .or_insert(term_id);
                }
                TermData::Not(inner) if idx < negation_scan_limit => {
                    negated_terms.insert(inner);
                }
                _ => {}
            }
        }
        // #8785: SMT-COMP storecomm encodes the explicit extensional witness
        // through aliases:
        //   e_l = select(A, k), e_r = select(B, k), e_l != e_r
        // Treat this as a direct select disequality so extensionality does not
        // fabricate a redundant `__ay_ext_diff_*` for the same array pair.
        let base_diseqs: Vec<(TermId, TermId)> = top_level_disequalities.iter().copied().collect();
        for (a, b) in base_diseqs {
            if let (Some(&sel_a), Some(&sel_b)) = (select_alias.get(&a), select_alias.get(&b)) {
                top_level_disequalities.insert(Self::ordered_term_pair(sel_a, sel_b));
            }
            if let Some(&sel_a) = select_alias.get(&a) {
                top_level_disequalities.insert(Self::ordered_term_pair(sel_a, b));
            }
            if let Some(&sel_b) = select_alias.get(&b) {
                top_level_disequalities.insert(Self::ordered_term_pair(a, sel_b));
            }
        }

        // For each unique array pair with a negation, create extensionality axiom
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for (eq_term, lhs, rhs, _index_sort) in array_eq_pairs {
            // #8615: Check interrupt between extensionality axiom pairs.
            if should_stop() {
                return;
            }
            if !negated_terms.contains(&eq_term) {
                continue;
            }
            // #8785: If the exact array equality atom is already asserted as a
            // top-level positive fact, the extensionality clause
            // `(= a b) OR select(a,k) != select(b,k)` is immediately satisfied.
            // Creating a fresh witness for that inactive clause only expands
            // the AUFLIA search space and can feed repeated exact-select
            // model-equality rounds on storecomm benchmarks.
            if top_level_positive_array_equalities.contains(&eq_term) {
                continue;
            }
            // An active exact finite-array axiom already supplies the full
            // pointwise biconditional for this equality, recursively through
            // every nested array layer. A fresh generic difference Skolem is
            // therefore redundant and can itself expose another symbolic
            // array-cell equality (the historical fourth obligation for a
            // two-level Bool array). Do not infer coverage merely from the
            // sort: a route may not have run exact closure yet, or the query's
            // cumulative budget may have deferred this particular candidate.
            if self.finite_array_equality_has_active_exact_coverage(eq_term) {
                continue;
            }
            let pair = if lhs.0 <= rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            if !seen_pairs.insert(pair) {
                continue; // Already added axiom for this pair
            }

            // Port of Z3's `already_diseq`: when an explicit top-level witness
            // `not (= (select lhs k) (select rhs k))` already exists, do not
            // create a redundant fresh extensionality Skolem for the same pair.
            if self.has_explicit_select_disequality_witness(
                lhs,
                rhs,
                &selects_by_array,
                &top_level_disequalities,
            ) {
                continue;
            }

            // #r3-nested-arrayext wrong-UNSAT: when the equality `(= lhs rhs)` we
            // are about to add extensionality for is over a NESTED array (its
            // value sort is itself an array) AND one of `lhs`/`rhs` is the BASE of
            // a `store` that is itself read by a `select` (the nested
            // store-of-array then selected pattern), the fresh outer `__ay_ext_diff`
            // Skolem is REDUNDANT and HARMFUL: the inner ROW/congruence machinery
            // over the nested store already pins the relevant inner-array index,
            // while the extra outer Skolem generates `(= i2 __ay_ext_diff)`-style
            // index equalities that — combined with an UNRELATED top-level index
            // disequality (e.g. `i0 != i1`) — unit-force a spurious level-0
            // conflict over `select(lhs,__ay_ext_diff) != select(rhs,__ay_ext_diff)`
            // (the #8741 failure mode one array level up). Suppressing this
            // fresh-witness conservative extension is sound: it leaves the
            // original formula unchanged and can only lose refutational
            // completeness. The nested ROW decomposition still closes any
            // genuine nested-array UNSAT.
            //
            // #nested-ext-deep-witness (completeness restoration): plain
            // suppression left the nested pair with NO witness machinery at
            // all, so on the SAT side the model never differentiates the two
            // nested arrays and the strict validation gate correctly refuses
            // to certify the model (Sat degrades to Unknown — the
            // `test_gate_qf_ax_nested_array_store_ext_not_unsat` red). Emit a
            // DEEP extensionality Skolem chain instead: iterate the index
            // sorts down to the first NON-array element sort and assert
            //   (= lhs rhs) ∨ ¬(= lhs[k1]..[kn] rhs[k1]..[kn])
            // with fresh Skolems k1..kn. Equisatisfiable by n applications of
            // extensionality (if lhs != rhs, some index path witnesses an
            // element-level difference), and the disequality literal now lives
            // at the ELEMENT sort, not the array sort — so the `(= i2 k)`
            // index-equality interplay cannot unit-force the #8741 array-level
            // spurious conflict the suppressed OUTER Skolem caused.
            if self.nested_array_outer_ext_redundant(lhs, rhs) {
                let mut sel_a = lhs;
                let mut sel_b = rhs;
                let mut level = 0usize;
                let mut witness_failed = false;
                let mut witness_bindings = Vec::new();
                while let Sort::Array(arr) = self.ctx.terms.sort(sel_a).clone() {
                    let Some(diff_var) = deep_array_extensionality_witness(
                        &mut self.ctx.terms,
                        &mut self.array_ext_witness_cache,
                        lhs,
                        rhs,
                        level,
                        arr.index_sort.clone(),
                    ) else {
                        // A reserved-name sort collision can only come from an
                        // internal invariant violation. Skip the optional axiom
                        // rather than constructing a wrong-sorted witness.
                        witness_failed = true;
                        break;
                    };
                    witness_bindings.push(ArrayExtWitnessBinding {
                        witness: diff_var,
                        array_a: sel_a,
                        array_b: sel_b,
                    });
                    sel_a = self.ctx.terms.mk_select(sel_a, diff_var);
                    sel_b = self.ctx.terms.mk_select(sel_b, diff_var);
                    level += 1;
                    if level > 8 {
                        // Defensive depth cap; array sorts this deep do not
                        // occur in practice. Falling out mid-chain is still
                        // sound: the truncated fresh-witness chain remains a
                        // conservative, equisatisfiable extension.
                        break;
                    }
                }
                if witness_failed {
                    continue;
                }
                let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);
                let not_sel_eq = self.ctx.terms.mk_not(sel_eq);
                let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);
                self.array_ext_witness_cache.record_generated_clause(
                    &self.ctx.terms,
                    ext_clause,
                    witness_bindings,
                );
                self.push_array_axiom_assertion_site(ext_clause, "deep_ext_axiom");
                self.array_ext_shadow.record(eq_term, lhs, rhs, not_sel_eq);
                continue;
            }

            // Create/reuse the reserved Skolem with the array's index sort.
            let Some(diff_var) = array_extensionality_witness(
                &mut self.ctx.terms,
                &mut self.array_ext_witness_cache,
                lhs,
                rhs,
            ) else {
                continue;
            };

            // Create select(a, diff) and select(b, diff)
            let sel_a = self.ctx.terms.mk_select(lhs, diff_var);
            let sel_b = self.ctx.terms.mk_select(rhs, diff_var);

            // Create (= (select a diff) (select b diff))
            let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);

            // Create ¬(= (select a diff) (select b diff))
            let not_sel_eq = self.ctx.terms.mk_not(sel_eq);

            // Create extensionality clause: (= a b) ∨ ¬(= (select a diff) (select b diff))
            let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);
            self.array_ext_witness_cache.record_generated_clause(
                &self.ctx.terms,
                ext_clause,
                vec![ArrayExtWitnessBinding {
                    witness: diff_var,
                    array_a: lhs,
                    array_b: rhs,
                }],
            );

            // Add the fresh-witness conservative extension as an assertion.
            self.push_array_axiom_assertion_site(ext_clause, "ext_axiom");

            // D1 shadow (lazy-extensionality campaign): record this EAGER witness
            // so the finalizer can correlate it against the DEMANDED set (pairs
            // whose `(= a b)` atom the search actually forced false). Measurement
            // only — the eager emission above stays authoritative.
            self.array_ext_shadow.record(eq_term, lhs, rhs, not_sel_eq);

            // #qfax-ext-row-seed: eagerly materialize the ROW unrolling of the
            // extensionality witness down BOTH store chains. The lazy Row2Down
            // machinery blocks forever when the inner select(base, diff) term
            // or the (= diff i) atom does not already exist (axiom_checkers.rs
            // keeps the pending axiom in `remaining` with 0 array conflicts,
            // and the wrong model is rejected fail-closed -> unknown on the
            // whole swap_t/storeinv_t _np_ unsat families). Each level adds
            // two guarded ROW instances at the witness index — pure array
            // tautologies, linear in chain depth:
            //   (= diff i)  ∨ (= (select (store b i v) diff) (select b diff))
            //   ¬(= diff i) ∨ (= (select (store b i v) diff) v)
            // Measured: fires (75 levels on swap_t1_np_nf_00007_004) but does
            // NOT yet convert the family — the QF_AX route's arrays checkers
            // still degrade via the strict oracle; the transitive select-value
            // chain the seed creates needs e-graph closure the checker-based
            // route lacks. Kept OPT-IN for the follow-up interplay work.
            if ay_core::misc_cli_flags().ext_row_seed {
                for side in [lhs, rhs] {
                    let mut t = side;
                    let mut depth = 0usize;
                    while depth < 24 {
                        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
                            break;
                        };
                        if sym.name() != "store" || args.len() != 3 {
                            break;
                        }
                        let (b, i, v) = (args[0], args[1], args[2]);
                        let sel_outer = self.ctx.terms.mk_select(t, diff_var);
                        let sel_inner = self.ctx.terms.mk_select(b, diff_var);
                        let idx_eq = self.ctx.terms.mk_eq(diff_var, i);
                        let not_idx_eq = self.ctx.terms.mk_not(idx_eq);
                        let row1 = {
                            let eq = self.ctx.terms.mk_eq(sel_outer, sel_inner);
                            self.ctx.terms.mk_or(vec![idx_eq, eq])
                        };
                        let row2 = {
                            let eq = self.ctx.terms.mk_eq(sel_outer, v);
                            self.ctx.terms.mk_or(vec![not_idx_eq, eq])
                        };
                        self.push_array_axiom_assertion_site(row1, "ext_row_seed");
                        self.push_array_axiom_assertion_site(row2, "ext_row_seed");
                        if ay_core::misc_cli_flags().debug_row_seed {
                            eprintln!(
                                "[row-seed] level depth={depth} side={} store={}",
                                side.0, t.0
                            );
                        }
                        t = b;
                        depth += 1;
                    }
                }
            }
        }
    }

    /// Store base decomposition axioms (#6282).
    ///
    /// For every pair of array-sorted terms X, Y where X = store(A, i, v1)
    /// and Y = store(B, j, v2) (either directly or via asserted equalities),
    /// adds axioms that decompose a potential X = Y into base equality:
    ///
    ///   `¬(= X Y) ∨ (= i diff_AB) ∨ (= j diff_AB) ∨ (= A B)`
    ///   `(= A B) ∨ ¬(= select(A, diff_AB) select(B, diff_AB))`
    ///
    /// This covers both direct store-store equalities and the transitive case
    /// where X and Y are variables equal to stores (e.g., `v6 = store(v4, i4, ...)`
    /// and `v7 = store(v5, i4, ...)`). When X = Y is asserted or derived during
    /// search, the decomposition axiom forces A = B or the diff is at a stored index.
    ///
    /// This enables the storeinv proof chain: from top-level store equality,
    /// propagate down through nested store layers to reach `a1 = a2`, which
    /// contradicts the Skolem witness of difference.
    pub(in crate::executor) fn add_store_store_base_decomposition_axioms(&mut self) {
        // #8615: Check interrupt/deadline so store decomposition axiom
        // generation can be cancelled on long-running array formulas.
        let should_stop = self.make_should_stop();

        // #8741: Port of Z3's `theory_array_base::already_diseq` gate from
        // `reference/z3/src/smt/theory_array_base.cpp:274`. If an explicit
        // select-disequality witness `(not (= (select a k) (select b k)))`
        // already pins down an index where (a, b) differ, do NOT fabricate
        // a fresh store-base decomposition Skolem — the existing witness
        // already decomposes the equality. Introducing a parallel Skolem
        // plus the decomp clause combines with array-congruence-store
        // chains to unit-force both `(= i1 __ay_ext_diff)` and
        // `(= i2 __ay_ext_diff)` at level 0, collapsing to spurious UNSAT
        // on satisfiable formulas like the #8741 minimal repro.
        let top_level_disequalities = self.collect_top_level_disequalities();
        let mut selects_by_array: HashMap<TermId, HashMap<TermId, TermId>> = HashMap::default();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term_id).clone() {
                if sym.name() == "select" && args.len() == 2 {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .entry(args[1])
                        .or_insert(term_id);
                }
            }
        }

        // Phase 1: collect every (variable/term, store_base, store_index) triple
        // from equalities `(= X store(A, i, v))` in the term store.
        // Also collect direct store-store equalities.
        struct StoreInfo {
            /// The "named" side (X in X = store(A,i,v), or the store term itself)
            named: TermId,
            base: TermId,
            idx: TermId,
            /// The defining equality `(= X store(A,i,v))` when `named` is an
            /// ALIAS of the store (None when `named` IS the store term).
            /// #qfax-sbd-guard: Phase 1 harvests equalities from the WHOLE term
            /// store, including hypothetical literals inside earlier fixpoint
            /// clauses that are never asserted. A Phase-2b decomposition built
            /// from an alias is only entailed GIVEN its defining equalities, so
            /// the emitted clause must carry ¬def as a guard literal — without
            /// it the clause is a non-tautology and produced FALSE UNSATs on
            /// the :status-sat swap/storeinv `_invalid_` families (z3-checked:
            /// the unguarded t39/t60 clauses are not entailed; the guarded
            /// ones are).
            def_eq: Option<TermId>,
        }

        // Map from store index (as a TermId) to all StoreInfos with that index.
        // We group by store index because base decomposition only links stores
        // at the same index (or includes both index disjuncts).
        let mut store_infos: Vec<StoreInfo> = Vec::new();

        // Also track existing store-store equalities for direct decomposition.
        struct DirectStoreStoreEq {
            eq_term: TermId,
            base_a: TermId,
            idx_a: TermId,
            base_b: TermId,
            idx_b: TermId,
        }
        let mut direct_eqs: Vec<DirectStoreStoreEq> = Vec::new();

        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term_id).clone() {
                if sym.name() == "=" && args.len() == 2 {
                    let lhs = args[0];
                    let rhs = args[1];
                    if lhs == rhs {
                        continue;
                    }
                    let lhs_store = match self.ctx.terms.get(lhs).clone() {
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3 => {
                            Some((a[0], a[1]))
                        }
                        _ => None,
                    };
                    let rhs_store = match self.ctx.terms.get(rhs).clone() {
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3 => {
                            Some((a[0], a[1]))
                        }
                        _ => None,
                    };

                    match (lhs_store, rhs_store) {
                        (Some((base_a, idx_a)), Some((base_b, idx_b))) => {
                            if base_a != base_b {
                                direct_eqs.push(DirectStoreStoreEq {
                                    eq_term: term_id,
                                    base_a,
                                    idx_a,
                                    base_b,
                                    idx_b,
                                });
                            }
                            // Both sides are stores — record both with their
                            // "named" side as the store term itself (no alias
                            // guard needed: `named = store(...)` is reflexive).
                            store_infos.push(StoreInfo {
                                named: lhs,
                                base: base_a,
                                idx: idx_a,
                                def_eq: None,
                            });
                            store_infos.push(StoreInfo {
                                named: rhs,
                                base: base_b,
                                idx: idx_b,
                                def_eq: None,
                            });
                        }
                        (Some((base, store_idx)), None) => {
                            // (= store(A,i,v) X) — record X as named, guarded
                            // by this defining equality (#qfax-sbd-guard).
                            store_infos.push(StoreInfo {
                                named: rhs,
                                base,
                                idx: store_idx,
                                def_eq: Some(term_id),
                            });
                        }
                        (None, Some((base, store_idx))) => {
                            // (= X store(A,i,v)) — record X as named, guarded
                            // by this defining equality (#qfax-sbd-guard).
                            store_infos.push(StoreInfo {
                                named: lhs,
                                base,
                                idx: store_idx,
                                def_eq: Some(term_id),
                            });
                        }
                        (None, None) => {}
                    }
                }
            }
        }

        // Phase 2: for each pair of StoreInfos with the same store index,
        // where the named sides are different, create a conditional base
        // decomposition axiom:
        //   ¬(= named_X named_Y) ∨ (= idx diff_AB) ∨ (= A B)
        //
        // This fires when X = Y becomes true (asserted or propagated).
        let mut seen_base_pairs: HashSet<(TermId, TermId)> = HashSet::default();

        // #8741: Pre-compute base pairs that already have an explicit
        // select-disequality witness — these get no new decomposition
        // (see `already_diseq` gate above).
        let has_explicit_witness_for_base_pair =
            |base_a: TermId, base_b: TermId, exec: &Self| -> bool {
                exec.has_explicit_select_disequality_witness(
                    base_a,
                    base_b,
                    &selects_by_array,
                    &top_level_disequalities,
                )
            };
        let mut skolem_diseq_cache: HashMap<(TermId, TermId), bool> = HashMap::default();
        for dse in &direct_eqs {
            let base_pair = if dse.base_a.0 <= dse.base_b.0 {
                (dse.base_a, dse.base_b)
            } else {
                (dse.base_b, dse.base_a)
            };
            skolem_diseq_cache.entry(base_pair).or_insert_with(|| {
                has_explicit_witness_for_base_pair(base_pair.0, base_pair.1, self)
            });
        }
        for si in &store_infos {
            for sj in &store_infos {
                if si.base == sj.base {
                    continue;
                }
                let base_pair = if si.base.0 <= sj.base.0 {
                    (si.base, sj.base)
                } else {
                    (sj.base, si.base)
                };
                skolem_diseq_cache.entry(base_pair).or_insert_with(|| {
                    has_explicit_witness_for_base_pair(base_pair.0, base_pair.1, self)
                });
            }
        }

        // Helper: creates extensionality + decomposition for a base pair.
        // Returns true if new axioms were added.
        let terms = &mut self.ctx.terms;
        let assertions = &mut self.ctx.assertions;
        let witness_cache = &mut self.array_ext_witness_cache;

        let mut add_decomp =
            |named_x: TermId,
             named_y: TermId,
             idx_a: TermId,
             idx_b: TermId,
             base_a: TermId,
             base_b: TermId,
             eq_term: Option<TermId>,
             def_eq_x: Option<TermId>,
             def_eq_y: Option<TermId>,
             seen: &mut HashSet<(TermId, TermId)>,
             skolem_cache: &HashMap<(TermId, TermId), bool>| {
                // Mixed array sorts can share the same store index term in one
                // formula (for example Array Int Bool and Array Int Int on the same
                // symbolic index). Store decomposition only applies to same-sorted
                // array pairs; otherwise mk_eq/select would fabricate cross-sort
                // terms and panic (#1753 / model-checker-consumer mixed-array benchmark).
                if terms.sort(base_a) != terms.sort(base_b)
                    || terms.sort(idx_a) != terms.sort(idx_b)
                {
                    return;
                }
                if eq_term.is_none() && terms.sort(named_x) != terms.sort(named_y) {
                    return;
                }

                let base_pair = if base_a.0 <= base_b.0 {
                    (base_a, base_b)
                } else {
                    (base_b, base_a)
                };

                // #8741: Skip this pair when an explicit select-disequality
                // witness already exists (Z3's already_diseq gate). The
                // existing witness makes the fresh Skolem redundant and
                // harmful — see function-level comment.
                if skolem_cache.get(&base_pair).copied().unwrap_or(false) {
                    return;
                }

                // Create or get the (= named_x named_y) equality term.
                let xy_eq = eq_term.unwrap_or_else(|| terms.mk_eq(named_x, named_y));
                let not_xy_eq = terms.mk_not(xy_eq);

                // Create extensionality Skolem for the base pair (once per pair).
                if let Sort::Array(_) = terms.sort(base_a).clone() {
                    // Reuse the cache-owned extensionality witness for the same
                    // base-array pair instead of introducing a parallel store-base
                    // decomposition witness. This keeps the array proof search on a
                    // single distinguishing index for `(base_a, base_b)` (#6282).
                    let Some(diff_var) = array_extensionality_witness(
                        terms,
                        witness_cache,
                        base_pair.0,
                        base_pair.1,
                    ) else {
                        return;
                    };
                    let base_eq = terms.mk_eq(base_a, base_b);

                    if seen.insert(base_pair) {
                        // First time: add extensionality axiom for (A, B).
                        let sel_a = terms.mk_select(base_a, diff_var);
                        let sel_b = terms.mk_select(base_b, diff_var);
                        let sel_eq = terms.mk_eq(sel_a, sel_b);
                        let not_sel_eq = terms.mk_not(sel_eq);
                        let ext_axiom = terms.mk_or(vec![base_eq, not_sel_eq]);
                        witness_cache.record_generated_clause(
                            terms,
                            ext_axiom,
                            vec![ArrayExtWitnessBinding {
                                witness: diff_var,
                                array_a: base_a,
                                array_b: base_b,
                            }],
                        );
                        if ay_core::debug_channel_active(ay_core::DebugChannel::ArrayAxiomSite) {
                            eprintln!(
                                "[array_axiom] site=sbd_ext axiom=#{} data={:?}",
                                ext_axiom.0,
                                terms.get(ext_axiom)
                            );
                        }
                        assertions.push(ext_axiom);
                    }

                    // Decomposition:
                    //   [¬def_x ∨ ¬def_y ∨] ¬(= X Y) ∨ (= idx_a diff) ∨ [opt: (= idx_b diff)] ∨ (= A B)
                    // #qfax-sbd-guard: the alias guards make the clause a
                    // theory-valid consequence of the alias definitions and
                    // the fresh-witness extensionality constraint;
                    // they resolve away when the defining equalities are
                    // asserted top-level units (the storeinv/swap `_sf_`
                    // benchmarks), preserving the intended refutations.
                    let mut decomp_lits = vec![not_xy_eq];
                    for def in [def_eq_x, def_eq_y].into_iter().flatten() {
                        if def != xy_eq {
                            decomp_lits.push(terms.mk_not(def));
                        }
                    }
                    let idx_a_eq_diff = terms.mk_eq(idx_a, diff_var);
                    decomp_lits.push(idx_a_eq_diff);
                    if idx_a != idx_b {
                        let idx_b_eq_diff = terms.mk_eq(idx_b, diff_var);
                        decomp_lits.push(idx_b_eq_diff);
                    }
                    decomp_lits.push(base_eq);
                    let decomp_axiom = terms.mk_or(decomp_lits);
                    if ay_core::debug_channel_active(ay_core::DebugChannel::ArrayAxiomSite) {
                        eprintln!(
                            "[array_axiom] site=sbd_decomp axiom=#{} data={:?}",
                            decomp_axiom.0,
                            terms.get(decomp_axiom)
                        );
                    }
                    assertions.push(decomp_axiom);
                }
            };

        // Phase 2a: handle direct store-store equalities.
        for dse in &direct_eqs {
            if should_stop() {
                return;
            }
            add_decomp(
                dse.eq_term, // not used as named, but we pass eq_term directly
                dse.eq_term, // dummy
                dse.idx_a,
                dse.idx_b,
                dse.base_a,
                dse.base_b,
                Some(dse.eq_term),
                None,
                None,
                &mut seen_base_pairs,
                &skolem_diseq_cache,
            );
        }

        // Phase 2b: handle transitive pairs — variables equal to stores at the
        // same index. For each pair (si, sj) where si.idx == sj.idx and
        // si.named != sj.named, add decomposition.
        // Group by index for efficiency.
        let mut by_index: HashMap<TermId, Vec<usize>> = HashMap::default();
        for (i, si) in store_infos.iter().enumerate() {
            by_index.entry(si.idx).or_default().push(i);
        }
        for (_idx, group) in &by_index {
            if should_stop() {
                return;
            }
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    let si = &store_infos[group[i]];
                    let sj = &store_infos[group[j]];
                    // Skip if same named side or same base
                    if si.named == sj.named || si.base == sj.base {
                        continue;
                    }
                    add_decomp(
                        si.named,
                        sj.named,
                        si.idx,
                        sj.idx,
                        si.base,
                        sj.base,
                        None,
                        si.def_eq,
                        sj.def_eq,
                        &mut seen_base_pairs,
                        &skolem_diseq_cache,
                    );
                }
            }
        }
    }

    /// Index-guided witness ROW unroll for storeinv/swap store-chain proofs
    /// (#perf1-storeinv, #perf5-qfax-storeinv).
    ///
    /// The QF_AX/QF_AUFLIA storeinv/swap families assert (dis)equalities between
    /// deep nested store chains plus a difference witness (an explicit
    /// select-disequality, or a raw array disequality whose extensionality
    /// Skolem fabricates one). The decisive refutation reads BOTH chains at the
    /// witness index `d` and case-splits on `d = i_m` per store level:
    ///
    ///   ¬(= d i) ∨ (= (select (store Y i v) d) v)            [ROW1 at d]
    ///     (= d i) ∨ (= (select (store Y i v) d) (select Y d)) [ROW2 at d]
    ///
    /// In the `d = i_m` branch the stored value `v` is itself a syntactic
    /// `select(other_chain, i_m)` term, and EUF congruence (`d = i_m`) merges it
    /// with the already-instantiated `select(other_chain, d)`, so the unroll
    /// continues down the other chain WITHOUT instantiating at any additional
    /// index. Total surface: 2 clauses × (chain nodes) × (witness indices) —
    /// linear in chain depth, no blind index-pair enumeration.
    ///
    /// This replaces (via the `has_storeinv_witness` suppression in
    /// `run_array_axiom_fixpoint_at_plan`) the previous eager-ROW2b +
    /// store-base-decomposition budget-scaled machinery on exactly this shape,
    /// whose unfocused O(n²) clause surface made the CDCL search cost double per
    /// chain level (storeinv_nf_size9: 6.1s) and exhausted the lazy budgets on
    /// the raw-diseq QF_AX variants (unknown).
    ///
    /// SOUNDNESS: every clause added is either
    ///   (a) a guarded read-over-write instance — a genuine array-theory
    ///       tautology; or
    ///   (b) the standard extensionality skolemization
    ///       `(= A B) ∨ ¬(= (select A d) (select B d))` with the pair's
    ///       same cache-owned current-query witness used by
    ///       `add_array_extensionality_axioms` (one identity per pair).
    /// ROW tautologies and fresh-witness extensionality preserve satisfiability in
    /// both directions, so this pass can NEVER flip a genuine sat to unsat
    /// (the `storeinv_invalid_*`/`swap_invalid_*` `:status sat` siblings stay
    /// sat) nor a genuine unsat to sat.
    ///
    /// Fires only when the chain+witness shape is present: a top-level array
    /// (dis)equality with a store-nesting depth >= 2 side, AND at least one
    /// witness index. Returns `true` iff the full (untruncated) instantiation
    /// was emitted — callers may then suppress the legacy eager-ROW2b path;
    /// on truncation the legacy path stays on (fail-open to old behavior).
    pub(in crate::executor) fn add_witness_guided_chain_row_axioms(&mut self) -> bool {
        const MAX_WITNESSES: usize = 8;
        const MAX_CHAIN_DEPTH: usize = 64;
        const MAX_CLAUSES: usize = 4096;

        // Phase 1: scan TOP-LEVEL assertions only (never the raw term store —
        // hypothetical literals inside clauses must not seed the unroll).
        let mut pos_chain_eqs: Vec<(TermId, TermId)> = Vec::new();
        let mut neg_array_eqs: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut plain_diseq_pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut select_alias: HashMap<TermId, TermId> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            match self.ctx.terms.get(assertion) {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    let (lhs, rhs) = (args[0], args[1]);
                    if lhs == rhs {
                        continue;
                    }
                    if matches!(self.ctx.terms.sort(lhs), Sort::Array(_))
                        && self.is_store_term(lhs)
                        && self.is_store_term(rhs)
                    {
                        pos_chain_eqs.push((lhs, rhs));
                    }
                    // Alias `v = (select A k)` — SMT-COMP storeinv/storecomm
                    // route the witness disequality through element aliases.
                    let (var, sel) = match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                        (TermData::Var(_, _), TermData::App(s2, a2))
                            if s2.name() == "select" && a2.len() == 2 =>
                        {
                            (lhs, rhs)
                        }
                        (TermData::App(s2, a2), TermData::Var(_, _))
                            if s2.name() == "select" && a2.len() == 2 =>
                        {
                            (rhs, lhs)
                        }
                        _ => continue,
                    };
                    select_alias.entry(var).or_insert(sel);
                }
                TermData::Not(inner) => {
                    let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                        continue;
                    };
                    if sym.name() != "=" || args.len() != 2 || args[0] == args[1] {
                        continue;
                    }
                    if matches!(self.ctx.terms.sort(args[0]), Sort::Array(_)) {
                        neg_array_eqs.push((*inner, args[0], args[1]));
                    } else {
                        plain_diseq_pairs.push((args[0], args[1]));
                    }
                }
                _ => {}
            }
        }

        // Fire condition: a deep (>= 2 levels on some side) chain (dis)equality.
        let deep_pos = pos_chain_eqs
            .iter()
            .any(|&(s, t)| self.store_nesting_depth(s).max(self.store_nesting_depth(t)) >= 2);
        let deep_neg = neg_array_eqs
            .iter()
            .any(|&(_, a, b)| self.store_nesting_depth(a).max(self.store_nesting_depth(b)) >= 2);
        if !deep_pos && !deep_neg {
            return false;
        }

        // Phase 2: collect store-chain nodes (X = store(Y, i, v)) reachable
        // along the store spine of every chain-shaped (dis)equality side.
        // (Runs BEFORE witness creation so the storecomm gate below can bail
        // out without having pushed any clause.)
        let mut nodes: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut seen_nodes: HashSet<TermId> = HashSet::default();
        let mut chain_roots: Vec<TermId> = Vec::new();
        for &(s, t) in &pos_chain_eqs {
            chain_roots.push(s);
            chain_roots.push(t);
        }
        for &(_, a, b) in &neg_array_eqs {
            chain_roots.push(a);
            chain_roots.push(b);
        }
        for root in chain_roots {
            let mut cur = root;
            for _ in 0..MAX_CHAIN_DEPTH {
                let TermData::App(sym, args) = self.ctx.terms.get(cur) else {
                    break;
                };
                if sym.name() != "store" || args.len() != 3 {
                    break;
                }
                let (y, i, v) = (args[0], args[1], args[2]);
                if seen_nodes.insert(cur) {
                    nodes.push((cur, y, i, v));
                }
                cur = y;
            }
        }
        if nodes.is_empty() {
            return false;
        }

        // storecomm gate: when the ONLY chain-shaped fact is a NEGATED chain
        // equality (no positive chain identity), require some chain node to
        // store a SELECT value — directly (`_nf_`, let-inlined) or through a
        // top-level element alias `(= e_k (select …))` (the `_sf_` store-flat
        // encoding) — the swap/storeinv cross-read signature whose upward
        // propagation the lazy ArraySolver misses (baseline: unknown).
        // storecomm chains store FREE element constants (zero `select`
        // occurrences in the whole file, so neither arm can match); the
        // existing lazy machinery already solves that family fast
        // (t1_np_nf_00030: 0.05s), and firing here measurably regressed it
        // (0.05s → 1.9s) for zero verdict gain.
        let stores_select_value = nodes.iter().any(|&(_, _, _, v)| {
            matches!(self.ctx.terms.get(v),
                     TermData::App(s, a) if s.name() == "select" && a.len() == 2)
                || select_alias.contains_key(&v)
        });
        if pos_chain_eqs.is_empty() && !stores_select_value {
            return false;
        }

        // Phase 3: witness indices.
        let mut witnesses: Vec<TermId> = Vec::new();
        let push_witness = |w: TermId, witnesses: &mut Vec<TermId>| {
            if !witnesses.contains(&w) && witnesses.len() < MAX_WITNESSES {
                witnesses.push(w);
            }
        };
        // (a) explicit select-disequality witnesses (direct or via aliases).
        for &(u, v) in &plain_diseq_pairs {
            let resolve = |t: TermId, this: &Self| -> Option<(TermId, TermId)> {
                this.select_args(t)
                    .or_else(|| select_alias.get(&t).and_then(|&s| this.select_args(s)))
            };
            let (Some((_, ku)), Some((_, kv))) = (resolve(u, self), resolve(v, self)) else {
                continue;
            };
            push_witness(ku, &mut witnesses);
            push_witness(kv, &mut witnesses);
        }
        // (b) extensionality Skolems for top-level array disequalities. Reuse
        // the cache-owned per-pair witness so the axiom generator and this
        // pass agree on ONE distinguishing index per pair.
        for &(eq_term, a, b) in &neg_array_eqs {
            let Sort::Array(_) = self.ctx.terms.sort(a).clone() else {
                continue;
            };
            if self.ctx.terms.sort(a) != self.ctx.terms.sort(b) {
                continue;
            }
            let Some(diff_var) = array_extensionality_witness(
                &mut self.ctx.terms,
                &mut self.array_ext_witness_cache,
                a,
                b,
            ) else {
                continue;
            };
            let sel_a = self.ctx.terms.mk_select(a, diff_var);
            let sel_b = self.ctx.terms.mk_select(b, diff_var);
            let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);
            let not_sel_eq = self.ctx.terms.mk_not(sel_eq);
            let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);
            self.array_ext_witness_cache.record_generated_clause(
                &self.ctx.terms,
                ext_clause,
                vec![ArrayExtWitnessBinding {
                    witness: diff_var,
                    array_a: a,
                    array_b: b,
                }],
            );
            self.push_array_axiom_assertion_site(ext_clause, "witness_row_ext");
            push_witness(diff_var, &mut witnesses);
        }
        if witnesses.is_empty() {
            return false;
        }

        // Phase 3b (swap shape ONLY): chain store indices join the
        // relevant-index set. The swap `_np_nf_` chains CROSS-store their
        // values (`select(?v, i0)` is stored at index `i2`), so a `d = i2`
        // branch exposes a select at `i0` that is NOT congruent to any
        // `select(_, d)` — reducing it needs ROW instances at `i0` itself.
        // Store indices coincide with the syntactic select indices in these
        // families, so this is the audit's RelevantIdx = {syntactic select
        // indices} ∪ {witness indices}.
        //
        // Scope: only when there is NO positive chain equality. The storeinv
        // shape (positive store-store identity + base diseq) refutes with the
        // witness index ALONE — its stored values are selects at the SAME
        // level index, so the `d = i_m` branch closes by congruence — and
        // adding the chain indices there measurably regresses it (size8
        // 0.07s → 8.2s). The swap shape (negated chain equality only) needs
        // them. Witnesses keep priority; chain indices are dropped wholesale
        // if they would blow the cap (fall back to witness-only).
        const MAX_CHAIN_INDICES: usize = 24;
        let mut relevant_indices: Vec<TermId> = witnesses.clone();
        if pos_chain_eqs.is_empty() {
            let mut chain_indices: Vec<TermId> = Vec::new();
            for &(_, _, i, _) in &nodes {
                if !chain_indices.contains(&i) && !relevant_indices.contains(&i) {
                    chain_indices.push(i);
                }
            }
            if chain_indices.len() <= MAX_CHAIN_INDICES {
                relevant_indices.extend(chain_indices);
            }
        }

        // Phase 4: instantiate both ROW directions at every relevant index.
        let mut clauses = 0_usize;
        let mut truncated = false;
        'outer: for &(x, y, i, v) in &nodes {
            let Sort::Array(arr) = self.ctx.terms.sort(x).clone() else {
                continue;
            };
            for &d in &relevant_indices {
                if *self.ctx.terms.sort(d) != arr.index_sort {
                    continue;
                }
                if clauses + 2 > MAX_CLAUSES {
                    truncated = true;
                    break 'outer;
                }
                let eq_di = self.ctx.terms.mk_eq(d, i);
                let not_eq_di = self.ctx.terms.mk_not(eq_di);
                let sel_xd = self.ctx.terms.mk_select(x, d);
                let sel_yd = self.ctx.terms.mk_select(y, d);
                let row1 = {
                    let eq = self.ctx.terms.mk_eq(sel_xd, v);
                    self.ctx.terms.mk_or(vec![not_eq_di, eq])
                };
                let row2 = {
                    let eq = self.ctx.terms.mk_eq(sel_xd, sel_yd);
                    self.ctx.terms.mk_or(vec![eq_di, eq])
                };
                self.push_array_axiom_assertion_site(row1, "witness_row1");
                self.push_array_axiom_assertion_site(row2, "witness_row2");
                clauses += 2;
            }
        }
        if ay_core::misc_cli_flags().debug_wgr {
            eprintln!(
                "[wgr-dbg] fired: nodes={} witnesses={} relevant={} clauses={} truncated={} pos_chain_eqs={} neg_array_eqs={}",
                nodes.len(),
                witnesses.len(),
                relevant_indices.len(),
                clauses,
                truncated,
                pos_chain_eqs.len(),
                neg_array_eqs.len(),
            );
        }
        clauses > 0 && !truncated
    }
}

#[cfg(test)]
mod singleton_sort_closure_tests {
    use super::*;
    use crate::executor_types::UnknownReason;
    use ay_core::time::Instant;
    use ay_frontend::parse;
    use std::time::Duration;

    fn register_singleton_datatype(exec: &mut Executor) {
        let commands = parse("(declare-datatype D1 ((c)))").expect("parse singleton datatype");
        assert!(exec
            .execute_all(&commands)
            .expect("register singleton datatype")
            .is_empty());
    }

    fn singleton_sort() -> Sort {
        Sort::Uninterpreted("D1".to_string())
    }

    /// Three same-sort roots require exactly a two-edge star. Re-running the
    /// pass must be idempotent rather than growing duplicate assertions.
    #[test]
    fn ground_singleton_closure_is_linear_deterministic_and_idempotent() {
        let mut exec = Executor::new();
        register_singleton_datatype(&mut exec);
        let sort = singleton_sort();
        let a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("a"), vec![], sort.clone());
        let b = exec
            .ctx
            .terms
            .mk_app(Symbol::named("b"), vec![], sort.clone());
        let c = exec.ctx.terms.mk_app(Symbol::named("c2"), vec![], sort);
        let roots = [a, b, c];

        assert_eq!(
            exec.add_ground_singleton_sort_equalities(&roots),
            SingletonSortClosureStatus::Complete
        );
        assert_eq!(exec.ctx.assertions.len(), 2, "n roots need n - 1 facts");

        let mut pairs = Vec::new();
        for &assertion in &exec.ctx.assertions {
            let TermData::App(sym, args) = exec.ctx.terms.get(assertion) else {
                panic!("singleton closure emitted a non-application");
            };
            assert_eq!(sym.name(), "=");
            assert_eq!(args.len(), 2);
            pairs.push((args[0], args[1]));
        }
        pairs.sort_unstable_by_key(|&(lhs, rhs)| (lhs.0, rhs.0));
        assert_eq!(pairs, vec![(a, b), (a, c)]);

        assert_eq!(
            exec.add_ground_singleton_sort_equalities(&roots),
            SingletonSortClosureStatus::Complete
        );
        assert_eq!(
            exec.ctx.assertions.len(),
            2,
            "repeated closure must not duplicate facts"
        );
    }

    /// Bound variables must never escape into a generated ground equality.
    #[test]
    fn singleton_closure_does_not_descend_into_quantifiers() {
        let mut exec = Executor::new();
        register_singleton_datatype(&mut exec);
        let sort = singleton_sort();
        let bound = exec.ctx.terms.mk_var("x", sort.clone());
        let ctor = exec
            .ctx
            .terms
            .mk_app(Symbol::named("c"), vec![], sort.clone());
        let body = exec.ctx.terms.mk_eq(bound, ctor);
        let quantified = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), sort)], body);

        assert_eq!(
            exec.add_ground_singleton_sort_equalities(&[quantified]),
            SingletonSortClosureStatus::Complete
        );
        assert!(
            exec.ctx.assertions.is_empty(),
            "quantifier body equality was hoisted out of scope"
        );
    }

    /// Let-bound variables are local too. Let nodes should normally be expanded
    /// earlier, but the soundness pass must remain safe if one reaches it.
    #[test]
    fn singleton_closure_does_not_descend_into_let_bindings() {
        let mut exec = Executor::new();
        register_singleton_datatype(&mut exec);
        let sort = singleton_sort();
        let local = exec.ctx.terms.mk_var("x", sort.clone());
        let ctor = exec.ctx.terms.mk_app(Symbol::named("c"), vec![], sort);
        let body = exec.ctx.terms.mk_eq(local, ctor);
        let let_term = exec.ctx.terms.mk_let(vec![("x".to_string(), ctor)], body);

        assert_eq!(
            exec.add_ground_singleton_sort_equalities(&[let_term]),
            SingletonSortClosureStatus::Complete
        );
        assert!(
            exec.ctx.assertions.is_empty(),
            "let body equality was hoisted out of scope"
        );
    }

    /// An expired solve budget must decline before emitting any subset of the
    /// closure, leaving callers an explicit fail-closed status to consume.
    #[test]
    fn singleton_closure_aborts_on_expired_deadline_without_emitting_facts() {
        let mut exec = Executor::new();
        register_singleton_datatype(&mut exec);
        let sort = singleton_sort();
        let a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("a"), vec![], sort.clone());
        let b = exec.ctx.terms.mk_app(Symbol::named("b"), vec![], sort);
        let assertion_count = exec.ctx.assertions.len();
        let expired_deadline = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must be representable");
        exec.set_solve_controls(None, Some(expired_deadline));

        assert_eq!(
            exec.add_ground_singleton_sort_equalities(&[a, b]),
            SingletonSortClosureStatus::Aborted
        );
        assert_eq!(
            exec.ctx.assertions.len(),
            assertion_count,
            "an entry checkpoint must not emit a partial closure"
        );
        assert!(exec.last_result().is_some_and(|r| r.is_unknown()));
        assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Timeout));
    }
}

#[cfg(test)]
mod finite_enum_pigeonhole_clique_tests {
    use super::*;
    use ay_core::Sort;

    /// Build `n` distinct term-graph nodes (sort is irrelevant to the search).
    fn mk_nodes(exec: &mut Executor, n: usize) -> Vec<TermId> {
        (0..n)
            .map(|i| exec.ctx.terms.mk_var(format!("n{i}"), Sort::Int))
            .collect()
    }

    fn edge(a: TermId, b: TermId) -> (TermId, TermId) {
        Executor::ordered_term_pair(a, b)
    }

    /// Externally re-verify a clique: pairwise-distinct members, every pair an
    /// edge of the input graph, and size strictly greater than `k`.
    fn assert_genuine_clique(clique: &[TermId], edges: &HashSet<(TermId, TermId)>, k: usize) {
        assert!(
            clique.len() > k,
            "clique of {} does not exceed k={k}",
            clique.len()
        );
        for (i, &a) in clique.iter().enumerate() {
            for &b in &clique[i + 1..] {
                assert_ne!(a, b, "clique repeats a member");
                assert!(
                    edges.contains(&edge(a, b)),
                    "claimed clique pair is not an input disequality edge"
                );
            }
        }
    }

    /// Regression (#smtcomp-2025 Bouvier unsat cliff): the clique search must
    /// handle graphs beyond the old 96-node hard cap. 120 nodes, k = 4: a
    /// 5-clique embedded among 115 low-degree chain nodes must be found and
    /// must survive external pairwise re-verification.
    #[test]
    fn clique_search_finds_verified_clique_beyond_old_96_node_cap() {
        let mut exec = Executor::new();
        let nodes = mk_nodes(&mut exec, 120);
        let mut edges: HashSet<(TermId, TermId)> = HashSet::default();
        // Embedded 5-clique on nodes 0..5.
        for i in 0..5 {
            for j in (i + 1)..5 {
                edges.insert(edge(nodes[i], nodes[j]));
            }
        }
        // Chain padding over nodes 5..120 (degree <= 2 < k: peeled away).
        for w in nodes.windows(2).skip(4) {
            edges.insert(edge(w[0], w[1]));
        }
        let k = 4;
        let clique = exec
            .disequality_graph_clique_exceeding(&edges, k)
            .expect("must find the embedded 5-clique in a 120-node graph");
        assert_genuine_clique(&clique, &edges, k);
    }

    /// Soundness control at scale: the same 120-node graph WITHOUT a clique
    /// exceeding `k` must return `None` — the pass must never fabricate a
    /// conflict on a satisfiable (k-colorable) disequality graph.
    #[test]
    fn clique_search_no_false_positive_beyond_old_96_node_cap() {
        let mut exec = Executor::new();
        let nodes = mk_nodes(&mut exec, 120);
        let mut edges: HashSet<(TermId, TermId)> = HashSet::default();
        // A 4-clique (exactly k, NOT exceeding it) plus chain padding.
        for i in 0..4 {
            for j in (i + 1)..4 {
                edges.insert(edge(nodes[i], nodes[j]));
            }
        }
        for w in nodes.windows(2).skip(3) {
            edges.insert(edge(w[0], w[1]));
        }
        assert!(
            exec.disequality_graph_clique_exceeding(&edges, 4).is_none(),
            "no clique of size > 4 exists; the search must not invent one"
        );
    }

    /// Dense-graph path (greedy pre-pass territory, e.g. Bouvier vlsat3_e97):
    /// a complete graph over 60 nodes with k = 40 — the witness must be found
    /// (greedy reaches it directly) and re-verify externally.
    #[test]
    fn clique_search_dense_graph_greedy_finds_witness() {
        let mut exec = Executor::new();
        let nodes = mk_nodes(&mut exec, 60);
        let mut edges: HashSet<(TermId, TermId)> = HashSet::default();
        for i in 0..60 {
            for j in (i + 1)..60 {
                edges.insert(edge(nodes[i], nodes[j]));
            }
        }
        let k = 40;
        let clique = exec
            .disequality_graph_clique_exceeding(&edges, k)
            .expect("K60 contains a 41-clique");
        assert_genuine_clique(&clique, &edges, k);
    }
}
