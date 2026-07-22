// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array extensionality and store-base decomposition axiom generation.
//!
//! Congruence axioms are in `array_congruence`. ROW/ROW2b axioms are in `array_row`.

use super::super::super::Executor;
use super::pigeonhole_core::EnumDiseqEdges;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId};
use num_bigint::BigInt;

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

/// Finite index domain of an array equality, over which exact
/// extensionality is expanded (`add_finite_index_array_extensionality`).
#[derive(Clone)]
enum FiniteArrayIndexDomain {
    /// BitVec index of the given width: the `2^width` concrete bit-vectors.
    BitVec(u32),
    /// Bool index: the two values `false` / `true`.
    Bool,
    /// All-nullary (enum) datatype index: the constructor constants, built
    /// with the given index sort. The inhabitants of an all-nullary datatype
    /// are exactly its constructor constants, so this enumerates the full
    /// (finite) index domain.
    EnumDatatype(Vec<String>, Sort),
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
            Sort::BitVec(bv) => {
                // 2^w, capped. Widths past the cap are "effectively unbounded".
                if (bv.width as usize) >= (Self::FINITE_CARDINALITY_CAP.trailing_zeros() as usize) {
                    return None;
                }
                Some(1usize << bv.width)
            }
            Sort::Array(arr) => {
                let idx = self.sort_finite_cardinality_inner(&arr.index_sort, in_progress)?;
                let elem = self.sort_finite_cardinality_inner(&arr.element_sort, in_progress)?;
                // |Array I E| = |E| ^ |I|. Bail (None) on any overflow / cap breach.
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

    /// Soundness pass: when an array's ELEMENT sort has cardinality one, the
    /// array sort `(Array I E)` has a single inhabitant, so any two arrays of
    /// that sort are necessarily equal. For each top-level array disequality
    /// `(assert (not (= a b)))` / `(assert (distinct a b ...))` whose element
    /// sort is a provable singleton, assert the forced equality `(= a b)`. The
    /// asserted disequality then becomes UNSAT, matching the theory. Positive
    /// uses are unaffected (the equality is implied anyway). When the element
    /// sort cardinality cannot be proven to be one, nothing is asserted (we
    /// never guess Sat/Unsat for an undetermined cardinality).
    pub(in crate::executor) fn add_singleton_array_sort_equalities(&mut self) {
        let mut forced_equalities: Vec<(TermId, TermId)> = Vec::new();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            self.collect_singleton_array_forced_equalities(assertion, &mut forced_equalities);
        }

        for (lhs, rhs) in forced_equalities {
            let eq = self.ctx.terms.mk_eq(lhs, rhs);
            self.push_array_axiom_assertion_site(eq, "singleton_elem_array_eq");
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

    /// Soundness pass: for every equality atom `(= a b)` whose operand SORT is a
    /// provable singleton, ASSERT `(= a b)` as a top-level fact. A singleton sort
    /// has exactly one inhabitant, so `a` and `b` are necessarily equal in every
    /// model and the fact removes no models. The solver then propagates `a = b`
    /// by congruence, forcing the (shared) equality atom true wherever it
    /// appears.
    ///
    /// This generalizes `add_singleton_array_sort_equalities` (which only forced
    /// equality for TOP-LEVEL array disequalities) to positive and nested uses,
    /// closing wrong-SAT where a positive equality over a singleton sort was
    /// left as a free Boolean — e.g. `(= v (store v i c))` over `(Array Int D8)`
    /// with `D8 = {c9}` a singleton, which is a store no-op.
    ///
    /// CRITICAL: it ASSERTS the equality rather than REWRITING the atom to
    /// `true`. Rewriting would also delete the atom from any DEFINITIONAL role —
    /// e.g. the `(= sk c0)` enum-skolem-coverage fact that links a Skolem
    /// constant to the sole constructor — and the EUF core (which does not
    /// independently know the sort is a singleton) would then float the Skolem
    /// free, producing a spurious SAT (#bug10 regression). Asserting adds the
    /// fact without removing any structure. Sound: only fires when the sort
    /// cardinality is PROVABLY one (conservative under-approximation).
    pub(in crate::executor) fn fold_singleton_sort_equalities(&mut self) {
        let mut eq_pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            self.collect_singleton_sort_eq_atoms(assertion, &mut eq_pairs, &mut seen);
        }
        for (lhs, rhs) in eq_pairs {
            let eq = self.ctx.terms.mk_eq(lhs, rhs);
            self.push_array_axiom_assertion_site(eq, "singleton_sort_eq_fact");
        }
    }

    /// Collect `(lhs, rhs)` of equality atoms `(= a b)` (a != b) reachable from
    /// `term` whose operand sort is a provable singleton, recursing through all
    /// structure.
    fn collect_singleton_sort_eq_atoms(
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
                if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                    let sort = self.ctx.terms.sort(args[0]).clone();
                    if self.sort_cardinality_is_one(&sort) {
                        out.push((args[0], args[1]));
                    }
                }
                for arg in args {
                    self.collect_singleton_sort_eq_atoms(arg, out, seen);
                }
            }
            TermData::Not(inner) => self.collect_singleton_sort_eq_atoms(inner, out, seen),
            TermData::Ite(c, t, e) => {
                self.collect_singleton_sort_eq_atoms(c, out, seen);
                self.collect_singleton_sort_eq_atoms(t, out, seen);
                self.collect_singleton_sort_eq_atoms(e, out, seen);
            }
            _ => {}
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
    fn select_eq_at_binder(
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
    /// finite-index extensionality (`add_finite_index_array_extensionality`).
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

    /// True when `term`'s OWN sort is a provable singleton (datatype with one
    /// nullary-or-all-singleton-field constructor, or an array whose element sort
    /// is such). Any two terms of a singleton sort are necessarily equal.
    fn term_sort_is_singleton(&self, term: TermId) -> bool {
        let sort = self.ctx.terms.sort(term).clone();
        self.sort_cardinality_is_one(&sort)
    }

    /// Collect `(lhs, rhs)` pairs that must be equal (because their SORT is a
    /// provable singleton — a singleton datatype, or an array whose element sort
    /// is one) but are asserted distinct. Walks top-level `and` conjuncts and
    /// recognises both `(not (= a b))` and direct `(distinct a b ...)`. Generalized
    /// from array-only to any singleton sort so the EXTENSIONALITY-EXPANDED element
    /// disequality `(not (= (select a k) (select (store a i c) k)))` over a
    /// singleton datatype element (e.g. `D8 = {c9}`) is forced equal — closing the
    /// singleton-store / singleton-datatype wrong-sat.
    fn collect_singleton_array_forced_equalities(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, TermId)>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_singleton_array_forced_equalities(arg, out);
                }
            }
            // `(distinct a b ...)` over a singleton sort: every pair is forced
            // equal, so asserting any of them distinct is a conflict.
            TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                let args = args.clone();
                if !self.term_sort_is_singleton(args[0]) {
                    return;
                }
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        if args[i] != args[j] {
                            out.push((args[i], args[j]));
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                    return;
                };
                if sym.name() == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    if lhs != rhs && self.term_sort_is_singleton(lhs) {
                        out.push((lhs, rhs));
                    }
                } else if sym.name() == "distinct" && args.len() >= 2 {
                    // `(not (distinct ...))` is a positive constraint, not a
                    // disequality — nothing to force.
                }
            }
            _ => {}
        }
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
    /// (`add_singleton_array_sort_equalities` / `fold_singleton_sort_equalities`
    /// only handle the `k == 1` singleton case.)
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

        let debug_pigeonhole = std::env::var_os("AY_DEBUG_PIGEONHOLE").is_some();
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
            let false_term = self.ctx.terms.false_term();
            self.push_array_axiom_assertion_site(false_term, "finite_enum_pigeonhole");
            // One asserted `false` already makes the whole problem UNSAT; no
            // need to scan the remaining sorts.
            return true;
        }
        false
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

    /// Maximum BitVec index width for which finite-domain array extensionality
    /// is expanded eagerly. Width `w` enumerates `2^w` indices; `w <= 8` keeps
    /// this at <= 256 select pairs per array equality, which the bit-blaster
    /// handles cheaply while making such equalities EXACTLY decided.
    const FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH: u32 = 8;

    /// Eager, sound + COMPLETE finite-domain extensionality for array equalities
    /// over a small BitVec index domain.
    ///
    /// For an array sort `(Array (_ BitVec w) E)` with `w` small, the index
    /// domain is finite (`2^w` values), so two arrays are equal iff they agree
    /// at every index. The lazy single-Skolem extensionality axiom used
    /// elsewhere can only *witness* a difference; it cannot *refute* an
    /// equality that secretly fails (or holds) at a specific concrete index,
    /// which left QF_ABV array equalities involving `(as const ...)` /
    /// store-chains under-constrained and produced wrong-SAT.
    ///
    /// This pass asserts the exact biconditional for each such equality atom
    /// `(= a b)` reachable from the assertions:
    ///   `(= a b)  <=>  AND_{i in domain} (= (select a i) (select b i))`
    /// which the underlying solver then decides completely. Fires for BitVec
    /// index widths `<= FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH` and for Bool
    /// indices (2 values, `false`/`true`); larger / infinite index domains are
    /// left to the lazy machinery (no soundness impact — it just stays as-is).
    /// (Soundness fix: finite-index / as-const array (dis)equality wrong-SAT.)
    pub(in crate::executor) fn add_finite_index_array_extensionality(&mut self) {
        let mut eq_atoms: Vec<(TermId, TermId, TermId, FiniteArrayIndexDomain)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            self.collect_finite_index_array_eq_atoms(assertion, &mut eq_atoms, &mut seen);
        }

        for (eq_atom, lhs, rhs, domain) in eq_atoms {
            // Enumerate the full (finite) index domain.
            let indices: Vec<TermId> = match domain {
                FiniteArrayIndexDomain::BitVec(width) => (0..(1u64 << width))
                    .map(|i| self.ctx.terms.mk_bitvec(BigInt::from(i), width))
                    .collect(),
                FiniteArrayIndexDomain::Bool => {
                    vec![self.ctx.terms.mk_bool(false), self.ctx.terms.mk_bool(true)]
                }
                // A nullary datatype constructor reference elaborates to
                // `mk_var(name, sort)` (frontend elaborate/term.rs), so build the
                // index constants the SAME way — otherwise they would be fresh
                // `App` terms that do not match the existing constructor terms in
                // the store and the select/store rewrites would not fold.
                FiniteArrayIndexDomain::EnumDatatype(ctor_names, index_sort) => ctor_names
                    .iter()
                    .map(|name| self.ctx.terms.mk_var(name.clone(), index_sort.clone()))
                    .collect(),
            };
            // Build AND over all indices of (= (select lhs i) (select rhs i)).
            let mut conjuncts = Vec::with_capacity(indices.len());
            for idx in indices {
                let sel_lhs = self.ctx.terms.mk_select(lhs, idx);
                let sel_rhs = self.ctx.terms.mk_select(rhs, idx);
                let sel_eq = self.ctx.terms.mk_eq(sel_lhs, sel_rhs);
                conjuncts.push(sel_eq);
            }
            let conjunction = self.ctx.terms.mk_and(conjuncts);
            // (= eq_atom conjunction) over Bool is the biconditional.
            let biconditional = self.ctx.terms.mk_eq(eq_atom, conjunction);
            self.push_array_axiom_assertion_site(biconditional, "finite_index_array_ext");
        }
    }

    /// (#array-const-store-ext) Restricted extensionality for `const-array = store
    /// chain` over an INFINITE index domain, where
    /// [`add_finite_index_array_extensionality`](Self::add_finite_index_array_extensionality)
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
                self.push_array_axiom_assertion_site(imp, "const_store_array_ext");
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

    /// Back-compat alias for the BV-array route (#bv array ext). Now also covers
    /// Bool-indexed arrays; the name is kept for the existing call site.
    pub(in crate::executor) fn add_finite_bv_array_extensionality(&mut self) {
        self.add_finite_index_array_extensionality()
    }

    /// Soundness pass (#arr-finite-symbolic-index): a `(select arr i)` over an
    /// array with a FINITE index domain (Bool / small BitVec / enum datatype) and
    /// a SYMBOLIC (non-constant) index `i` must equal the array's value at
    /// whichever domain element `i` is. Without this, `(select a p) = 0` with
    /// `a[true] = 2 ∧ a[false] = 7` over `(Array Bool Int)` was wrongly SAT — the
    /// solver never case-split `p` over `{true,false}` nor linked `(select a p)`
    /// to `(select a true)`/`(select a false)`. Emit
    /// `(= (select arr i) (ite (= i d0) (select arr d0) (ite (= i d1) … )))` over
    /// the finite index domain.
    ///
    /// Sound: `i` provably equals one of the domain elements, so the ITE chain is
    /// a tautology — it removes no models and just makes the value reachable to
    /// the ground array/EUF solver.
    pub(in crate::executor) fn add_finite_index_select_expansion(&mut self) {
        let assertions = self.ctx.assertions.clone();
        let mut selects: Vec<(TermId, TermId, FiniteArrayIndexDomain)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &assertion in &assertions {
            self.collect_finite_symbolic_selects(assertion, &mut selects, &mut seen);
        }
        for (arr, idx, domain) in selects {
            let domain_vals: Vec<TermId> = self.finite_index_domain_values(&domain);
            let Some((&last, rest)) = domain_vals.split_last() else {
                continue;
            };
            // Fold from the last domain element to build the ITE chain.
            let mut acc = self.ctx.terms.mk_select(arr, last);
            for &d in rest.iter().rev() {
                let d_eq = self.ctx.terms.mk_eq(idx, d);
                let sel_d = self.ctx.terms.mk_select(arr, d);
                acc = self.ctx.terms.mk_ite(d_eq, sel_d, acc);
            }
            let sel_orig = self.ctx.terms.mk_select(arr, idx);
            if sel_orig == acc {
                continue; // already folded (e.g. literal index)
            }
            let axiom = self.ctx.terms.mk_eq(sel_orig, acc);
            if !self.ctx.assertions.contains(&axiom) {
                self.push_array_axiom_assertion_site(axiom, "finite_index_select_expansion");
            }
        }
    }

    /// Enumerate the index constants of a finite array index domain (shared by
    /// the extensionality and select-expansion passes).
    fn finite_index_domain_values(&mut self, domain: &FiniteArrayIndexDomain) -> Vec<TermId> {
        match domain {
            FiniteArrayIndexDomain::BitVec(width) => (0..(1u64 << width))
                .map(|i| self.ctx.terms.mk_bitvec(BigInt::from(i), *width))
                .collect(),
            FiniteArrayIndexDomain::Bool => {
                vec![self.ctx.terms.mk_bool(false), self.ctx.terms.mk_bool(true)]
            }
            FiniteArrayIndexDomain::EnumDatatype(ctor_names, index_sort) => ctor_names
                .iter()
                .map(|name| self.ctx.terms.mk_var(name.clone(), index_sort.clone()))
                .collect(),
        }
    }

    /// Collect `(select arr i)` sub-terms whose index `i` has a finite domain
    /// (Bool / small BitVec / enum) and is NOT a constant/literal index. Records
    /// the index domain for enumeration.
    fn collect_finite_symbolic_selects(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, TermId, FiniteArrayIndexDomain)>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let TermData::App(sym, args) = self.ctx.terms.get(term).clone() {
            if sym.name() == "select" && args.len() == 2 {
                let (arr, idx) = (args[0], args[1]);
                if !matches!(self.ctx.terms.get(idx), TermData::Const(_)) {
                    // Restrict to SMALL domains (Bool, enum datatype). A symbolic
                    // BitVec index is decided by EUF/bit-blasting and a 2^w ITE
                    // chain per select would blow up, so it is intentionally left
                    // to the BV machinery.
                    match self.finite_index_domain_of(idx) {
                        Some(domain @ FiniteArrayIndexDomain::Bool)
                        | Some(domain @ FiniteArrayIndexDomain::EnumDatatype(..)) => {
                            out.push((arr, idx, domain));
                        }
                        _ => {}
                    }
                }
            }
            for arg in args {
                self.collect_finite_symbolic_selects(arg, out, seen);
            }
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => self.collect_finite_symbolic_selects(inner, out, seen),
            TermData::Ite(c, t, e) => {
                self.collect_finite_symbolic_selects(c, out, seen);
                self.collect_finite_symbolic_selects(t, out, seen);
                self.collect_finite_symbolic_selects(e, out, seen);
            }
            _ => {}
        }
    }

    /// The finite index domain of a term `idx` based on its SORT (Bool, small
    /// BitVec, or enum datatype), or `None` for infinite/large domains.
    fn finite_index_domain_of(&self, idx: TermId) -> Option<FiniteArrayIndexDomain> {
        match self.ctx.terms.sort(idx).clone() {
            Sort::Bool => Some(FiniteArrayIndexDomain::Bool),
            Sort::BitVec(bv)
                if bv.width >= 1 && bv.width <= Self::FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH =>
            {
                Some(FiniteArrayIndexDomain::BitVec(bv.width))
            }
            ref s => self
                .finite_enum_datatype_ctors(s)
                .map(|ctors| FiniteArrayIndexDomain::EnumDatatype(ctors, s.clone())),
        }
    }

    /// Collect distinct array-equality atoms `(= a b)` whose index sort is a
    /// small finite domain (`(_ BitVec w)` with `w <= cap`, or `Bool`),
    /// reachable from `term`, recursing through boolean structure. Records the
    /// index domain for enumeration.
    fn collect_finite_index_array_eq_atoms(
        &self,
        term: TermId,
        out: &mut Vec<(TermId, TermId, TermId, FiniteArrayIndexDomain)>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                if sym.name() == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    if let Sort::Array(arr) = self.ctx.terms.sort(lhs).clone() {
                        if lhs != rhs {
                            match &arr.index_sort {
                                Sort::BitVec(bv)
                                    if bv.width >= 1
                                        && bv.width
                                            <= Self::FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH =>
                                {
                                    out.push((
                                        term,
                                        lhs,
                                        rhs,
                                        FiniteArrayIndexDomain::BitVec(bv.width),
                                    ));
                                }
                                Sort::Bool => {
                                    out.push((term, lhs, rhs, FiniteArrayIndexDomain::Bool));
                                }
                                idx_sort => {
                                    if let Some(ctors) = self.finite_enum_datatype_ctors(idx_sort) {
                                        out.push((
                                            term,
                                            lhs,
                                            rhs,
                                            FiniteArrayIndexDomain::EnumDatatype(
                                                ctors,
                                                idx_sort.clone(),
                                            ),
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                for arg in args {
                    self.collect_finite_index_array_eq_atoms(arg, out, seen);
                }
            }
            TermData::Not(inner) => {
                self.collect_finite_index_array_eq_atoms(inner, out, seen);
            }
            TermData::Ite(c, t, e) => {
                self.collect_finite_index_array_eq_atoms(c, out, seen);
                self.collect_finite_index_array_eq_atoms(t, out, seen);
                self.collect_finite_index_array_eq_atoms(e, out, seen);
            }
            _ => {}
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
    /// relevant inner-array index; the additional outer `__ext_diff` Skolem only
    /// injects spurious index equalities that combine with unrelated top-level
    /// index literals into a wrong-UNSAT (#r3-nested-arrayext).
    ///
    /// Conditions (all required):
    ///   - the array sort of `(lhs, rhs)` is NESTED (value/element sort is itself
    ///     an array); and
    ///   - some `(select (store OP ..) ..)` term exists in the problem where
    ///     `OP` is `lhs` or `rhs`.
    ///
    /// SOUNDNESS: the suppressed clause is the array-extensionality tautology
    /// `(= lhs rhs) ∨ select(lhs,k) != select(rhs,k)`. Removing a tautology can
    /// only lose completeness (a missed refutation), never manufacture a wrong
    /// verdict — so this can NEVER introduce a new wrong-UNSAT or wrong-SAT on a
    /// pair that was genuinely refutable by other means. The nested ROW/store
    /// congruence axioms still decompose the store-of-array, closing any genuine
    /// nested-array UNSAT.
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
        // `__ext_diff` select-disequality Skolem for exactly this atom, and
        // the storeinv refutation then needs the same eager ROW2b/decomposition
        // unroll as the explicit-witness `_sf_` variants. Without this, the
        // two-base `_np_` shape (positive store-store equality + negated base
        // equality) kept a lazy ArraySolver that misses upward select
        // propagation, certifying a witness-less model: false SAT (4 residual
        // conflicts in the 2026-07-02 QF_AX sweep after the same-base fix).
        // OPT-IN research gate (AY_QFAX_NEG_EQ_WITNESS=1). Same latent
        // eager-axiom unsoundness as the negated-chain gate above:
        // storeinv_invalid_t3_np_nf_ai_00002_001 (`:status sat`) flips to
        // FALSE UNSAT when this fires. Default OFF until the eager fixpoint
        // derivation is fixed; the storeinv `_np_` wrong-SAT models this was
        // added for are instead degraded fail-closed by the unwitnessed
        // array-disequality guard in model validation.
        if std::env::var_os("AY_QFAX_NEG_EQ_WITNESS").is_none_or(|v| v != "1") {
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
            // depth the fabricated `__ext_diff` witness has to unroll through.
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
    /// the `__ext_diff` Skolem fabricated by `add_array_extensionality_axioms`.
    /// Refuting it requires unrolling `select(chain, __ext_diff)` down BOTH
    /// chains (ROW2b upward propagation), which the lazy runtime ArraySolver's
    /// event-driven queues never trigger for unnamed nested stores — leaving a
    /// model that satisfies ROW1/ROW2 locally but violates extensionality
    /// globally, i.e. false SAT (the 2026-07-02 QF_AX sweep found 40 of these).
    /// Firing the same eager-ROW2b rescue as `has_storeinv_extensionality_witness`
    /// closes the gap; the ROW2b budget bounds the cost. Depth >= 2 on at least
    /// one side: single stores are handled exactly by the lazy solver.
    pub(in crate::executor) fn has_negated_deep_store_chain_array_equality(&self) -> bool {
        // OPT-IN research gate (AY_QFAX_NEG_CHAIN_GATE=1). Firing eager
        // ROW2b on every negated deep-chain equality exposed a LATENT
        // eager-axiom unsoundness: `:status sat` siblings of the swap `_np_`
        // family (e.g. swap_invalid_t1_np_sf_ai_00002_008) flip to FALSE
        // UNSAT, and the family's solve rate collapses (2026-07-02 postfix
        // sweep: QF_AX 231 -> 95 solved). Until the eager fixpoint derivation
        // is proven sound on these shapes, the sound default is OFF: wrong
        // lazy models are caught fail-closed by the strict-gate array oracle
        // (`store_chain_equality_violated`) and degrade to unknown instead.
        if std::env::var_os("AY_QFAX_NEG_CHAIN_GATE").is_none_or(|v| v != "1") {
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
    /// i.e. equal arrays have equal defaults. `default` is the "value at almost
    /// all indices" function with the standard array-theory simplifications
    /// (already implemented in `TermStore::mk_array_default`):
    ///   - `default((as const C) c) = c`
    ///   - `default(store(b, i, v)) = default(b)`
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
    /// The default axiom captures the disagreement WITHOUT a witness index:
    /// `default(store(const 0, k, v))` simplifies to `default(const 0) = 0`,
    /// `default(const 1) = 1`, so the consequent `(= 0 1)` folds to `false`
    /// and the clause becomes `¬(= a b)` — refuting the equality. This mirrors
    /// Z3's `theory_array` default/extensionality axioms, which it instantiates
    /// on array terms unconditionally (regardless of whether a disequality is
    /// asserted), making the const-default mismatch a theorem.
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
            if !matches!(self.ctx.terms.sort(lhs), Sort::Array(_)) {
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
            let default_lhs = self.ctx.terms.mk_array_default(lhs);
            let default_rhs = self.ctx.terms.mk_array_default(rhs);
            // `mk_array_default` only simplifies through const / store / lambda
            // structure; for two opaque array variables the defaults are fresh
            // uninterpreted terms and the axiom is a no-op constraint. Skip those
            // to avoid littering the search with inert `default(x)` atoms and the
            // LIA oscillation they can induce (#4304). Only emit when at least one
            // side's default is structurally determined (a non-`default` term),
            // which is exactly when the axiom can do useful refutation.
            let lhs_resolved = self.ctx.terms.get_array_default(default_lhs).is_none();
            let rhs_resolved = self.ctx.terms.get_array_default(default_rhs).is_none();
            if !lhs_resolved && !rhs_resolved {
                continue;
            }
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

    /// Add eager extensionality axioms for array equality atoms.
    ///
    /// For every equality atom `(= a b)` in the term store where a, b have
    /// `Sort::Array(...)`, creates:
    ///   - A fresh Skolem variable `__ext_diff_N` with the array's index sort
    ///   - Select terms `(select a __ext_diff_N)` and `(select b __ext_diff_N)`
    ///   - The extensionality clause: `(= a b) ∨ ¬(= (select a k) (select b k))`
    ///
    /// This is a valid tautology in the theory of arrays. Adding it before
    /// Tseitin encoding ensures the SAT solver has the atoms needed to enforce
    /// the extensionality axiom: if `a ≠ b`, the diff witness must differ.
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
                        // cause — the redundant OUTER `__ext_diff` Skolem for the
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
        // fabricate a redundant `__ext_diff_*` for the same array pair.
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
        for (eq_term, lhs, rhs, index_sort) in array_eq_pairs {
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
            // store-of-array then selected pattern), the fresh outer `__ext_diff`
            // Skolem is REDUNDANT and HARMFUL: the inner ROW/congruence machinery
            // over the nested store already pins the relevant inner-array index,
            // while the extra outer Skolem generates `(= i2 __ext_diff)`-style
            // index equalities that — combined with an UNRELATED top-level index
            // disequality (e.g. `i0 != i1`) — unit-force a spurious level-0
            // conflict over `select(lhs,__ext_diff) != select(rhs,__ext_diff)`
            // (the #8741 failure mode one array level up). Suppressing the
            // tautological extensionality Skolem is sound (a tautology removed can
            // only lose completeness, never flip a verdict); the nested ROW
            // decomposition still closes any genuine nested-array UNSAT.
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
                let pair_key = if lhs.0 <= rhs.0 {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                let mut sel_a = lhs;
                let mut sel_b = rhs;
                let mut level = 0usize;
                loop {
                    let Sort::Array(arr) = self.ctx.terms.sort(sel_a).clone() else {
                        break;
                    };
                    let skolem_name = format!(
                        "__ext_diff_deep_{}_{}_{}",
                        pair_key.0 .0, pair_key.1 .0, level
                    );
                    let diff_var = self.ctx.terms.mk_var(skolem_name, arr.index_sort.clone());
                    sel_a = self.ctx.terms.mk_select(sel_a, diff_var);
                    sel_b = self.ctx.terms.mk_select(sel_b, diff_var);
                    level += 1;
                    if level > 8 {
                        // Defensive depth cap; array sorts this deep do not
                        // occur in practice. Falling out mid-chain is still
                        // sound: the clause below stays a tautology.
                        break;
                    }
                }
                let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);
                let not_sel_eq = self.ctx.terms.mk_not(sel_eq);
                let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);
                self.push_array_axiom_assertion_site(ext_clause, "deep_ext_axiom");
                self.array_ext_shadow.record(eq_term, lhs, rhs, not_sel_eq);
                continue;
            }

            // Create fresh Skolem diff variable with the array's index sort
            let skolem_name = format!("__ext_diff_{}_{}", lhs.0, rhs.0);
            let diff_var = self.ctx.terms.mk_var(skolem_name, index_sort);

            // Create select(a, diff) and select(b, diff)
            let sel_a = self.ctx.terms.mk_select(lhs, diff_var);
            let sel_b = self.ctx.terms.mk_select(rhs, diff_var);

            // Create (= (select a diff) (select b diff))
            let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);

            // Create ¬(= (select a diff) (select b diff))
            let not_sel_eq = self.ctx.terms.mk_not(sel_eq);

            // Create extensionality clause: (= a b) ∨ ¬(= (select a diff) (select b diff))
            let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);

            // Add as an assertion (it's a tautology, so it preserves equivalence)
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
            if std::env::var_os("AY_EXT_ROW_SEED").is_some() {
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
                        if std::env::var_os("AY_DEBUG_ROW_SEED").is_some() {
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
        // chains to unit-force both `(= i1 __ext_diff)` and
        // `(= i2 __ext_diff)` at level 0, collapsing to spurious UNSAT
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
                if let Sort::Array(ref arr_sort) = terms.sort(base_a).clone() {
                    let index_sort = arr_sort.index_sort.clone();
                    // Reuse the canonical extensionality witness name for the same
                    // base-array pair instead of introducing a parallel store-base
                    // decomposition witness. This keeps the array proof search on a
                    // single distinguishing index for `(base_a, base_b)` (#6282).
                    let skolem_name = format!("__ext_diff_{}_{}", base_pair.0 .0, base_pair.1 .0);
                    let diff_var = terms.mk_var(skolem_name, index_sort);
                    let base_eq = terms.mk_eq(base_a, base_b);

                    if seen.insert(base_pair) {
                        // First time: add extensionality axiom for (A, B).
                        let sel_a = terms.mk_select(base_a, diff_var);
                        let sel_b = terms.mk_select(base_b, diff_var);
                        let sel_eq = terms.mk_eq(sel_a, sel_b);
                        let not_sel_eq = terms.mk_not(sel_eq);
                        let ext_axiom = terms.mk_or(vec![base_eq, not_sel_eq]);
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
                    // genuine theory tautology modulo the Skolem definition;
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
    ///       canonical `__ext_diff_{a}_{b}` Skolem (same construction and
    ///       naming as `add_array_extensionality_axioms`, so hash-consing
    ///       reuses one witness per pair).
    /// Tautologies and skolemized extensionality preserve satisfiability in
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
        // the canonical per-pair witness name so the axiom generator and this
        // pass agree on ONE distinguishing index per pair.
        for &(eq_term, a, b) in &neg_array_eqs {
            let Sort::Array(arr) = self.ctx.terms.sort(a).clone() else {
                continue;
            };
            if self.ctx.terms.sort(a) != self.ctx.terms.sort(b) {
                continue;
            }
            let skolem_name = format!("__ext_diff_{}_{}", a.0, b.0);
            let diff_var = self.ctx.terms.mk_var(skolem_name, arr.index_sort.clone());
            let sel_a = self.ctx.terms.mk_select(a, diff_var);
            let sel_b = self.ctx.terms.mk_select(b, diff_var);
            let sel_eq = self.ctx.terms.mk_eq(sel_a, sel_b);
            let not_sel_eq = self.ctx.terms.mk_not(sel_eq);
            let ext_clause = self.ctx.terms.mk_or(vec![eq_term, not_sel_eq]);
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
        if std::env::var_os("AY_DEBUG_WGR").is_some() {
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
