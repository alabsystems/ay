// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unsat-only reduction of QF_ALIA to QF_LIA via complete eager array-axiom
//! saturation + Ackermannization (#qf-alia-row2-divergence).
//!
//! The lazy AUFLIA split loop refines ONE concrete model per iteration
//! (`NeedModelEquality` / down-lemmas / per-model Farkas conflicts against a
//! fresh `TheoryCombiner`). Over an infinite Int index domain that is model
//! enumeration: on the SVC processor-verification QF_ALIA family (read2,
//! pp-dmem*, pp-bloaddata*) it grinds 70k+ refinement rounds and diverges,
//! while z3 answers unsat in ~0.02s by finite up-front case splitting.
//!
//! This module implements the classic complete decision procedure for
//! extensional Int/Int arrays as a *rescue* reduction, mirroring the
//! `try_unsat_via_mod_free_subset` pattern (solve a transformed problem with a
//! different engine, accept ONLY unsat, restore all state otherwise):
//!
//! 0. Definitional array-`ite` elimination: `(ite c X Y)` (array-sorted)
//!    becomes a fresh array variable with guarded array equalities.
//! 1. Read-over-write elimination: every `select` over a `store` chain is
//!    FULLY unrolled into an `ite` chain (`RowUnroller`; exact).
//! 2. Extensionality: for every array (dis)equality atom `(= X Y)` mint a
//!    fresh witness index `k` and assert
//!    `(= X Y) ∨ ¬(= (select X k) (select Y k))`.
//! 3. Equality congruence: for every array equality atom and every relevant
//!    index `j` (all select/store indices plus all witnesses) assert
//!    `¬(= X Y) ∨ (= (select X j) (select Y j))`.
//! 4. Read-over-read (Ackermann) congruence: for reads sharing a base
//!    variable, `¬(= i j) ∨ (= (select A i) (select A j))`.
//! 5. Abstraction: replace every remaining `select(A, i)` (base variable) by a
//!    fresh Int variable keyed on `(A, i)`, and every array-equality atom by a
//!    fresh Bool variable keyed on its (canonically ordered) sides.
//!
//! The result is pure QF_LIA. When its only integer content is bare constants
//! and (dis)equalities it is first tried on the fast EUF engine (sound
//! standalone: distinct numerals are distinct EUF constants), then on
//! `solve_lia`, whose integrated CDCL search resolves the finite index case
//! split directly. This pass runs BEFORE the lazy AUFLIA loop, so it must
//! never starve an instance that loop already solves: the reduced problem is
//! only solved when it is small (solve-size cap), and the inner solve runs
//! under a time slice of at most half the remaining budget — beyond either
//! bound the pass bails to the untouched normal pipeline.
//!
//! # Soundness (the only direction we act on)
//!
//! Steps 1–4 add array-theory TAUTOLOGIES (each clause is entailed by every
//! model of the theory of extensional arrays), so they cannot turn a
//! satisfiable problem unsatisfiable. Step 5 replaces subterms by FRESH
//! unconstrained symbols consistently (an over-approximation: every original
//! model induces a model of the abstraction). Therefore
//! `reduced UNSAT ⇒ original UNSAT`, unconditionally — even a bug in the
//! applicability analysis could only lose completeness, never produce a wrong
//! `unsat`. A `sat`/`unknown` answer from the reduced problem is DISCARDED and
//! the normal AUFLIA pipeline runs exactly as before (models, validation, and
//! sat verdicts always come from the unreduced path).
//!
//! # Completeness / applicability
//!
//! With witnesses + full congruence + Ackermann over the complete relevant
//! index set, the reduction is the standard decision procedure for
//! quantifier-free extensional arrays, so on this fragment the reduced
//! problem's unsat answers cover exactly the original's. The pass bails out
//! (returns `None`, lazily solved as today) when the fragment is exceeded:
//! quantifiers, incremental mode, UF applications, non-`(Array Int Int)`
//! arrays, array-sorted `ite`/`distinct`/function results, or when the
//! candidate axiom count exceeds the budget (all-or-nothing bounding).

// #8529: Use deterministic hash maps/sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};
use ay_core::{Sort, TermData, TermId, TermStore};

/// All-or-nothing budget on generated saturation axioms (ext witnesses +
/// congruence instances + Ackermann pairs). The targeted QF_ALIA family needs
/// well under 1000; the cap only protects large instances, whose behavior
/// stays exactly today's lazy loop.
const ARRAYS_TO_LIA_AXIOM_BUDGET: usize = 20_000;

/// Terms interned per generated read-over-read (Ackermann) axiom:
/// `(= i1 i2)`, its negation, `(= s1 s2)`, and the enclosing `or`.
const ARRAYS_TO_LIA_TERMS_PER_ACK_PAIR: usize = 4;

/// How far this speculative reduction may inflate the SHARED term store,
/// as a multiple of the original reachable problem size (#arr2lia-inflate).
const ARRAYS_TO_LIA_MAX_TERM_INFLATION: usize = 20;

/// Floor for the inflation allowance, so tiny inputs can still be rescued.
const ARRAYS_TO_LIA_MIN_TERM_ALLOWANCE: usize = 5_000;

fn is_store(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::App(sym, args) if sym.name() == "store" && args.len() == 3)
}

fn int_int_array_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Array(a) => a.index_sort == Sort::Int && a.element_sort == Sort::Int,
        _ => false,
    }
}

/// Post-order rewrite replacing base-variable `select`s by fresh Int vars and
/// array-equality atoms by fresh Bool vars. Keys use REWRITTEN children so
/// occurrences that become identical after abstraction share one symbol
/// (required for functional consistency).
struct Abstraction {
    cache: HashMap<TermId, TermId>,
    select_vars: HashMap<(TermId, TermId), TermId>,
    eq_vars: HashMap<(TermId, TermId), TermId>,
    /// Set when a term outside the supported fragment is hit; the caller must
    /// then abandon the reduction (never act on a partial abstraction).
    failed: bool,
}

impl Abstraction {
    fn rewrite(&mut self, terms: &mut TermStore, t: TermId) -> TermId {
        if let Some(&r) = self.cache.get(&t) {
            return r;
        }
        let result = match terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(..) => t,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.rewrite(terms, a)).collect();
                if sym.name() == "select"
                    && new_args.len() == 2
                    && matches!(terms.get(new_args[0]), TermData::Var(..))
                    && int_int_array_sort(terms.sort(new_args[0]))
                {
                    let key = (new_args[0], new_args[1]);
                    if let Some(&v) = self.select_vars.get(&key) {
                        v
                    } else {
                        let name = format!("__ay_arr2lia_sel_{}_{}", key.0 .0, key.1 .0);
                        let v = terms.mk_var(name, Sort::Int);
                        self.select_vars.insert(key, v);
                        v
                    }
                } else if sym.name() == "="
                    && new_args.len() == 2
                    && int_int_array_sort(terms.sort(new_args[0]))
                {
                    let key = if new_args[0] <= new_args[1] {
                        (new_args[0], new_args[1])
                    } else {
                        (new_args[1], new_args[0])
                    };
                    if key.0 == key.1 {
                        terms.true_term()
                    } else if let Some(&v) = self.eq_vars.get(&key) {
                        v
                    } else {
                        let name = format!("__ay_arr2lia_aeq_{}_{}", key.0 .0, key.1 .0);
                        let v = terms.mk_var(name, Sort::Bool);
                        self.eq_vars.insert(key, v);
                        v
                    }
                } else {
                    let rebuilt = terms.rebuild_app(&sym, new_args, t);
                    // Anything still array-sorted or select/store shaped after
                    // child rewriting is outside the abstraction (e.g. a store
                    // that never got consumed by an eq atom).
                    if matches!(terms.sort(rebuilt), Sort::Array(_))
                        && !is_store(terms, rebuilt)
                        && !matches!(terms.get(rebuilt), TermData::Var(..))
                    {
                        self.failed = true;
                    }
                    rebuilt
                }
            }
            TermData::Not(inner) => {
                let ni = self.rewrite(terms, inner);
                terms.mk_not(ni)
            }
            TermData::Ite(c, th, el) => {
                if matches!(terms.sort(t), Sort::Array(_)) {
                    self.failed = true;
                    return t;
                }
                let nc = self.rewrite(terms, c);
                let nt = self.rewrite(terms, th);
                let ne = self.rewrite(terms, el);
                terms.mk_ite(nc, nt, ne)
            }
            _ => {
                self.failed = true;
                t
            }
        };
        self.cache.insert(t, result);
        result
    }
}

/// Definitional elimination of array-sorted `ite` terms: `(ite c X Y)` is
/// replaced by a fresh array variable `V` with guarded array equalities
/// `¬c ∨ (= V X)` and `c ∨ (= V Y)` (an equisatisfiable definitional
/// extension). The new equalities then get the full extensionality/congruence
/// treatment like any other array equality atom.
struct ArrayIteElim {
    cache: HashMap<TermId, TermId>,
    defs: Vec<TermId>,
    /// `(fresh array var, eliminated ite term)` pairs, recorded so the proof
    /// re-scoping pass (#arr2lia-proof-rescope) can substitute the internal
    /// variable back by its defining term at Alethe export.
    var_defs: Vec<(TermId, TermId)>,
    failed: bool,
}

impl ArrayIteElim {
    fn rewrite(&mut self, terms: &mut TermStore, t: TermId) -> TermId {
        if let Some(&r) = self.cache.get(&t) {
            return r;
        }
        let result = match terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(..) => t,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.rewrite(terms, a)).collect();
                terms.rebuild_app(&sym, new_args, t)
            }
            TermData::Not(inner) => {
                let ni = self.rewrite(terms, inner);
                terms.mk_not(ni)
            }
            TermData::Ite(c, th, el) => {
                let nc = self.rewrite(terms, c);
                let nt = self.rewrite(terms, th);
                let ne = self.rewrite(terms, el);
                let rebuilt = terms.mk_ite(nc, nt, ne);
                if matches!(terms.sort(rebuilt), Sort::Array(_)) {
                    if !int_int_array_sort(terms.sort(rebuilt)) {
                        self.failed = true;
                        return t;
                    }
                    // mk_ite may fold (c const / branches equal); only a
                    // surviving ite needs a definition.
                    if let TermData::Ite(fc, ft, fe) = terms.get(rebuilt).clone() {
                        let v = terms.mk_var(
                            format!("__ay_arr2lia_ite_{}", rebuilt.0),
                            terms.sort(rebuilt).clone(),
                        );
                        let eq_t = terms.mk_eq(v, ft);
                        let eq_e = terms.mk_eq(v, fe);
                        let not_c = terms.mk_not(fc);
                        let then_def = terms.mk_or(vec![not_c, eq_t]);
                        let else_def = terms.mk_or(vec![fc, eq_e]);
                        self.defs.push(then_def);
                        self.defs.push(else_def);
                        self.var_defs.push((v, rebuilt));
                        v
                    } else {
                        rebuilt
                    }
                } else {
                    rebuilt
                }
            }
            _ => {
                self.failed = true;
                t
            }
        };
        self.cache.insert(t, result);
        result
    }
}

/// Complete read-over-write unrolling: rewrites every `select` so no select
/// base is a `store`. Unlike `expand_select_store_all` (which caps symbolic
/// `ite` branches at `SYMBOLIC_ITE_BUDGET = 4` and leaves the rest to the lazy
/// theory), this unrolls the FULL chain — required for the reduction's
/// completeness, and linear per (chain, index) pair because array-sorted `ite`s
/// were already eliminated definitionally (no branching left in array terms).
struct RowUnroller {
    cache: HashMap<TermId, TermId>,
    read_cache: HashMap<(TermId, TermId), TermId>,
    failed: bool,
}

impl RowUnroller {
    /// `read(arr, idx)` with `arr` fully rewritten already.
    fn read(&mut self, terms: &mut TermStore, arr: TermId, idx: TermId) -> TermId {
        if let Some(&r) = self.read_cache.get(&(arr, idx)) {
            return r;
        }
        let result = match terms.get(arr).clone() {
            TermData::Var(..) => terms.mk_select(arr, idx),
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                let eq = terms.mk_eq(args[1], idx);
                if terms.is_true(eq) {
                    args[2]
                } else if terms.is_false(eq) || terms.are_provably_distinct_indices(args[1], idx) {
                    self.read(terms, args[0], idx)
                } else {
                    let else_branch = self.read(terms, args[0], idx);
                    terms.mk_ite(eq, args[2], else_branch)
                }
            }
            _ => {
                self.failed = true;
                terms.mk_select(arr, idx)
            }
        };
        self.read_cache.insert((arr, idx), result);
        result
    }

    fn rewrite(&mut self, terms: &mut TermStore, t: TermId) -> TermId {
        if let Some(&r) = self.cache.get(&t) {
            return r;
        }
        let result = match terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(..) => t,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.rewrite(terms, a)).collect();
                if sym.name() == "select" && new_args.len() == 2 {
                    self.read(terms, new_args[0], new_args[1])
                } else {
                    terms.rebuild_app(&sym, new_args, t)
                }
            }
            TermData::Not(inner) => {
                let ni = self.rewrite(terms, inner);
                terms.mk_not(ni)
            }
            TermData::Ite(c, th, el) => {
                let nc = self.rewrite(terms, c);
                let nt = self.rewrite(terms, th);
                let ne = self.rewrite(terms, el);
                terms.mk_ite(nc, nt, ne)
            }
            _ => {
                self.failed = true;
                t
            }
        };
        self.cache.insert(t, result);
        result
    }
}

impl Executor {
    /// Attempt the arrays→LIA Ackermann reduction; `Some(unsat)` on success,
    /// `None` (state fully restored) otherwise. See module docs.
    pub(in crate::executor) fn try_unsat_via_arrays_to_lia_ackermann(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        if self.mod_div_or_branch_rescue_depth > 0
            || self.incremental_mode
            || self.original_problem_had_quantifiers
        {
            {
                tracing::debug!("arr2lia bail: unsupported-mode");
                return Ok(None);
            }
        }

        // Step 0: definitional array-ite elimination (fresh var + guarded
        // array equalities), so the SVC pipeline-style `(ite c (store …) A)`
        // terms enter the Var/store fragment.
        let mut ite_elim = ArrayIteElim {
            cache: HashMap::default(),
            defs: Vec::new(),
            var_defs: Vec::new(),
            failed: false,
        };
        let base_assertions = self.ctx.assertions.clone();
        let mut assertions: Vec<TermId> = base_assertions
            .iter()
            .map(|&a| ite_elim.rewrite(&mut self.ctx.terms, a))
            .collect();
        if ite_elim.failed {
            {
                tracing::debug!("arr2lia bail: array-ite-elim-unsupported-node");
                return Ok(None);
            }
        }
        let n_ite_defs = ite_elim.defs.len();
        assertions.extend(ite_elim.defs);
        let assertions = assertions;
        let reachable = crate::executor::theories::reachable_term_set(&self.ctx.terms, &assertions);
        tracing::debug!(
            input_assertions = base_assertions.len(),
            ite_defs = n_ite_defs,
            original_terms = reachable.len(),
            "arr2lia entry"
        );

        // ---- Applicability scan + collection ------------------------------
        let mut eq_atoms: Vec<(TermId, TermId, TermId)> = Vec::new(); // (atom, lhs, rhs)
        let mut index_set: Vec<TermId> = Vec::new();
        let mut index_seen: HashSet<TermId> = HashSet::default();
        let mut has_array_content = false;
        let mut ids: Vec<u32> = reachable.iter().map(|t| t.0).collect();
        ids.sort_unstable();
        for id in ids {
            let t = TermId(id);
            let sort_is_array = matches!(self.ctx.terms.sort(t), Sort::Array(_));
            if sort_is_array {
                has_array_content = true;
                // Only Int/Int array variables and store chains are supported.
                if !int_int_array_sort(self.ctx.terms.sort(t)) {
                    {
                        tracing::debug!("arr2lia bail: non-int-int-array");
                        return Ok(None);
                    }
                }
                match self.ctx.terms.get(t) {
                    TermData::Var(..) => {}
                    TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {}
                    _ => return Ok(None),
                }
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => match sym.name() {
                    "=" if args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_)) =>
                    {
                        eq_atoms.push((t, args[0], args[1]));
                    }
                    "distinct"
                        if args
                            .iter()
                            .any(|&a| matches!(self.ctx.terms.sort(a), Sort::Array(_))) =>
                    {
                        tracing::debug!("arr2lia bail: array-distinct");
                        return Ok(None);
                    }
                    "select" if args.len() == 2 => {
                        if index_seen.insert(args[1]) {
                            index_set.push(args[1]);
                        }
                    }
                    "store" if args.len() == 3 => {
                        if index_seen.insert(args[1]) {
                            index_set.push(args[1]);
                        }
                    }
                    _ => {}
                },
                TermData::Forall(..) | TermData::Exists(..) => return Ok(None),
                _ => {}
            }
        }
        if !has_array_content {
            {
                tracing::debug!("arr2lia bail: no-array-content");
                return Ok(None);
            }
        }
        // The abstraction handles arrays + LIA only: any UF application would
        // survive into the "LIA" problem and misroute. (select/store are not
        // counted as UF by StaticFeatures.)
        let features = crate::features::StaticFeatures::collect(&self.ctx.terms, &assertions);
        if features.has_uf
            || features.has_real
            || features.has_bv
            || features.has_strings
            || features.has_seq
            || features.has_fpa
            || features.has_quantifiers
        {
            {
                tracing::debug!("arr2lia bail: non-lia-theory");
                return Ok(None);
            }
        }

        // Rough candidate count BEFORE generating anything (all-or-nothing).
        let n_eq = eq_atoms.len();
        let n_idx = index_set.len() + n_eq; // indices + witnesses
        if n_eq.saturating_mul(n_idx + 1) > ARRAYS_TO_LIA_AXIOM_BUDGET {
            {
                tracing::debug!("arr2lia bail: over-budget-congruence");
                return Ok(None);
            }
        }

        // Project the READ-OVER-READ cost too, and do it HERE (#arr2lia-inflate).
        //
        // The `ack_pairs` budget further down is only consulted AFTER saturation
        // has already interned every read it counts, so bailing there cannot undo
        // the growth it exists to prevent — and this is a speculative rescue whose
        // terms outlive it in the SHARED store. Saturation gives each of the
        // distinct array bases one read per index, so Ackermann is quadratic in
        // `n_idx` per base while the congruence check above is only linear in it.
        // A chain of `(= a b)` array equalities plus any arithmetic atom therefore
        // sails through the check above and still interns tens of thousands of
        // terms; downstream AUFLIA passes that scan the WHOLE term store then cost
        // far more than the search this reduction was meant to rescue (measured:
        // 32 aliased `(Array Int Int)` vars + `(>= p 0)` → 66,595 terms, 7.5s,
        // versus 0.10s once this bails).
        //
        // Keep the allowance proportional to the original problem so genuinely
        // large inputs can still be rescued; only disproportionate inflation bails.
        let distinct_bases = {
            let mut bases: Vec<TermId> = eq_atoms
                .iter()
                .flat_map(|&(_, lhs, rhs)| [lhs, rhs])
                .collect();
            bases.sort_unstable_by_key(|t| t.0);
            bases.dedup();
            bases.len()
        };
        let projected_ack_pairs =
            distinct_bases.saturating_mul(n_idx.saturating_mul(n_idx.saturating_sub(1)) / 2);
        let projected_terms = projected_ack_pairs.saturating_mul(ARRAYS_TO_LIA_TERMS_PER_ACK_PAIR);
        let inflation_cap = reachable
            .len()
            .saturating_mul(ARRAYS_TO_LIA_MAX_TERM_INFLATION)
            .max(ARRAYS_TO_LIA_MIN_TERM_ALLOWANCE);
        if projected_ack_pairs > ARRAYS_TO_LIA_AXIOM_BUDGET || projected_terms > inflation_cap {
            tracing::debug!(
                distinct_bases,
                n_idx,
                projected_ack_pairs,
                projected_terms,
                inflation_cap,
                "arr2lia bail: over-budget-ack-projected"
            );
            return Ok(None);
        }

        // ---- Saturation ----------------------------------------------------
        // Extensionality witnesses (deterministic names keyed on the atom id;
        // non-incremental mode, so re-interning on a repeated solve is fine).
        let mut witnesses: Vec<TermId> = Vec::with_capacity(n_eq);
        for &(atom, _, _) in &eq_atoms {
            let w = self
                .ctx
                .terms
                .mk_var(format!("__ay_arr2lia_wit_{}", atom.0), Sort::Int);
            witnesses.push(w);
            if index_seen.insert(w) {
                index_set.push(w);
            }
        }

        let mut axioms: Vec<TermId> = Vec::new();
        for (k, &(atom, lhs, rhs)) in eq_atoms.iter().enumerate() {
            let w = witnesses[k];
            let sl = self.ctx.terms.mk_select(lhs, w);
            let sr = self.ctx.terms.mk_select(rhs, w);
            let wit_eq = self.ctx.terms.mk_eq(sl, sr);
            let wit_ne = self.ctx.terms.mk_not(wit_eq);
            let ext = self.ctx.terms.mk_or(vec![atom, wit_ne]);
            axioms.push(ext);

            let not_atom = self.ctx.terms.mk_not(atom);
            for &j in &index_set {
                let sl = self.ctx.terms.mk_select(lhs, j);
                let sr = self.ctx.terms.mk_select(rhs, j);
                let sel_eq = self.ctx.terms.mk_eq(sl, sr);
                let cong = self.ctx.terms.mk_or(vec![not_atom, sel_eq]);
                axioms.push(cong);
            }
        }

        // Complete ROW elimination over everything (assertions + saturation
        // axioms): after this, no select has a store base.
        let mut reduced: Vec<TermId> = assertions.clone();
        reduced.extend(axioms);
        let mut unroller = RowUnroller {
            cache: HashMap::default(),
            read_cache: HashMap::default(),
            failed: false,
        };
        let mut reduced: Vec<TermId> = reduced
            .iter()
            .map(|&a| unroller.rewrite(&mut self.ctx.terms, a))
            .collect();
        if unroller.failed {
            return Ok(None);
        }

        // Read-over-read (Ackermann) congruence over the now base-variable
        // reads, grouped by base.
        let post_reachable =
            crate::executor::theories::reachable_term_set(&self.ctx.terms, &reduced);
        let mut reads_by_base: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut post_ids: Vec<u32> = post_reachable.iter().map(|t| t.0).collect();
        post_ids.sort_unstable();
        for id in post_ids {
            let t = TermId(id);
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if sym.name() == "select" && args.len() == 2 {
                    if !matches!(self.ctx.terms.get(args[0]), TermData::Var(..)) {
                        // ROW expansion must have eliminated every non-variable
                        // base; anything else is outside the fragment.
                        {
                            tracing::debug!("arr2lia bail: residual-select-over-store");
                            return Ok(None);
                        }
                    }
                    reads_by_base.entry(args[0]).or_default().push((t, args[1]));
                }
            }
        }
        let ack_pairs: usize = reads_by_base
            .values()
            .map(|v| v.len() * v.len().saturating_sub(1) / 2)
            .sum();
        if ack_pairs > ARRAYS_TO_LIA_AXIOM_BUDGET {
            {
                tracing::debug!("arr2lia bail: over-budget-ack");
                return Ok(None);
            }
        }
        let mut bases: Vec<TermId> = reads_by_base.keys().copied().collect();
        bases.sort_unstable_by_key(|t| t.0);
        for base in bases {
            let reads = reads_by_base[&base].clone();
            for a in 0..reads.len() {
                for b in (a + 1)..reads.len() {
                    let (s1, i1) = reads[a];
                    let (s2, i2) = reads[b];
                    let idx_eq = self.ctx.terms.mk_eq(i1, i2);
                    if self.ctx.terms.is_false(idx_eq) {
                        continue;
                    }
                    let not_idx_eq = self.ctx.terms.mk_not(idx_eq);
                    let sel_eq = self.ctx.terms.mk_eq(s1, s2);
                    let ack = self.ctx.terms.mk_or(vec![not_idx_eq, sel_eq]);
                    reduced.push(ack);
                }
            }
        }

        // ---- Abstraction ---------------------------------------------------
        let mut abstraction = Abstraction {
            cache: HashMap::default(),
            select_vars: HashMap::default(),
            eq_vars: HashMap::default(),
            failed: false,
        };
        let abstracted: Vec<TermId> = reduced
            .iter()
            .map(|&a| abstraction.rewrite(&mut self.ctx.terms, a))
            .collect();
        if abstraction.failed {
            {
                tracing::debug!("arr2lia bail: abstraction-unsupported-node");
                return Ok(None);
            }
        }
        // Belt-and-braces: the abstracted problem must be array-free.
        let final_reachable =
            crate::executor::theories::reachable_term_set(&self.ctx.terms, &abstracted);
        if final_reachable
            .iter()
            .any(|&t| matches!(self.ctx.terms.sort(t), Sort::Array(_)))
        {
            {
                tracing::debug!("arr2lia bail: residual-array-terms");
                return Ok(None);
            }
        }

        tracing::debug!(
            eq_atoms = n_eq,
            indices = index_set.len(),
            ack_pairs,
            assertions = abstracted.len(),
            "arrays->LIA Ackermann reduction: dispatching to solve_lia"
        );

        // ---- Starvation guards (review requirement #1) ----------------------
        // The rescue runs BEFORE the (potentially divergent) lazy AUFLIA loop,
        // so its inner solve MUST be cheap on instances the normal pipeline
        // already handles (e.g. QF_ALIA queue-th2-6: ~1s on the main path; an
        // unbounded rescue LIA solve starved it to the 300s safety net). Two
        // bounds, both required:
        //   a) Size bound on the problem actually SOLVED (distinct from the
        //      generation budget above): the reduction is only worth solving
        //      when it is small. The target SVC read/pointer family reduces
        //      tightly (read2: 743 assertions / 637 Ackermann pairs), while
        //      already-solved instances that merely pass the fragment check
        //      reduce an order of magnitude larger (queue-th2-6: 8314 / 7701)
        //      and their reduced LIA solve diverges. Beyond the cap, bail to
        //      the untouched normal pipeline in milliseconds.
        //   b) Time bound: the inner solve gets at most a QUARTER of the
        //      remaining budget, capped at 10s absolute (read2's winning inner
        //      solve is ~4s release). Never a 30s defensive default — a
        //      sub-solve without its own deadline must not inherit a huge slice
        //      inside a caller's (e.g. ay-chc portfolio) budget. On expiry the
        //      inner solve returns Unknown, which is discarded below and the
        //      normal pipeline runs.
        const ARRAYS_TO_LIA_SOLVE_SIZE_CAP: usize = 2_000;
        if abstracted.len() > ARRAYS_TO_LIA_SOLVE_SIZE_CAP {
            tracing::debug!(
                assertions = abstracted.len(),
                "arr2lia bail: reduced-problem-over-solve-size-cap"
            );
            return Ok(None);
        }
        // #arr2lia-starvation: size FLOOR, gated on ORIGINAL problem size. The
        // rescue exists for the QF_ALIA read/pointer family whose divergence
        // needs a RICH reduction (read2: 743 abstracted assertions incl. 637
        // Ackermann pairs). A bare `abstracted.len() < 400` floor conflated two
        // very different 'small reduction' populations:
        //
        //   1. Oracle-style sub-queries (the ay-chc portfolio's BMC steps /
        //      witness replays): SMALL originals (heap__swaparray_000 measured:
        //      11-156 reachable terms per sub-query) producing small
        //      reductions, where an unsat-only rescue mostly meets
        //      genuinely-SAT queries and can never win — but each attempt
        //      burned up to half the remaining budget, starving the caller's
        //      lanes (bisected: heap__swaparray_000 Unsafe->
        //      Unknown(Inconclusive); 142 calls, ~29.8s of a 30s portfolio
        //      budget, inner verdicts Sat 112x / Unknown 28x, unsat 0x).
        //
        //   2. The SVC pointer/load family (pp-bloaddata: 2102 reachable
        //      terms / 775 ites; pp-dmem2: 1879), where a HUGE original
        //      collapsing to a handful of abstracted assertions (bloaddata: 7)
        //      is exactly the massive abstraction win the rescue exists for —
        //      the inner EUF solve settles it in ~1s while the lazy AUFLIA
        //      loop diverges. The bare floor regressed these to unknown@30s.
        //
        // Discriminator: the ORIGINAL reachable term count (already computed
        // above for the applicability scan; zero extra cost, no caller-context
        // plumbing). Measured populations are an order of magnitude apart
        // (<=156 vs >=1879); the 1000 threshold sits in the gap. Small
        // reductions from small originals bail here in microseconds
        // (fail-closed: only re-runs the exact pre-rescue pipeline; verdict
        // acceptance untouched), so N repeated portfolio sub-queries pay ~0
        // aggregate. Small reductions from large originals proceed, but under
        // a TIGHTER inner time slice (3s vs 10s, below) so that even a
        // hypothetical large-original oracle sub-query cannot starve a
        // portfolio caller.
        const ARRAYS_TO_LIA_SOLVE_SIZE_FLOOR: usize = 400;
        const ARRAYS_TO_LIA_ORIGINAL_TERMS_FLOOR_OVERRIDE: usize = 1_000;
        let small_reduction = abstracted.len() < ARRAYS_TO_LIA_SOLVE_SIZE_FLOOR;
        if small_reduction && reachable.len() < ARRAYS_TO_LIA_ORIGINAL_TERMS_FLOOR_OVERRIDE {
            tracing::debug!(
                assertions = abstracted.len(),
                original_terms = reachable.len(),
                "arr2lia bail: small-reduction-from-small-original"
            );
            return Ok(None);
        }
        // Rich reductions get the standard 10s cap (read2's winning inner
        // solve is ~4s release); small reductions from large originals win
        // fast or not at all (bloaddata: ~1s inner EUF), so they get 3s.
        let inner_solve_cap = std::time::Duration::from_secs(if small_reduction { 3 } else { 10 });
        let now = ay_core::time::Instant::now();
        let inner_deadline = match self.solve_deadline.get() {
            Some(dl) => now + (dl.saturating_duration_since(now) / 4).min(inner_solve_cap),
            None => now + inner_solve_cap,
        };

        // ---- Solve the reduced problem, accept only unsat -------------------
        // Mirrors try_unsat_via_mod_free_subset: full state save/restore.
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, abstracted.clone());
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        // The inner solve's diagnostics (e.g. model_validation_failures from a
        // discarded auxiliary model) must not leak into the caller-visible
        // statistics of the real solve — same isolation as
        // post-split verify (#8778 precedent above).
        let saved_statistics = std::mem::take(&mut self.last_statistics);
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        // Both inner solves run under the starvation time slice (guard (b)
        // above): a slice expiry surfaces as a non-unsat outcome, which is
        // discarded below and the caller's normal path runs unchanged.
        // Value-save/set/restore of a deliberately TIGHT inner sub-solve
        // window (same pattern as the alternation-validation windows): the
        // inner solve must NOT observe later backstop extensions, so a value
        // snapshot is the correct semantics here (see solve_deadline.rs).
        let saved_deadline = self.solve_deadline.get();
        self.solve_deadline.set(Some(match saved_deadline {
            Some(dl) => dl.min(inner_deadline),
            None => inner_deadline,
        }));
        // When the reduced problem's only integer content is bare constants
        // and (dis)equalities, EUF is sound standalone (distinct Int constants
        // are distinct EUF atoms; UNSAT derivations hold under the Int
        // interpretation — the same argument the QfAuflia array-EUF escalation
        // documents) and typically orders of magnitude faster than the LIA
        // pipeline. Any non-unsat outcome falls through to solve_lia below,
        // then to the caller's normal path.
        let constants_only = crate::term_helpers::int_constraints_are_constants_only(
            &self.ctx.terms,
            &self.ctx.assertions,
        );
        let mut result = if constants_only {
            self.solve_euf()
        } else {
            Ok(SolveResult::Unknown)
        };
        // EUF is a fast filter only; anything but unsat falls through to the
        // complete LIA route (Err short-circuits like the precedent paths).
        if matches!(result, Ok(ref r) if !r.is_unsat()) {
            self.last_model = None;
            self.last_model_validated = false;
            self.last_unknown_reason = None;
            self.last_result = None;
            self.skip_model_eval = false;
            // solve_euf rewrites ctx.assertions in place (ite lifting, lemma
            // injection); restart solve_lia from the pristine reduction.
            self.ctx.assertions = abstracted;
            result = self.solve_lia();
        }
        self.solve_deadline.set(saved_deadline);
        self.mod_div_or_branch_rescue_depth -= 1;
        self.ctx.assertions = saved_assertions;
        self.last_statistics = saved_statistics;
        tracing::debug!(?result, "arr2lia reduced solve outcome");

        match result {
            Ok(result) if result.is_unsat() => {
                self.last_unknown_reason = None;
                // #arr2lia-proof-rescope: the inner solve's proof is stated
                // over the REDUCED problem (internal `__ay_arr2lia_*`
                // symbols, saturation-axiom assumes absent from the
                // problem). Rewrite it into problem scope so the exported
                // Alethe certificate parses against the original file:
                // internal symbols substituted by their defining terms,
                // non-problem assumes demoted to honest `hole` steps.
                if self.produce_proofs_enabled() {
                    let witness_sides: Vec<(TermId, TermId, TermId)> = witnesses
                        .iter()
                        .zip(eq_atoms.iter())
                        .map(|(&w, &(_, lhs, rhs))| (w, lhs, rhs))
                        .collect();
                    self.arr2lia_rescope_proof_to_problem(
                        &base_assertions,
                        &abstraction.select_vars,
                        &abstraction.eq_vars,
                        &ite_elim.var_defs,
                        &witness_sides,
                    );
                }
                Ok(Some(result))
            }
            Ok(_) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Err(err)
            }
        }
    }

    /// #arr2lia-proof-rescope: rewrite the accepted inner refutation into
    /// ORIGINAL-problem scope for Alethe export.
    ///
    /// The inner solve proves the REDUCED problem, so its proof (a) references
    /// internal `__ay_arr2lia_{sel,aeq,ite}_*` symbols undeclared in the
    /// problem file (carcara: parser error, total rejection) and (b) `assume`s
    /// the reduced assertions, which are not the problem's assertions
    /// (carcara: assume-match failure). This pass makes the certificate
    /// externally checkable to the honest extent carcara's rule set allows
    /// (it has no array rules):
    ///
    /// 1. Every internal DEFINED symbol is substituted by its defining term
    ///    (`sel_(A,i) := (select A i)`, `aeq_(X,Y) := (= X Y)`,
    ///    `ite_k := (ite c X Y)`), recursively — the proof then mentions only
    ///    problem symbols plus extensionality witnesses.
    /// 2. Each extensionality witness (a genuine skolem, no defining problem
    ///    term) is rendered as its Hilbert-choice definition
    ///    `(choice ((k Int)) (not (= (select X k) (select Y k))))` via a
    ///    printer term-override, so every step that states a witness property
    ///    is a VALID array-theory statement, not an axiom about an arbitrary
    ///    constant.
    /// 3. Every `assume` whose (substituted) term is not literally one of the
    ///    problem assertions is demoted to a premise-free `hole` step, and
    ///    `Generic` ("trust", a rule carcara rejects as unknown) theory
    ///    lemmas likewise become `hole`. After back-substitution these steps
    ///    are exactly the reduction's array tautologies / definitional
    ///    guards / ROW-unrolled originals — true statements carcara simply
    ///    has no array rules to check, so `hole` (checked-as-holey,
    ///    attributed) is the honest encoding.
    ///
    /// Resolution / clausification steps are checked by carcara AFTER the
    /// uniform substitution, which preserves their syntactic shape. Verdicts,
    /// solve paths, and non-rescue proofs are untouched.
    fn arr2lia_rescope_proof_to_problem(
        &mut self,
        problem_assertions: &[TermId],
        select_vars: &HashMap<(TermId, TermId), TermId>,
        eq_vars: &HashMap<(TermId, TermId), TermId>,
        ite_var_defs: &[(TermId, TermId)],
        witness_sides: &[(TermId, TermId, TermId)],
    ) {
        use ay_core::{AletheRule, ProofStep, TheoryLemmaKind};

        let Some(mut proof) = self.last_proof.take() else {
            return;
        };

        let mut subst = Arr2LiaSubst {
            defs: HashMap::default(),
            cache: HashMap::default(),
        };
        for (&(arr, idx), &v) in select_vars {
            let def = self.ctx.terms.mk_select(arr, idx);
            subst.defs.insert(v, def);
        }
        for (&(lhs, rhs), &v) in eq_vars {
            let def = self.ctx.terms.mk_eq(lhs, rhs);
            subst.defs.insert(v, def);
        }
        for &(v, def) in ite_var_defs {
            subst.defs.insert(v, def);
        }

        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
        for step in &mut proof.steps {
            match step {
                ProofStep::Assume(term) => {
                    let rewritten = subst.apply(&mut self.ctx.terms, *term);
                    if problem_set.contains(&rewritten) {
                        // The inner build registered the problem file's own
                        // surface spelling (e.g. the original `let` form) as a
                        // print override keyed on the REDUCED assume term; the
                        // assume now carries the back-substituted term, so the
                        // override must follow it for carcara's assume
                        // matching.
                        if rewritten != *term {
                            if let Some(surface) = overrides.remove(term) {
                                overrides.insert(rewritten, surface);
                            }
                        }
                        *term = rewritten;
                    } else {
                        // Not a problem assertion: a saturation axiom,
                        // definitional guard, or ROW-unrolled original —
                        // valid in the theory of arrays (+ the choice-skolem
                        // definitions), but carcara has no rule to check it.
                        *step = ProofStep::Step {
                            rule: AletheRule::Hole,
                            clause: vec![rewritten],
                            premises: Vec::new(),
                            args: Vec::new(),
                        };
                    }
                }
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: _,
                    clause2: _,
                } => {
                    for lit in clause.iter_mut() {
                        *lit = subst.apply(&mut self.ctx.terms, *lit);
                    }
                    *pivot = subst.apply(&mut self.ctx.terms, *pivot);
                }
                ProofStep::TheoryLemma { clause, kind, .. } => {
                    for lit in clause.iter_mut() {
                        *lit = subst.apply(&mut self.ctx.terms, *lit);
                    }
                    // `Generic` renders as `:rule trust`, which carcara
                    // rejects as an unknown rule (hard invalid); `hole` is
                    // the spec placeholder it accepts and attributes.
                    if matches!(kind, TheoryLemmaKind::Generic) {
                        *step = ProofStep::Step {
                            rule: AletheRule::Hole,
                            clause: std::mem::take(clause),
                            premises: Vec::new(),
                            args: Vec::new(),
                        };
                    }
                }
                ProofStep::Step {
                    rule, clause, args, ..
                } => {
                    for lit in clause.iter_mut() {
                        *lit = subst.apply(&mut self.ctx.terms, *lit);
                    }
                    for arg in args.iter_mut() {
                        *arg = subst.apply(&mut self.ctx.terms, *arg);
                    }
                    // `:rule trust` is not an Alethe rule; carcara rejects the
                    // whole proof on it as "unknown rule". `hole` is the spec
                    // placeholder it accepts (result: holey) and attributes.
                    if matches!(rule, AletheRule::Trust) {
                        *rule = AletheRule::Hole;
                    }
                }
                ProofStep::Anchor { .. } => {}
                _ => {}
            }
        }

        // Alethe `or` requires the conclusion literals in the premise
        // or-term's own disjunct order. The reduced proof's decomposition
        // clauses come from the SAT layer, which stores literals in its own
        // order; realign each (same multiset, order only — downstream
        // resolution checking is order-insensitive).
        for idx in 0..proof.steps.len() {
            let ProofStep::Step {
                rule: AletheRule::Or,
                premises,
                clause,
                ..
            } = &proof.steps[idx]
            else {
                continue;
            };
            let &[premise] = premises.as_slice() else {
                continue;
            };
            let premise_term = match proof.steps.get(premise.0 as usize) {
                Some(ProofStep::Assume(t)) => *t,
                Some(ProofStep::Step {
                    clause: pclause, ..
                }) if pclause.len() == 1 => pclause[0],
                _ => continue,
            };
            let TermData::App(sym, disjuncts) = self.ctx.terms.get(premise_term).clone() else {
                continue;
            };
            if sym.name() != "or" || disjuncts.len() != clause.len() {
                continue;
            }
            let mut a = disjuncts.clone();
            let mut b = clause.clone();
            a.sort_unstable_by_key(|t| t.0);
            b.sort_unstable_by_key(|t| t.0);
            if a != b {
                continue;
            }
            if let ProofStep::Step { clause, .. } = &mut proof.steps[idx] {
                *clause = disjuncts;
            }
        }

        // Extensionality witnesses: render each as its Hilbert-choice
        // definition. The override string splices printer-rendered subterms,
        // so quoting/canonicalization matches the surrounding proof text and
        // every occurrence parses to the identical term (resolution stays
        // syntactic).
        const WIT_BOUND_VAR: &str = "__ay_arr2lia_k";
        for &(wit, lhs, rhs) in witness_sides {
            let lhs = subst.apply(&mut self.ctx.terms, lhs);
            let rhs = subst.apply(&mut self.ctx.terms, rhs);
            let k = self.ctx.terms.mk_var(WIT_BOUND_VAR, Sort::Int);
            let sel_l = self.ctx.terms.mk_select(lhs, k);
            let sel_r = self.ctx.terms.mk_select(rhs, k);
            let eq = self.ctx.terms.mk_eq(sel_l, sel_r);
            let ne = self.ctx.terms.mk_not(eq);
            let body = ay_proof::format_term_alethe(&self.ctx.terms, ne);
            overrides.insert(wit, format!("(choice (({WIT_BOUND_VAR} Int)) {body})"));
        }
        self.last_proof_term_overrides = Some(overrides);
        self.last_proof = Some(proof);
    }
}

/// Recursive back-substitution of internal arr2lia variables by their
/// defining terms across proof terms (#arr2lia-proof-rescope).
struct Arr2LiaSubst {
    defs: HashMap<TermId, TermId>,
    cache: HashMap<TermId, TermId>,
}

impl Arr2LiaSubst {
    fn apply(&mut self, terms: &mut TermStore, t: TermId) -> TermId {
        if let Some(&r) = self.cache.get(&t) {
            return r;
        }
        let result = match terms.get(t).clone() {
            TermData::Var(..) => match self.defs.get(&t).copied() {
                // A defining term may itself contain earlier-created internal
                // variables (nested ite eliminations; abstracted indices
                // inside select keys); recurse. Well-founded: a definition
                // only references terms created before its variable.
                Some(def) => self.apply(terms, def),
                None => t,
            },
            TermData::Const(_) => t,
            // Shape-preserving rebuilds: identical children return the SAME
            // TermId, and changed children are re-interned RAW (no smart
            // constructors). Normalizing rebuilds (NNF pushes, De Morgan,
            // ite folds) would detach untouched assumes from the problem's
            // own spelling and break the syntactic shape carcara's
            // clausification rules (or_pos/and_pos/ite_pos/or) check.
            TermData::Not(inner) => {
                let ni = self.apply(terms, inner);
                if ni == inner {
                    t
                } else {
                    terms.mk_not_raw(ni)
                }
            }
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.apply(terms, a)).collect();
                if new_args == args {
                    t
                } else if sym.name() == "=" && new_args.len() == 2 {
                    // Equalities go through the canonical constructor: the
                    // store keeps ONE argument order per equality, and an
                    // assume must land on the exact TermId of its problem
                    // assertion to stay an assume (mk_eq only orders — it
                    // cannot change the literal's polarity or shape).
                    terms.mk_eq(new_args[0], new_args[1])
                } else {
                    let sort = terms.sort(t).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Ite(c, th, el) => {
                let nc = self.apply(terms, c);
                let nt = self.apply(terms, th);
                let ne = self.apply(terms, el);
                if nc == c && nt == th && ne == el {
                    t
                } else {
                    terms.mk_ite_raw(nc, nt, ne)
                }
            }
            // Binders / lets are outside the fragment this rescue accepts;
            // no internal symbol can occur beneath one.
            _ => t,
        };
        self.cache.insert(t, result);
        result
    }
}
