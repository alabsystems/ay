// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DT selector projection, tester evaluation, exhaustiveness, constructor,
//! equality-to-tester, injectivity, exclusion, disjointness, and
//! variable-transitivity axioms (A-I).
//!
//! Extracted from `dt_axioms.rs` as part of the code-health module split.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use super::SelectorList;
use crate::executor::Executor;

/// Warm-start recursive-datatype unroll depth for the eager DT axiom pass.
///
/// The eager [`Executor::dt_selector_axioms`] pass unrolls recursive selector
/// structure (`sel_i(sel_j(...))`) to this depth as a fast path for shallow
/// problems. Historically the only bound (`MAX_RECURSIVE_DT_DEPTH = 3`), it was
/// sound but INCOMPLETE: obligations whose UNSAT proof needs a constructor
/// case-split deeper than this returned Unknown (or, in adversarial shapes,
/// spurious SAT). The lazy DT final-check in `solve_dt` now re-solves at a
/// larger depth on Unknown, so this value is purely a performance knob: large
/// enough to settle the common shallow cases in one pass, small enough to keep
/// the eager axiom count bounded.
pub(in crate::executor) const DT_WARM_START_DEPTH: usize = 3;

/// Hard ceiling on the lazy DT final-check's iterative deepening.
///
/// Each deepening round adds one more level of (sound) datatype-theory
/// tautologies and re-solves. Genuinely recursive datatypes never reach a
/// structural fixpoint (each (C) axiom synthesizes a deeper selector term), so
/// the loop is bounded by this ceiling. Hitting it yields a fail-closed
/// `Unknown`, never a wrong answer. See `solve_dt`.
pub(in crate::executor) const DT_MAX_DEEPENING_DEPTH: usize = 64;

// Type aliases for datatype axiom generation (fixes clippy::type_complexity)
/// Constructor application info: (constructor_term, args, selectors)
type CtorAppInfo = (TermId, Vec<TermId>, SelectorList);
/// Constructor binding: (constructor_name, args, selectors)
type CtorBinding = (String, Vec<TermId>, SelectorList);
/// Constructor args and selectors (for nested resolution)
type CtorArgsAndSelectors = (Vec<TermId>, SelectorList);

fn mk_eq_same_sort(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> Option<TermId> {
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }
    Some(terms.mk_eq(lhs, rhs))
}

/// If `sort` is a declared datatype sort, return its datatype name.
///
/// Datatype sorts appear either as `Sort::Datatype` or, after the eager
/// uninterpreted lowering, as `Sort::Uninterpreted(name)` where `name` is a
/// declared datatype. Used to detect datatype-valued selector fields when
/// unrolling the value-equality congruence biconditional.
fn dt_sort_name(sort: &Sort, datatype_ctors: &HashMap<String, Vec<String>>) -> Option<String> {
    match sort {
        Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => Some(n.clone()),
        Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => Some(dt.name.clone()),
        _ => None,
    }
}

impl Executor {
    /// Instance-correct selector signature: resolves `ctor_name`'s field sorts
    /// for the SPECIFIC datatype instance `dt_name`. Parametric datatypes
    /// monomorphize to several instances that share a constructor name but
    /// differ in field sorts; using this (rather than the by-name map, which
    /// keeps only the last instance) keeps synthesized selector/constructor
    /// terms well-sorted so two instantiations can coexist without the axiom
    /// machinery emitting sort-confused terms.
    fn selector_signature_in(&self, dt_name: &str, ctor_name: &str) -> Option<SelectorList> {
        self.ctx.constructor_selector_info_in(dt_name, ctor_name)
    }

    /// The datatype (instance) sort name of `term`, if it has a datatype sort.
    fn dt_name_of(&self, term: TermId) -> Option<String> {
        match self.ctx.terms.sort(term) {
            Sort::Uninterpreted(n) => Some(n.clone()),
            Sort::Datatype(dt) => Some(dt.name.clone()),
            _ => None,
        }
    }

    /// True when `term` is a datatype constructor application `C(...)`.
    ///
    /// Such terms have a known, explicit constructor, so the exhaustiveness (D)
    /// and constructor (C) axioms — which exist to case-split genuinely free
    /// datatype variables — are redundant for them.
    fn term_is_constructor_app(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(Symbol::Named(n), _) if self.ctx.is_constructor(n).is_some()
        )
    }

    /// Field-level selector-congruence for DATATYPE-valued array selects under
    /// symbolic indices (option C; the development design notes).
    ///
    /// ay's datatype theory is a static preprocessing pass — it does not re-fire
    /// on equalities the SAT solver derives during search. So for a datatype-
    /// valued select `select(a, i)` at a SYMBOLIC index, the field projections
    /// `f(select(a,i))` are never connected to the pinned concrete-index rows,
    /// and ay returns a spurious `sat`. The eager-BV array theory IS dynamic,
    /// but its functional-consistency consequent has no bit representation for a
    /// datatype-valued select (it is a no-op there).
    ///
    /// This pass closes the gap WITHOUT touching the DT theory, the combiner, or
    /// the DPLL(T) loop: for each pair of datatype-valued selects on a common
    /// base array with at least one NON-constant index, it asserts, for every
    /// selector `f` of the element datatype (recursing through datatype-valued
    /// fields, bounded depth), the FIELD-level congruence
    ///   `(= idx_i idx_j) ⟹ (= f(select(a,idx_i)) f(select(a,idx_j)))`.
    /// Those field projections ARE bit-blasted, so the implication participates
    /// in the bit-blasted search like the scalar FC consequent.
    ///
    /// SOUNDNESS: every emitted assertion is a ground instance of the valid
    /// composition of array congruence and selector/function congruence,
    /// `i = j ⟹ select(a,i) = select(a,j) ⟹ f(select(a,i)) = f(select(a,j))`,
    /// valid for every selector and index pair. Only entailed facts are added,
    /// so no false-`unsat` is possible. Both-constant index pairs are skipped
    /// (already handled by the static path; this also contains the completeness
    /// caveat where these axioms may turn a genuine-SAT instance into `unknown`,
    /// never into a wrong `unsat`).
    pub(in crate::executor) fn dt_array_select_field_congruence_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Recursion bound for datatype-valued fields (mirrors the DT-depth cap).
        const MAX_RECURSIVE_DT_DEPTH: usize = 3;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }

        // datatype name -> constructor names
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline): only emit
        // congruence for selects actually constrained by the problem, to keep
        // the lemma set minimal and bound the completeness caveat.
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
            visited
        };

        // Collect reachable datatype-valued select terms: (select, base, index, dt_name).
        let mut dt_selects: Vec<(TermId, TermId, TermId, String)> = Vec::new();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let (array, index) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            let dt_name = match self.ctx.terms.sort(term) {
                Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => n.clone(),
                Sort::Datatype(dt) => dt.name.clone(),
                _ => continue,
            };
            dt_selects.push((term, array, index, dt_name));
        }
        if dt_selects.len() < 2 {
            return Vec::new();
        }

        // Group by base array.
        let mut by_base: HashMap<TermId, Vec<(TermId, TermId, String)>> = HashMap::default();
        for (sel, array, index, dt) in dt_selects {
            by_base.entry(array).or_default().push((sel, index, dt));
        }

        let mut axioms: Vec<TermId> = Vec::new();
        // Iterate deterministically over groups.
        let mut bases: Vec<TermId> = by_base.keys().copied().collect();
        bases.sort_unstable_by_key(|t| t.0);
        for base in bases {
            let group = &by_base[&base];
            for x in 0..group.len() {
                for y in (x + 1)..group.len() {
                    let (sel_i, idx_i, ref dt_name) = group[x];
                    let (sel_j, idx_j, _) = group[y];
                    if sel_i == sel_j {
                        continue;
                    }
                    // Skip both-constant pairs (concrete indices already handled
                    // by the static datatype path; gating here contains the
                    // genuine-SAT -> unknown completeness caveat).
                    let i_const = matches!(self.ctx.terms.get(idx_i), TermData::Const(_));
                    let j_const = matches!(self.ctx.terms.get(idx_j), TermData::Const(_));
                    if i_const && j_const {
                        continue;
                    }
                    let dt_name = dt_name.clone();
                    let Some(idx_eq) = mk_eq_same_sort(&mut self.ctx.terms, idx_i, idx_j) else {
                        continue;
                    };
                    self.emit_dt_field_congruence(
                        sel_i,
                        sel_j,
                        &dt_name,
                        idx_eq,
                        &datatype_ctors,
                        0,
                        MAX_RECURSIVE_DT_DEPTH,
                        &mut axioms,
                    );
                }
            }
        }
        axioms
    }

    /// SCALAR-PROJECTION select-congruence for datatype-valued array selects at
    /// SYMBOLIC indices (#dt-array-select-scalar-projection). z3-style lazy
    /// datatype-array reasoning: route each scalar-leaf field projection of a
    /// datatype-valued select through a FRESH SCALAR array so the eager array
    /// theory's OWN select-congruence — which connects a DERIVED-equal index
    /// (`(bvadd i c)=(bvadd j c)` ⇒ the two selects agree) — does the work.
    ///
    /// WHY the sibling `dt_array_select_field_congruence_axioms` is not enough:
    /// it emits a GUARDED implication `(= i j) ⇒ (= f(sel_i) f(sel_j))`, but for a
    /// datatype-VALUED select the guard `(= i j)` (a BV atom) does NOT
    /// bit-blast-connect to a DERIVED index equality — the datatype-valued
    /// consequent is EUF/opaque, so the mixed BV-guard→EUF-consequent implication
    /// leaves the guard a free Boolean the solver sets false to escape (verified:
    /// scalar-element arrays and ASSERTED `(= i j)` both work; datatype-element +
    /// DERIVED index does not). Introducing a fresh SCALAR array `A_f` and pinning
    /// `(select A_f k) = f(select A k)` at every observed index `k` makes the
    /// congruence consequent `(select A_f i) = (select A_f j)` SCALAR (bit-blasted),
    /// so the eager array lane's own `i=j ⇒ A_f[i]=A_f[j]` fires and forces
    /// `f(sel_i)=f(sel_j)`; the value-eq biconditional
    /// (`dt_datatype_value_equality_congruence_axioms`) then lifts field agreement
    /// to `(select A i)=(select A j)`, refuting a `distinct`. Multi-constructor /
    /// enum testers are projected through a fresh BOOL array the same way.
    ///
    /// SOUND: each fresh array `A_f` is UNCONSTRAINED except by the pinning
    /// equalities that DEFINE its observed cells (`A_f[k] := f(A[k])`), and array
    /// select-congruence (`i=j ⇒ A_f[i]=A_f[j]`) is a theory tautology — so the
    /// added axioms only prune models that violate datatype-valued select
    /// congruence (impossible ones), never a genuine SAT.
    pub(in crate::executor) fn dt_array_select_scalar_projection_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Recursion bound for datatype-valued field projection paths.
        const MAX_PROJ_DT_DEPTH: usize = 3;
        /// Cap on emitted axioms (fresh arrays × observed indices). Env-tunable
        /// (#dt-array-fc-lazy): a huge datatype-array instance (many arrays ×
        /// reads) can exceed the default and leave datatype-VALUE select
        /// congruence uncovered, so the base solve returns a congruence-violating
        /// model the census then rejects. Raising the cap covers more pairs
        /// eagerly (O(reads) via fresh scalar arrays) so the base model is
        /// congruent. Sound at any value: these are select-congruence tautologies.
        let max_proj_axioms: usize = std::env::var("AY_PROJ_AXIOM_BUDGET")
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
            .unwrap_or(50_000);

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (identical discipline to the
        // sibling passes).
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
            visited
        };

        // Collect datatype-valued select-CHAINS `(select … (select AA v) … )` that
        // depend on one or more SYMBOLIC indices `v0..vk` (at any depth of the
        // array chain). Group by a TEMPLATE key = the chain with EACH symbolic
        // index abstracted to a per-SLOT sentinel (slot = order of first
        // occurrence), so a single-level `(select A v)` and a nested `(select
        // (select AA v) c)` each pair with their sibling (whose immediate base
        // differs syntactically — plain base grouping would miss it). The combined
        // congruence PARAMETER is `bvconcat(v0..vk)` (injective, so
        // `concat=concat' ⟺ each vp=vp'`), letting the eager scalar-array
        // congruence connect a DERIVED-equal MULTI-index read pair. Each group
        // records (element datatype, combined-index sort, [(combined index, dt
        // term)]). BV indices only (concat needs bit-vectors); a non-BV symbolic
        // chain index is skipped (kept a hazard by the relaxed degrade gate).
        let mut sentinels: HashMap<String, TermId> = HashMap::default();
        // key template term -> (dt_name, combined-idx sort, Vec<(combined idx, dt term)>)
        let mut groups: HashMap<TermId, (String, Sort, Vec<(TermId, TermId)>)> = HashMap::default();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            // Must be a `select` yielding a datatype VALUE.
            if !matches!(
                self.ctx.terms.get(term),
                TermData::App(Symbol::Named(n), args) if n == "select" && args.len() == 2
            ) {
                continue;
            }
            let elem_dt = match self.ctx.terms.sort(term) {
                Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => n.clone(),
                Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                _ => continue,
            };
            // Symbolic indices along the array-select chain, deduped in first-
            // occurrence order (a repeated index shares one slot / placeholder).
            let mut raw_syms: Vec<TermId> = Vec::new();
            self.collect_chain_symbolic_indices(term, &mut raw_syms, 16);
            let mut seen_s: HashSet<TermId> = HashSet::default();
            let uniq: Vec<TermId> = raw_syms.into_iter().filter(|x| seen_s.insert(*x)).collect();
            if uniq.is_empty() {
                continue;
            }
            // All symbolic indices must be BitVec so a combined `bvconcat`
            // parameter exists (single BV index needs no concat).
            if !uniq
                .iter()
                .all(|&v| self.ctx.terms.sort(v).bitvec_width().is_some())
            {
                continue;
            }
            // Per-slot placeholders (fresh var per (slot, index-sort)) — consistent
            // across reads so matching chains hash-cons to the same template.
            let mut phs: Vec<TermId> = Vec::with_capacity(uniq.len());
            for (slot, &v) in uniq.iter().enumerate() {
                let s = self.ctx.terms.sort(v).clone();
                let key = format!("{slot}:{s}");
                let ph = *sentinels
                    .entry(key)
                    .or_insert_with(|| self.ctx.terms.mk_fresh_var("dt_proj_ph", s.clone()));
                phs.push(ph);
            }
            if uniq.iter().zip(&phs).any(|(v, ph)| v == ph) {
                continue;
            }
            let template = self.ctx.terms.substitute(term, &uniq, &phs);
            // Combined congruence index: a single index as-is, else bvconcat.
            let combined = if uniq.len() == 1 {
                uniq[0]
            } else {
                self.ctx.terms.mk_bvconcat(uniq.clone())
            };
            let combined_sort = self.ctx.terms.sort(combined).clone();
            groups
                .entry(template)
                .or_insert_with(|| (elem_dt, combined_sort, Vec::new()))
                .2
                .push((combined, term));
        }

        let mut axioms: Vec<TermId> = Vec::new();
        let mut fresh_ctr: u32 = 0;
        let mut group_keys: Vec<TermId> = groups.keys().copied().collect();
        group_keys.sort_unstable_by_key(|t| t.0);
        let n_groups = group_keys.len();
        for key in group_keys {
            let (dt_name, idx_sort, members) = &groups[&key];
            // Dedup by index value; need >= 2 distinct values for a congruence pair.
            let mut seen_idx: HashSet<TermId> = HashSet::default();
            let observed: Vec<(TermId, TermId)> = members
                .iter()
                .filter_map(|&(v, t)| seen_idx.insert(v).then_some((v, t)))
                .collect();
            if observed.len() < 2 {
                continue;
            }
            let dt_name = dt_name.clone();
            let idx_sort = idx_sort.clone();
            self.emit_dt_scalar_projection(
                &observed,
                &dt_name,
                &idx_sort,
                &datatype_ctors,
                0,
                MAX_PROJ_DT_DEPTH,
                &mut fresh_ctr,
                &mut axioms,
            );
            if axioms.len() >= max_proj_axioms {
                break;
            }
        }
        if std::env::var_os("AY_PHASE_TRACE").is_some() && !axioms.is_empty() {
            eprintln!(
                "c phase-trace dt-select-scalar-projection groups={n_groups} axioms={}",
                axioms.len()
            );
        }
        axioms
    }

    /// Collect the SYMBOLIC (non-constant) array indices along the select-chain
    /// rooted at datatype-valued select `t` — its own index and, recursively, the
    /// indices of any `select`/`store` in its array operand — down to a bound.
    /// Used to template-group datatype-array select-congruence obligations by
    /// their single symbolic parameter. Helper for
    /// [`Self::dt_array_select_scalar_projection_axioms`].
    fn collect_chain_symbolic_indices(&self, t: TermId, out: &mut Vec<TermId>, bound: usize) {
        let mut cur = t;
        let mut steps = 0;
        while steps < bound {
            steps += 1;
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), args) if n == "select" && args.len() == 2 => {
                    // Collect this select's index as a congruence parameter. At the
                    // OUTERMOST select (steps==1, a scalar/datatype-valued read) a
                    // CONSTANT index is skipped: constant-indexed scalar reads are
                    // common and abstracting them all would explode the groups
                    // (#8286). But at a NESTED array-of-array select (steps>1, whose
                    // result is the array operand of the outer read) the index must
                    // be collected EVEN IF CONSTANT — otherwise a const inner index
                    // and a symbolic inner index that ALIAS (`(select (select R c) i)`
                    // vs `(select (select R k) i)` with `k == c` in the model) land in
                    // DIFFERENT templates and their reads are never tied, leaving the
                    // datatype-array congruence unenforced (#dt-array-nested-const-idx).
                    let is_const = matches!(self.ctx.terms.get(args[1]), TermData::Const(_));
                    if !is_const || steps > 1 {
                        out.push(args[1]);
                    }
                    cur = args[0];
                }
                TermData::App(Symbol::Named(n), args) if n == "store" && args.len() == 3 => {
                    // Descend the store's base array; a symbolic store index would
                    // make the chain multi-parameter (caller drops it via the
                    // `chain_syms.len() != 1` guard), so do NOT collect it here.
                    cur = args[0];
                }
                _ => break,
            }
        }
    }

    /// Recursively pin every scalar-leaf (and tester) projection of the `observed`
    /// (index, datatype-value) pairs through a FRESH array whose index sort is
    /// `idx_sort`, so the eager array select-congruence forces derived-equal-index
    /// agreement. Helper for [`Self::dt_array_select_scalar_projection_axioms`];
    /// soundness argued there.
    #[allow(clippy::too_many_arguments)]
    fn emit_dt_scalar_projection(
        &mut self,
        observed: &[(TermId, TermId)],
        dt_name: &str,
        idx_sort: &Sort,
        datatype_ctors: &HashMap<String, Vec<String>>,
        depth: usize,
        max_depth: usize,
        fresh_ctr: &mut u32,
        axioms: &mut Vec<TermId>,
    ) {
        if depth >= max_depth || observed.len() < 2 {
            return;
        }
        let Some(ctors) = datatype_ctors.get(dt_name).cloned() else {
            return;
        };
        let multi_ctor = ctors.len() > 1;
        for ctor in ctors {
            // TESTER projection (enum / multi-ctor): pin `is-C(value)` through a
            // fresh Bool array so `i=j` forces the testers to agree.
            if multi_ctor {
                let tester_name = format!("is-{ctor}");
                *fresh_ctr += 1;
                let arr = self
                    .ctx
                    .terms
                    .mk_fresh_var("dt_proj_isc", Sort::array(idx_sort.clone(), Sort::Bool));
                for (index, value) in observed {
                    let tester = self.ctx.terms.mk_app(
                        Symbol::named(&tester_name),
                        vec![*value],
                        Sort::Bool,
                    );
                    let cell = self.ctx.terms.mk_select(arr, *index);
                    let eq = self.ctx.terms.mk_eq(cell, tester);
                    axioms.push(eq);
                }
            }
            let Some(selectors) = self.selector_signature_in(dt_name, &ctor) else {
                continue;
            };
            for (sel_name, sel_sort) in selectors {
                let nested_dt = match &sel_sort {
                    Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => Some(n.clone()),
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => {
                        Some(dt.name.clone())
                    }
                    _ => None,
                };
                if let Some(nested) = nested_dt {
                    // Datatype-valued field: recurse with the composed projection
                    // `sel_name(value)` (still a datatype value at each index).
                    let next: Vec<(TermId, TermId)> = observed
                        .iter()
                        .map(|(index, value)| {
                            let proj = self.ctx.terms.mk_app(
                                Symbol::named(sel_name.clone()),
                                vec![*value],
                                sel_sort.clone(),
                            );
                            (*index, proj)
                        })
                        .collect();
                    self.emit_dt_scalar_projection(
                        &next,
                        &nested,
                        idx_sort,
                        datatype_ctors,
                        depth + 1,
                        max_depth,
                        fresh_ctr,
                        axioms,
                    );
                } else if !matches!(&sel_sort, Sort::Array(_)) {
                    // Scalar (bit-blastable) leaf: pin `sel_name(value)` through a
                    // fresh scalar array so array select-congruence connects it.
                    *fresh_ctr += 1;
                    let arr = self
                        .ctx
                        .terms
                        .mk_fresh_var("dt_proj", Sort::array(idx_sort.clone(), sel_sort.clone()));
                    for (index, value) in observed {
                        let proj = self.ctx.terms.mk_app(
                            Symbol::named(sel_name.clone()),
                            vec![*value],
                            sel_sort.clone(),
                        );
                        let cell = self.ctx.terms.mk_select(arr, *index);
                        if let Some(eq) = mk_eq_same_sort(&mut self.ctx.terms, cell, proj) {
                            axioms.push(eq);
                        }
                    }
                }
                // Array-valued fields are left to the existing datatype-array-field
                // congruence / witness machinery (a scalar projection does not
                // apply to an array-valued field).
            }
        }
    }

    /// Emit `idx_eq ⟹ (= f(ti) f(tj))` for every selector `f` of datatype
    /// `dt_name` whose field is a scalar (bit-blastable) leaf; recurse (bounded)
    /// through datatype-valued fields. Helper for
    /// [`Self::dt_array_select_field_congruence_axioms`]; soundness argument there.
    #[allow(clippy::too_many_arguments)]
    fn emit_dt_field_congruence(
        &mut self,
        ti: TermId,
        tj: TermId,
        dt_name: &str,
        idx_eq: TermId,
        datatype_ctors: &HashMap<String, Vec<String>>,
        depth: usize,
        max_depth: usize,
        axioms: &mut Vec<TermId>,
    ) {
        if depth >= max_depth {
            return;
        }
        let Some(ctors) = datatype_ctors.get(dt_name) else {
            return;
        };
        for ctor in ctors.clone() {
            // TESTER congruence (#dt-select-tester-congruence): `(= ti tj) =>
            // (= is-C(ti) is-C(tj))`. ESSENTIAL for enum / nullary-constructor
            // datatypes (no selectors, so the selector loop below emits nothing):
            // the value is determined solely by WHICH tester holds, so two
            // datatype-valued array selects at equal indices must agree on every
            // tester — otherwise `(select A i)=red` and `(select A k)=green` with a
            // DERIVED `i=k` (e.g. from `(bvadd i c)=(bvadd k c)`) slips through as a
            // spurious SAT (the eager bit-blast never enforces datatype-valued-
            // SELECT congruence). Also strengthens multi-constructor congruence.
            // SOUND: pure congruence over the TOTAL tester function — `(= ti tj)`
            // implies `is-C(ti) = is-C(tj)` in every model, so it can only prune
            // spurious models, never cause a false-UNSAT.
            let tester_name = format!("is-{ctor}");
            let ti_tester =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![ti], Sort::Bool);
            let tj_tester =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![tj], Sort::Bool);
            if ti_tester != tj_tester {
                let tester_eq = self.ctx.terms.mk_eq(ti_tester, tj_tester);
                axioms.push(self.ctx.terms.mk_implies(idx_eq, tester_eq));
            }
            let Some(selectors) = self.selector_signature_in(dt_name, &ctor) else {
                continue;
            };
            for (sel_name, sel_sort) in selectors {
                let fi = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![ti],
                    sel_sort.clone(),
                );
                let fj = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![tj],
                    sel_sort.clone(),
                );
                let nested_dt = match &sel_sort {
                    Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => Some(n.clone()),
                    Sort::Datatype(dt) => Some(dt.name.clone()),
                    _ => None,
                };
                if let Some(nested) = nested_dt {
                    self.emit_dt_field_congruence(
                        fi,
                        fj,
                        &nested,
                        idx_eq,
                        datatype_ctors,
                        depth + 1,
                        max_depth,
                        axioms,
                    );
                } else if let Some(field_eq) = mk_eq_same_sort(&mut self.ctx.terms, fi, fj) {
                    let implication = self.ctx.terms.mk_implies(idx_eq, field_eq);
                    axioms.push(implication);
                }
            }
        }
    }

    /// Field-level decomposition for datatype-valued equalities where EXACTLY
    /// ONE side is a constructor application and the other is a NON-constructor
    /// datatype operand (canonically an array `select`) — the seam between the
    /// static selector pass and the bare-value congruence pass
    /// (#dt-select-ctor-field-decomposition).
    ///
    /// model-checker-consumer's BMC encoding materializes Rust array aggregates as
    /// select-equality assertions (its ay#5148 store/select workaround):
    ///   `(= (Slice_mk p l d) (select params #x0))`
    /// The static DT selector pass does not connect the bit-blasted constructor
    /// fields to the (bit-less) datatype-valued select, the bare-value pass
    /// gates itself OUT when either side is a constructor application, and the
    /// pairwise select-congruence pass skips select-vs-constructor shapes
    /// entirely. Result: nothing ties `p/l/d` to `select(params, #x0)`'s field
    /// lane, the SAT core picks inconsistent values, and the strict
    /// datatype-field oracle (fail-closed) degrades the Sat to Unknown —
    /// observed end-to-end on the aterm parser BMC instance.
    ///
    /// For each reachable equality atom `(= C(v_1..v_k) S)` (either operand
    /// order) with `S` NOT a constructor application, emit for every selector
    /// `sel_j` of `C`:
    ///   `(=> (= C(v..) S) (= v_j (sel_j S)))`
    /// recursing (bounded) when `v_j` is itself a constructor application of a
    /// datatype-valued field, and for MULTI-constructor datatypes the tester
    /// pin `(=> (= C(v..) S) (is-C S))`.
    ///
    /// SOUNDNESS: every emitted implication is a datatype-theory TAUTOLOGY —
    /// if `S = C(v_1..v_k)` then `sel_j(S) = sel_j(C(v..)) = v_j` (selector-of-
    /// constructor + congruence) and `is-C(S)` holds. Valid axioms can only
    /// shrink the model space toward theory-consistent models; they can never
    /// flip a verdict or cause a false-UNSAT. Scalar consequents are
    /// bit-blasted; array-sorted consequents (e.g. a slice's backing store)
    /// are discharged by the eager AUFBV array lane — the same discharge
    /// argument as `dt_datatype_value_equality_congruence_axioms`.
    pub(in crate::executor) fn dt_array_select_ctor_field_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Recursion bound for datatype-valued fields (mirrors the DT-depth cap).
        const MAX_RECURSIVE_DT_DEPTH: usize = 3;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline) — identical
        // walk to the sibling passes above.
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
            visited
        };

        // Collect reachable datatype-sort equality atoms with EXACTLY ONE
        // constructor-application side.
        let mut hits: Vec<(TermId, TermId, String, TermId, String)> = Vec::new();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let (x, y) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            if x == y {
                continue;
            }
            let dt_name = match self.ctx.terms.sort(x) {
                Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => n.clone(),
                Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                _ => continue,
            };
            let x_ctor = self.term_is_constructor_app(x);
            let y_ctor = self.term_is_constructor_app(y);
            let (ctor_term, other) = match (x_ctor, y_ctor) {
                (true, false) => (x, y),
                (false, true) => (y, x),
                // Both-ctor: injectivity pass territory. Neither: bare-value pass.
                _ => continue,
            };
            let ctor_name = match self.ctx.terms.get(ctor_term) {
                TermData::App(Symbol::Named(n), _) => n.clone(),
                _ => continue,
            };
            hits.push((term, ctor_term, ctor_name, other, dt_name));
        }
        if hits.is_empty() {
            return Vec::new();
        }

        let mut axioms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
        for (eq_term, ctor_term, ctor_name, other, dt_name) in hits {
            if !seen.insert((ctor_term, other)) {
                continue;
            }
            self.emit_dt_ctor_field_decomposition(
                eq_term,
                ctor_term,
                &ctor_name,
                other,
                &dt_name,
                &datatype_ctors,
                0,
                MAX_RECURSIVE_DT_DEPTH,
                &mut axioms,
            );
        }
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!(
                "c phase-trace dt-ctor-field-axioms hits={} axioms={}",
                seen.len(),
                axioms.len()
            );
        }
        axioms
    }

    /// Emit `(=> antecedent_eq (= v_j (sel_j other)))` for every selector of
    /// `ctor_name`, recursing (bounded) into constructor-application fields of
    /// datatype sort. Helper for
    /// [`Self::dt_array_select_ctor_field_axioms`]; soundness argument there.
    #[allow(clippy::too_many_arguments)]
    fn emit_dt_ctor_field_decomposition(
        &mut self,
        antecedent_eq: TermId,
        ctor_term: TermId,
        ctor_name: &str,
        other: TermId,
        dt_name: &str,
        datatype_ctors: &HashMap<String, Vec<String>>,
        depth: usize,
        max_depth: usize,
        axioms: &mut Vec<TermId>,
    ) {
        if depth >= max_depth {
            return;
        }
        // Tester pin for multi-constructor datatypes: `eq => (is-C other)`.
        if datatype_ctors.get(dt_name).is_some_and(|cs| cs.len() > 1) {
            let tester_name = format!("is-{ctor_name}");
            let tester =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![other], Sort::Bool);
            axioms.push(self.ctx.terms.mk_implies(antecedent_eq, tester));
        }
        let ctor_args: Vec<TermId> = match self.ctx.terms.get(ctor_term) {
            TermData::App(_, args) => args.clone(),
            _ => return,
        };
        let Some(selectors) = self.selector_signature_in(dt_name, ctor_name) else {
            return;
        };
        for ((sel_name, sel_sort), &arg) in selectors.iter().zip(ctor_args.iter()) {
            let proj = self.ctx.terms.mk_app(
                Symbol::named(sel_name.clone()),
                vec![other],
                sel_sort.clone(),
            );
            // Datatype-valued field whose ctor argument is itself a constructor
            // application: recurse so the NESTED fields also land in
            // bit-blastable consequents (a bare datatype equality one level
            // down would re-create the exact gap this pass closes).
            let nested_dt = match sel_sort {
                Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => Some(n.clone()),
                Sort::Datatype(dt) => Some(dt.name.clone()),
                _ => None,
            };
            if let Some(nested) = nested_dt {
                let nested_ctor: Option<String> = match self.ctx.terms.get(arg) {
                    TermData::App(Symbol::Named(n), _) if self.ctx.is_constructor(n).is_some() => {
                        Some(n.clone())
                    }
                    _ => None,
                };
                if let Some(nctor) = nested_ctor {
                    self.emit_dt_ctor_field_decomposition(
                        antecedent_eq,
                        arg,
                        &nctor,
                        proj,
                        &nested,
                        datatype_ctors,
                        depth + 1,
                        max_depth,
                        axioms,
                    );
                    continue;
                }
            }
            if let Some(field_eq) = mk_eq_same_sort(&mut self.ctx.terms, arg, proj) {
                axioms.push(self.ctx.terms.mk_implies(antecedent_eq, field_eq));
            }
        }
    }

    /// Value-equality congruence for BARE datatype-valued operands `(= x y)`
    /// where NEITHER side is a constructor application (#dt-value-eq-congruence).
    ///
    /// The static DT axiom pass ([`Self::dt_selector_axioms`]) only emits
    /// selector/tester/injectivity congruence when one side of an asserted
    /// equality is a CONSTRUCTOR APPLICATION `p = C(args)`. A bare datatype-value
    /// equality `(= x y)` between two datatype-valued operands where neither side
    /// is a constructor application (e.g. two record consts whose fields are
    /// `(Array (_ BitVec 64) (_ BitVec 16))`) gets NO congruence axiom at all.
    /// The eager DT+AUFBV bit-blast then reads the atom's truth off EUF
    /// equivalence-class identity, and nothing forces `x` and `y` into the same
    /// class even when the field theory pins every field equal — a spurious
    /// candidate model that the `#dt-bv-congruence` validation gate degrades
    /// (fail-closed) to `unknown`/`incomplete` on the search orders that miss it.
    ///
    /// This pass closes the gap by asserting, for each such reachable equality
    /// atom, the EXACT datatype-equality biconditional:
    ///   - single-constructor `D{C; sel_1..sel_n}`:
    ///     `(= x y) <=> (and_k (= (sel_k x) (sel_k y)))`
    ///   - multi-constructor `D{C_i; sel_ik}`:
    ///     `(= x y) <=> (and_i (= (is-Ci x) (is-Ci y)))
    ///     and (and_{i,k} (=> (is-Ci x) (= (sel_ik x) (sel_ik y))))`
    ///
    /// Both shapes are datatype TAUTOLOGIES (constructor injectivity + tester
    /// agreement + exhaustiveness): they hold in EVERY datatype model. Adding
    /// them can therefore only SHRINK the model space and NEVER cause a
    /// false-UNSAT — the same soundness argument as `dt_selector_axioms_to_depth`
    /// (selector.rs ~325-330). The Array/BV-sorted field equalities they
    /// introduce are discharged by the eager AUFBV `array_uf_eq` reification
    /// layer; datatype-valued fields are unrolled recursively (bounded depth)
    /// into their own biconditionals.
    ///
    /// GATING (mirrors [`Self::dt_array_select_field_congruence_axioms`]): only
    /// equality atoms reachable from `base_assertions` (#5082 discipline), only
    /// operands that are datatype-valued and NOT themselves constructor
    /// applications (those are already covered by the selector (A) / injectivity
    /// (F) passes), de-duplicated per operand pair to bound clause growth.
    pub(in crate::executor) fn dt_datatype_value_equality_congruence_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Recursion bound for datatype-valued fields (mirrors the DT-depth cap).
        const MAX_RECURSIVE_DT_DEPTH: usize = 3;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }

        // datatype name -> constructor names
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline): only emit
        // congruence for equality atoms actually constrained by the problem, to
        // keep the lemma set minimal. Identical walk to
        // `dt_array_select_field_congruence_axioms`.
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
            visited
        };

        // Collect reachable datatype-sort equality atoms `(= x y)` whose operands
        // are datatype-valued and NEITHER is a constructor application.
        let mut pairs: Vec<(TermId, TermId, String)> = Vec::new();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let (x, y) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            if x == y {
                continue;
            }
            // Both operands share the same datatype sort (equality invariant);
            // read the datatype name off the lhs.
            let dt_name = match self.ctx.terms.sort(x) {
                Sort::Uninterpreted(n) if datatype_ctors.contains_key(n) => n.clone(),
                Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                _ => continue,
            };
            // Neither side may be a constructor application — those are already
            // handled by the selector (A) / injectivity (F) passes (and would be
            // double-covered here).
            if self.term_is_constructor_app(x) || self.term_is_constructor_app(y) {
                continue;
            }
            pairs.push((x, y, dt_name));
        }
        if pairs.is_empty() {
            return Vec::new();
        }

        let mut axioms: Vec<TermId> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for (x, y, dt_name) in pairs {
            self.emit_dt_value_eq_congruence(
                x,
                y,
                &dt_name,
                &datatype_ctors,
                0,
                MAX_RECURSIVE_DT_DEPTH,
                &mut axioms,
                &mut seen_pairs,
            );
        }
        axioms
    }

    /// Emit the EXACT datatype-equality biconditional for the operand pair
    /// `(x, y)` of datatype `dt_name`, recursing (bounded) into datatype-valued
    /// fields. Helper for
    /// [`Self::dt_datatype_value_equality_congruence_axioms`]; the soundness
    /// argument (the biconditional is a datatype tautology in both directions)
    /// is documented there.
    #[allow(clippy::too_many_arguments)]
    fn emit_dt_value_eq_congruence(
        &mut self,
        x: TermId,
        y: TermId,
        dt_name: &str,
        datatype_ctors: &HashMap<String, Vec<String>>,
        depth: usize,
        max_depth: usize,
        axioms: &mut Vec<TermId>,
        seen_pairs: &mut HashSet<(TermId, TermId)>,
    ) {
        if depth >= max_depth || x == y {
            return;
        }
        // Canonical (min,max) key so `(x,y)` and `(y,x)` dedup to one
        // biconditional and recursion on a recursive datatype terminates.
        let key = if x.0 <= y.0 { (x, y) } else { (y, x) };
        if !seen_pairs.insert(key) {
            return;
        }
        let Some(ctors) = datatype_ctors.get(dt_name) else {
            return;
        };
        if ctors.is_empty() {
            return;
        }

        // The equality atom `(= x y)`.
        let Some(eq_xy) = mk_eq_same_sort(&mut self.ctx.terms, x, y) else {
            return;
        };

        // Datatype-valued field pairs to unroll AFTER this level's biconditional.
        let mut nested: Vec<(TermId, TermId, String)> = Vec::new();
        let mut conjuncts: Vec<TermId> = Vec::new();

        if ctors.len() == 1 {
            // Single constructor: `(= x y) <=> (and_k (= (sel_k x) (sel_k y)))`.
            let Some(selectors) = self.selector_signature_in(dt_name, &ctors[0]) else {
                return;
            };
            for (sel_name, sel_sort) in &selectors {
                let fi = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![x],
                    sel_sort.clone(),
                );
                let fj = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![y],
                    sel_sort.clone(),
                );
                if let Some(nested_dt) = dt_sort_name(sel_sort, datatype_ctors) {
                    nested.push((fi, fj, nested_dt));
                }
                if let Some(field_eq) = mk_eq_same_sort(&mut self.ctx.terms, fi, fj) {
                    conjuncts.push(field_eq);
                }
            }
        } else {
            // Multi-constructor:
            //   tester agreement:    (= (is-Ci x) (is-Ci y))                for all i
            //   guarded field cong:  (=> (is-Ci x) (= (sel_ik x) (sel_ik y)))  for all i,k
            //
            // Together with exhaustiveness (some tester holds) and the
            // constructor axiom these characterize datatype equality EXACTLY.
            // Guarding on `(is-Ci x)` is sound: the agreement conjuncts force
            // `(is-Ci x) <=> (is-Ci y)`, so the guard polarity does not matter.
            for ctor in ctors {
                let tester_name = format!("is-{ctor}");
                let tx = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![x], Sort::Bool);
                let ty = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![y], Sort::Bool);
                // Bool-Bool equality is a biconditional (#6869: not decomposed).
                conjuncts.push(self.ctx.terms.mk_eq(tx, ty));
            }
            for ctor in ctors {
                let tester_name = format!("is-{ctor}");
                let tx = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![x], Sort::Bool);
                let Some(selectors) = self.selector_signature_in(dt_name, ctor) else {
                    continue;
                };
                for (sel_name, sel_sort) in &selectors {
                    let fi = self.ctx.terms.mk_app(
                        Symbol::named(sel_name.clone()),
                        vec![x],
                        sel_sort.clone(),
                    );
                    let fj = self.ctx.terms.mk_app(
                        Symbol::named(sel_name.clone()),
                        vec![y],
                        sel_sort.clone(),
                    );
                    if let Some(nested_dt) = dt_sort_name(sel_sort, datatype_ctors) {
                        nested.push((fi, fj, nested_dt));
                    }
                    if let Some(field_eq) = mk_eq_same_sort(&mut self.ctx.terms, fi, fj) {
                        let imp = self.ctx.terms.mk_implies(tx, field_eq);
                        conjuncts.push(imp);
                    }
                }
            }
        }

        if conjuncts.is_empty() {
            // No fields to relate (e.g. a single nullary constructor). The bare
            // equality is left to the existing DT passes; sound to skip.
            return;
        }

        let rhs = self.ctx.terms.mk_and(conjuncts);
        // Bool-Bool equality is the biconditional `(= x y) <=> rhs` (#6869).
        let biconditional = self.ctx.terms.mk_eq(eq_xy, rhs);
        axioms.push(biconditional);

        // Recurse into datatype-valued fields so nested record/enum structure is
        // also connected. Bounded by `max_depth`; only adds further tautologies.
        for (fi, fj, nested_dt) in nested {
            self.emit_dt_value_eq_congruence(
                fi,
                fj,
                &nested_dt,
                datatype_ctors,
                depth + 1,
                max_depth,
                axioms,
                seen_pairs,
            );
        }
    }

    /// Cross-vocabulary UF congruence over datatype selector-bridge equalities
    /// (#dt-uf-bridge-congruence).
    ///
    /// verification-consumer encodes a datatype field-read in TWO vocabularies at once: the
    /// declared datatype selector (`enum_payload_get_1_1(x)`) AND a shadow
    /// uninterpreted selector (`list_cons_1(x)`), linked by a guarded bridge
    /// equality `is-Cons(x) ⟹ enum_payload_get_1_1(x) = list_cons_1(x)`. A
    /// recursively-defined logic function (`logic_sum`) is then applied to BOTH
    /// terms — its recursive body reads `logic_sum(list_cons_1(x))` while the
    /// child-unfold / nonneg facts speak of `logic_sum(enum_payload_get_1_1(x))`.
    /// The refutation needs the congruence
    ///   `list_cons_1(x) = enum_payload_get_1_1(x)`
    ///     ⟹ `logic_sum(list_cons_1(x)) = logic_sum(enum_payload_get_1_1(x))`
    /// to reach the arithmetic (LIA) side. EUF closes this congruence only in the
    /// branch where the bridge equality is already asserted, and the combined
    /// UF+LIA loop can return a UF-containing-expression split (#7884) from a
    /// candidate assignment BEFORE that branch is explored, degrading a provable
    /// UNSAT to `unknown`/`incomplete` (the `inc_some_list`/rusthorn recursive-ADT
    /// wall: z3 refutes it in <1s; ay diverges).
    ///
    /// This pass emits the missing congruence STATICALLY as a clause the SAT/LIA
    /// layer sees from the start: for every pair of EXISTING same-symbol
    /// applications `f(..a..)`, `f(..b..)` that differ in exactly one argument
    /// position whose operand pair `(a, b)` appears as an asserted datatype
    /// equality atom (the bridge), it asserts
    ///   `(= a b) ⟹ (= f(..a..) f(..b..))`.
    ///
    /// SOUNDNESS: `(= a b) ⟹ (= f(a) f(b))` is the congruence tautology for the
    /// function symbol `f` — it holds in EVERY model regardless of `f`'s
    /// interpretation, so adding it can only PRUNE spurious models and NEVER
    /// cause a false-UNSAT (the same argument as the sibling `dt_*_congruence`
    /// passes). Both applications are read off the EXISTING term store, so the
    /// pass synthesizes no new function applications — only the guard/consequent
    /// equality atoms and the implication wrapper. Scoped to base-reachable terms
    /// (#5082 discipline), gated to datatype-sorted differing operands (the
    /// dual-vocabulary bridge shape), deduplicated per application pair, and hard-
    /// capped to bound clause growth.
    ///
    /// PERF RESIDUAL — profiled 2026-07-16 (RELEASE, verification-consumer library config,
    /// proofs OFF, `inc_some_list`/rusthorn end-to-end). This pass is NOT the
    /// per-obligation wall-clock cost, and neither is the per-depth DT selector
    /// re-mint. Measured on the faithful decisive obligation
    /// (`dt_uf_bridge_congruence_inc_some_list.smt2`):
    ///   * this pass: 56 axioms / +123 terms / **0 ms**;
    ///   * `dt_selector_axioms_to_depth` (per depth): 999 axioms / +1980 terms / **~1 ms**;
    ///   * depth-3 UNSAT ground solve (library, proofs off): **~90 ms**.
    /// (The ~3.5 s seen in the *CLI* is Alethe proof construction + checking, which
    /// the verification-consumer library path never requests — do not profile with the plain
    /// `ay <file>` CLI; use `--no-proof`.)
    ///
    /// The residual `inc_some_list` (and `inc_some_2_list`/`tree`/`2_tree`,
    /// `binary_search_list`) end-to-end timeout is the DRIVER's SAT-shaped,
    /// GOAL-LESS recursive-datatype base/vacuity solves (the ~20 s "base recheck"
    /// slice; obligation flow snapshots the base sans the negated goal). Those are
    /// **SAT** (z3 finds a model in <15 s for every captured budget-eater), but
    /// ay's combined DT+EUF+**LIA** solve diverges in the LRA rational simplex:
    /// bignum-rational blow-up (`Rational::cmp`, `BigUint` gcd/shift/normalize,
    /// `Ratio::reduce`, `compute_materialization_delta`) churns to the per-
    /// obligation deadline → Unknown, 7×~22.6 s ≈ 158 s per test. This bridge pass
    /// is confirmed NEUTRAL there (the base solve diverges byte-identically with
    /// AND without it). The residual is the base-SAT model-finalization / LRA
    /// engine class (see the model-finalization campaign), i.e. architecture-scale
    /// and OUT of scope for this DT pass — recorded here so it is not re-chased to
    /// the bridge emitter or the DT depth ladder again.
    pub(in crate::executor) fn dt_uf_bridge_congruence_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Bound the emitted clause count so deep unrolls cannot flood the solver.
        const MAX_BRIDGE_CONG_AXIOMS: usize = 512;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline): identical walk
        // to `dt_datatype_value_equality_congruence_axioms`.
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
            visited
        };

        let canon = |a: TermId, b: TermId| if a.0 <= b.0 { (a, b) } else { (b, a) };
        let is_dt_sort = |sort: &Sort| dt_sort_name(sort, &datatype_ctors).is_some();

        // Candidate operand pairs: reachable datatype-sorted `(= x y)` atoms where
        // neither side is a constructor application (those are already covered by
        // the selector (A) / injectivity (F) passes). These are the bridge edges.
        let mut candidate: HashSet<(TermId, TermId)> = HashSet::default();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let (x, y) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            if x == y || !is_dt_sort(self.ctx.terms.sort(x)) {
                continue;
            }
            if self.term_is_constructor_app(x) || self.term_is_constructor_app(y) {
                continue;
            }
            candidate.insert(canon(x, y));
        }
        if candidate.is_empty() {
            return Vec::new();
        }

        // Index reachable uninterpreted applications by (symbol, arity). Skip
        // interpreted operators (congruence is already built into their theory)
        // and datatype constructors/testers (structural, covered elsewhere);
        // datatype/shadow SELECTORS and the recursive logic functions are kept —
        // they are exactly the symbols the bridge must lift through.
        let mut by_sym: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                continue;
            };
            if args.is_empty() {
                continue;
            }
            let n = name.as_str();
            if matches!(
                n,
                "+" | "-"
                    | "*"
                    | "/"
                    | "div"
                    | "mod"
                    | "abs"
                    | "="
                    | "<="
                    | "<"
                    | ">"
                    | ">="
                    | "distinct"
                    | "and"
                    | "or"
                    | "not"
                    | "=>"
                    | "ite"
                    | "select"
                    | "store"
            ) || n.starts_with("is-")
                || self.ctx.is_constructor(n).is_some()
            {
                continue;
            }
            by_sym
                .entry((name.to_string(), args.len()))
                .or_default()
                .push((term, args.to_vec()));
        }

        // For every same-symbol application pair differing in EXACTLY one argument
        // position whose operand pair is a bridge candidate, emit the guarded
        // congruence `(= a b) ⟹ (= f(..a..) f(..b..))`.
        let mut axioms: Vec<TermId> = Vec::new();
        let mut emitted: HashSet<(TermId, TermId)> = HashSet::default();
        'outer: for apps in by_sym.values() {
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    let (a_app, a_args) = &apps[i];
                    let (b_app, b_args) = &apps[j];
                    let mut diff: Option<(TermId, TermId)> = None;
                    let mut single = true;
                    for (&ai, &bi) in a_args.iter().zip(b_args.iter()) {
                        if ai == bi {
                            continue;
                        }
                        if diff.is_some() {
                            single = false;
                            break;
                        }
                        diff = Some((ai, bi));
                    }
                    if !single {
                        continue;
                    }
                    let Some((ai, bi)) = diff else {
                        continue;
                    };
                    if !candidate.contains(&canon(ai, bi)) {
                        continue;
                    }
                    if !emitted.insert(canon(*a_app, *b_app)) {
                        continue;
                    }
                    let Some(arg_eq) = mk_eq_same_sort(&mut self.ctx.terms, ai, bi) else {
                        continue;
                    };
                    let Some(app_eq) = mk_eq_same_sort(&mut self.ctx.terms, *a_app, *b_app) else {
                        continue;
                    };
                    let imp = self.ctx.terms.mk_implies(arg_eq, app_eq);
                    axioms.push(imp);
                    if axioms.len() >= MAX_BRIDGE_CONG_AXIOMS {
                        break 'outer;
                    }
                }
            }
        }
        axioms
    }

    /// Datatype constructor-injectivity/disjointness bridge through array
    /// STORE-value equality (#dt-array-store-value-injectivity).
    ///
    /// The combined DT + Array/BV (and DT + Array/LIA) routes decide an array
    /// equality `store(a,i,v1) = store(b,j,v2)` by bit-blasting / N-O over the
    /// array + value theories, but neither of those participants carries
    /// datatype constructor injectivity. So for datatype-VALUED stores such as
    ///   `(= (store a i (Alive x)) (store b i (Alive (x+1))))`
    /// the value-injectivity fact `v1 = v2` — and, through constructor
    /// injectivity, `x = x+1` (UNSAT) — is never derived, yielding a spurious
    /// SAT that the `problem_has_datatype_carrying_array` gate has to degrade
    /// (fail-closed) to `unknown`. This pass restores the completeness the gate
    /// cost by emitting the missing entailment STATICALLY, so every combined
    /// route (which threads its `extra_axioms` through the SAME bit-blast / N-O
    /// pipeline) reasons over it directly.
    ///
    /// For each reachable pair of same-array-sort store terms
    /// `s1 = store(a,i,v1)`, `s2 = store(b,j,v2)` whose element sort carries a
    /// datatype, emit
    ///   `(=> (and (= s1 s2) (= i j)) INJ(v1, v2))`
    /// where `INJ(v1, v2)` is
    ///   - `(and (= a_k b_k) ...)` when `v1 = C(a..)`, `v2 = C(b..)` share a
    ///     constructor (constructor INJECTIVITY, recursing bounded-depth through
    ///     datatype-valued fields),
    ///   - `false` when `v1 = C(..)`, `v2 = D(..)` use DISTINCT constructors
    ///     (constructor DISJOINTNESS — the implication collapses to
    ///     `(not (and (= s1 s2) (= i j)))`),
    ///   - the bare value equality `(= v1 v2)` otherwise (at least one operand is
    ///     not a constructor application; the existing DT value-equality
    ///     congruence pass then relates it).
    ///
    /// SOUNDNESS: `store(a,i,v1) = store(b,j,v2) ∧ i = j` entails `v1 = v2` by
    /// array extensionality + read-over-write (`select(·,i)` of equal arrays are
    /// equal, and each equals its stored value), and `v1 = v2` entails argument
    /// equality (injectivity) / falsity (disjointness) by the datatype axioms.
    /// Every emitted implication is therefore a valid Array+DT consequence: it
    /// can only SHRINK the model space, never cause a false-UNSAT. This mirrors
    /// the soundness argument of `dt_selector_axioms_to_depth`.
    /// Read-over-equality congruence for DATATYPE-ELEMENT array equalities
    /// (#dt-array-eq-read-congruence).
    ///
    /// The eager bit-blast has NO representation for a datatype VALUE, so an
    /// array equality `(= X Y)` over a datatype-element array (`Array _ D` with
    /// `D` a declared datatype) carries no cell-level semantics of its own:
    /// unlike a scalar-element array equality (which bit-blasts to "agree at
    /// every index"), asserting `(= X Y)` does NOT force `(select X i) =
    /// (select Y i)`. Constructor injectivity is therefore never surfaced when
    /// such an equality reaches the solver only INDIRECTLY — e.g. `X` bound to
    /// `(ite g (store a i (C v)) a)` — because the store-value injectivity pass
    /// keys its antecedent on a synthesized `(= store_a store_b)` the solver
    /// never derives across the ite. The result is a spurious SAT: for
    ///   `(= v (ite g (store a i (mk p l1)) a))`,
    ///   `(= v (ite g (store b i (mk p l2)) b))`, `g`, `(distinct l1 l2)`
    /// which is UNSAT, AY reported SAT (the datatype-array degrade gate could
    /// not fire because `dt_array_injectivity_fully_modeled` believed the sort
    /// bridge-modeled).
    ///
    /// For every reachable datatype-element-array equality atom `(= X Y)` and
    /// every index `i` observed in a store/select over a same-index-sort
    /// datatype-element array, emit the read-over-equality
    ///   `(=> (= X Y) (= (select X i) (select Y i)))`.
    /// The synthesized selects pick up the ordinary array ROW / select-over-ite
    /// axioms, so `(select (ite g (store a i (C v)) a) i)` folds to `(C v)` and
    /// the constructor fields become bit-blastable — closing the gap (verified:
    /// the probe above then returns UNSAT).
    ///
    /// SOUNDNESS: read-over-array-equality (`X = Y ==> X[i] = Y[i]`, functional
    /// congruence / Leibniz) is valid in EVERY model, so the emitted
    /// implications can only prune models the array theory should already have
    /// excluded — they can never cause a false-UNSAT. Quantifier bodies are
    /// excluded from the reachable walk (bound-variable capture); quantified
    /// datatype-array problems keep the fail-closed gate.
    pub(in crate::executor) fn dt_array_equality_read_congruence_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        /// Cap on emitted implications (equalities x observed indices).
        const MAX_READ_CONGRUENCE_AXIOMS: usize = 50_000;
        /// Recursion bound for datatype-valued constructor fields (mirrors the
        /// sibling decomposition passes).
        const MAX_READ_CONGRUENCE_DT_DEPTH: usize = 3;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline). Descends into
        // ite/or/not so an equality or store reachable only under a guard is
        // still seen; NOT into quantifier bodies (bound-variable capture).
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                    _ => {}
                }
            }
            visited
        };

        // Datatype-element array = an `Array _ D` whose element sort `D` is a
        // declared datatype; returns (index-sort key, index sort, element sort).
        let dt_elem_array = |sort: &Sort| -> Option<(String, Sort, Sort)> {
            match sort {
                Sort::Array(a) if dt_sort_name(&a.element_sort, &datatype_ctors).is_some() => {
                    Some((
                        format!("{}", a.index_sort),
                        a.index_sort.clone(),
                        a.element_sort.clone(),
                    ))
                }
                _ => None,
            }
        };

        // Pass 1 (TermId order -> deterministic): collect datatype-element-array
        // equality atoms, and the indices observed in stores/selects over such
        // arrays, bucketed by index-sort so synthesized selects stay well-sorted.
        let mut eq_atoms: Vec<(TermId, TermId, TermId, String, Sort)> = Vec::new();
        let mut value_eq_atoms: Vec<(TermId, TermId, TermId, String)> = Vec::new();
        let mut indices_by_sort: HashMap<String, Vec<TermId>> = HashMap::default();
        let mut seen_index: HashSet<(String, TermId)> = HashSet::default();
        // Index sorts of the datatype-element arrays that appear in an equality /
        // disequality — these get a fresh witness index (extensionality Skolem).
        let mut idx_sort_by_key: HashMap<String, Sort> = HashMap::default();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            // Extract head+args without holding the term-store borrow.
            let parts: Option<(&'static str, Vec<TermId>)> = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => {
                    Some(("=", args.clone()))
                }
                TermData::App(Symbol::Named(n), args) if n == "store" && args.len() == 3 => {
                    Some(("store", args.clone()))
                }
                TermData::App(Symbol::Named(n), args) if n == "select" && args.len() == 2 => {
                    Some(("select", args.clone()))
                }
                _ => None,
            };
            let Some((head, args)) = parts else {
                continue;
            };
            if head == "=" {
                let (x, y) = (args[0], args[1]);
                if x == y {
                    continue;
                }
                let x_sort = self.ctx.terms.sort(x).clone();
                if let Some((idx_key, index_sort, elem)) = dt_elem_array(&x_sort) {
                    // A witness is minted only for a NON-RECURSIVE element datatype
                    // (a recursive-element array is fail-closed by the bypass, and
                    // its witness read over a store folds to an unbounded-depth
                    // McCarthy ite that flips a sound Unknown to a false SAT).
                    let elem_recursive = dt_sort_name(&elem, &datatype_ctors)
                        .is_some_and(|d| self.dt_is_recursive(&d, &datatype_ctors));
                    if !elem_recursive {
                        idx_sort_by_key.entry(idx_key.clone()).or_insert(index_sort);
                    }
                    // Also mint witness indices for the array-of-datatype FIELD
                    // arrays of the element datatype: a nested const-array clash
                    // `(= (const (c1 (const (c2 #b0)))) (const (c1 (const (c2
                    // #b1)))))` lives at the INNER index, reached by folding the
                    // outer witness read `c1(inner)` through the `f1` selector into
                    // `inner`, then reading `inner` at its own witness
                    // (#dt-array-extensionality-witness, nested const class).
                    if let Some(elem_dt) = dt_sort_name(&elem, &datatype_ctors) {
                        let mut field_arrs: Vec<(String, Sort)> = Vec::new();
                        let mut fa_vis: HashSet<String> = HashSet::default();
                        self.dt_field_array_index_sorts(
                            &elem_dt,
                            &datatype_ctors,
                            &mut fa_vis,
                            &mut field_arrs,
                        );
                        for (k, s) in field_arrs {
                            idx_sort_by_key.entry(k).or_insert(s);
                        }
                    }
                    eq_atoms.push((term, x, y, idx_key, elem));
                } else if let Some(dt) = dt_sort_name(&x_sort, &datatype_ctors) {
                    // Datatype-VALUE equality. The pure-DT path enforces
                    // injectivity, but the combined DT+Array path can leave a
                    // reduction-synthesized constructor equality — e.g.
                    // `(= (mk p1 D) (mk p2 D))` produced by array ROW /
                    // extensionality over a datatype-with-array-field element —
                    // WITHOUT it: the value-congruence pass skips both-constructor
                    // pairs, and the static injectivity relies on EUF congruence
                    // the eager array-aware encoding does not apply to an opaque
                    // datatype value (observed false SAT, adversarial audit).
                    // Collect it when an operand is a constructor app or ite so
                    // the FOLDED field/tester congruence below surfaces the
                    // injectivity (`p1 = p2`). ALSO collect it — even between two
                    // BARE VARIABLES — when the datatype (transitively) has a
                    // datatype-ELEMENT array field: `(= l1 l2)` then congruence-
                    // derives an array-of-datatype equality `(= (hd l1) (hd l2))`
                    // that no atom witnesses, so its cells could disagree
                    // (adversarial audit, nested-dt-array). Mint witness indices
                    // for those field arrays so the read-over-equality reaches them.
                    let mut field_arrs: Vec<(String, Sort)> = Vec::new();
                    let mut fa_visited: HashSet<String> = HashSet::default();
                    self.dt_field_array_index_sorts(
                        &dt,
                        &datatype_ctors,
                        &mut fa_visited,
                        &mut field_arrs,
                    );
                    if self.dt_is_ctor_or_ite(x)
                        || self.dt_is_ctor_or_ite(y)
                        || !field_arrs.is_empty()
                    {
                        for (k, s) in field_arrs {
                            idx_sort_by_key.entry(k).or_insert(s);
                        }
                        value_eq_atoms.push((term, x, y, dt));
                    }
                }
            } else {
                // store / select: args[0] = array, args[1] = index.
                let arr_sort = self.ctx.terms.sort(args[0]).clone();
                if dt_elem_array(&arr_sort).is_some() {
                    let index = args[1];
                    let idx_key = format!("{}", self.ctx.terms.sort(index));
                    if seen_index.insert((idx_key.clone(), index)) {
                        indices_by_sort.entry(idx_key).or_default().push(index);
                    }
                }
            }
        }
        if eq_atoms.is_empty() && value_eq_atoms.is_empty() {
            return Vec::new();
        }
        // Witness-index extensionality (#dt-array-extensionality-witness). The
        // read-over-equality pass below instantiates `(= X Y) => (select X i) =
        // (select Y i)` only at OBSERVED indices `i`. A const-array / large-domain
        // equality whose contradiction lives at an index NEVER read (e.g.
        // `(= ((as const) (mk #b0)) ((as const) (mk #b1)))` — no select anywhere)
        // therefore carries no cell-level constraint, and the eager bit-blast
        // cannot enumerate the 2^n index domain to find the clash: the fundamental
        // eager-array wall, and the source of the adversarial audit's const-array /
        // nested / large-index false SATs.
        //
        // Fix (the sound essence of z3's lazy array reasoning): for each index
        // sort carrying a datatype-element array equality, mint ONE fresh SYMBOLIC
        // witness index and add it to the observed set. Extensionality is then
        // instantiated at the witness, and the const-array / store folds
        // (dt_fold_select) reduce `(select X w)` to the fill / stored value — so
        // the clash surfaces symbolically, WITHOUT enumerating the domain. The
        // witness is SHARED across all equalities of its index sort so the
        // transitive chain closes: `select X w = fill1`, `select Y w = fill2`,
        // `(= X Y) => select X w = select Y w` together force `fill1 = fill2`.
        //
        // SOUND: instantiating the extensionality universal `forall k. X=Y =>
        // X[k]=Y[k]` at the fresh ground term `w` is a valid consequence in every
        // model, and a fresh variable adds no constraint of its own — so this can
        // only prune spurious models, never cause a false-UNSAT. (Disequalities
        // need a DISTINCT witness each and are handled separately below.)
        for (idx_key, index_sort) in idx_sort_by_key {
            let witness = self.ctx.terms.mk_fresh_var("dt_ext_witness", index_sort);
            if seen_index.insert((idx_key.clone(), witness)) {
                indices_by_sort.entry(idx_key).or_default().push(witness);
            }
        }
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!(
                "c phase-trace dt-array-eq-read array_eqs={} value_eqs={} indices={}",
                eq_atoms.len(),
                value_eq_atoms.len(),
                indices_by_sort.values().map(|v| v.len()).sum::<usize>()
            );
        }

        // Pass 2: emit `(=> (= X Y) (= (select X i) (select Y i)))` per equality
        // and each observed same-index-sort index. Both selects are FOLDED
        // through ROW / ite-distribution at emission time (see `dt_fold_select`):
        // the ordinary array ROW simplification runs in preprocessing, BEFORE
        // this pass adds its synthesized selects, so a raw `(select (store a i
        // (C v)) i)` would stay opaque (its datatype element has no bits) and
        // never reduce to `(C v)`. Folding here makes the stored constructor
        // bit-blastable regardless of pass ordering.
        let mut axioms: Vec<TermId> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        'outer: for (eq_term, x, y, idx_key, elem_sort) in eq_atoms {
            let Some(indices) = indices_by_sort.get(&idx_key).cloned() else {
                continue;
            };
            let Some(dt_name) = dt_sort_name(&elem_sort, &datatype_ctors) else {
                continue;
            };
            // DISEQUALITY SKOLEM (#dt-array-diseq-skolem). The positive witness
            // extensionality below fires only when `(= X Y)` HOLDS; a DISEQUALITY
            // `(not (= X Y))` over a datatype-element array carries no cell-level
            // constraint, so a finite-cardinality pigeonhole (`distinct A B C` over
            // a 2-inhabitant datatype) or a forced-equal-but-claimed-distinct pair
            // escapes as a false SAT / degrades. Mint ONE FRESH witness `w'` per
            // equality atom and Skolemize the existential difference:
            //   `(not (= X Y)) => (not (= (select X w') (select Y w')))`
            // — in any model where X != Y they differ at SOME index, and the fresh
            // `w'` can be set to it, so this is SOUND (a Skolem, never a false
            // UNSAT); it is vacuous when X = Y. The folded witness reads reduce
            // through const-array / ROW, and the value-eq biconditional emitted for
            // the read pair relays the datatype-value inequality down to a field
            // inequality (`(mk a) != (mk b) <=> a != b`), so the pigeonhole's
            // forced-equal fills contradict the witnessed difference -> UNSAT.
            if let Sort::Array(arr) = self.ctx.terms.sort(x) {
                let index_sort = arr.index_sort.clone();
                let w = self.ctx.terms.mk_fresh_var("dt_diseq_witness", index_sort);
                let fx = self.dt_fold_select(x, w, &elem_sort, 0);
                let fy = self.dt_fold_select(y, w, &elem_sort, 0);
                if fx != fy {
                    if let Some(veq) = mk_eq_same_sort(&mut self.ctx.terms, fx, fy) {
                        let not_eq = self.ctx.terms.mk_not(eq_term);
                        let not_veq = self.ctx.terms.mk_not(veq);
                        axioms.push(self.ctx.terms.mk_implies(not_eq, not_veq));
                        // Relay the value inequality to field inequalities.
                        let mut diseq_seen: HashSet<(TermId, TermId)> = HashSet::default();
                        self.emit_dt_value_eq_congruence(
                            fx,
                            fy,
                            &dt_name,
                            &datatype_ctors,
                            0,
                            MAX_READ_CONGRUENCE_DT_DEPTH,
                            &mut axioms,
                            &mut diseq_seen,
                        );
                    }
                }
            }
            for i in indices {
                if axioms.len() >= MAX_READ_CONGRUENCE_AXIOMS {
                    break 'outer;
                }
                let fold_x = self.dt_fold_select(x, i, &elem_sort, 0);
                let fold_y = self.dt_fold_select(y, i, &elem_sort, 0);
                if fold_x == fold_y {
                    continue;
                }
                // Read-over-equality at the value level: `(= X Y) => X[i] = Y[i]`.
                if let Some(cons) = mk_eq_same_sort(&mut self.ctx.terms, fold_x, fold_y) {
                    axioms.push(self.ctx.terms.mk_implies(eq_term, cons));
                }
                // A folded select is a datatype VALUE with no bit representation,
                // so the value equality above cannot, on its own, propagate a
                // contradiction: `(select v i)` over a bare-Var array is opaque,
                // and `(ite g (mk ..) (select a i))` (from folding an
                // ite-of-array constructions) is opaque too. Emit guarded
                // field/tester congruence `(=> (= X Y) (= sel_k(foldX)
                // sel_k(foldY)))` — but with the SELECTORS/TESTERS themselves
                // FOLDED through ite/constructor at emission time
                // (dt_fold_selector/dt_fold_tester). This mirrors dt_fold_select:
                // the selector-over-ite and selector-of-constructor rewrites run
                // in preprocessing, before these synthesized projections exist, so
                // a raw `sel_k(ite g (mk p1 d) (select a i))` would stay opaque and
                // never reduce to `ite g p1 sel_k(select a i)`. Folding here makes
                // `p1 = p2` (etc.) bit-blastable — closing the residual false SATs
                // the adversarial audit found (ite-of-array-variables and nested-
                // datatype/array-field shapes). SOUND: `a = b => sel_k(a) =
                // sel_k(b)` / `is-C(a) = is-C(b)` are congruence over TOTAL
                // functions, and the folds apply only valid selector-of-
                // constructor / selector-over-ite identities — never a false-UNSAT.
                self.emit_dt_read_field_congruence(
                    eq_term,
                    fold_x,
                    fold_y,
                    &dt_name,
                    &datatype_ctors,
                    &indices_by_sort,
                    0,
                    MAX_READ_CONGRUENCE_DT_DEPTH,
                    &mut axioms,
                    &mut seen_pairs,
                );
            }
        }
        // Datatype-VALUE equalities `(= x y)` with a constructor/ite operand:
        // emit folded field/tester congruence directly (no index — these are
        // values, not arrays). Closes the reduction-synthesized constructor
        // injectivity gap on the combined DT+Array path (#dt-value-eq-injectivity).
        for (eq_term, x, y, dt_name) in value_eq_atoms {
            if axioms.len() >= MAX_READ_CONGRUENCE_AXIOMS {
                break;
            }
            self.emit_dt_read_field_congruence(
                eq_term,
                x,
                y,
                &dt_name,
                &datatype_ctors,
                &indices_by_sort,
                0,
                MAX_READ_CONGRUENCE_DT_DEPTH,
                &mut axioms,
                &mut seen_pairs,
            );
        }
        axioms
    }

    /// Whether `t` is a datatype constructor application or an `ite` — the shapes
    /// whose selector/tester projections need folding (a bare datatype variable's
    /// projections are already leaf terms the DT theory relates). Helper for
    /// [`Self::dt_array_equality_read_congruence_axioms`].
    fn dt_is_ctor_or_ite(&self, t: TermId) -> bool {
        match self.ctx.terms.get(t) {
            TermData::Ite(..) => true,
            TermData::App(Symbol::Named(n), _) => self.ctx.is_constructor(n).is_some(),
            _ => false,
        }
    }

    /// Whether datatype `dt_name` is RECURSIVE — a constructor field (directly, or
    /// as an array element) transitively re-enters `dt_name`, so its values have
    /// unbounded depth (`Lst = nil | cons(hd, tl:Lst)`). A witness read over a
    /// recursive-element array store folds to a McCarthy `ite` over unbounded
    /// datatype values whose bounded field congruence cannot refute a deep clash;
    /// such an array is fail-closed by the bypass anyway, so minting its witness is
    /// both useless and (observed on `store a i L64 = store a i R64`) harmful — it
    /// flips a sound Unknown to a false SAT. Skip it.
    fn dt_is_recursive(
        &self,
        dt_name: &str,
        datatype_ctors: &HashMap<String, Vec<String>>,
    ) -> bool {
        fn go(
            exec: &Executor,
            dt: &str,
            ctors: &HashMap<String, Vec<String>>,
            path: &mut Vec<String>,
        ) -> bool {
            if path.iter().any(|n| n == dt) {
                return true;
            }
            let Some(cs) = ctors.get(dt).cloned() else {
                return false;
            };
            path.push(dt.to_string());
            for c in cs {
                if let Some(sels) = exec.selector_signature_in(dt, &c) {
                    for (_, fsort) in &sels {
                        let child = match fsort {
                            Sort::Array(a) => dt_sort_name(&a.element_sort, ctors),
                            s => dt_sort_name(s, ctors),
                        };
                        if let Some(child) = child {
                            if go(exec, &child, ctors, path) {
                                path.pop();
                                return true;
                            }
                        }
                    }
                }
            }
            path.pop();
            false
        }
        go(self, dt_name, datatype_ctors, &mut Vec::new())
    }

    /// Index sorts `(key, sort)` of every datatype-ELEMENT array field reachable
    /// through the constructor fields of datatype `dt_name` (transitively via
    /// datatype-valued fields), bounded by a `visited` set.
    ///
    /// A datatype whose field is an `Array _ <datatype>` (e.g. `Lst =
    /// nil | cons(hd: Array _ Inner)`, or `Slice_Slice = mk(Array _ Slice)`)
    /// turns a datatype-VALUE equality `(= l1 l2)` — even between two BARE
    /// VARIABLES — into a congruence-DERIVED array-of-datatype equality
    /// `(= (hd l1) (hd l2))` that is never asserted as an atom, so
    /// [`Self::dt_array_equality_read_congruence_axioms`] never witnesses it and
    /// its cells can disagree (adversarial audit, nested-dt-array class:
    /// datatype-with-array-field congruence). Collecting the value equality (see
    /// below) and minting witness indices for these field arrays closes it.
    fn dt_field_array_index_sorts(
        &self,
        dt_name: &str,
        datatype_ctors: &HashMap<String, Vec<String>>,
        visited: &mut HashSet<String>,
        out: &mut Vec<(String, Sort)>,
    ) {
        if !visited.insert(dt_name.to_string()) {
            return;
        }
        let Some(ctors) = datatype_ctors.get(dt_name).cloned() else {
            return;
        };
        for ctor in ctors {
            let Some(sels) = self.selector_signature_in(dt_name, &ctor) else {
                continue;
            };
            for (_, fsort) in &sels {
                match fsort {
                    Sort::Array(a) => {
                        if let Some(elem_dt) = dt_sort_name(&a.element_sort, datatype_ctors) {
                            out.push((format!("{}", a.index_sort), a.index_sort.clone()));
                            self.dt_field_array_index_sorts(&elem_dt, datatype_ctors, visited, out);
                        }
                    }
                    other => {
                        if let Some(child) = dt_sort_name(other, datatype_ctors) {
                            self.dt_field_array_index_sorts(&child, datatype_ctors, visited, out);
                        }
                    }
                }
            }
        }
    }

    /// Fold `(select arr idx)` through store chains, `ite`, and const-arrays,
    /// returning a term SEMANTICALLY EQUAL to the raw select. Helper for
    /// [`Self::dt_array_equality_read_congruence_axioms`]: the array ROW pass
    /// has already run by the time that pass synthesizes selects, and a
    /// datatype-element select carries no bits, so an unfolded
    /// `(select (store a i (C v)) i)` would never reduce to `(C v)`.
    ///
    /// SOUNDNESS: every rewrite is a valid array identity —
    /// `(select (store b i v) i) = v` (ROW1), `(select (store b i v) j) =
    /// (select b j)` when `i,j` are distinct constants (ROW2), the general
    /// McCarthy `(ite (= i j) v (select b j))`, and `(select (ite g A B) j) =
    /// (ite g (select A j) (select B j))` — so the folded term denotes the same
    /// value in every model. Falls back to the raw select at the recursion
    /// bound or on any other array head.
    fn dt_fold_select(
        &mut self,
        arr: TermId,
        idx: TermId,
        elem_sort: &Sort,
        depth: usize,
    ) -> TermId {
        /// Bound on store-chain / ite nesting to fold through.
        const FOLD_BOUND: usize = 64;
        enum Head {
            Store(TermId, TermId, TermId),
            Ite(TermId, TermId, TermId),
            Other,
        }
        if depth >= FOLD_BOUND {
            return self.ctx.terms.mk_app(
                Symbol::named("select"),
                vec![arr, idx],
                elem_sort.clone(),
            );
        }
        // Const-array fold: `(select ((as const _) v) i) = v` for EVERY index i
        // (#dt-array-extensionality-witness). Without this, a const-array over a
        // datatype element hits `Head::Other` below and stays an opaque select —
        // so a const-array equality whose contradiction lives at the (symbolic
        // witness) index could never surface the field disagreement. The const
        // fill is index-independent, so this is sound in every model.
        if let Some(fill) = self.ctx.terms.get_const_array(arr) {
            return fill;
        }
        let head = match self.ctx.terms.get(arr) {
            TermData::App(Symbol::Named(n), args) if n == "store" && args.len() == 3 => {
                Head::Store(args[0], args[1], args[2])
            }
            TermData::Ite(g, th, el) => Head::Ite(*g, *th, *el),
            _ => Head::Other,
        };
        match head {
            Head::Store(base, sidx, sval) => {
                if sidx == idx {
                    return sval; // ROW1 (hash-consed identical index)
                }
                let i_const = matches!(self.ctx.terms.get(idx), TermData::Const(_));
                let s_const = matches!(self.ctx.terms.get(sidx), TermData::Const(_));
                if i_const && s_const {
                    // Distinct constant indices -> read straight through (ROW2).
                    return self.dt_fold_select(base, idx, elem_sort, depth + 1);
                }
                // Symbolic: exact McCarthy expansion (sound in every model).
                let base_read = self.dt_fold_select(base, idx, elem_sort, depth + 1);
                let cond = self.ctx.terms.mk_eq(idx, sidx);
                self.ctx.terms.mk_ite(cond, sval, base_read)
            }
            Head::Ite(g, th, el) => {
                let tr = self.dt_fold_select(th, idx, elem_sort, depth + 1);
                let er = self.dt_fold_select(el, idx, elem_sort, depth + 1);
                self.ctx.terms.mk_ite(g, tr, er)
            }
            Head::Other => {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), vec![arr, idx], elem_sort.clone())
            }
        }
    }

    /// Emit guarded field/tester congruence `(=> guard (= sel(a) sel(b)))` /
    /// `(=> guard (= is-C(a) is-C(b)))` for the datatype-valued term pair
    /// `(a, b)`, recursing (bounded) into datatype-valued fields. The selectors
    /// and testers are FOLDED through ite/constructor (dt_fold_selector /
    /// dt_fold_tester) so they reduce even though the ordinary
    /// selector-over-ite / selector-of-constructor rewrites already ran before
    /// these synthesized terms existed. Helper for
    /// [`Self::dt_array_equality_read_congruence_axioms`]; soundness argued
    /// there (congruence over total selectors/testers).
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    fn emit_dt_read_field_congruence(
        &mut self,
        guard: TermId,
        a: TermId,
        b: TermId,
        dt_name: &str,
        datatype_ctors: &HashMap<String, Vec<String>>,
        indices_by_sort: &HashMap<String, Vec<TermId>>,
        depth: usize,
        max_depth: usize,
        axioms: &mut Vec<TermId>,
        seen: &mut HashSet<(TermId, TermId)>,
    ) {
        if depth >= max_depth || a == b {
            return;
        }
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if !seen.insert(key) {
            return;
        }
        let Some(ctors) = datatype_ctors.get(dt_name).cloned() else {
            return;
        };
        if ctors.is_empty() {
            return;
        }
        // Multi-constructor: folded tester agreement `is-C(a) = is-C(b)` for
        // every constructor (this also discharges cross-constructor disjointness
        // — mismatched tags force `guard` false).
        if ctors.len() > 1 {
            for ctor in &ctors {
                let ta = self.dt_fold_tester(ctor, a, 0);
                let tb = self.dt_fold_tester(ctor, b, 0);
                if ta != tb {
                    let eq = self.ctx.terms.mk_eq(ta, tb);
                    axioms.push(self.ctx.terms.mk_implies(guard, eq));
                }
            }
        }
        // Folded field congruence for every selector of every constructor
        // (selectors are total, so this is unconditional congruence).
        let mut nested: Vec<(TermId, TermId, String)> = Vec::new();
        for ctor in &ctors {
            let Some(selectors) = self.selector_signature_in(dt_name, ctor) else {
                continue;
            };
            for (sel_name, sel_sort) in &selectors {
                let fa = self.dt_fold_selector(sel_name, sel_sort, dt_name, a, 0);
                let fb = self.dt_fold_selector(sel_name, sel_sort, dt_name, b, 0);
                if fa == fb {
                    continue;
                }
                if let Some(nested_dt) = dt_sort_name(sel_sort, datatype_ctors) {
                    nested.push((fa, fb, nested_dt));
                }
                if let Some(feq) = mk_eq_same_sort(&mut self.ctx.terms, fa, fb) {
                    axioms.push(self.ctx.terms.mk_implies(guard, feq));
                }
                // ARRAY-of-datatype field (#dt-field-array-congruence): a field
                // like `Cell.d : (Array _ Inner)` makes `(= fa fb)` itself a
                // datatype-ELEMENT-array equality, so recurse the read-over-
                // equality into it — for every observed index `j` of the
                // field-array's index sort emit `(=> guard (= (select fa j)
                // (select fb j)))` and recurse the field/tester congruence into
                // the ELEMENT datatype. Without this the nested chain
                // `(= (mk D0)(mk D1)) => (= D0 D1) => (= (select D0 j)(select D1
                // j))` never reaches the element selects, so they can disagree —
                // a spurious model. SOUND: read-over-array-equality + selector/
                // tester congruence are theory tautologies.
                if let Sort::Array(arr) = sel_sort {
                    if let Some(elem_dt) = dt_sort_name(&arr.element_sort, datatype_ctors) {
                        let idx_key = format!("{}", arr.index_sort);
                        if let Some(indices) = indices_by_sort.get(&idx_key).cloned() {
                            let elem_sort = arr.element_sort.clone();
                            for j in indices {
                                // FOLD the inner select through const-array / ROW /
                                // ite (`dt_fold_select`): when `fa` is a folded
                                // const-array (e.g. `f1(c1(inner))` reduced to the
                                // inner const-array), `(select fa j)` must reduce to
                                // its fill `(c2 #b0)` for the leaf clash to surface —
                                // a raw select over a datatype-element const-array
                                // carries no bits and never reduces (nested const
                                // class). A bare-Var field array folds to the raw
                                // select unchanged (sound no-op).
                                let sel_a = self.dt_fold_select(fa, j, &elem_sort, 0);
                                let sel_b = self.dt_fold_select(fb, j, &elem_sort, 0);
                                if sel_a == sel_b {
                                    continue;
                                }
                                if let Some(seq) =
                                    mk_eq_same_sort(&mut self.ctx.terms, sel_a, sel_b)
                                {
                                    axioms.push(self.ctx.terms.mk_implies(guard, seq));
                                }
                                nested.push((sel_a, sel_b, elem_dt.clone()));
                            }
                        }
                    }
                }
            }
        }
        for (fa, fb, ndt) in nested {
            self.emit_dt_read_field_congruence(
                guard,
                fa,
                fb,
                &ndt,
                datatype_ctors,
                indices_by_sort,
                depth + 1,
                max_depth,
                axioms,
                seen,
            );
        }
    }

    /// Fold a selector application `sel_name(t)` through `ite` and constructor
    /// heads, returning a term SEMANTICALLY EQUAL to the raw selector app.
    /// `sel_name(ite g x y) = ite g sel(x) sel(y)`; `sel_name(C(args)) =
    /// args[k]` when `sel_name` is `C`'s k-th selector (else the value is
    /// unspecified, so the raw app is kept). Needed because these synthesized
    /// projections postdate the selector-over-ite / selector-of-constructor
    /// rewrite passes. SOUND: only valid datatype identities are applied.
    fn dt_fold_selector(
        &mut self,
        sel_name: &str,
        sel_sort: &Sort,
        dt_name: &str,
        t: TermId,
        depth: usize,
    ) -> TermId {
        /// Bound on ite nesting to fold through.
        const FOLD_BOUND: usize = 64;
        enum Head {
            Ite(TermId, TermId, TermId),
            Ctor(String),
            Other,
        }
        let mk_raw = |terms: &mut TermStore| {
            terms.mk_app(Symbol::named(sel_name), vec![t], sel_sort.clone())
        };
        if depth >= FOLD_BOUND {
            return mk_raw(&mut self.ctx.terms);
        }
        let head = match self.ctx.terms.get(t) {
            TermData::Ite(g, x, y) => Head::Ite(*g, *x, *y),
            TermData::App(Symbol::Named(n), _) if self.ctx.is_constructor(n).is_some() => {
                Head::Ctor(n.clone())
            }
            _ => Head::Other,
        };
        match head {
            Head::Ite(g, x, y) => {
                let fx = self.dt_fold_selector(sel_name, sel_sort, dt_name, x, depth + 1);
                let fy = self.dt_fold_selector(sel_name, sel_sort, dt_name, y, depth + 1);
                self.ctx.terms.mk_ite(g, fx, fy)
            }
            Head::Ctor(cn) => {
                let args = match self.ctx.terms.get(t) {
                    TermData::App(_, args) => args.clone(),
                    _ => return mk_raw(&mut self.ctx.terms),
                };
                if let Some(selectors) = self.selector_signature_in(dt_name, &cn) {
                    if let Some(pos) = selectors.iter().position(|(sn, _)| sn == sel_name) {
                        if pos < args.len() {
                            return args[pos];
                        }
                    }
                }
                mk_raw(&mut self.ctx.terms)
            }
            Head::Other => mk_raw(&mut self.ctx.terms),
        }
    }

    /// Fold a tester `is-ctor_name(t)` through `ite` and constructor heads to a
    /// Bool term semantically equal to the raw tester: `is-C(ite g x y) = ite g
    /// is-C(x) is-C(y)`; `is-C(D(..)) = (C == D)` as a bool literal. SOUND:
    /// valid datatype identities only.
    fn dt_fold_tester(&mut self, ctor_name: &str, t: TermId, depth: usize) -> TermId {
        const FOLD_BOUND: usize = 64;
        enum Head {
            Ite(TermId, TermId, TermId),
            Ctor(String),
            Other,
        }
        let tester = format!("is-{ctor_name}");
        if depth >= FOLD_BOUND {
            return self
                .ctx
                .terms
                .mk_app(Symbol::named(&tester), vec![t], Sort::Bool);
        }
        let head = match self.ctx.terms.get(t) {
            TermData::Ite(g, x, y) => Head::Ite(*g, *x, *y),
            TermData::App(Symbol::Named(n), _) if self.ctx.is_constructor(n).is_some() => {
                Head::Ctor(n.clone())
            }
            _ => Head::Other,
        };
        match head {
            Head::Ite(g, x, y) => {
                let fx = self.dt_fold_tester(ctor_name, x, depth + 1);
                let fy = self.dt_fold_tester(ctor_name, y, depth + 1);
                self.ctx.terms.mk_ite(g, fx, fy)
            }
            Head::Ctor(cn) => self.ctx.terms.mk_bool(cn == ctor_name),
            Head::Other => self
                .ctx
                .terms
                .mk_app(Symbol::named(&tester), vec![t], Sort::Bool),
        }
    }

    pub(in crate::executor) fn dt_store_value_injectivity_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        // AY-MARKER: dt_store_value_injectivity_axioms
        /// Recursion bound for datatype-valued constructor fields (mirrors the
        /// DT-depth cap used by the sibling congruence passes).
        const MAX_RECURSIVE_DT_DEPTH: usize = 3;

        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }

        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if datatype_ctors.is_empty() {
            return Vec::new();
        }

        // Reachable terms from the asserted set (#5082 discipline): only bridge
        // stores actually constrained by the problem.
        //
        // Deliberately does NOT descend into quantifier bodies: a store under a
        // binder mentions BOUND variables, and emitting a ground implication over
        // it would capture those variables outside their scope (a malformed /
        // unsound axiom). Ground stores — every store in our decidable target
        // fragment — are still collected. Quantified datatype-array problems keep
        // the fail-closed gate (see `dt_array_injectivity_fully_modeled`).
        let reachable: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    // Quantifier bodies are opaque here (bound-variable capture).
                    TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                    _ => {}
                }
            }
            visited
        };

        // Collect reachable datatype-valued store terms: (store_term, index, value).
        let mut dt_stores: Vec<(TermId, TermId, TermId)> = Vec::new();
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            if !reachable.contains(&term) {
                continue;
            }
            let (index, value) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                    (args[1], args[2])
                }
                _ => continue,
            };
            if dt_sort_name(self.ctx.terms.sort(value), &datatype_ctors).is_none() {
                continue;
            }
            dt_stores.push((term, index, value));
        }
        if dt_stores.len() < 2 {
            return Vec::new();
        }

        let mut axioms: Vec<TermId> = Vec::new();
        for a in 0..dt_stores.len() {
            for b in (a + 1)..dt_stores.len() {
                let (s1, idx1, v1) = dt_stores[a];
                let (s2, idx2, v2) = dt_stores[b];
                // Two stores can only be equal if they share the full array sort
                // (index AND element). `mk_eq_same_sort` guards this below, but
                // bail early to avoid pointless work.
                if self.ctx.terms.sort(s1) != self.ctx.terms.sort(s2) {
                    continue;
                }
                let Some(consequent) =
                    self.dt_store_value_injectivity_consequent(v1, v2, 0, MAX_RECURSIVE_DT_DEPTH)
                else {
                    continue;
                };
                let Some(store_eq) = mk_eq_same_sort(&mut self.ctx.terms, s1, s2) else {
                    continue;
                };
                let antecedent = if idx1 == idx2 {
                    store_eq
                } else {
                    let Some(idx_eq) = mk_eq_same_sort(&mut self.ctx.terms, idx1, idx2) else {
                        continue;
                    };
                    self.ctx.terms.mk_and(vec![store_eq, idx_eq])
                };
                let implication = self.ctx.terms.mk_implies(antecedent, consequent);
                axioms.push(implication);
            }
        }
        axioms
    }

    /// Compute the datatype constructor injectivity/disjointness consequent for
    /// the store-value pair `(v1, v2)`; helper for
    /// [`Self::dt_store_value_injectivity_axioms`] (soundness argued there).
    ///
    /// Returns `None` when the pair imposes no constraint (structurally
    /// identical values), otherwise a Bool term:
    ///   - the interned `false` constant for distinct constructors (disjoint),
    ///   - a conjunction of field equalities for a shared constructor
    ///     (injective, recursing bounded-depth through datatype-valued fields),
    ///   - the bare value equality `(= v1 v2)` when at least one side is not a
    ///     constructor application.
    fn dt_store_value_injectivity_consequent(
        &mut self,
        v1: TermId,
        v2: TermId,
        depth: usize,
        max_depth: usize,
    ) -> Option<TermId> {
        if v1 == v2 {
            return None;
        }
        match (self.dt_ctor_app_parts(v1), self.dt_ctor_app_parts(v2)) {
            (Some((c1, args1)), Some((c2, args2))) => {
                if c1 != c2 {
                    // Distinct constructors: `v1 = v2` is impossible. The caller
                    // turns `(=> A false)` into `(not A)`.
                    return Some(self.ctx.terms.mk_bool(false));
                }
                // Shared constructor: injectivity relates the field arguments.
                if args1.len() != args2.len() {
                    // Defensive: a shared constructor always has matching arity;
                    // fall back to the bare value equality if not.
                    return mk_eq_same_sort(&mut self.ctx.terms, v1, v2);
                }
                let false_term = self.ctx.terms.mk_bool(false);
                let mut conjuncts: Vec<TermId> = Vec::new();
                for (a, b) in args1.into_iter().zip(args2) {
                    if a == b {
                        continue;
                    }
                    let sub = if depth + 1 < max_depth
                        && self.dt_ctor_app_parts(a).is_some()
                        && self.dt_ctor_app_parts(b).is_some()
                    {
                        self.dt_store_value_injectivity_consequent(a, b, depth + 1, max_depth)
                    } else {
                        mk_eq_same_sort(&mut self.ctx.terms, a, b)
                    };
                    if let Some(c) = sub {
                        // A nested disjointness makes the whole equality
                        // impossible: `C(.. D(..) ..) = C(.. E(..) ..)` is UNSAT.
                        if c == false_term {
                            return Some(false_term);
                        }
                        conjuncts.push(c);
                    }
                }
                if conjuncts.is_empty() {
                    return None;
                }
                Some(self.ctx.terms.mk_and(conjuncts))
            }
            // At least one operand is not a constructor application: emit the
            // bare value equality. The store-value injectivity `A => (= v1 v2)`
            // is still a valid array consequence, and the existing DT
            // value-equality congruence pass relates `(= v1 v2)` further.
            _ => mk_eq_same_sort(&mut self.ctx.terms, v1, v2),
        }
    }

    /// Constructor name + argument terms of a datatype constructor application.
    ///
    /// Handles BOTH non-nullary constructors (stored as `App`) and nullary
    /// constructors (stored as `Var`, with no arguments).
    fn dt_ctor_app_parts(&self, term: TermId) -> Option<(String, Vec<TermId>)> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(n), args) if self.ctx.is_constructor(n).is_some() => {
                Some((n.clone(), args.clone()))
            }
            TermData::Var(n, _) if self.ctx.is_constructor(n).is_some() => {
                Some((n.clone(), Vec::new()))
            }
            _ => None,
        }
    }

    /// Generate DT selector, tester, exhaustiveness, constructor, and equality axioms.
    ///
    /// This is the central DT axiom generator for combined DT+theory solver paths
    /// (DT_AUFLIA, DT_AUFLRA, DT_AUFLIRA, DT_UFBV, DT_AUFBV, DT_AX). It produces
    /// five classes of axioms:
    ///
    /// (A) Selector projection: `sel_i(C(a_0, ..., a_n)) = a_i`
    /// (B) Tester evaluation: `is-C(C(...)) = true`, `is-C'(C(...)) = false`
    /// (B') Tester evaluation for axiom-C terms (second pass, #2766)
    /// (C) Constructor: `is-C(x) => x = C(sel_1(x), ..., sel_n(x))`
    /// (D) Exhaustiveness: `(or (is-C1 x) ... (is-Ck x))` for DT variables
    /// (E) Equality-to-tester: `x = C(...) => is-C(x)` (#1737)
    ///
    /// Also handles:
    /// - Transitive equality propagation via union-find (#1741)
    /// - Variable indirection: `p = C(args)` => selector axioms for `p` (#1740)
    /// - Nested selector resolution (#1765)
    /// - Reachability filtering to avoid combinatorial explosion (#5082)
    pub(in crate::executor) fn dt_selector_axioms(
        &mut self,
        base_assertions: &HashSet<TermId>,
    ) -> Vec<TermId> {
        // Warm-start depth: the eager pass unrolls recursive selector structure to
        // this fixed depth as a fast path for shallow problems. The lazy DT
        // final-check (`solve_dt` iterative deepening) is the completeness backstop
        // for anything deeper. See `DT_WARM_START_DEPTH` and `solve_dt`.
        self.dt_selector_axioms_to_depth(base_assertions, DT_WARM_START_DEPTH)
    }

    /// Generate DT selector/tester/constructor axioms, unrolling recursive
    /// datatype structure to `max_recursive_depth` levels.
    ///
    /// This is the depth-parameterized core of [`Self::dt_selector_axioms`].
    /// Calling it with a larger `max_recursive_depth` materializes deeper
    /// selector subterms (`sel_i(sel_j(...))`) and generates their exhaustiveness
    /// (D) + constructor (C) + tester (B') axioms, allowing the SAT solver to
    /// case-split deeper. Every axiom added is a datatype-theory tautology
    /// (exhaustiveness: a DT value matches exactly one constructor;
    /// `sel_i(C(a)) = a_i`), so a deeper unroll can only SHRINK the model space
    /// and never cause a false-UNSAT — it only retires the depth-bounded
    /// incompleteness (spurious SAT / Unknown) of shallower unrolls.
    pub(in crate::executor) fn dt_selector_axioms_to_depth(
        &mut self,
        base_assertions: &HashSet<TermId>,
        max_recursive_depth: usize,
    ) -> Vec<TermId> {
        // Capture the current term-store size so we don't scan terms created during
        // axiom generation itself.
        let base_term_len = self.ctx.terms.len();
        if base_term_len == 0 {
            return Vec::new();
        }

        // First pass: collect constructor applications + selector metadata without
        // mutating the term store (avoids borrow conflicts and unstable references).
        let mut ctor_apps: Vec<CtorAppInfo> = Vec::new();

        // Collect ALL constructor terms (including nullary) for tester evaluation axioms (B).
        // Each entry: (term, ctor_name, dt_name) where dt_name is the datatype.
        // Note: Nullary constructors are stored as Var terms, not App terms (#1745).
        let mut ctor_terms_for_testers: Vec<(TermId, String, String)> = Vec::new();

        // Union-find for computing equivalence classes of asserted equalities.
        // This handles transitive equality propagation (#1741): if `p = q` and `q = C(args)`,
        // we need to generate selector axioms for `p` as well.
        let mut uf_parent: HashMap<TermId, TermId> = HashMap::default();
        let uf_find = |parent: &mut HashMap<TermId, TermId>, mut x: TermId| -> TermId {
            let mut path = Vec::new();
            while let Some(&p) = parent.get(&x) {
                if p == x {
                    break;
                }
                path.push(x);
                x = p;
            }
            // Path compression
            for node in path {
                parent.insert(node, x);
            }
            x
        };
        let uf_union = |parent: &mut HashMap<TermId, TermId>, a: TermId, b: TermId| {
            let ra = uf_find(parent, a);
            let rb = uf_find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        };

        // Collect asserted equalities for union-find
        let mut asserted_equalities: Vec<(TermId, TermId)> = Vec::new();

        // Maps: term p -> (ctor_name, args, selectors) for direct `p = C(args)` equalities
        let mut var_to_ctor: HashMap<TermId, CtorBinding> = HashMap::default();

        // Collect selector applications in the term store: sel_name -> [(sel_app, arg)]
        // where sel_app = sel(arg).
        let mut selector_apps: HashMap<String, Vec<(TermId, TermId)>> = HashMap::default();

        for idx in 0..base_term_len {
            debug_assert!(u32::try_from(idx).is_ok(), "term id overflow");
            let term = TermId::new(idx as u32);

            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    // Check if this is a constructor application
                    if let Some(selectors) = self.ctx.constructor_selectors(name) {
                        let selectors_empty = selectors.is_empty();
                        let arg_len = args.len();
                        // Resolve the datatype from the term's actual sort so that
                        // parametric instances (e.g. (Opt Int) vs (Opt Bool)) stay
                        // distinct instead of aliasing on the shared constructor name.
                        let dt_of_term = self.dt_name_of(term);

                        // Track ALL constructor terms for tester axioms (B) (#1745)
                        if let Some((dt_name, ctor_name)) = self.ctx.is_constructor(name) {
                            let dt = dt_of_term.clone().unwrap_or(dt_name);
                            ctor_terms_for_testers.push((term, ctor_name, dt));
                        }

                        // Only collect selector metadata for non-nullary constructors
                        if !selectors_empty {
                            if let Some(selector_syms) = dt_of_term
                                .as_deref()
                                .and_then(|dt| self.selector_signature_in(dt, name))
                            {
                                if selector_syms.len() == arg_len {
                                    ctor_apps.push((term, args.clone(), selector_syms));
                                }
                            }
                        }
                    }

                    // Check if this is a selector application (single argument function
                    // where the function name is a registered selector).
                    if args.len() == 1 {
                        // Check if name is a selector by looking for it in any constructor's
                        // selector list.
                        for (_ctor_name, sel_list) in self.ctx.ctor_selectors_iter() {
                            if sel_list.contains(&name.clone()) {
                                selector_apps
                                    .entry(name.clone())
                                    .or_default()
                                    .push((term, args[0]));
                                break;
                            }
                        }
                    }

                    // Check if this is an equality `= p C(args)` or `= C(args) p`
                    // CRITICAL: Only process equalities that are directly asserted,
                    // not equalities nested inside larger formulas (e.g., disjunctions).
                    // Generating axioms for non-asserted equalities is unsound (#1740 audit).
                    if name == "=" && args.len() == 2 && base_assertions.contains(&term) {
                        let (lhs, rhs) = (args[0], args[1]);

                        // Check if either side is a constructor
                        let lhs_is_ctor = matches!(
                            self.ctx.terms.get(lhs),
                            TermData::App(Symbol::Named(n), _)
                            if self.ctx.constructor_selectors(n).is_some()
                        );
                        let rhs_is_ctor = matches!(
                            self.ctx.terms.get(rhs),
                            TermData::App(Symbol::Named(n), _)
                            if self.ctx.constructor_selectors(n).is_some()
                        );

                        // Collect variable-to-variable equalities for union-find (#1741)
                        if !lhs_is_ctor && !rhs_is_ctor {
                            asserted_equalities.push((lhs, rhs));
                        }

                        // Try to find which side is a constructor
                        for (p, ctor_term) in [(lhs, rhs), (rhs, lhs)] {
                            if let TermData::App(Symbol::Named(ctor_name), ctor_args) =
                                self.ctx.terms.get(ctor_term)
                            {
                                if let Some(selectors) = self.ctx.constructor_selectors(ctor_name) {
                                    if !selectors.is_empty() {
                                        if let Some(selector_syms) =
                                            self.dt_name_of(ctor_term).and_then(|dt| {
                                                self.selector_signature_in(&dt, ctor_name)
                                            })
                                        {
                                            if selector_syms.len() == ctor_args.len() {
                                                // Only record if p is NOT itself a constructor
                                                // app (direct ctor apps are handled above)
                                                let p_is_ctor = if p == lhs {
                                                    lhs_is_ctor
                                                } else {
                                                    rhs_is_ctor
                                                };
                                                if !p_is_ctor {
                                                    var_to_ctor.insert(
                                                        p,
                                                        (
                                                            ctor_name.clone(),
                                                            ctor_args.clone(),
                                                            selector_syms,
                                                        ),
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Handle nullary constructors stored as Var terms (#1745)
                // In ay, nullary constructors like `None` are stored as Var("None", id)
                // not App("None", []), so we need to check Var terms as well.
                TermData::Var(name, _) => {
                    if let Some((dt_name, ctor_name)) = self.ctx.is_constructor(name) {
                        ctor_terms_for_testers.push((term, ctor_name, dt_name));
                    }
                }
                _ => continue,
            }
        }

        // Build union-find from asserted equalities (#1741)
        for (a, b) in &asserted_equalities {
            uf_union(&mut uf_parent, *a, *b);
        }

        // Propagate var_to_ctor through equivalence classes (#1741)
        // If q = C(args) and p = q (transitively), then p should also map to C(args)
        // Sort for deterministic propagation order (#3060)
        let mut direct_mappings: Vec<_> =
            var_to_ctor.iter().map(|(k, v)| (*k, v.clone())).collect();
        direct_mappings.sort_by_key(|(term, _)| term.0);
        for (term, ctor_info) in direct_mappings {
            let root = uf_find(&mut uf_parent, term);
            // Find all terms in same equivalence class
            for (a, b) in &asserted_equalities {
                for t in [*a, *b] {
                    if t != term && uf_find(&mut uf_parent, t) == root {
                        var_to_ctor.entry(t).or_insert_with(|| ctor_info.clone());
                    }
                }
            }
        }

        // Second pass: generate equality axioms.
        //
        // For each constructor application `C(a_0, ..., a_{n-1})` and its ordered selector list
        // `[sel_0, ..., sel_{n-1}]`, generate the theory axiom:
        // `sel_i(C(a_0, ..., a_{n-1})) = a_i`.
        //
        // We also track which selector applications equal constructors, so we can generate
        // transitive axioms for nested selectors (#1765).
        let mut extra: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();

        // Track selector apps that equal constructor terms: sel_app -> (ctor_args, selectors)
        // This is used for nested selector resolution (#1765).
        let mut sel_app_to_ctor: HashMap<TermId, CtorArgsAndSelectors> = HashMap::default();

        for (ctor_term, args, selectors) in &ctor_apps {
            debug_assert_eq!(selectors.len(), args.len());
            for (idx, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                let sel_app = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    vec![*ctor_term],
                    sel_sort.clone(),
                );
                let Some(eq) = mk_eq_same_sort(&mut self.ctx.terms, sel_app, args[idx]) else {
                    continue;
                };

                if base_assertions.contains(&eq) {
                    continue;
                }
                if seen.insert(eq) {
                    extra.push(eq);
                }

                // Track that sel_app equals args[idx], which may be a constructor (#1765).
                // This enables nested selector resolution: if args[idx] is a constructor C2(...),
                // then any selector applied to sel_app should get axioms based on C2.
                let arg = args[idx];
                if let TermData::App(Symbol::Named(inner_ctor_name), inner_args) =
                    self.ctx.terms.get(arg)
                {
                    if let Some(inner_selectors) = self.ctx.constructor_selectors(inner_ctor_name) {
                        if !inner_selectors.is_empty() {
                            if let Some(inner_selector_syms) = self
                                .dt_name_of(arg)
                                .and_then(|dt| self.selector_signature_in(&dt, inner_ctor_name))
                            {
                                if inner_selector_syms.len() == inner_args.len() {
                                    sel_app_to_ctor
                                        .insert(sel_app, (inner_args.clone(), inner_selector_syms));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Third pass: generate selector axioms for variable indirection (#1740).
        //
        // For each equality `p = C(a_0, ..., a_{n-1})` in the assertions and each
        // selector application `sel_i(p)` in the term store, generate:
        // `sel_i(p) = a_i`.
        //
        // This handles cases like:
        //   (assert (= p (mk-pair x y)))
        //   (assert (not (= (fst p) x)))
        // Where we need `fst(p) = x` to derive a contradiction.
        for (p, (_ctor_name, args, selectors)) in &var_to_ctor {
            for (idx, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                // Check if sel_i(p) appears in the term store
                if let Some(apps) = selector_apps.get(sel_name) {
                    for &(sel_app, sel_arg) in apps {
                        if sel_arg == *p {
                            // Found sel_i(p), generate axiom sel_i(p) = a_i
                            let Some(eq) = mk_eq_same_sort(&mut self.ctx.terms, sel_app, args[idx])
                            else {
                                continue;
                            };

                            if base_assertions.contains(&eq) {
                                continue;
                            }
                            if seen.insert(eq) {
                                extra.push(eq);
                            }
                        }
                    }
                }

                // Also generate the canonical axiom sel_i(p) = a_i even if sel_i(p)
                // doesn't appear explicitly, because the SAT solver may need it.
                let sel_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(sel_name), vec![*p], sel_sort.clone());
                let Some(eq) = mk_eq_same_sort(&mut self.ctx.terms, sel_app, args[idx]) else {
                    continue;
                };

                if base_assertions.contains(&eq) {
                    continue;
                }
                if seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (E) Nested selector axioms for recursive datatypes (#1765).
        //
        // When sel(ctor(...)) = inner_ctor(...), any selector applied to sel(ctor(...))
        // should get axioms based on inner_ctor.
        //
        // Example: For Wrapper = base | c(f: Wrapper)
        //   f(c(c(base))) = c(base)     (generated in second pass)
        //   f(f(c(c(base)))) should equal f(c(base)) = base
        //
        // We iterate to fixpoint: keep generating axioms until no new ones are added.
        // This handles arbitrarily deep nesting.
        //
        // Safety bound: 100 iterations handles extremely deep nesting while protecting
        // against infinite loops from potential bugs. Each iteration processes one nesting
        // level, so this supports up to 100 levels of selector application.
        const MAX_NESTED_ITERATIONS: usize = 100;
        for _iteration in 0..MAX_NESTED_ITERATIONS {
            let mut new_axioms = Vec::new();
            let mut new_mappings: Vec<CtorAppInfo> = Vec::new();

            // For each selector application sel(arg) in the term store, check if arg
            // is known to equal a constructor (via sel_app_to_ctor).
            for (sel_name, apps) in &selector_apps {
                for &(sel_app_term, sel_arg) in apps {
                    // If sel_arg is a selector application that equals a constructor...
                    if let Some((ctor_args, ctor_selectors)) = sel_app_to_ctor.get(&sel_arg) {
                        // Find which selector index sel_name corresponds to
                        for (idx, (ctor_sel_name, _ctor_sel_sort)) in
                            ctor_selectors.iter().enumerate()
                        {
                            if ctor_sel_name == sel_name {
                                // Generate axiom: sel(sel_arg) = ctor_args[idx]
                                // But we already have sel_app_term = sel(sel_arg), so:
                                let Some(eq) = mk_eq_same_sort(
                                    &mut self.ctx.terms,
                                    sel_app_term,
                                    ctor_args[idx],
                                ) else {
                                    continue;
                                };
                                if !base_assertions.contains(&eq) && seen.insert(eq) {
                                    new_axioms.push(eq);

                                    // Track if the result is also a constructor
                                    let result = ctor_args[idx];
                                    if let TermData::App(Symbol::Named(inner_name), inner_args) =
                                        self.ctx.terms.get(result)
                                    {
                                        if let Some(inner_sels) =
                                            self.ctx.constructor_selectors(inner_name)
                                        {
                                            if !inner_sels.is_empty() {
                                                if let Some(inner_sel_syms) =
                                                    self.dt_name_of(result).and_then(|dt| {
                                                        self.selector_signature_in(&dt, inner_name)
                                                    })
                                                {
                                                    if inner_sel_syms.len() == inner_args.len() {
                                                        new_mappings.push((
                                                            sel_app_term,
                                                            inner_args.clone(),
                                                            inner_sel_syms,
                                                        ));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            }

            // If no new axioms were generated, we've reached fixpoint.
            if new_axioms.is_empty() {
                break;
            }

            extra.extend(new_axioms);
            for (sel_app, args, sels) in new_mappings {
                sel_app_to_ctor.entry(sel_app).or_insert((args, sels));
            }
        }

        // (D) Exhaustiveness axioms for datatype variables (#1738).
        //
        // For each datatype-sorted variable `x : D` with constructors `C_1..C_k`, assert:
        // `(or (is-C1 x) ... (is-Ck x))`
        //
        // This ensures at least one constructor applies to any datatype value.
        //
        // Note: Datatype sorts are stored as Sort::Uninterpreted("<name>") in ay, not
        // Sort::Datatype. We identify datatype-sorted symbols by checking if their sort
        // name matches a declared datatype.
        //
        // Implementation: Build a map from datatype name -> constructors once, then use it
        // for both identifying DT-sorted variables and generating axioms.
        let datatype_ctors: HashMap<String, Vec<String>> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();

        // Collect all term IDs reachable from assertions to avoid generating
        // axioms for unconstrained DT variables (#5082). Benchmarks like
        // typed_v5l20092 declare 15 DT variables but only use 1 in assertions;
        // generating exhaustiveness + constructor axioms for all 15 creates a
        // combinatorial explosion that prevents solving.
        let reachable_terms: HashSet<TermId> = {
            let mut visited = HashSet::default();
            let mut stack: Vec<TermId> = base_assertions.iter().copied().collect();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Const(_) | TermData::Var(_, _) => {}
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, val) in bindings {
                            stack.push(*val);
                        }
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        stack.push(*body);
                    }
                    // All current TermData variants are handled above.
                    // This arm is required by #[non_exhaustive] and catches future variants.
                    other => unreachable!(
                        "unhandled TermData variant in dt_axioms reachability: {other:?}"
                    ),
                }
            }
            visited
        };

        let dt_vars: Vec<(TermId, String)> = {
            let mut result: Vec<(TermId, String)> = self
                .ctx
                .symbol_iter()
                .filter_map(|(sym_name, info)| {
                    // Skip constructor symbols themselves - they get tester evaluation axioms (B),
                    // not exhaustiveness axioms (D). Exhaustiveness is for user-declared variables.
                    if self.ctx.is_constructor(sym_name).is_some() {
                        return None;
                    }
                    if let Sort::Uninterpreted(sort_name) = &info.sort {
                        if datatype_ctors.contains_key(sort_name) {
                            // Only generate axioms for variables reachable from assertions (#5082).
                            // Skip symbols already bound to a constructor application (e.g. the
                            // eager datatype-elimination of a single-constructor constant): their
                            // constructor is explicit, so exhaustiveness (D) and constructor (C)
                            // axioms are redundant. Worse, (C) would synthesize fresh
                            // selector-over-constructor sub-terms whose interaction with a
                            // constructor=constructor equality drives the combined-theory solver
                            // to `unknown` on an otherwise-SAT problem. The ctor-app's structure
                            // is fully covered by the selector (A), tester (B), and injectivity
                            // (F) passes that scan constructor applications directly.
                            return info
                                .term
                                .filter(|t| reachable_terms.contains(t))
                                .filter(|t| !self.term_is_constructor_app(*t))
                                .map(|t| (t, sort_name.clone()));
                        }
                    }
                    // Also check Sort::Datatype for completeness
                    if let Sort::Datatype(dt) = &info.sort {
                        return info
                            .term
                            .filter(|t| reachable_terms.contains(t))
                            .filter(|t| !self.term_is_constructor_app(*t))
                            .map(|t| (t, dt.name.clone()));
                    }
                    None
                })
                .collect();

            // (#6190) Also collect DT-sorted selector applications from assertions.
            //
            // Selector applications like `(cdr x4)` produce values of datatype
            // sort but are not declared symbols. Without exhaustiveness axioms
            // for these sub-terms, the solver cannot derive that e.g.
            // `(cdr x4)` must be one of the constructors, causing false SAT.
            //
            // (#6201) Only add exhaustiveness for selector applications, not ALL
            // DT-sorted sub-terms. The original #6190 fix was too broad — adding
            // exhaustiveness for every DT-sorted reachable term caused a 13.8%
            // performance regression on QF_DT benchmarks (174→150 solves).
            // Selector applications are the specific case that caused the soundness
            // bug; other DT-sorted terms (ITE, UF) inherit exhaustiveness from
            // their constituent variables.
            let existing: HashSet<TermId> = result.iter().map(|(t, _)| *t).collect();
            let selector_term_ids: HashSet<TermId> = selector_apps
                .values()
                .flat_map(|apps| apps.iter().map(|(sel_app, _arg)| *sel_app))
                .collect();
            for &t in &selector_term_ids {
                if existing.contains(&t) || !reachable_terms.contains(&t) {
                    continue;
                }
                let sort = self.ctx.terms.sort(t);
                let dt_name = match sort {
                    Sort::Uninterpreted(name) if datatype_ctors.contains_key(name) => name.clone(),
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                    _ => continue,
                };
                result.push((t, dt_name));
            }

            // (#dt-array-WS) Also collect DT-sorted array `select` applications.
            // `(select A i)` of a datatype element sort must be one of that
            // datatype's constructors, but without an exhaustiveness axiom the SAT
            // solver may leave every tester false (e.g. both `(not (is-none_i
            // (select A 3)))` and `(not (is-some_i (select A 3)))`) — a phantom DT
            // inhabitant -> false SAT. Narrowly scoped to array selects (not all
            // DT-sorted UF apps) to avoid the #6201 blanket-exhaustiveness perf
            // regression; still bounded by reachability.
            let seen: HashSet<TermId> = result.iter().map(|(t, _)| *t).collect();
            for &t in &reachable_terms {
                if seen.contains(&t) {
                    continue;
                }
                let TermData::App(sym, _) = self.ctx.terms.get(t) else {
                    continue;
                };
                if sym.name() != "select" {
                    continue;
                }
                let dt_name = match self.ctx.terms.sort(t) {
                    Sort::Uninterpreted(name) if datatype_ctors.contains_key(name) => name.clone(),
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                    _ => continue,
                };
                result.push((t, dt_name));
            }

            // (fuzzer-found false-SAT) A DT-sorted UF-application or `ite` term
            // that is the ARGUMENT of a reachable tester `(_ is c) t` needs its own
            // exhaustiveness (D) + constructor (C) axioms. Without them a UF/ite DT
            // result is a phantom inhabitant: `(_ is c0)(f x)` and `(_ is c1)(f x)`
            // can BOTH be true (false-SAT) because nothing forces `(f x) = c0` AND
            // `= c1` into a constructor clash the way the (C) axiom does for plain
            // variables. The #6201 "ITE/UF inherit exhaustiveness from constituent
            // variables" assumption is unsound for UF results. Scoped to
            // tester-argument terms (a small set) to avoid the #6201
            // blanket-exhaustiveness perf regression; still bounded by reachability.
            let already: HashSet<TermId> = result.iter().map(|(t, _)| *t).collect();
            let mut derived_dt: Vec<TermId> = Vec::new();
            for &t in &reachable_terms {
                if let TermData::App(sym, targs) = self.ctx.terms.get(t) {
                    let nm = sym.name();
                    if nm.starts_with("is-")
                        && targs.len() == 1
                        && self.ctx.is_constructor(&nm[3..]).is_some()
                    {
                        derived_dt.push(targs[0]);
                    }
                }
            }
            for t in derived_dt {
                if already.contains(&t)
                    || !matches!(self.ctx.terms.get(t), TermData::App(..) | TermData::Ite(..))
                    || self.term_is_constructor_app(t)
                {
                    continue;
                }
                let dt_name = match self.ctx.terms.sort(t) {
                    Sort::Uninterpreted(name) if datatype_ctors.contains_key(name) => name.clone(),
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => dt.name.clone(),
                    _ => continue,
                };
                result.push((t, dt_name));
            }
            result
        };

        for (var_term, dt_name) in &dt_vars {
            let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                continue;
            };

            if dt_ctors.is_empty() {
                continue;
            }

            // Build disjunction of all testers: (or (is-C1 x) ... (is-Ck x))
            let mut tester_apps = Vec::new();
            for ctor_name in dt_ctors {
                let tester_name = format!("is-{ctor_name}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![*var_term], Sort::Bool);
                tester_apps.push(tester_app);
            }

            let axiom = self.ctx.terms.mk_or(tester_apps);
            if !base_assertions.contains(&axiom) && seen.insert(axiom) {
                extra.push(axiom);
            }
        }

        // (B) Tester evaluation axioms (#1745).
        //
        // For each constructor term `C(...)` in the term store, generate:
        // - `is-C(C(...)) = true` (positive case)
        // - `is-C'(C(...)) = false` for all other constructors C' of the same datatype (negative case)
        //
        // This ensures that recognizers evaluate correctly for concrete constructor values,
        // including nullary constructors like `None` where `is-None(None) = true`.
        for (ctor_term, ctor_name, dt_name) in ctor_terms_for_testers {
            // Get all constructors of this datatype
            let Some(dt_ctors) = datatype_ctors.get(&dt_name) else {
                continue;
            };

            let true_term = self.ctx.terms.true_term();
            let false_term = self.ctx.terms.false_term();

            for other_ctor in dt_ctors {
                let tester_name = format!("is-{other_ctor}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![ctor_term], Sort::Bool);

                // is-C(C(...)) = true, is-C'(C(...)) = false for C' != C
                let expected = if other_ctor == &ctor_name {
                    true_term
                } else {
                    false_term
                };

                let eq = self.ctx.terms.mk_eq(tester_app, expected);
                if !base_assertions.contains(&eq) && seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (C) + (D-recursive) + (B') Constructor axioms with recursive depth expansion (#5108).
        //
        // For recursive datatypes (e.g., Tower = stack(Enum, Tower) | empty), axiom (C)
        // creates selector applications like `sel_2(x) : Tower`. These sub-terms need
        // their own exhaustiveness (D) and constructor (C) axioms to allow the SAT solver
        // to case-split on them. Without this, the solver cannot reason about the
        // structure of recursive sub-terms, causing timeouts on benchmarks like
        // blocksworld and typed CVC.
        //
        // We iterate: at each depth level, generate (C) + (D) + (B') axioms for the
        // current DT variable set, then collect newly created DT-sorted selector terms
        // as the next level's variable set. This is bounded by `max_recursive_depth`
        // to prevent infinite expansion on genuinely recursive datatypes (each (C)
        // axiom synthesizes a deeper `sel_i(...)` term, so an unbounded unroll would
        // never terminate).
        //
        // Reference: Z3's theory_datatype::final_check() + mk_split() perform dynamic
        // case splitting lazily. We approximate this with bounded eager unrolling as a
        // WARM-START fast path (depth `DT_WARM_START_DEPTH`), and rely on the lazy DT
        // final-check in `solve_dt` (iterative deepening: re-solve at a larger
        // `max_recursive_depth` whenever the bounded unroll returns Unknown) for
        // completeness on deeper structures. A deeper unroll only ADDS datatype-theory
        // tautologies, so it can never cause a false-UNSAT.

        // Track all DT-sorted terms that have received axioms to avoid duplicates.
        let mut axiomatized_dt_terms: HashSet<TermId> = dt_vars.iter().map(|(t, _)| *t).collect();

        // All constructor terms from axiom (C) across all depths, for (B') generation.
        let mut all_axiom_c_ctor_terms: Vec<(TermId, String, String)> = Vec::new();

        // Current depth level's DT variables to process.
        let mut current_level_vars: Vec<(TermId, String)> = dt_vars;

        for _depth in 0..max_recursive_depth {
            if current_level_vars.is_empty() {
                break;
            }

            // Track the term store size before axiom (C) to detect new selector terms.
            let pre_axiom_c_term_count = self.ctx.terms.len();

            // Generate axiom (C) for current level's DT variables.
            for (var_term, dt_name) in &current_level_vars {
                let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                    continue;
                };

                for ctor_name in dt_ctors {
                    let tester_name = format!("is-{ctor_name}");
                    let tester_app = self.ctx.terms.mk_app(
                        Symbol::named(&tester_name),
                        vec![*var_term],
                        Sort::Bool,
                    );

                    let selectors: Vec<String> = match self.ctx.constructor_selectors(ctor_name) {
                        Some(sels) => sels.to_vec(),
                        None => continue,
                    };
                    let ctor_term = if selectors.is_empty() {
                        let dt_sort = Sort::Uninterpreted(dt_name.clone());
                        self.ctx.terms.mk_var(ctor_name.clone(), dt_sort)
                    } else {
                        let Some(selector_info) = self.selector_signature_in(dt_name, ctor_name)
                        else {
                            continue;
                        };
                        if selector_info.len() != selectors.len() {
                            continue;
                        }

                        let mut sel_apps = Vec::with_capacity(selectors.len());
                        for (sel_name, (_, sel_sort)) in selectors.iter().zip(selector_info.iter())
                        {
                            let sel_app = self.ctx.terms.mk_app(
                                Symbol::named(sel_name),
                                vec![*var_term],
                                sel_sort.clone(),
                            );
                            sel_apps.push(sel_app);
                        }

                        let dt_sort = Sort::Uninterpreted(dt_name.clone());
                        self.ctx
                            .terms
                            .mk_app(Symbol::named(ctor_name), sel_apps, dt_sort)
                    };

                    if !selectors.is_empty() {
                        all_axiom_c_ctor_terms.push((
                            ctor_term,
                            ctor_name.clone(),
                            dt_name.clone(),
                        ));
                    }

                    let Some(eq) = mk_eq_same_sort(&mut self.ctx.terms, *var_term, ctor_term)
                    else {
                        continue;
                    };
                    let implication = self.ctx.terms.mk_implies(tester_app, eq);

                    if !base_assertions.contains(&implication) && seen.insert(implication) {
                        extra.push(implication);
                    }
                }
            }

            // Collect DT-sorted selector applications created by axiom (C) at this depth.
            // These are new terms in the term store (index >= pre_axiom_c_term_count)
            // that have a datatype sort. We exclude constructor applications (they
            // already have a known constructor and don't need exhaustiveness axioms)
            // and non-application terms (variables, constants).
            let mut next_level_vars: Vec<(TermId, String)> = Vec::new();
            let post_axiom_c_term_count = self.ctx.terms.len();
            for idx in pre_axiom_c_term_count..post_axiom_c_term_count {
                let term = TermId::new(idx as u32);

                // Skip constructor applications — they already have a known constructor
                // and generating exhaustiveness for them is redundant. Only selector
                // applications (and other non-constructor function applications) need
                // exhaustiveness + constructor axioms at the next depth level.
                let is_ctor_app = matches!(
                    self.ctx.terms.get(term),
                    TermData::App(Symbol::Named(name), _)
                    if self.ctx.is_constructor(name).is_some()
                );
                if is_ctor_app {
                    continue;
                }
                // Also skip non-application terms (variables, constants, Booleans, etc.)
                // Only function applications (selectors) need recursive expansion.
                let is_app = matches!(self.ctx.terms.get(term), TermData::App(_, _));
                if !is_app {
                    continue;
                }

                let sort = self.ctx.terms.sort(term);
                let dt_name = match sort {
                    Sort::Uninterpreted(ref name) if datatype_ctors.contains_key(name) => {
                        name.clone()
                    }
                    Sort::Datatype(ref dt) if datatype_ctors.contains_key(&dt.name) => {
                        dt.name.clone()
                    }
                    _ => continue,
                };
                // Only include terms not already axiomatized.
                if axiomatized_dt_terms.insert(term) {
                    next_level_vars.push((term, dt_name));
                }
            }

            // Generate exhaustiveness axioms (D) for next level's DT-sorted terms.
            for (var_term, dt_name) in &next_level_vars {
                let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                    continue;
                };
                if dt_ctors.is_empty() {
                    continue;
                }

                let mut tester_apps = Vec::new();
                for ctor_name in dt_ctors {
                    let tester_name = format!("is-{ctor_name}");
                    let tester_app = self.ctx.terms.mk_app(
                        Symbol::named(&tester_name),
                        vec![*var_term],
                        Sort::Bool,
                    );
                    tester_apps.push(tester_app);
                }

                let axiom = self.ctx.terms.mk_or(tester_apps);
                if !base_assertions.contains(&axiom) && seen.insert(axiom) {
                    extra.push(axiom);
                }
            }

            current_level_vars = next_level_vars;
        }

        // (B') Tester evaluation for axiom-C constructor terms (#2766).
        //
        // Axiom (C) creates constructor terms like `Err(sel-err(x))` that were not in the
        // original formula. Axiom (B) ran before (C) and only saw pre-existing constructor
        // terms. Without this second pass, the combined DT+arithmetic solver (AUFLIA path)
        // cannot derive `is-Ok(Err(sel-err(x))) = false`, breaking cross-tester reasoning.
        //
        // In the pure DT path (solve_dt), the interactive DtSolver + DPLL(T) loop handles
        // this: tester decisions propagate equalities that lead to constructor clash
        // detection, so explicit tester-evaluation axioms are unnecessary. The axiom-based
        // AUFLIA/AUFLRA paths lack this dynamic interaction and need explicit axioms.
        //
        // (#5108) Now covers constructor terms from all recursive depth levels.
        for (ctor_term, ctor_name, dt_name) in all_axiom_c_ctor_terms {
            let Some(dt_ctors) = datatype_ctors.get(&dt_name) else {
                continue;
            };

            let true_term = self.ctx.terms.true_term();
            let false_term = self.ctx.terms.false_term();

            for other_ctor in dt_ctors {
                let tester_name = format!("is-{other_ctor}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![ctor_term], Sort::Bool);

                let expected = if other_ctor == &ctor_name {
                    true_term
                } else {
                    false_term
                };

                let eq = self.ctx.terms.mk_eq(tester_app, expected);
                if !base_assertions.contains(&eq) && seen.insert(eq) {
                    extra.push(eq);
                }
            }
        }

        // (E) Equality-to-tester axiom (#1737): x = C(...) → is-C(x).
        //
        // For each asserted equality `eq := (= x t)` where `t := C(a_1, ..., a_n)` is
        // a constructor application, assert `(is-C x)`.
        //
        // This is a "micro congruence" lemma that avoids needing full EUF congruence
        // for testers. Together with axiom (C), it enables:
        // 1. x = C(args) implies is-C(x) (this axiom)
        // 2. is-C(x) implies x = C(sel_1(x), ..., sel_n(x)) (axiom C)
        // 3. DtSolver injectivity detects a_i = sel_i(x) must hold
        //
        // Note: We assert is-C(x) directly since the equality is already asserted.
        // This is equivalent to modus ponens on (=> (= x C(args)) (is-C x)).
        for (p, (ctor_name, _args, _selectors)) in &var_to_ctor {
            let tester_name = format!("is-{ctor_name}");
            let tester_app =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&tester_name), vec![*p], Sort::Bool);

            if !base_assertions.contains(&tester_app) && seen.insert(tester_app) {
                extra.push(tester_app);
            }
        }

        // (F) Injectivity axioms (#8419): C(a1,...,an) = C(b1,...,bn) → ai = bi.
        //
        // When two same-constructor applications are asserted equal (directly or
        // transitively through the union-find), their corresponding fields must
        // also be equal. In the DPLL(T) path (solve_dt), the DtSolver discovers
        // this dynamically via check_injectivity_conflicts(). But in the axiom-
        // based path (DT+BV, DT+LIA, etc.), no interactive DT solver runs during
        // solving, so injectivity must be encoded as explicit axioms.
        //
        // Without this, consumers must flatten DT+BV encoding to avoid relying
        // on injectivity reasoning, which takes substantial workaround code.
        //
        // We generate injectivity axioms for:
        // (F1) Direct equalities: (= C(a1,...) C(b1,...)) in assertions
        // (F2) Transitive equalities: C(a1,...) and C(b1,...) in the same
        //       union-find equivalence class via var_to_ctor chains
        {
            // (F1) Scan base assertions for direct constructor-constructor equalities.
            for idx in 0..base_term_len {
                let term = TermId::new(idx as u32);
                if !base_assertions.contains(&term) {
                    continue;
                }
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (lhs, rhs) = (args[0], args[1]);

                // Extract constructor info for both sides.
                let lhs_ctor = match self.ctx.terms.get(lhs) {
                    TermData::App(Symbol::Named(n), a) => {
                        self.ctx.is_constructor(n).map(|(_, cn)| (cn, a.clone()))
                    }
                    _ => None,
                };
                let rhs_ctor = match self.ctx.terms.get(rhs) {
                    TermData::App(Symbol::Named(n), a) => {
                        self.ctx.is_constructor(n).map(|(_, cn)| (cn, a.clone()))
                    }
                    _ => None,
                };

                if let (Some((lhs_cn, lhs_args)), Some((rhs_cn, rhs_args))) = (lhs_ctor, rhs_ctor) {
                    if lhs_cn == rhs_cn && lhs_args.len() == rhs_args.len() {
                        // Same constructor: generate field equalities.
                        for (a, b) in lhs_args.iter().zip(rhs_args.iter()) {
                            if a != b {
                                let Some(field_eq) = mk_eq_same_sort(&mut self.ctx.terms, *a, *b)
                                else {
                                    continue;
                                };
                                if !base_assertions.contains(&field_eq) && seen.insert(field_eq) {
                                    extra.push(field_eq);
                                }
                            }
                        }
                    }
                }
            }

            // (F2) Injectivity via variable indirection.
            //
            // When p = C(a1,...) and q = C(b1,...) and p,q are in the same
            // equivalence class, we need ai = bi. This handles chains like
            // p = C(a), q = C(b), p = q → a = b.
            let mut uf_class_ctors: HashMap<TermId, Vec<(&String, &Vec<TermId>)>> =
                HashMap::default();
            for (p, (ctor_name, args, _selectors)) in &var_to_ctor {
                let rep = uf_find(&mut uf_parent, *p);
                uf_class_ctors
                    .entry(rep)
                    .or_default()
                    .push((ctor_name, args));
            }
            for (_rep, ctors_in_class) in &uf_class_ctors {
                // Group by constructor name within the class.
                let mut by_ctor: HashMap<&str, Vec<&Vec<TermId>>> = HashMap::default();
                for (ctor_name, args) in ctors_in_class {
                    by_ctor.entry(ctor_name.as_str()).or_default().push(args);
                }
                for (_cn, arg_lists) in &by_ctor {
                    if arg_lists.len() < 2 {
                        continue;
                    }
                    // For each pair, assert field equalities.
                    for i in 0..arg_lists.len() {
                        for j in (i + 1)..arg_lists.len() {
                            let a_args = arg_lists[i];
                            let b_args = arg_lists[j];
                            if a_args.len() != b_args.len() {
                                continue;
                            }
                            for (a, b) in a_args.iter().zip(b_args.iter()) {
                                if a != b {
                                    let Some(field_eq) =
                                        mk_eq_same_sort(&mut self.ctx.terms, *a, *b)
                                    else {
                                        continue;
                                    };
                                    if !base_assertions.contains(&field_eq) && seen.insert(field_eq)
                                    {
                                        extra.push(field_eq);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // (F3) Constructor-equality BICONDITIONAL for variable/selector operands
        // (#dt-ite-ctor-payload).
        //
        // (F1)/(F2) above relate only the FIELDS of two same-constructor
        // applications that are ALREADY known equal (asserted directly, or
        // transitively in the same union-find class). They do NOT decide an
        // equality between a datatype VARIABLE and a constructor application whose
        // truth is itself UNDECIDED. That is exactly the composite-return shape
        // deductive-checks lowers from a contract like
        // `result == if feasible { Accept(actual) } else { Reject }` over an enum
        // `Verdict { Reject, Accept(i128) }`: a variable `result = Accept(claimed)`
        // together with a disequality `result != Accept(actual)`. Nothing connects
        // those two atoms, so the eager DT+BV bit-blast admits a (spurious) model
        // with `claimed = actual` yet `result != Accept(actual)` — a
        // constructor-congruence violation. The strict DT model-validation oracle
        // correctly rejects that model, and the whole solve degrades to Unknown
        // (NEVER a wrong verdict — fail-closed): on the VALID combined form (which
        // should be UNSAT) and on the SAT wrong-control (whose genuine model the
        // solver then never returns).
        //
        // The natural repair — emit the constructor congruence biconditional
        // `(C(a) = C(b)) <=> (a = b)` and let EUF transitivity link
        // `result = C(a)`, `C(a) = C(b)`, `result = C(b)` — does NOT work here:
        // the eager DT+BV path treats datatype-sorted equalities as opaque
        // Booleans and does NOT run congruence closure over them (the documented
        // Nelson-Oppen gap, bv_axioms_euf.rs). So we relate the variable-vs-
        // constructor atom DIRECTLY to the variable's selectors/tester, which the
        // BV theory CAN decide:
        //   (t = C(b_0..b_n)) <=> (is-C(t) AND sel_0(t)=b_0 AND ... AND sel_n(t)=b_n)
        //   (t = C)            <=> is-C(t)                 (nullary constructor C)
        // This is a valid datatype-theory tautology (a value equals `C(b)` iff its
        // constructor is C and its fields are the b_i), so it can only PRUNE
        // spurious models — never cause a false-UNSAT. SOUNDNESS preserved:
        // Unknown->UNSAT only when genuinely valid; the constructor-clash /
        // distinctness / wrong-control refutations are untouched (they remain
        // SAT/refuted). With the atom pinned to BV/Bool-decidable selector/tester
        // facts, the family is decided without any DT-sorted EUF transitivity.
        {
            for idx in 0..base_term_len {
                let term = TermId::new(idx as u32);
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (lhs, rhs) = (args[0], args[1]);
                // Identify the constructor-application side and the
                // datatype-variable side. Exactly one side must be a constructor
                // application (App for non-nullary, Var for nullary) and the other
                // a datatype-sorted NON-constructor term (variable / selector
                // result). ctor=ctor pairs are handled by (F1)/(F2)/injectivity.
                let ctor_of = |exec: &Self, t: TermId| -> Option<(String, Vec<TermId>)> {
                    match exec.ctx.terms.get(t) {
                        TermData::App(Symbol::Named(n), a) => {
                            exec.ctx.is_constructor(n).map(|(_, cn)| (cn, a.clone()))
                        }
                        TermData::Var(n, _) => {
                            exec.ctx.is_constructor(n).map(|(_, cn)| (cn, Vec::new()))
                        }
                        _ => None,
                    }
                };
                let lhs_ctor = ctor_of(self, lhs);
                let rhs_ctor = ctor_of(self, rhs);
                let (dt_term, ctor_name, ctor_args) = match (lhs_ctor, rhs_ctor) {
                    (Some(_), Some(_)) => continue, // ctor = ctor: handled elsewhere
                    (Some((cn, ca)), None) => (rhs, cn, ca),
                    (None, Some((cn, ca))) => (lhs, cn, ca),
                    (None, None) => continue,
                };
                // The variable side must be datatype-sorted.
                let Some(dt_name) = self.dt_name_of(dt_term) else {
                    continue;
                };
                let tester_name = format!("is-{ctor_name}");
                let tester_app =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![dt_term], Sort::Bool);
                let conj = if ctor_args.is_empty() {
                    // Nullary constructor: (t = C) <=> is-C(t).
                    tester_app
                } else {
                    let Some(selector_info) = self.selector_signature_in(&dt_name, &ctor_name)
                    else {
                        continue;
                    };
                    if selector_info.len() != ctor_args.len() {
                        continue;
                    }
                    let mut conjuncts: Vec<TermId> = Vec::with_capacity(ctor_args.len() + 1);
                    conjuncts.push(tester_app);
                    let mut well_sorted = true;
                    for ((sel_name, sel_sort), &b) in selector_info.iter().zip(ctor_args.iter()) {
                        let sel_app = self.ctx.terms.mk_app(
                            Symbol::named(sel_name),
                            vec![dt_term],
                            sel_sort.clone(),
                        );
                        match mk_eq_same_sort(&mut self.ctx.terms, sel_app, b) {
                            Some(e) => conjuncts.push(e),
                            None => {
                                well_sorted = false;
                                break;
                            }
                        }
                    }
                    if !well_sorted {
                        continue;
                    }
                    self.ctx.terms.mk_and(conjuncts)
                };
                // Bool=Bool is the iff; both operands (the atom `term` and `conj`)
                // are Bool here.
                let biconditional = self.ctx.terms.mk_eq(term, conj);
                if !base_assertions.contains(&biconditional) && seen.insert(biconditional) {
                    extra.push(biconditional);
                }
            }
        }

        // (G) Tester mutual exclusion axioms (#8419):
        //     (is-Ci x) => (not (is-Cj x)) for all i != j.
        //
        // The exhaustiveness axiom (D) says at least one tester holds. But without
        // mutual exclusion, the SAT solver can assign multiple testers true
        // simultaneously for the same variable. In the DPLL(T) path, the DT solver
        // detects tester-constructor conflicts dynamically. In the axiom-based path,
        // we need explicit at-most-one constraints.
        //
        // Encoding: For each pair of distinct constructors Ci, Cj, assert:
        //   (not (and (is-Ci x) (is-Cj x)))
        // Equivalently: (=> (is-Ci x) (not (is-Cj x)))
        //
        // For k constructors, this produces k*(k-1)/2 pairwise exclusion axioms
        // per DT variable. Since most Rust enums have 2-5 variants, this is small.
        //
        // Collect DT-sorted terms with their datatype name first (avoids borrow
        // conflict between immutable sort() lookups and mutable mk_* calls).
        let exclusion_vars: Vec<(TermId, String)> = axiomatized_dt_terms
            .iter()
            .filter_map(|t| {
                let sort = self.ctx.terms.sort(*t);
                match sort {
                    Sort::Uninterpreted(name) if datatype_ctors.contains_key(name) => {
                        Some((*t, name.clone()))
                    }
                    Sort::Datatype(dt) if datatype_ctors.contains_key(&dt.name) => {
                        Some((*t, dt.name.clone()))
                    }
                    _ => None,
                }
            })
            .collect();
        for (var_term, dt_name) in &exclusion_vars {
            let Some(dt_ctors) = datatype_ctors.get(dt_name) else {
                continue;
            };
            if dt_ctors.len() < 2 {
                continue;
            }

            // Build tester applications for this variable.
            let tester_apps: Vec<TermId> = dt_ctors
                .iter()
                .map(|ctor_name| {
                    let tester_name = format!("is-{ctor_name}");
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(&tester_name), vec![*var_term], Sort::Bool)
                })
                .collect();

            // Pairwise exclusion: (not (and (is-Ci x) (is-Cj x)))
            for i in 0..tester_apps.len() {
                for j in (i + 1)..tester_apps.len() {
                    let conjunction = self.ctx.terms.mk_and(vec![tester_apps[i], tester_apps[j]]);
                    let exclusion = self.ctx.terms.mk_not(conjunction);
                    if !base_assertions.contains(&exclusion) && seen.insert(exclusion) {
                        extra.push(exclusion);
                    }
                }
            }
        }

        // (H) Constructor disjointness axioms (#8419):
        //     (= C1(...) C2(...)) is UNSAT for C1 != C2 in the same datatype.
        //
        // For each asserted equality where both sides are constructors of the same
        // datatype but different constructors, assert false. The DT solver catches
        // this dynamically via check_clash(), but the axiom-based path needs it.
        //
        // Encoding: (=> (= C1(a...) C2(b...)) false)
        // Which simplifies to: (not (= C1(a...) C2(b...)))
        //
        // This prevents the SAT solver from satisfying equalities between
        // different constructors in DT+BV formulas.
        for idx in 0..base_term_len {
            let term = TermId::new(idx as u32);
            // Only process equalities reachable from assertions to avoid explosion.
            if !reachable_terms.contains(&term) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);

            let lhs_ctor_info = match self.ctx.terms.get(lhs) {
                TermData::App(Symbol::Named(n), _) => self.ctx.is_constructor(n),
                TermData::Var(n, _) => self.ctx.is_constructor(n),
                _ => None,
            };
            let rhs_ctor_info = match self.ctx.terms.get(rhs) {
                TermData::App(Symbol::Named(n), _) => self.ctx.is_constructor(n),
                TermData::Var(n, _) => self.ctx.is_constructor(n),
                _ => None,
            };

            if let (Some((lhs_dt, lhs_cn)), Some((rhs_dt, rhs_cn))) = (lhs_ctor_info, rhs_ctor_info)
            {
                if lhs_dt == rhs_dt && lhs_cn != rhs_cn {
                    // Different constructors of the same datatype: unsatisfiable.
                    let neg_eq = self.ctx.terms.mk_not(term);
                    if !base_assertions.contains(&neg_eq) && seen.insert(neg_eq) {
                        extra.push(neg_eq);
                    }
                }
            }
        }

        // (I) Variable transitivity via shared constructor binding (#8419).
        //
        // When two or more variables are each asserted equal to the same constructor
        // application (i.e., identical constructor name and identical argument term IDs),
        // those variables must be equal. Hash-consing causes `mk-val(#x01)` to produce
        // a single term ID, so `s = mk-val(#x01)` and `t = mk-val(#x01)` both bind to
        // the exact same constructor term. But:
        //
        // - The union-find only tracks var-to-var equalities (line 167: !lhs_is_ctor && !rhs_is_ctor)
        // - Axiom (F2) generates field equalities, but when args are identical IDs, a == b
        //   so no field equality is generated
        // - EUF congruence in BV path requires 2+ distinct applications of the same function
        //   (hash-consing produces only 1)
        //
        // Without this axiom, `(= s (mk-val #x01)), (= t (mk-val #x01)), (not (= s t))`
        // is falsely satisfiable. Z3 returns UNSAT (correct); AY returns SAT (BUG).
        //
        // Fix: Group var_to_ctor entries by (ctor_name, args). For each group with 2+
        // variables, generate pairwise equality axioms.
        {
            // Group variables by their constructor binding: (ctor_name, args) -> [var_term]
            let mut binding_groups: HashMap<(&str, &[TermId]), Vec<TermId>> = HashMap::default();
            for (p, (ctor_name, args, _selectors)) in &var_to_ctor {
                binding_groups
                    .entry((ctor_name.as_str(), args.as_slice()))
                    .or_default()
                    .push(*p);
            }

            for (_binding, vars) in &binding_groups {
                if vars.len() < 2 {
                    continue;
                }
                // Generate pairwise equality axioms for all variables bound to
                // the same constructor application.
                for i in 0..vars.len() {
                    for j in (i + 1)..vars.len() {
                        let eq = self.ctx.terms.mk_eq(vars[i], vars[j]);
                        if !base_assertions.contains(&eq) && seen.insert(eq) {
                            extra.push(eq);
                        }
                    }
                }
            }
        }

        extra
    }
}
