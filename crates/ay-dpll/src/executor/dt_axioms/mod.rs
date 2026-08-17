// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype (DT) axiom generation for combined DT+theory solver paths.
//!
//! Three DT axiom generators used by the executor's combined solver dispatch:
//!
//! - [`Executor::dt_selector_axioms`]: Selector projection, tester evaluation,
//!   exhaustiveness, constructor, and equality-to-tester axioms (A-E).
//! - [`Executor::dt_acyclicity_depth_axioms`]: Depth-function acyclicity encoding
//!   via rank functions (Barrett, Shikanian, Tinelli 2007).
//! - [`Executor::dt_occurs_check_unsat_from_equalities`]: Fast-path cycle detection
//!   using the pure DT solver's occurs-check.
//!
//! Originally a single file (`dt_axioms.rs`), split into submodules for code health.

mod acyclicity;
mod selector;

// Re-export the DT unroll-depth knobs so the DT solve entrypoints
// (`executor::theories::euf::dt`) can drive the lazy iterative-deepening
// final-check.
pub(in crate::executor) use selector::{DT_MAX_DEEPENING_DEPTH, DT_WARM_START_DEPTH};

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TheorySolver};
use ay_dt::DtSolver;

use super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::TheoryKind;

/// Selector metadata: list of (selector_name, selector_sort) pairs
pub(in crate::executor) type SelectorList = Vec<(String, Sort)>;

impl Executor {
    /// Fast path: detect datatype cycles using the pure DT solver's occurs-check.
    ///
    /// This is used for combined DT+arithmetic paths (DT_AUFLIA/DT_AUFLRA). The depth-axiom
    /// encoding is incomplete for multi-hop equality cycles (#1776), but acyclicity is a
    /// datatype-only property and can be decided without arithmetic reasoning.
    ///
    /// Considers top-level asserted/assumed *equalities* (no Boolean structure) plus
    /// top-level *true testers* `((_ is C) v)`. A true tester is semantically equivalent
    /// to `v = C(sel_1(v), ..., sel_n(v))` (SMT-LIB datatype semantics). Rather than
    /// materialize a constructor term — which would pollute the shared term store seen by
    /// the downstream solver — the tester and the constructor's selector signature are fed
    /// to the `DtSolver`, whose occurs-check derives the implicit `v ⊳ sel_i(v)` edges from
    /// the *existing* selector-application terms only. This lets it catch selector-equation
    /// cycles such as `((_ is succ) v) ∧ (pred v) = v` ⇒ `v = succ(v)` (UNSAT by
    /// well-foundedness), which have no explicit constructor term (#dt-acyclic-tester).
    ///
    /// Safety: this path only ever returns `true` (UNSAT). The tester-induced edges are
    /// each implied by an asserted true tester, so any cycle found is a genuine cycle in
    /// the asserted facts; it can never manufacture a spurious cycle (a false theorem).
    pub(in crate::executor) fn dt_occurs_check_unsat_from_equalities(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> bool {
        // If no datatypes are declared, the DT solver has nothing to contribute.
        if self.ctx.datatype_iter().next().is_none() {
            return false;
        }

        // Pre-pass (#dt-acyclic-negated-tester): for a TWO-constructor datatype
        // `{C, C'}`, a top-level `(not ((_ is C) v))` is equivalent to
        // `((_ is C') v)` (every value is exactly one constructor). The
        // occurs-check below keys off POSITIVE testers, so a negated tester that
        // pins the recursive constructor — e.g. `(not (is-zero v)) ⟹ (is-succ v)`
        // over `Nat = zero | succ(pred)` — combined with `(pred v) = v` (the cycle
        // `v = succ(v)`, UNSAT) was reported SAT. Materialize the implied positive
        // tester so the occurs-check sees the recursive structure. The derived
        // term is fed only to the local DtSolver; it is NOT added to the problem
        // (no proof obligation beyond the genuine cycle the occurs-check finds).
        let derived_testers = self.derive_two_ctor_negated_testers(assertions, assumptions);

        // Each top-level assertion is modelled as a DISJUNCTION OF CONJUNCTIVE
        // FACT-SETS (`Vec<DisjunctOption>`), where a fact-set is a list of
        // equality/tester literals fed together to the DT solver:
        //
        //  - a plain equality / true tester `f` contributes the single disjunct
        //    `Some(vec![f])`;
        //  - a top-level `(ite g t e)` whose branches are themselves DT facts
        //    contributes `disjuncts(t) ++ disjuncts(e)` — the GUARD IS DROPPED
        //    (#dt-acyclic-ite). `mk_eq` eagerly Shannon-lifts a DT-sorted ite
        //    equality `L = ite(g,x,y)` into exactly this `(ite g (= L x) (= L y))`
        //    Bool-ite, which the opaque-App occurs-check never decomposed — so a
        //    `cons(F) = F` (b-true, occurs cycle) / `cons(F) = nil` (b-false,
        //    clash) was reported SAT;
        //  - an opaque branch (a fact we cannot decompose) contributes the
        //    UNREFUTABLE disjunct `None`.
        //
        // The asserted conjunction is UNSAT iff, for EVERY selection of one
        // disjunct per assertion, the union of the selected fact-sets is UNSAT in
        // the DT theory (and no selected disjunct is `None`). Soundness: in any
        // model each `ite` resolves to exactly one branch, so the model satisfies
        // one specific selection; if every selection is independently UNSAT, no
        // model exists. Dropping the guard only WEAKENS each branch's constraints,
        // so an UNSAT selection stays UNSAT — never a spurious refutation, hence no
        // false-UNSAT. Unrecognized top-level assertions are ignored entirely
        // (dropping a conjunct only weakens the set, preserving UNSAT soundness).
        let mut base_facts: Vec<TermId> = Vec::new();
        let mut assertion_disjunctions: Vec<Vec<DisjunctOption>> = Vec::new();
        let mut saw_fact = false;

        // Entailed Boolean units, used to prune dead `ite` branches during the
        // Shannon expansion below so a determined guard does not inject an
        // unreachable (and possibly satisfiable) disjunct that defeats the
        // all-selections-UNSAT refutation (#dt-acyclic-guarded-ite).
        let bool_units = self.collect_bool_units(assertions, assumptions);
        // Guard-eval memo, valid for exactly this `bool_units` instance.
        let mut gmemo: HashMap<TermId, Option<bool>> = HashMap::default();

        for &t in assertions.iter().chain(assumptions.iter()) {
            let mut disjuncts: Vec<DisjunctOption> = Vec::new();
            self.collect_dt_fact_disjuncts(t, &mut disjuncts, &bool_units, 0, &mut gmemo);
            match disjuncts.len() {
                0 => {} // not a recognized DT fact: ignore (sound to drop).
                1 => match disjuncts.into_iter().next().unwrap() {
                    // A single concrete fact-set with no branching: fold straight
                    // into the always-present base facts.
                    DisjunctOption::Facts(facts) => {
                        if !facts.is_empty() {
                            saw_fact = true;
                            base_facts.extend(facts);
                        }
                    }
                    // A single opaque disjunct constrains nothing we can refute.
                    DisjunctOption::Opaque => {}
                },
                _ => {
                    saw_fact = true;
                    assertion_disjunctions.push(disjuncts);
                }
            }
        }

        // Derived positive testers (implied by negated testers over a
        // two-constructor datatype). Each is true by construction.
        for &t in &derived_testers {
            saw_fact = true;
            base_facts.push(t);
        }

        if !saw_fact {
            return false;
        }

        // Unconditional refutation first: the `base_facts` are each implied by a
        // top-level assertion (plain equalities / true testers), so if they are
        // ALREADY contradictory the whole formula is UNSAT regardless of any
        // branch selection. Checking this first preserves the pre-existing
        // occurs/clash detection — a genuine cycle like `v = succ(v)` must still
        // be caught even when OTHER assertions contain undecomposable `ite`
        // branches (which would otherwise abort the cross-product below).
        if !base_facts.is_empty() && self.dt_facts_unsat(&base_facts, &[]) {
            return true;
        }

        // No branching assertions: the base-only check above already decided it.
        if assertion_disjunctions.is_empty() {
            return false;
        }

        // Bound the disjunct cross-product. If it would exceed the cap, fall back
        // to the (sound, incomplete) base-only check rather than enumerate an
        // enormous space.
        const MAX_BRANCH_COMBOS: usize = 256;
        let mut combos: usize = 1;
        for d in &assertion_disjunctions {
            combos = combos.saturating_mul(d.len());
        }
        if combos == 0 || combos > MAX_BRANCH_COMBOS {
            // Too many combinations to enumerate cheaply. The base-only refutation
            // was already tried above and failed, so fall back to "not provably
            // UNSAT" (sound: we simply decline to refute via the fast path).
            return false;
        }

        // Require EVERY selection to be independently UNSAT.
        for combo_idx in 0..combos {
            let mut extra_facts: Vec<TermId> = Vec::new();
            let mut rem = combo_idx;
            let mut opaque = false;
            for d in &assertion_disjunctions {
                let pick = rem % d.len();
                rem /= d.len();
                match &d[pick] {
                    DisjunctOption::Facts(facts) => extra_facts.extend(facts.iter().copied()),
                    DisjunctOption::Opaque => {
                        opaque = true;
                        break;
                    }
                }
            }
            // An opaque branch is a satisfiable possibility we cannot refute, so
            // this selection (and therefore the whole formula) is not provably
            // UNSAT via the occurs-check.
            if opaque || !self.dt_facts_unsat(&base_facts, &extra_facts) {
                return false;
            }
        }
        true
    }

    /// Build a fresh `DtSolver`, register the declared datatypes and selector
    /// signatures, feed `base_facts` plus `extra_facts` (additional equality/tester
    /// literals selected from one branch combination), and return whether the
    /// pure-DT occurs/clash check reports UNSAT. All fed terms already exist in the
    /// store; they are fed ONLY to this throwaway solver and never added to the
    /// problem assertions, matching the `#dt-acyclic-tester` discipline.
    fn dt_facts_unsat(&mut self, base_facts: &[TermId], extra_facts: &[TermId]) -> bool {
        let mut dt = DtSolver::new(&self.ctx.terms);
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            dt.register_datatype(dt_name, constructors);
            for ctor_name in constructors {
                if let Some(info) = self.ctx.constructor_selector_info(ctor_name) {
                    let sel_names: Vec<String> = info.iter().map(|(n, _)| n.clone()).collect();
                    dt.register_ctor_selectors(ctor_name, &sel_names);
                }
            }
        }
        for &t in base_facts.iter().chain(extra_facts.iter()) {
            dt.assert_literal(t, true);
        }
        matches!(dt.check(), ay_core::TheoryResult::Unsat(_))
    }

    /// Decompose a top-level assertion `t` into a DISJUNCTION OF CONJUNCTIVE
    /// FACT-SETS for the occurs-check (#dt-acyclic-ite). Pushes one
    /// [`DisjunctOption`] per disjunct into `out`:
    ///
    ///  - equality `(= a b)` or true tester `(is-C v)`  → `Facts(vec![t])`;
    ///  - `(ite g then else)`  → the disjuncts of `then` AND of `else` (the guard
    ///    `g` is dropped — it only constrains which branch is selected, never
    ///    relaxes a branch, so dropping it keeps the per-selection check
    ///    fail-CLOSED);
    ///  - anything else  → `Opaque` (an unrefutable disjunct).
    ///
    /// Bounds recursion depth; on overflow the term is treated as `Opaque` (sound:
    /// an unrefutable branch can only make the formula *less* provably UNSAT).
    fn collect_dt_fact_disjuncts(
        &self,
        t: TermId,
        out: &mut Vec<DisjunctOption>,
        units: &HashMap<TermId, bool>,
        depth: usize,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) {
        const MAX_ITE_DEPTH: usize = 16;
        if depth >= MAX_ITE_DEPTH {
            out.push(DisjunctOption::Opaque);
            return;
        }
        match self.ctx.terms.get(t).clone() {
            // Bool-sorted `ite` over fact branches: disjunction of the branches.
            // A guard ENTAILED true/false selects only the live branch (sound and
            // stronger); an undetermined guard expands both (dropping the guard
            // only weakens, preserving the UNSAT-soundness of each selection).
            TermData::Ite(g, then_t, else_t) if self.ctx.terms.sort(t) == &Sort::Bool => match self
                .eval_bool_guard(g, units, gmemo)
            {
                Some(true) => self.collect_dt_fact_disjuncts(then_t, out, units, depth + 1, gmemo),
                Some(false) => self.collect_dt_fact_disjuncts(else_t, out, units, depth + 1, gmemo),
                None => {
                    self.collect_dt_fact_disjuncts(then_t, out, units, depth + 1, gmemo);
                    self.collect_dt_fact_disjuncts(else_t, out, units, depth + 1, gmemo);
                }
            },
            // Top-level equality fact.
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                let _ = args;
                out.push(DisjunctOption::Facts(vec![t]));
            }
            // Disjunction: each arg is a disjunct (#dt-embedded-cycle false-SAT).
            // This is EXACT (not a weakening): `(or e1 .. en)` asserts that every
            // model satisfies at least one `e_i`, which is precisely the
            // disjunction-of-fact-sets semantics the all-selections-UNSAT
            // cross-product refutes. Without this arm, an `or` of constructor
            // equalities was a single Opaque disjunct, so an indirect cycle split
            // across disjunctions — `(or (= x (cons a y)) (= x (cons b y)))` ∧
            // `(or (= y (cons a x)) (= y (cons b x)))`, UNSAT — escaped the
            // occurs-check (and, on the DT+BV route, escaped as a FALSE SAT).
            // A disjunct ENTAILED false by the Boolean units is DEAD in every
            // model and is dropped (exact, not a weakening); a disjunct entailed
            // true short-circuits the whole disjunction to a single Opaque
            // (satisfiable without constraining the DT facts, hence unrefutable).
            TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
                for &d in &args {
                    if self.eval_bool_guard(d, units, gmemo) == Some(true) {
                        out.push(DisjunctOption::Opaque);
                        return;
                    }
                }
                for &d in &args {
                    if self.eval_bool_guard(d, units, gmemo) == Some(false) {
                        continue; // dead disjunct: no model selects it
                    }
                    self.collect_dt_fact_disjuncts(d, out, units, depth + 1, gmemo);
                }
                // All disjuncts entailed false: the assertion is itself
                // contradictory; contribute an (unrefutable-here) Opaque rather
                // than an empty disjunction (the Boolean core will refute it).
                if out.is_empty() {
                    out.push(DisjunctOption::Opaque);
                }
            }
            // `xor` entails the plain disjunction of its args (odd parity needs
            // at least one true arg), so treating it as `or` only WEAKENS each
            // branch — the per-selection UNSAT check stays fail-closed
            // (#dt-embedded-cycle).
            TermData::App(Symbol::Named(name), args) if name == "xor" && args.len() >= 2 => {
                for &d in &args {
                    self.collect_dt_fact_disjuncts(d, out, units, depth + 1, gmemo);
                }
            }
            // `(=> a1 .. an c)`: when every antecedent is ENTAILED true the
            // consequent must hold (modus ponens — exact); otherwise the
            // implication is unrefutable here (Opaque) (#dt-embedded-cycle).
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() >= 2 => {
                let (antecedents, consequent) = args.split_at(args.len() - 1);
                if antecedents
                    .iter()
                    .all(|&a| self.eval_bool_guard(a, units, gmemo) == Some(true))
                {
                    self.collect_dt_fact_disjuncts(consequent[0], out, units, depth + 1, gmemo);
                } else {
                    out.push(DisjunctOption::Opaque);
                }
            }
            // De Morgan disjunctions produced by `(not (distinct ..))` lowering
            // (#dt-embedded-cycle): `(not (not e))` ⇒ `e`, and
            // `(not (and (not e1) .. (not en)))` ⇒ `e1 ∨ .. ∨ en`. A conjunct
            // that is not a negation makes its (negated) disjunct Opaque; one
            // ENTAILED true makes its negation a dead disjunct (dropped, exact).
            TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                TermData::Not(e) => self.collect_dt_fact_disjuncts(e, out, units, depth + 1, gmemo),
                TermData::App(Symbol::Named(name), conj_args) if name == "and" => {
                    for &c in &conj_args {
                        match self.ctx.terms.get(c) {
                            TermData::Not(e) => {
                                let e = *e;
                                self.collect_dt_fact_disjuncts(e, out, units, depth + 1, gmemo);
                            }
                            _ => {
                                if self.eval_bool_guard(c, units, gmemo) == Some(true) {
                                    continue; // negation is dead in every model
                                }
                                out.push(DisjunctOption::Opaque);
                            }
                        }
                    }
                    if out.is_empty() {
                        out.push(DisjunctOption::Opaque);
                    }
                }
                _ => out.push(DisjunctOption::Opaque),
            },
            // Top-level true tester `((_ is C) v)`.
            TermData::App(Symbol::Named(name), args) if args.len() == 1 => {
                if name
                    .strip_prefix("is-")
                    .is_some_and(|c| self.ctx.is_constructor(c).is_some())
                {
                    out.push(DisjunctOption::Facts(vec![t]));
                } else {
                    out.push(DisjunctOption::Opaque);
                }
            }
            _ => out.push(DisjunctOption::Opaque),
        }
    }

    /// Materialize the positive testers implied by top-level negated testers over
    /// TWO-constructor datatypes (#dt-acyclic-negated-tester). For `(not (is-C v))`
    /// where `v`'s datatype is exactly `{C, C'}`, returns the term `(is-C' v)`
    /// (`¬is-C(v) ⟺ is-C'(v)` for a two-inhabitant constructor choice). Descends
    /// only through top-level `and` conjuncts (a negated tester under `or`/`ite`
    /// is conditional, not an unconditional fact). Scoped to k == 2 datatypes (for
    /// k != 2 a single negated tester does not pin one constructor).
    fn derive_two_ctor_negated_testers(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Vec<TermId> {
        // Collect top-level conjuncts (descend positive `and` only).
        let mut conjuncts: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions
            .iter()
            .chain(assumptions.iter())
            .copied()
            .collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                if name == "and" {
                    stack.extend(args.iter().copied());
                    continue;
                }
            }
            conjuncts.push(t);
        }

        // First pass (immutable): collect `(subject, is-C')` pins from negated
        // testers `(not (is-C v))`, disequalities `(not (= v C))`, and
        // `(distinct ..)` operands; and collect the UNCONDITIONAL equality pairs
        // used to propagate a pin across equal terms.
        let mut pending: Vec<(TermId, String)> = Vec::new();
        let mut eq_pairs: Vec<(TermId, TermId)> = Vec::new();
        for &conj in &conjuncts {
            match self.ctx.terms.get(conj) {
                // Unconditional equality: an edge for pin propagation below.
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    eq_pairs.push((args[0], args[1]));
                }
                // `(distinct t1 .. tn)`: every operand is `!=` every other, so an
                // operand that is a NULLARY constructor `C` of a two-constructor
                // datatype pins each OTHER operand to `is-C'`. This is how a cycle
                // driver such as `(tl v) != nil` reaches the occurs-check — it was
                // previously buried inside the `distinct` and never harvested
                // (#dt-acyclic-distinct-pin).
                TermData::App(Symbol::Named(name), args)
                    if name == "distinct" && args.len() >= 2 =>
                {
                    let args = args.clone();
                    for i in 0..args.len() {
                        for j in 0..args.len() {
                            if i != j {
                                if let Some(found) = self.two_ctor_diseq_other(args[j], args[i]) {
                                    pending.push(found);
                                }
                            }
                        }
                    }
                }
                TermData::Not(inner) => {
                    let inner = *inner;
                    // Disequality form `(not (= v C))` where `C` is a NULLARY
                    // constructor of a two-constructor datatype: `v != C` ⟹
                    // `v = C'` ⟹ `is-C'(v)` (same well-foundedness driver as the
                    // negated tester, just expressed as `(not (= v zero))`).
                    if let TermData::App(Symbol::Named(eqname), eargs) = self.ctx.terms.get(inner) {
                        if eqname == "=" && eargs.len() == 2 {
                            let (a, b) = (eargs[0], eargs[1]);
                            if let Some(found) = self
                                .two_ctor_diseq_other(a, b)
                                .or_else(|| self.two_ctor_diseq_other(b, a))
                            {
                                pending.push(found);
                            }
                            continue;
                        }
                    }
                    let TermData::App(Symbol::Named(tester_name), iargs) =
                        self.ctx.terms.get(inner)
                    else {
                        continue;
                    };
                    if iargs.len() != 1 {
                        continue;
                    }
                    let v = iargs[0];
                    let Some(ctor_name) = tester_name.strip_prefix("is-") else {
                        continue;
                    };
                    let Some((dt_name, _)) = self.ctx.is_constructor(ctor_name) else {
                        continue;
                    };
                    let ctors: Vec<String> = self
                        .ctx
                        .datatype_iter()
                        .find(|(n, _)| *n == dt_name)
                        .map(|(_, cs)| cs.to_vec())
                        .unwrap_or_default();
                    if ctors.len() != 2 {
                        continue;
                    }
                    if let Some(other) = ctors.iter().find(|c| c.as_str() != ctor_name) {
                        pending.push((v, format!("is-{other}")));
                    }
                }
                _ => {}
            }
        }

        // Propagate each pin across the UNCONDITIONAL equality graph: `is-C'(X)`
        // together with `X = Y` entails `is-C'(Y)`. This lands the tester on the
        // actual occurs-cycle subject — e.g. `(tl v) != nil` pins `is-cons(tl v)`,
        // and `v = (tl v)` then pins `is-cons(v)`, the tester the occurs-check
        // needs (its `v |> (tl v)` proper-subterm edge is built from the EXISTING
        // selector term `(tl v)`; the edge `(tl v) |> (tl (tl v))` would need a
        // non-existent term). Bounded; skipping only leaves a conflict undetected,
        // never a wrong answer (#dt-acyclic-eq-pin).
        if !eq_pairs.is_empty() && !pending.is_empty() {
            const MAX_EQ_CLOSURE_NODES: usize = 256;
            let mut adj: HashMap<TermId, Vec<TermId>> = HashMap::default();
            for &(a, b) in &eq_pairs {
                if a != b {
                    adj.entry(a).or_default().push(b);
                    adj.entry(b).or_default().push(a);
                }
            }
            let mut propagated: Vec<(TermId, String)> = Vec::new();
            for (subject, tester) in &pending {
                let mut class: HashSet<TermId> = HashSet::default();
                class.insert(*subject);
                let mut stack = vec![*subject];
                while let Some(t) = stack.pop() {
                    if class.len() > MAX_EQ_CLOSURE_NODES {
                        break;
                    }
                    if let Some(neighbors) = adj.get(&t) {
                        for &n in neighbors {
                            if class.insert(n) {
                                propagated.push((n, tester.clone()));
                                stack.push(n);
                            }
                        }
                    }
                }
            }
            pending.extend(propagated);
        }

        // Second pass (mutable): materialize the implied positive tester terms.
        let mut derived: Vec<TermId> = Vec::new();
        for (v, other_tester_name) in pending {
            let tester =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&other_tester_name), vec![v], Sort::Bool);
            if !derived.contains(&tester) {
                derived.push(tester);
            }
        }
        derived
    }

    /// If `maybe_ctor` is a NULLARY constructor `C` of a datatype with EXACTLY
    /// two constructors `{C, C'}`, return `(subject, "is-C'")` — the positive
    /// tester implied by `subject != C` (every value is `C` or `C'`, so `!= C`
    /// pins `C'`). Returns `None` unless `maybe_ctor` is a bare nullary
    /// constructor of a two-constructor datatype (a non-nullary constructor
    /// application like `(succ x)` never appears as a bare term and a `!= (succ
    /// x)` would not pin a single constructor anyway).
    fn two_ctor_diseq_other(
        &self,
        maybe_ctor: TermId,
        subject: TermId,
    ) -> Option<(TermId, String)> {
        let ctor_name = match self.ctx.terms.get(maybe_ctor) {
            TermData::Var(name, _) => name.clone(),
            TermData::App(Symbol::Named(name), args) if args.is_empty() => name.clone(),
            _ => return None,
        };
        let (dt_name, _) = self.ctx.is_constructor(&ctor_name)?;
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(n, _)| *n == dt_name)
            .map(|(_, cs)| cs.to_vec())
            .unwrap_or_default();
        if ctors.len() != 2 {
            return None;
        }
        let other = ctors.iter().find(|c| c.as_str() != ctor_name)?;
        Some((subject, format!("is-{other}")))
    }

    /// Mine guarded datatype-acyclicity clauses from disjunctive contexts
    /// (#dt-acyclic-case-split).
    ///
    /// The one-shot occurs-check fast path
    /// ([`Self::dt_occurs_check_unsat_from_equalities`]) only inspects
    /// *syntactically top-level* `=` literals and positive testers; it never
    /// sees an equality that is merely one *disjunct* of a case split. So a
    /// formula like `(not (distinct (nd y x) lf x))` — which De Morgan's into
    /// `(= (nd y x) lf) ∨ (= (nd y x) x) ∨ (= lf x)` — reaches the SAT core with
    /// the constructor `nd` treated as plain UF, and the surviving disjunct
    /// `x = nd(y, x)` (a structural cycle, UNSAT by datatype well-foundedness)
    /// is satisfied, yielding a false `sat`.
    ///
    /// This pass scans every top-level assertion/assumption for a *disjunction
    /// of equalities* and, for each equality disjunct `(= a b)` in which one
    /// side is a constructor application whose immediate/transitive
    /// constructor-argument closure contains the other side, returns the
    /// **guarded acyclicity clause** `(not (= a b))`.
    ///
    /// Disjunctive forms recognized (both produced by the frontend):
    ///   - `(or e1 .. en)` — an `App("or", ..)` term.
    ///   - `(not (and (not e1) .. (not en)))` — the De Morgan shape that
    ///     `(not (distinct ..))` lowers to (binary `distinct` → `not (= ..)`,
    ///     n-ary `distinct` → `and` of pairwise `not (= ..)`).
    ///
    /// Soundness: `(= a b)` with `a = C(.. b ..)` (transitively) is *valid*ly
    /// `false` in every datatype model — an inductive value can never be a
    /// proper subterm of itself (the rank/depth strictly decreases along
    /// constructor edges). The emitted `(not (= a b))` is therefore a logical
    /// consequence of the datatype theory alone; it can only *constrain* the
    /// search and can never manufacture a spurious cycle or a false `unsat`.
    /// The closure descends through constructor applications *only*, so no
    /// non-structural (e.g. selector/UF) edge is ever treated as a subterm
    /// relation.
    pub(in crate::executor) fn dt_guarded_acyclicity_disjuncts(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Vec<TermId> {
        // No datatypes declared ⇒ nothing structural to reason about.
        if self.ctx.datatype_iter().next().is_none() {
            return Vec::new();
        }

        // Phase 1 (immutable scan): collect the (a, b) equality pairs that are
        // genuine structural cycles. We split the immutable scan from the
        // mutable term construction to avoid aliasing `self.ctx.terms`.
        let mut cyclic_pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();

        // Entailed Boolean unit assignments, used to resolve `ite` guards while
        // walking the constructor closure (a guarded recursive occurrence behind
        // a guard pinned by another assertion — e.g. `(not (and v13 true))`
        // forcing `v13 = false` — is still an UNCONDITIONAL cycle).
        let bool_units = self.collect_bool_units(assertions, assumptions);
        // Guard-eval memo, valid for exactly this `bool_units` instance. Shared
        // across ALL assertions in this pass — the pass was formerly quadratic+
        // (every assertion re-walking the shared guard DAG) and dominated large
        // BMC solves.
        let mut gmemo: HashMap<TermId, Option<bool>> = HashMap::default();

        for &t in assertions.iter().chain(assumptions.iter()) {
            // Gather the equality disjuncts contributed by this assertion.
            let mut eq_disjuncts: Vec<TermId> = Vec::new();
            self.collect_eq_disjuncts(t, &mut eq_disjuncts);
            // Also the UNCONDITIONAL equalities (bare, or under a top-level
            // `and`). A bare `(= X C(.. X ..))` self-containment — including one
            // whose recursive occurrence is behind a nested `ite` — is invisible
            // to the occurs-check fast path (its throwaway DtSolver does not
            // descend `ite` inside a constructor argument), so harvest it here
            // and let `ctor_closure_contains` (ite-aware) refute it
            // (#dt-acyclic-toplevel-eq).
            self.collect_unconditional_equalities(t, &bool_units, &mut eq_disjuncts, 0, &mut gmemo);

            for eq in eq_disjuncts {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(eq) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                // Refuted by datatype structure: a constructor cycle, a
                // constructor clash, or an injective-constructor argument
                // mismatch — accounting for guard-resolved `ite` branches.
                let cyclic = self.dt_eq_refuted(a, b, &bool_units, 0, &mut gmemo);
                if cyclic && seen_pairs.insert((a, b)) {
                    cyclic_pairs.push((a, b));
                }
            }
        }

        // Phase 2 (mutable): materialize the guarded clauses `(not (= a b))`.
        let mut out: Vec<TermId> = Vec::new();
        for (a, b) in cyclic_pairs {
            let eq = self.ctx.terms.mk_eq(a, b);
            let neq = self.ctx.terms.mk_not(eq);
            if !out.contains(&neq) {
                out.push(neq);
            }
        }
        out
    }

    /// Derive guard-FORCING unit lemmas from unconditional equalities whose
    /// constructor side hides a structural cycle behind a SINGLE Boolean guard
    /// and selector-on-constructor layers (#dt-acyclic-guard-forcing).
    ///
    /// The disjunctive/closure pass [`Self::dt_guarded_acyclicity_disjuncts`]
    /// only refutes an equality that is a cycle under EVERY branch selection (it
    /// requires the recursive occurrence under both `ite` branches and never
    /// reduces a selector applied to a constructor). It therefore cannot touch
    /// a cycle that appears under exactly ONE polarity of a free guard — e.g.
    /// `v = node(right(ite g v (node a b v)), ..)`, where `g = false` reduces
    /// `right(node a b v)` to `v` (the third/`right` argument), making `v` the
    /// `left` subterm of itself (a cycle), while `g = true` leaves
    /// `right(v)` opaque (no cycle). Such an equality is satisfiable ONLY when
    /// the guard takes the non-cyclic value, so that value is ENTAILED.
    ///
    /// This pass scans each UNCONDITIONAL equality `(= L R)` with `R` a
    /// constructor application, enumerates the free Boolean guards appearing in
    /// the `ite`s of `R`'s structural closure, and for each guard `g` tests both
    /// polarities: if, under the hypothesis `g = b` (selector-on-constructor
    /// reductions applied), `L` becomes a PROPER structural subterm of `R`, then
    /// `g = b` would assert a well-foundedness cycle, so it cannot hold —
    /// `g = ¬b` is entailed. The forcing literal (`g` when `b = false`, `(not g)`
    /// when `b = true`) is emitted.
    ///
    /// Soundness: the emitted literal is a logical consequence of the asserted
    /// equality plus the datatype acyclicity axiom. In any model, were the guard
    /// equal to `b`, the equality `L = R` would equate `L` with a constructor
    /// term that (after the model-valid selector reductions) contains `L` as a
    /// proper subterm — impossible, since the rank/depth strictly decreases along
    /// constructor edges. Hence the guard must take the other value. Every step
    /// of the reduction (ite branch selection under the hypothesised unit,
    /// selector-of-matching-constructor projection) is a datatype/Bool tautology,
    /// so the derived unit can only constrain the search; it can never cause a
    /// false-UNSAT. Restricting to a SINGLE guard at a time and to equalities
    /// whose constructor side is syntactically present is an incompleteness, not
    /// a soundness, concern.
    pub(in crate::executor) fn dt_guarded_acyclicity_guard_units(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Vec<TermId> {
        if self.ctx.datatype_iter().next().is_none() {
            return Vec::new();
        }
        let bool_units = self.collect_bool_units(assertions, assumptions);
        // Guard-eval memo for the base `bool_units` instance (NOT the per-guard
        // hypothesis maps below, which each get their own fresh memo — a memo is
        // only valid for the exact units map it was built against).
        let mut gmemo: HashMap<TermId, Option<bool>> = HashMap::default();

        // Phase 1 (immutable): collect the forcing literals as
        // (guard_term, forced_value). `forced_value = true` ⇒ emit `g`;
        // `false` ⇒ emit `(not g)`.
        let mut forced: Vec<(TermId, bool)> = Vec::new();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();

        for &t in assertions.iter().chain(assumptions.iter()) {
            let mut eqs: Vec<TermId> = Vec::new();
            self.collect_unconditional_equalities(t, &bool_units, &mut eqs, 0, &mut gmemo);
            for eq in eqs {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(eq) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                // Identify the constructor side `R` and the other side `L`.
                for (l, r) in [(a, b), (b, a)] {
                    if self.ctor_head(r).is_none() {
                        continue;
                    }
                    // Enumerate the free guards inside R's closure (bounded).
                    let mut guards: Vec<TermId> = Vec::new();
                    let mut gseen: HashSet<TermId> = HashSet::default();
                    self.collect_free_guards(
                        r,
                        &bool_units,
                        &mut guards,
                        &mut gseen,
                        0,
                        &mut gmemo,
                    );
                    for g in guards {
                        for hyp in [false, true] {
                            // Hypothesise `g = hyp` on top of the entailed units.
                            let mut hyp_units = bool_units.clone();
                            hyp_units.insert(g, hyp);
                            if let TermData::Not(inner) = self.ctx.terms.get(g) {
                                hyp_units.insert(*inner, !hyp);
                            }
                            // Is `l` a proper structural subterm of `r` under this
                            // hypothesis (selector-aware)? Fresh memos: `hyp_units`
                            // differs from `bool_units`, so the pass-level `gmemo`
                            // must NOT be used here (stale entries would be unsound).
                            let mut memo: HashMap<TermId, bool> = HashMap::default();
                            let mut hyp_gmemo: HashMap<TermId, Option<bool>> = HashMap::default();
                            let cyclic = self.sel_aware_ctor_closure_contains(
                                r,
                                l,
                                &hyp_units,
                                &mut memo,
                                &mut hyp_gmemo,
                            );
                            if cyclic {
                                // `g = hyp` ⇒ cycle ⇒ impossible. Force `g = !hyp`.
                                let lit = (g, !hyp);
                                if seen.insert(lit) {
                                    forced.push(lit);
                                }
                                // One refuting polarity is enough for this guard.
                                break;
                            }
                        }
                    }
                }
            }
        }

        // Phase 2 (mutable): materialize the forcing literals.
        let mut out: Vec<TermId> = Vec::new();
        for (g, val) in forced {
            let lit = if val { g } else { self.ctx.terms.mk_not(g) };
            if !out.contains(&lit) {
                out.push(lit);
            }
        }
        out
    }

    /// Collect the free Boolean guard terms of every `ite` in `term`'s
    /// constructor/selector/ite structural closure whose value is NOT already
    /// entailed by `units`. Descends constructor args, selector args, and both
    /// `ite` branches. Bounded; the `gseen` set dedups and the depth bound caps
    /// pathological inputs. Side-effect-free.
    fn collect_free_guards(
        &self,
        term: TermId,
        units: &HashMap<TermId, bool>,
        out: &mut Vec<TermId>,
        gseen: &mut HashSet<TermId>,
        depth: usize,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) {
        const MAX_GUARD_DEPTH: usize = 32;
        if depth >= MAX_GUARD_DEPTH || out.len() >= 16 {
            return;
        }
        if !gseen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::Ite(g, then_t, else_t) => {
                let (g, then_t, else_t) = (*g, *then_t, *else_t);
                if self.eval_bool_guard(g, units, gmemo).is_none() && out.len() < 16 {
                    out.push(g);
                }
                self.collect_free_guards(then_t, units, out, gseen, depth + 1, gmemo);
                self.collect_free_guards(else_t, units, out, gseen, depth + 1, gmemo);
            }
            TermData::App(Symbol::Named(_), args) => {
                let args = args.clone();
                for a in args {
                    self.collect_free_guards(a, units, out, gseen, depth + 1, gmemo);
                }
            }
            _ => {}
        }
    }

    /// Selector-aware variant of [`Self::ctor_closure_contains`]: `target` is a
    /// PROPER structural subterm of the constructor application `ctor` under the
    /// hypothesised `units`, following constructor arguments, guard-resolved
    /// `ite`s, AND selector-on-constructor projections
    /// (`sel_i(C(.. a_i ..)) → a_i`). The starting `ctor` must itself be a
    /// constructor application (an equality with a bare variable on the
    /// constructor side is not a structural cycle). See
    /// [`Self::dt_guarded_acyclicity_guard_units`] for the soundness argument.
    fn sel_aware_ctor_closure_contains(
        &self,
        ctor: TermId,
        target: TermId,
        units: &HashMap<TermId, bool>,
        memo: &mut HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> bool {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(ctor) else {
            return false;
        };
        if self.ctx.is_constructor(name).is_none() {
            return false;
        }
        let args = args.clone();
        // PROPER subterm: descend into each constructor argument, never the
        // whole `ctor` term itself.
        args.iter()
            .any(|&a| self.sel_aware_subterm_contains(a, target, units, memo, gmemo))
    }

    /// True iff `target` is a structural subterm of `term`'s value under the
    /// hypothesised `units`, reducing selector-on-constructor applications. An
    /// `ite` with an entailed guard takes only the live branch; an undetermined
    /// `ite` requires the occurrence under BOTH branches. A selector applied to
    /// a (reduced) constructor of the matching constructor projects to the
    /// selected argument; any other selector application is opaque (no edge).
    /// Memoized over the (term, units-hypothesis) walk — the memo is rebuilt per
    /// hypothesis, so it caches only within a single guard assignment.
    fn sel_aware_subterm_contains(
        &self,
        term: TermId,
        target: TermId,
        units: &HashMap<TermId, bool>,
        memo: &mut HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> bool {
        if term == target {
            return true;
        }
        if let Some(&cached) = memo.get(&term) {
            return cached;
        }
        memo.insert(term, false);
        let result = match self.ctx.terms.get(term) {
            // Constructor: present under ANY argument.
            TermData::App(Symbol::Named(name), args) if self.ctx.is_constructor(name).is_some() => {
                let args = args.clone();
                args.iter()
                    .any(|&a| self.sel_aware_subterm_contains(a, target, units, memo, gmemo))
            }
            // Selector application `(sel x)`: reduce `x` to a constructor (under
            // the hypothesised units) and, when `sel` is one of that
            // constructor's selectors, recurse into the projected argument.
            TermData::App(Symbol::Named(name), args) if args.len() == 1 => {
                if let Some((ctor_name, idx)) = self.selector_ctor_index(name) {
                    if let Some(reduced) = self.reduce_to_ctor(args[0], units, gmemo) {
                        if let TermData::App(Symbol::Named(rname), rargs) =
                            self.ctx.terms.get(reduced)
                        {
                            if *rname == ctor_name && idx < rargs.len() {
                                let projected = rargs[idx];
                                return {
                                    let r = self.sel_aware_subterm_contains(
                                        projected, target, units, memo, gmemo,
                                    );
                                    memo.insert(term, r);
                                    r
                                };
                            }
                        }
                    }
                }
                false
            }
            // `ite`: live branch when the guard is entailed, else require BOTH.
            TermData::Ite(g, then_t, else_t) => {
                let (g, then_t, else_t) = (*g, *then_t, *else_t);
                match self.eval_bool_guard(g, units, gmemo) {
                    Some(true) => {
                        self.sel_aware_subterm_contains(then_t, target, units, memo, gmemo)
                    }
                    Some(false) => {
                        self.sel_aware_subterm_contains(else_t, target, units, memo, gmemo)
                    }
                    None => {
                        self.sel_aware_subterm_contains(then_t, target, units, memo, gmemo)
                            && self.sel_aware_subterm_contains(else_t, target, units, memo, gmemo)
                    }
                }
            }
            _ => false,
        };
        memo.insert(term, result);
        result
    }

    /// Reduce `term` toward a constructor application under the hypothesised
    /// `units`: resolve a top-level guard-entailed `ite` to its live branch and
    /// project a selector-on-matching-constructor, repeating up to a small bound.
    /// Returns the reduced term when it is a constructor application, else
    /// `None`. Pure / read-only; every reduction is a datatype or Bool tautology
    /// under the hypothesis.
    fn reduce_to_ctor(
        &self,
        term: TermId,
        units: &HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> Option<TermId> {
        let mut cur = term;
        for _ in 0..16 {
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(name), _)
                    if self.ctx.is_constructor(name).is_some() =>
                {
                    return Some(cur);
                }
                TermData::Ite(g, then_t, else_t) => {
                    let (g, then_t, else_t) = (*g, *then_t, *else_t);
                    match self.eval_bool_guard(g, units, gmemo) {
                        Some(true) => cur = then_t,
                        Some(false) => cur = else_t,
                        None => return None,
                    }
                }
                TermData::App(Symbol::Named(name), args) if args.len() == 1 => {
                    let (name, arg) = (name.clone(), args[0]);
                    let (ctor_name, idx) = self.selector_ctor_index(&name)?;
                    let reduced = self.reduce_to_ctor(arg, units, gmemo)?;
                    let TermData::App(Symbol::Named(rname), rargs) = self.ctx.terms.get(reduced)
                    else {
                        return None;
                    };
                    if *rname != ctor_name || idx >= rargs.len() {
                        return None;
                    }
                    cur = rargs[idx];
                }
                _ => return None,
            }
        }
        None
    }

    /// If `name` is a datatype selector, return its `(constructor_name, index)`
    /// — the constructor it projects and the positional argument it selects.
    fn selector_ctor_index(&self, name: &str) -> Option<(String, usize)> {
        for (ctor_name, sels) in self.ctx.ctor_selectors_iter() {
            if let Some(idx) = sels.iter().position(|s| s == name) {
                return Some((ctor_name.clone(), idx));
            }
        }
        None
    }

    /// Collect the equality disjuncts of a "disjunction of equalities" assertion
    /// into `out`. Recognizes `(or ..)` and the `(not (and (not ..) ..))` De
    /// Morgan shape produced by `(not (distinct ..))`. Does not recurse into
    /// arbitrary Boolean structure (only the two disjunctive shapes), so it
    /// stays a syntactic, side-effect-free scan.
    fn collect_eq_disjuncts(&self, t: TermId, out: &mut Vec<TermId>) {
        match self.ctx.terms.get(t) {
            // `(or e1 .. en)`: each arg is a disjunct.
            TermData::App(Symbol::Named(name), args) if name == "or" => {
                let args = args.clone();
                for a in args {
                    out.push(a);
                }
            }
            // `(not inner)`: `(not (distinct ..))` lowers to either
            // `(not (not (= a b)))` (binary) or `(not (and (not e1) ..))`
            // (n-ary). Peel the outer `not` and read the disjuncts off the
            // negated conjunction / double-negation.
            TermData::Not(inner) => {
                let inner = *inner;
                match self.ctx.terms.get(inner) {
                    // Binary distinct: `(not (not (= a b)))` ⇒ disjunct `(= a b)`.
                    TermData::Not(eq) => out.push(*eq),
                    // N-ary distinct: `(not (and (not e1) .. (not en)))`
                    // ⇒ disjuncts e1 .. en.
                    TermData::App(Symbol::Named(name), conj_args) if name == "and" => {
                        let conj_args = conj_args.clone();
                        for c in conj_args {
                            if let TermData::Not(eq) = self.ctx.terms.get(c) {
                                out.push(*eq);
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Collect the UNCONDITIONAL equalities entailed by `t`: a bare `(= a b)`,
    /// those under an `(and ..)`, and those forced by an `(or ..)` whose other
    /// disjuncts are all entailed FALSE (a determined `ite` guard inside a CNF
    /// clause — e.g. `(or is-nil(cons ..) (and v15 (= v11 (node v11 ..))))` with
    /// `is-nil(cons ..) = false` forces the second disjunct). Every collected
    /// equality holds in every model, so an acyclicity lemma `(not (= a b))`
    /// derived from one is sound. Conditional equalities under an undetermined
    /// `or`/`ite`/`=>` are NOT collected here (#dt-acyclic-or-clause).
    fn collect_unconditional_equalities(
        &self,
        t: TermId,
        units: &HashMap<TermId, bool>,
        out: &mut Vec<TermId>,
        depth: usize,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) {
        if depth > Self::DT_EQ_REFUTE_MAX_DEPTH {
            return;
        }
        match self.ctx.terms.get(t) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                out.push(t);
            }
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                let args = args.clone();
                for a in args {
                    self.collect_unconditional_equalities(a, units, out, depth + 1, gmemo);
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "or" => {
                let args = args.clone();
                // If a disjunct is entailed TRUE the clause is already satisfied —
                // nothing is forced. Otherwise the disjuncts not entailed FALSE are
                // the only ways to satisfy this asserted clause; if exactly one
                // remains it is forced and its facts are unconditional.
                // Single pass: evaluate each disjunct once (memoized) instead of
                // the previous any()+filter() double evaluation.
                let mut live: Vec<TermId> = Vec::new();
                for &a in &args {
                    match self.eval_bool_guard(a, units, gmemo) {
                        Some(true) => return,
                        Some(false) => {}
                        None => live.push(a),
                    }
                }
                if live.len() == 1 {
                    self.collect_unconditional_equalities(live[0], units, out, depth + 1, gmemo);
                }
            }
            _ => {}
        }
    }

    /// Maximum recursion depth for [`Self::dt_eq_refuted`].
    const DT_EQ_REFUTE_MAX_DEPTH: usize = 48;

    /// True iff the equality `(= a b)` is UNSAT by datatype structure alone:
    /// a constructor CLASH (`C(..) = D(..)`, `C != D`), an injective-constructor
    /// argument mismatch (`C(x..) = C(y..)` with some `x_i = y_i` refuted), or a
    /// structural CYCLE (one side is a constructor whose closure contains the
    /// other). Guard-determined `ite`s are resolved to their live branch; an
    /// undetermined `ite` is refuted only when refuted under BOTH branches (so a
    /// conditional mismatch is never reported). Every leaf rule is a datatype
    /// theory tautology, so `(not (= a b))` derived from a `true` result is a
    /// valid lemma — it can constrain the search but never cause a false-UNSAT.
    fn dt_eq_refuted(
        &self,
        a: TermId,
        b: TermId,
        units: &HashMap<TermId, bool>,
        depth: usize,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> bool {
        if a == b || depth > Self::DT_EQ_REFUTE_MAX_DEPTH {
            return false;
        }
        // Resolve / split a top-level `ite` on either side.
        if let TermData::Ite(g, t, e) = self.ctx.terms.get(a) {
            let (g, t, e) = (*g, *t, *e);
            return match self.eval_bool_guard(g, units, gmemo) {
                Some(true) => self.dt_eq_refuted(t, b, units, depth + 1, gmemo),
                Some(false) => self.dt_eq_refuted(e, b, units, depth + 1, gmemo),
                None => {
                    self.dt_eq_refuted(t, b, units, depth + 1, gmemo)
                        && self.dt_eq_refuted(e, b, units, depth + 1, gmemo)
                }
            };
        }
        if let TermData::Ite(g, t, e) = self.ctx.terms.get(b) {
            let (g, t, e) = (*g, *t, *e);
            return match self.eval_bool_guard(g, units, gmemo) {
                Some(true) => self.dt_eq_refuted(a, t, units, depth + 1, gmemo),
                Some(false) => self.dt_eq_refuted(a, e, units, depth + 1, gmemo),
                None => {
                    self.dt_eq_refuted(a, t, units, depth + 1, gmemo)
                        && self.dt_eq_refuted(a, e, units, depth + 1, gmemo)
                }
            };
        }
        // Both sides are ite-free.
        match (self.ctor_head(a), self.ctor_head(b)) {
            (Some((ca, aargs)), Some((cb, bargs))) => {
                if ca != cb {
                    return true; // constructor clash: C(..) != D(..) in every model
                }
                // Same (injective) constructor: refuted iff some argument pair is.
                if aargs.len() == bargs.len()
                    && aargs
                        .iter()
                        .zip(bargs.iter())
                        .any(|(&x, &y)| self.dt_eq_refuted(x, y, units, depth + 1, gmemo))
                {
                    return true;
                }
                self.ctor_closure_contains(a, b, units, gmemo)
                    || self.ctor_closure_contains(b, a, units, gmemo)
            }
            (Some(_), None) => self.ctor_closure_contains(a, b, units, gmemo),
            (None, Some(_)) => self.ctor_closure_contains(b, a, units, gmemo),
            (None, None) => false,
        }
    }

    /// If `t` is a constructor application, return `(ctor_name, args)`.
    fn ctor_head(&self, t: TermId) -> Option<(String, Vec<TermId>)> {
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
            if self.ctx.is_constructor(name).is_some() {
                return Some((name.clone(), args.clone()));
            }
        }
        None
    }

    /// Returns `true` if `target` is a PROPER structural subterm of `ctor` under
    /// EVERY branch selection — i.e. `ctor` is a constructor application
    /// `C(.. target ..)` (transitively) in which `target` occurs unconditionally,
    /// so `(= ctor target)` is valid-false by datatype well-foundedness. The
    /// starting term `ctor` must itself be a constructor application (an equality
    /// `(= v target)` with `v` a bare variable is not a structural cycle).
    ///
    /// Descends through constructor applications (subterm under ANY argument) and
    /// `ite` (subterm only when present under BOTH branches — an occurrence in a
    /// single branch is conditional and is deliberately NOT reported, so e.g.
    /// `v = (cons x (ite b v nil))` stays SAT). Selectors / UF / arithmetic are
    /// opaque and never establish a structural edge (#dt-acyclic-ite-closure).
    fn ctor_closure_contains(
        &self,
        ctor: TermId,
        target: TermId,
        units: &HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> bool {
        // `ctor` must be a constructor application to root a structural cycle.
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(ctor) else {
            return false;
        };
        if self.ctx.is_constructor(name).is_none() {
            return false;
        }
        let args = args.clone();
        let mut memo: HashMap<TermId, bool> = HashMap::default();
        args.iter()
            .any(|&a| self.subterm_always_contains(a, target, units, &mut memo, gmemo))
    }

    /// True iff `target` is a structural subterm of `term`'s value under EVERY
    /// model: constructor args contribute under ANY argument, `ite` branches only
    /// when `target` is present under BOTH — UNLESS the guard is entailed
    /// true/false (via `units` / structural tester evaluation), in which case
    /// only the live branch counts. Memoized over the (acyclic, interned) term
    /// DAG. See [`Self::ctor_closure_contains`] for the soundness rationale.
    fn subterm_always_contains(
        &self,
        term: TermId,
        target: TermId,
        units: &HashMap<TermId, bool>,
        memo: &mut HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> bool {
        if term == target {
            return true;
        }
        if let Some(&cached) = memo.get(&term) {
            return cached;
        }
        // Provisional `false` guards against pathological sharing (terms are
        // acyclic, so this is only belt-and-suspenders) and is overwritten below.
        memo.insert(term, false);
        let result = match self.ctx.terms.get(term) {
            // Constructor: present if present under ANY argument.
            TermData::App(Symbol::Named(name), args) if self.ctx.is_constructor(name).is_some() => {
                let args = args.clone();
                args.iter()
                    .any(|&a| self.subterm_always_contains(a, target, units, memo, gmemo))
            }
            // `ite`: take only the live branch when the guard is entailed, else
            // require the occurrence under BOTH branches (guard-independent).
            TermData::Ite(g, then_t, else_t) => {
                let (g, then_t, else_t) = (*g, *then_t, *else_t);
                match self.eval_bool_guard(g, units, gmemo) {
                    Some(true) => self.subterm_always_contains(then_t, target, units, memo, gmemo),
                    Some(false) => self.subterm_always_contains(else_t, target, units, memo, gmemo),
                    None => {
                        self.subterm_always_contains(then_t, target, units, memo, gmemo)
                            && self.subterm_always_contains(else_t, target, units, memo, gmemo)
                    }
                }
            }
            _ => false,
        };
        memo.insert(term, result);
        result
    }

    /// Collect Boolean terms entailed true/false by the UNCONDITIONAL top-level
    /// conjuncts (descend positive `and` only), with a bounded fixpoint that
    /// propagates `(not X)`, `(and ..)`, `(or ..)`, and the Bool constants. Used
    /// only to resolve `ite` guards in the acyclicity closure; every recorded
    /// assignment is a logical consequence of the asserted conjuncts.
    fn collect_bool_units(
        &self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> HashMap<TermId, bool> {
        let mut units: HashMap<TermId, bool> = HashMap::default();
        // Seed from top-level conjuncts.
        let mut stack: Vec<TermId> = assertions
            .iter()
            .chain(assumptions.iter())
            .copied()
            .collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                if name == "and" {
                    stack.extend(args.iter().copied());
                    continue;
                }
            }
            units.insert(t, true);
            if let TermData::Not(inner) = self.ctx.terms.get(t) {
                units.insert(*inner, false);
            }
        }
        // Bounded fixpoint propagation over the recorded terms.
        for _ in 0..8 {
            let snapshot: Vec<(TermId, bool)> = units.iter().map(|(&k, &v)| (k, v)).collect();
            let before = units.len();
            for (term, val) in snapshot {
                match self.ctx.terms.get(term) {
                    TermData::Not(inner) => {
                        units.entry(*inner).or_insert(!val);
                    }
                    TermData::App(Symbol::Named(name), args) if name == "and" => {
                        let args = args.clone();
                        if val {
                            for a in args {
                                units.entry(a).or_insert(true);
                            }
                        } else {
                            // `and = false` with all-but-one operand known true.
                            let unknown: Vec<TermId> = args
                                .iter()
                                .copied()
                                .filter(|a| self.unit_value(*a, &units) != Some(true))
                                .collect();
                            if unknown.len() == 1 {
                                units.entry(unknown[0]).or_insert(false);
                            }
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "or" => {
                        let args = args.clone();
                        if !val {
                            for a in args {
                                units.entry(a).or_insert(false);
                            }
                        } else {
                            let unknown: Vec<TermId> = args
                                .iter()
                                .copied()
                                .filter(|a| self.unit_value(*a, &units) != Some(false))
                                .collect();
                            if unknown.len() == 1 {
                                units.entry(unknown[0]).or_insert(true);
                            }
                        }
                    }
                    _ => {}
                }
            }
            if units.len() == before {
                break;
            }
        }
        units
    }

    /// Read an already-recorded unit value, also honouring the Bool constants.
    fn unit_value(&self, t: TermId, units: &HashMap<TermId, bool>) -> Option<bool> {
        if let Some(&v) = units.get(&t) {
            return Some(v);
        }
        match self.ctx.terms.get(t) {
            TermData::Const(ay_core::Constant::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    /// Evaluate a Boolean guard term to a definite value when ENTAILED: by a
    /// recorded unit, the Bool constants, `not`/`and`/`or` of evaluable args, or
    /// a structural tester `(is-C (D ..))` (= `C == D`, a datatype tautology).
    /// Returns `None` when the value is not entailed. Sound for branch pruning:
    /// only ever returns a value the guard provably takes in every model.
    ///
    /// Memoized over the interned term DAG via `gmemo`, which MUST be scoped to
    /// a single `units` map (rebuild it whenever the units differ, e.g. per
    /// guard hypothesis in [`Self::dt_guarded_acyclicity_guard_units`]) — the
    /// same per-units-instance contract as `sel_aware_subterm_contains`'s memo.
    /// Without this, guard terms that share subterms (a hash-consed DAG — e.g.
    /// BMC path conditions, where `pc_n = pc_{n-1} AND cond_n`) are re-walked
    /// once per tree PATH instead of once per NODE, which is exponential in the
    /// nesting depth and made large BMC instances spin for minutes inside the
    /// DT acyclicity pass. The memoized result is identical to the unmemoized
    /// one (the evaluation is a pure function of `(g, units, term table)`), so
    /// this cannot change any verdict — only the time to reach it.
    fn eval_bool_guard(
        &self,
        g: TermId,
        units: &HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> Option<bool> {
        if let Some(v) = self.unit_value(g, units) {
            return Some(v);
        }
        if let Some(&cached) = gmemo.get(&g) {
            return cached;
        }
        let result = self.eval_bool_guard_uncached(g, units, gmemo);
        gmemo.insert(g, result);
        result
    }

    /// The single-node evaluation step of [`Self::eval_bool_guard`] (children go
    /// back through the memoized entry point). Never call directly.
    fn eval_bool_guard_uncached(
        &self,
        g: TermId,
        units: &HashMap<TermId, bool>,
        gmemo: &mut HashMap<TermId, Option<bool>>,
    ) -> Option<bool> {
        match self.ctx.terms.get(g) {
            TermData::Not(inner) => self.eval_bool_guard(*inner, units, gmemo).map(|v| !v),
            TermData::App(Symbol::Named(name), args) => {
                // Structural tester on a constructor application: `is-C (D ..)`.
                if let Some(ctor) = name.strip_prefix("is-") {
                    if self.ctx.is_constructor(ctor).is_some() && args.len() == 1 {
                        if let TermData::App(Symbol::Named(dname), _) = self.ctx.terms.get(args[0])
                        {
                            if self.ctx.is_constructor(dname).is_some() {
                                return Some(dname == ctor);
                            }
                        }
                    }
                }
                let args = args.clone();
                match name.as_str() {
                    "and" => {
                        let mut all_true = true;
                        for a in &args {
                            match self.eval_bool_guard(*a, units, gmemo) {
                                Some(false) => return Some(false),
                                Some(true) => {}
                                None => all_true = false,
                            }
                        }
                        all_true.then_some(true)
                    }
                    "or" => {
                        let mut all_false = true;
                        for a in &args {
                            match self.eval_bool_guard(*a, units, gmemo) {
                                Some(true) => return Some(true),
                                Some(false) => {}
                                None => all_false = false,
                            }
                        }
                        all_false.then_some(false)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Unified check-sat-assuming path for all DT-combined logics.
    ///
    /// Handles the common DT pattern:
    /// 1. Occurs-check fast path (returns UNSAT if cyclic)
    /// 2. DT selector axiom generation from assertions + assumptions
    /// 3. Optional acyclicity depth axiom generation
    /// 4. Dispatch to the appropriate theory solver
    ///
    /// # Arguments
    ///
    /// * `base_assertions` - The permanent assertions plus any scope-level additions
    /// * `assumptions` - Temporary assumptions for this check-sat call
    /// * `acyclicity_sort` - If `Some(sort)`, generate acyclicity depth axioms using
    ///   that sort for the depth function. `None` for BV/Array arms where the theory
    ///   solver cannot handle integer arithmetic (#1766).
    /// * `dispatch` - Which theory solver to route to after axiom generation.
    ///
    /// Extracted from 6 near-identical match arms in `check_sat_assuming` (#5564).
    pub(in crate::executor) fn dt_combined_check_sat_assuming(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        acyclicity_sort: Option<Sort>,
        dispatch: DtSolverDispatch,
    ) -> Result<SolveResult> {
        // Fast path: pure DT occurs-check can decide acyclicity even when the
        // depth-axiom encoding is incomplete for multi-hop cycles (#1776).
        if self.dt_occurs_check_unsat_from_equalities(base_assertions, assumptions) {
            self.last_unknown_reason = None;
            self.last_result = Some(SolveResult::unsat());
            self.last_assumption_core = Some(vec![]);
            return Ok(SolveResult::unsat());
        }

        // Include assumptions in base_set for DT axiom generation (#1768).
        // Equalities like `(= x (cons n x))` in assumptions must be processed.
        let mut base_set: HashSet<TermId> = base_assertions.iter().copied().collect();
        base_set.extend(assumptions.iter().copied());
        let dt_axioms = self.dt_selector_axioms(&base_set);
        // Field-level selector-congruence for datatype-valued array selects at
        // symbolic indices (the static DT path above does not cover these; see
        // dt_array_select_field_congruence_axioms). Sound (entailed instances
        // of array∘selector congruence), so it cannot cause false-unsat.
        let dt_field_cong = self.dt_array_select_field_congruence_axioms(&base_set);
        // Field-level decomposition for select-vs-constructor equalities
        // (#dt-select-ctor-field-decomposition) — sound (datatype tautologies).
        let dt_ctor_field = self.dt_array_select_ctor_field_axioms(&base_set);

        // Record the generated axiom terms so the validation's
        // #dt-embedded-cycle compound guard exempts them (entailed datatype
        // tautologies; see `dt_solver_added_axiom_terms`). Cleared below.
        self.dt_solver_added_axiom_terms.extend(
            dt_axioms
                .iter()
                .chain(dt_field_cong.iter())
                .chain(dt_ctor_field.iter())
                .copied(),
        );
        let mut extended_assertions = base_assertions.to_vec();
        extended_assertions.extend(dt_axioms);
        extended_assertions.extend(dt_field_cong);
        extended_assertions.extend(dt_ctor_field);

        // Generate and add acyclicity depth axioms if the theory solver can handle
        // the arithmetic encoding (Sort::Int or Sort::Real).
        let acyclicity_axioms = if let Some(sort) = acyclicity_sort {
            // Temporarily add assumptions to ctx.assertions for depth axiom
            // generation (#1768). This ensures depth congruence axioms are
            // generated for assumption equalities.
            let original_assertions_exact = self.ctx.assertions.clone();
            self.ctx.assertions.extend(assumptions.iter().copied());
            let axioms = self.dt_acyclicity_depth_axioms(sort);
            self.ctx.assertions = original_assertions_exact;

            self.dt_solver_added_axiom_terms
                .extend(axioms.iter().copied());
            extended_assertions.extend(axioms.iter().copied());
            axioms
        } else {
            vec![]
        };

        // Temporarily add acyclicity depth axioms to ctx.assertions so
        // validate_model checks them during check_sat_assuming, matching
        // the scope of the non-assuming DT solve methods (#3240). Selector
        // axioms are not added here because the model evaluator lacks full
        // DT selector-constructor reduction semantics.
        let pre_solve_assertions_exact = self.ctx.assertions.clone();
        self.ctx.assertions.extend(acyclicity_axioms);

        let result = match dispatch {
            DtSolverDispatch::AufLia => {
                self.solve_auf_lia_with_assumptions(&extended_assertions, assumptions)
            }
            DtSolverDispatch::AufLira => {
                self.solve_auflira_with_assumptions(&extended_assertions, assumptions)
            }
            DtSolverDispatch::Theory(kind) => {
                self.solve_with_assumptions_for_theory(&extended_assertions, assumptions, kind)
            }
        };

        // Restore assertions after solving.
        self.ctx.assertions = pre_solve_assertions_exact;
        self.dt_solver_added_axiom_terms.clear();
        result
    }
}

/// One disjunct of a top-level assertion decomposed for the DT occurs-check
/// (#dt-acyclic-ite). See [`Executor::collect_dt_fact_disjuncts`].
enum DisjunctOption {
    /// A conjunctive set of DT fact literals (equalities / true testers) that the
    /// DT solver can reason about together.
    Facts(Vec<TermId>),
    /// An opaque branch the occurs-check cannot decompose. It is treated as a
    /// satisfiable possibility (unrefutable), so any selection that includes it is
    /// NOT provably UNSAT — keeping the check fail-closed (no false-UNSAT).
    Opaque,
}

/// Dispatch variant for DT-combined solver routing.
///
/// Parameterizes which underlying theory solver the DT-combined path should
/// route to after generating DT axioms.
#[derive(Debug, Clone, Copy)]
pub(in crate::executor) enum DtSolverDispatch {
    /// Route to `solve_auf_lia_with_assumptions` (split-aware DT+LIA, #1771).
    AufLia,
    /// Route to `solve_auflira_with_assumptions` (DT+LIRA, #5402).
    AufLira,
    /// Route to `solve_with_assumptions_for_theory` with the given theory kind.
    Theory(TheoryKind),
}
