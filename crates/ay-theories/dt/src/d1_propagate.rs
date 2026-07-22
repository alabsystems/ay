// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D1: lazy datatype tester/selector propagation during CDCL search.
//!
//! Stage D1 of the development design notes: a
//! merge-driven propagation pass over the *existing* EUF congruence closure
//! that fires the Barrett–Shikanian–Tinelli evaluation rules the eager DtAx
//! axiom encoding only pre-instantiates for *syntactic* occurrences:
//!
//! - **Tester evaluation**: `t ~ C(u⃗)` in the e-graph (a *derived* merge, not
//!   necessarily an asserted equality) ⇒ `is-C(t)` is true and `is-D(t)` is
//!   false for every other constructor `D` of the same datatype.
//! - **Tester transfer / exclusion**: `x ~ y` ⇒ `is-C(x) ⇔ is-C(y)` and
//!   `is-C(x) ⇒ ¬is-D(y)` for `C ≠ D` — links tester atoms across merged
//!   classes that have no constructor application yet.
//! - **Selector evaluation**: `t ~ C(u⃗)` and `sel_i^C(t)` exists in the term
//!   store ⇒ `sel_i^C(t) = u_i` (SMT-LIB total-selector semantics: selectors
//!   of *other* constructors stay unconstrained and are never propagated).
//!
//! ## Conduit and soundness
//!
//! Every propagation is emitted as a permanent clause via
//! `TheoryResult::NeedLemmas` (the same conduit as the D0 pass and array ROW2
//! batching, #6546) — never as a bare `TheoryPropagation` and never as a
//! direct e-graph merge. This keeps the whole flow at the Boolean level: the
//! SAT core unit-propagates the clause, `assert_literal` streams the
//! consequence back into EUF, and every later conflict remains re-derivable
//! by the existing fail-closed conflict/propagation verifiers *without* any
//! datatype-aware re-derivation channel.
//!
//! Each emitted clause is an **assignment-independent DT+EUF tautology** of
//! the form `¬r₁ ∨ ... ∨ ¬rₖ ∨ lit` where `{r₁..rₖ} ⊨_EUF a ~ w` (the merge
//! justification from [`ay_euf::EufSolver::explain`]) and `a ~ w ⊨_DT lit` is
//! one of the three rules above (validated against the registered
//! constructor/selector/tester signatures). Before emission the EUF
//! entailment is **independently re-derived on a fresh (cached, verify-only)
//! EUF solver**: assert exactly `{r₁..rₖ}`, close, and require `a ~ w`. A
//! propagation whose explanation fails re-derivation is dropped with a
//! warning (fail-open for that propagation; the eager axioms and the model
//! gates remain the backstop) — an under-explained clause can never reach the
//! SAT core. Adding entailed tautology clauses can only prune models that
//! violate datatype semantics; it can never manufacture a false-UNSAT, and
//! Sat verdicts still pass through the always-on model gates.
//!
//! ## Cost model
//!
//! The pass is gated on [`ay_euf::EufSolver::take_dt_merge_dirty`] (set by
//! `incremental_merge`), so BCP rounds without e-class merges never re-scan.
//! On a dirty round the scan is `O(#ctor-apps + #testers + #selector-apps)`
//! root lookups; `explain` + fresh-EUF re-derivation run only for *new*
//! `(target, witness)` pairs (deduplicated forever in `handled`), and
//! per-round/total emission budgets bound the clause volume.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::{TheoryLemma, TheoryLit, TheoryResult, TheorySolver};
use ay_euf::EufSolver;

/// Maximum clauses emitted per `propagate_lemmas` call. When the cap is hit
/// the pass requests a re-run on the next call (`wants_rerun`) so nothing is
/// lost — the remaining pairs are picked up incrementally.
const D1_MAX_LEMMAS_PER_ROUND: usize = 128;

/// Total emission budget per propagator instance (one instance per solve /
/// combiner). Past it the pass goes inert (fail-open: the eager axioms and
/// the always-on gates remain authoritative).
const D1_MAX_LEMMAS_TOTAL: u64 = 100_000;

/// Interned constructor id.
type CtorId = u32;

/// Lazy DT tester/selector propagation over the EUF e-graph (stage D1).
///
/// Construct once per solve, register datatypes via
/// [`register_datatype`](Self::register_datatype) and selector signatures via
/// [`register_ctor_selectors`](Self::register_ctor_selectors), then call
/// [`propagate_lemmas`](Self::propagate_lemmas) from the theory's BCP-time
/// and final checks.
#[derive(Debug, Default)]
pub struct DtLazyPropagator {
    /// Constructor name -> interned id.
    ctor_ids: HashMap<String, CtorId>,
    /// Interned id -> (constructor name, datatype name).
    ctors: Vec<(String, String)>,
    /// Tester name (`is-C`) -> constructor id.
    tester_names: HashMap<String, CtorId>,
    /// Selector name -> (constructor id, argument position). SMT-LIB selector
    /// names are globally unique per (possibly instance-mangled) datatype;
    /// re-registration keeps the first entry and warns on disagreement.
    sel_defs: HashMap<String, (CtorId, usize)>,

    /// Term-store scan frontier (the store is append-only).
    scanned_len: usize,
    /// Constructor applications/constants: (term, ctor id).
    ctor_apps: Vec<(TermId, CtorId)>,
    /// Tester applications: (tester term, argument, ctor id).
    tester_apps: Vec<(TermId, TermId, CtorId)>,
    /// Selector applications: (selector term, argument, ctor id, position).
    sel_apps: Vec<(TermId, TermId, CtorId, usize)>,

    /// `(target, witness)` pairs already attempted (emitted or dropped).
    /// Clauses are permanent, so one emission per pair suffices.
    handled: HashSet<(TermId, TermId)>,
    /// Total clauses emitted by this instance.
    emitted_total: u64,
    /// Per-round cap was hit: re-run on the next call even without new merges.
    rerun_requested: bool,
    /// Verification failures observed (should stay 0; >0 signals an explain bug).
    rederive_failures: u64,
    /// Per-rule emission counters (tester eval / transfer+exclusion / selector eval).
    rule_tester_eval: u64,
    rule_transfer: u64,
    rule_sel_eval: u64,
    /// Rule 2 (tester transfer/exclusion) enablement. Default true;
    /// `AY_DT_D1_TRANSFER=0` disables it for A/B measurement (the transfer
    /// half is a pure-EUF tautology family the e-graph's bool-congruence
    /// propagation may already cover).
    transfer_enabled: bool,
}

impl DtLazyPropagator {
    /// Create an empty propagator (no datatypes registered; pass is inert).
    #[must_use]
    pub fn new() -> Self {
        Self {
            transfer_enabled: !std::env::var_os("AY_DT_D1_TRANSFER").is_some_and(|v| v == "0"),
            ..Self::default()
        }
    }

    /// Register a datatype and its constructor names (internal, possibly
    /// instance-mangled names — the same names the term store uses). Also
    /// derives the tester names (`is-<ctor>`, the frontend's elaboration of
    /// SMT-LIB `(_ is C)`).
    pub fn register_datatype(&mut self, dt_name: &str, constructors: &[String]) {
        for ctor in constructors {
            if self.ctor_ids.contains_key(ctor) {
                continue;
            }
            let id = self.ctors.len() as CtorId;
            self.ctor_ids.insert(ctor.clone(), id);
            self.ctors.push((ctor.clone(), dt_name.to_string()));
            self.tester_names.insert(format!("is-{ctor}"), id);
        }
    }

    /// Register a constructor's ordered selector (field-accessor) names.
    ///
    /// Without this the selector-evaluation rule is inert for that
    /// constructor (fail-open); tester rules need only the constructor names.
    pub fn register_ctor_selectors(&mut self, ctor_name: &str, selectors: &[String]) {
        let Some(&cid) = self.ctor_ids.get(ctor_name) else {
            tracing::warn!(
                ctor = ctor_name,
                "dt-d1: register_ctor_selectors for unregistered constructor; ignored"
            );
            return;
        };
        for (pos, sel) in selectors.iter().enumerate() {
            if let Some(&(prev_cid, prev_pos)) = self.sel_defs.get(sel) {
                if prev_cid != cid || prev_pos != pos {
                    tracing::warn!(
                        selector = %sel,
                        "dt-d1: selector registered with conflicting signature; keeping first"
                    );
                }
                continue;
            }
            self.sel_defs.insert(sel.clone(), (cid, pos));
        }
    }

    /// True when no datatypes are registered (pass is inert).
    #[must_use]
    pub fn is_inert(&self) -> bool {
        self.ctor_ids.is_empty() || self.emitted_total >= D1_MAX_LEMMAS_TOTAL
    }

    /// True when the previous round hit its per-round emission cap and left
    /// work behind: the caller should re-run even without new merges.
    #[must_use]
    pub fn wants_rerun(&self) -> bool {
        self.rerun_requested
    }

    /// Statistics: `(emitted_total, rederive_failures)`.
    #[must_use]
    pub fn stats(&self) -> (u64, u64) {
        (self.emitted_total, self.rederive_failures)
    }

    /// Per-rule emission counters:
    /// `(tester_eval, transfer_exclusion, selector_eval)`.
    #[must_use]
    pub fn rule_stats(&self) -> (u64, u64, u64) {
        (
            self.rule_tester_eval,
            self.rule_transfer,
            self.rule_sel_eval,
        )
    }

    /// Extend the memoized term indexes over newly created terms (the term
    /// store is append-only, so old entries stay valid).
    fn scan_new_terms(&mut self, terms: &TermStore) {
        let len = terms.len();
        for raw in self.scanned_len..len {
            let tid = TermId(raw as u32);
            match terms.get(tid) {
                TermData::App(Symbol::Named(name), args) => {
                    if let Some(&cid) = self.ctor_ids.get(name) {
                        self.ctor_apps.push((tid, cid));
                    } else if args.len() == 1 {
                        if let Some(&cid) = self.tester_names.get(name) {
                            self.tester_apps.push((tid, args[0], cid));
                        } else if let Some(&(cid, pos)) = self.sel_defs.get(name) {
                            self.sel_apps.push((tid, args[0], cid, pos));
                        }
                    }
                }
                // Nullary constructors are `Var` terms whose name is a
                // registered constructor (same convention as the D0 pass).
                TermData::Var(name, _) => {
                    if let Some(&cid) = self.ctor_ids.get(name) {
                        self.ctor_apps.push((tid, cid));
                    }
                }
                _ => {}
            }
        }
        self.scanned_len = len;
    }

    /// Run the D1 propagation rules over `euf`'s current e-graph and return
    /// entailed tautology clauses to inject via `TheoryResult::NeedLemmas`.
    ///
    /// `verifier` must be a solver over the SAME term store (typically cached
    /// and `verify_only`); it is used scope-locally (push/assert/check/pop)
    /// to independently re-derive every clause's EUF entailment before
    /// emission — a clause that fails re-derivation is dropped (fail-open).
    ///
    /// `fixpoint_assignments`: when `Some` (the Nelson-Oppen fixpoint call),
    /// only clauses the CANDIDATE MODEL actually violates are emitted — the
    /// propagated atom must be assigned OPPOSITE to its entailed value.
    /// Rationale: a `NeedLemmas` from the full `check()` costs one split-loop
    /// iteration (unlike the inline BCP conduit), so unconditional fixpoint
    /// emission burns the split budget into a fail-closed Unknown on
    /// instances whose intermediate deepening rounds repeatedly reach
    /// candidate models. Satisfied/unassigned candidates are skipped WITHOUT
    /// entering `handled`, so later search-time runs still emit them.
    pub fn propagate_lemmas(
        &mut self,
        terms: &TermStore,
        euf: &mut EufSolver<'_>,
        verifier: &mut EufSolver<'_>,
        fixpoint_assignments: Option<&HashMap<TermId, bool>>,
    ) -> Vec<TheoryLemma> {
        self.rerun_requested = false;
        if self.is_inert() {
            return Vec::new();
        }
        self.scan_new_terms(terms);
        if self.tester_apps.is_empty() && self.sel_apps.is_empty() {
            return Vec::new();
        }

        // --- Committed classes: root -> (witness ctor app, ctor id) ---------
        // A class with (at least) one constructor application is committed to
        // that constructor. Clashing classes (two distinct constructors) are
        // the D0 conflict pass's job — skip them here (deterministically: the
        // smallest witness TermId wins, clash flag disables the class).
        let mut committed: HashMap<u32, (TermId, CtorId)> = HashMap::default();
        let mut clashed: HashSet<u32> = HashSet::default();
        for &(app, cid) in &self.ctor_apps {
            let root = euf.enode_find_const(app.0);
            match committed.get_mut(&root) {
                None => {
                    committed.insert(root, (app, cid));
                }
                Some((w, wc)) => {
                    if *wc != cid {
                        clashed.insert(root);
                    } else if app < *w {
                        *w = app;
                    }
                }
            }
        }
        for root in &clashed {
            committed.remove(root);
        }

        let mut out: Vec<TheoryLemma> = Vec::new();

        // --- Rule 1: tester evaluation on committed classes ------------------
        // `t ~ C(u⃗)` ⇒ `is-C(t)` true / `is-D(t)` false. Deterministic order:
        // tester_apps is in term-creation order.
        for i in 0..self.tester_apps.len() {
            if out.len() >= D1_MAX_LEMMAS_PER_ROUND {
                self.rerun_requested = true;
                self.emitted_total += out.len() as u64;
                return out;
            }
            let (tester, arg, tcid) = self.tester_apps[i];
            let root = euf.enode_find_const(arg.0);
            let Some(&(witness, wcid)) = committed.get(&root) else {
                continue;
            };
            // Same-term tester-on-constructor is a syntactic fact the eager
            // tester-evaluation axioms already encode; the reason would be
            // empty. Keep the nonempty-reason invariant and skip.
            if arg == witness || self.handled.contains(&(tester, witness)) {
                continue;
            }
            // Cross-datatype testers cannot apply to a well-sorted argument;
            // never emit for them (defensive).
            if self.ctors[tcid as usize].1 != self.ctors[wcid as usize].1 {
                self.handled.insert((tester, witness));
                continue;
            }
            let value = tcid == wcid;
            // Fixpoint mode: only model-violated clauses; skip WITHOUT
            // marking handled so search-time runs still emit the pair.
            if let Some(assigns) = fixpoint_assignments {
                if assigns.get(&tester) != Some(&!value) {
                    continue;
                }
            }
            self.handled.insert((tester, witness));
            if let Some(clause) =
                self.entailed_clause(euf, verifier, arg, witness, TheoryLit::new(tester, value))
            {
                out.push(clause);
                self.rule_tester_eval += 1;
            }
        }

        // --- Rule 3: selector evaluation on committed classes ----------------
        // `t ~ C(u⃗)` and `sel_i^C(t)` exists ⇒ `sel_i^C(t) = u_i` — emitted
        // only when the equality ATOM already exists in the term store (the
        // pass cannot create terms; missing atoms fall back to the eager
        // instantiate axioms).
        for i in 0..self.sel_apps.len() {
            if out.len() >= D1_MAX_LEMMAS_PER_ROUND {
                self.rerun_requested = true;
                self.emitted_total += out.len() as u64;
                return out;
            }
            let (sel_app, arg, scid, pos) = self.sel_apps[i];
            let root = euf.enode_find_const(arg.0);
            let Some(&(witness, wcid)) = committed.get(&root) else {
                continue;
            };
            // Wrong-constructor selector: unconstrained under SMT-LIB
            // total-selector semantics — never propagate.
            if scid != wcid {
                continue;
            }
            if arg == witness || self.handled.contains(&(sel_app, witness)) {
                continue;
            }
            let TermData::App(_, wargs) = terms.get(witness) else {
                continue; // nullary constructor: has no selectors
            };
            let Some(&field) = wargs.get(pos) else {
                tracing::warn!(
                    "dt-d1: selector position out of range for witness constructor; skipped"
                );
                self.handled.insert((sel_app, witness));
                continue;
            };
            if sel_app == field {
                self.handled.insert((sel_app, witness));
                continue;
            }
            let Some(eq_atom) = terms.find_eq(sel_app, field) else {
                // Equality atom not in the term store: skip (fail-open) —
                // WITHOUT marking handled, since a later Tseitin/lift pass
                // may create the atom mid-solve.
                continue;
            };
            // Fixpoint mode: only model-violated clauses (see rule 1).
            if let Some(assigns) = fixpoint_assignments {
                if assigns.get(&eq_atom) != Some(&false) {
                    continue;
                }
            }
            self.handled.insert((sel_app, witness));
            if let Some(clause) =
                self.entailed_clause(euf, verifier, arg, witness, TheoryLit::new(eq_atom, true))
            {
                out.push(clause);
                self.rule_sel_eval += 1;
            }
        }

        // --- Rule 2: tester transfer / exclusion across merged classes ------
        // Runs LAST: the evaluation rules above are the pruning payload and
        // must not be starved by transfer-clause volume under the per-round
        // cap. Only for classes withOUT a committed constructor (Rule 1 is
        // strictly stronger there). Hub scheme: the smallest-TermId tester of
        // the class is the pivot; each other tester links to the pivot, so the
        // full pairwise closure is derivable by Boolean unit propagation.
        if !self.transfer_enabled {
            self.emitted_total += out.len() as u64;
            return out;
        }
        let mut testers_by_root: HashMap<u32, Vec<(TermId, TermId, CtorId)>> = HashMap::default();
        for &(tester, arg, cid) in &self.tester_apps {
            let root = euf.enode_find_const(arg.0);
            if committed.contains_key(&root) || clashed.contains(&root) {
                continue;
            }
            testers_by_root
                .entry(root)
                .or_default()
                .push((tester, arg, cid));
        }
        let mut roots: Vec<u32> = testers_by_root
            .iter()
            .filter(|(_, v)| v.len() > 1)
            .map(|(&r, _)| r)
            .collect();
        roots.sort_unstable();
        'transfer: for root in roots {
            let group = &testers_by_root[&root];
            let &(pivot, pivot_arg, pivot_cid) = group
                .iter()
                .min_by_key(|&&(t, _, _)| t.0)
                .expect("group nonempty");
            for &(tester, arg, cid) in group {
                if out.len() >= D1_MAX_LEMMAS_PER_ROUND {
                    self.rerun_requested = true;
                    break 'transfer;
                }
                if tester == pivot || arg == pivot_arg || self.handled.contains(&(tester, pivot)) {
                    // Same-argument tester pairs are covered by the eager
                    // same-term exclusion/exhaustiveness axioms (and would
                    // have an empty reason).
                    continue;
                }
                if self.ctors[cid as usize].1 != self.ctors[pivot_cid as usize].1 {
                    self.handled.insert((tester, pivot));
                    continue;
                }
                // Fixpoint mode: emit the pair only when the candidate model
                // violates one of its clauses (pivot true and partner
                // contradicting); skip WITHOUT marking handled otherwise.
                if let Some(assigns) = fixpoint_assignments {
                    let pivot_val = assigns.get(&pivot).copied();
                    let tester_val = assigns.get(&tester).copied();
                    let violated = if cid == pivot_cid {
                        // Transfer (either direction).
                        (pivot_val == Some(true) && tester_val == Some(false))
                            || (tester_val == Some(true) && pivot_val == Some(false))
                    } else {
                        // Exclusion.
                        pivot_val == Some(true) && tester_val == Some(true)
                    };
                    if !violated {
                        continue;
                    }
                }
                self.handled.insert((tester, pivot));
                if cid == pivot_cid {
                    // Transfer (both directions): is-C(x) ∧ x~y ⇒ is-C(y).
                    if let Some(clause) = self.entailed_clause_with_extra(
                        euf,
                        verifier,
                        pivot_arg,
                        arg,
                        TheoryLit::new(pivot, false),
                        TheoryLit::new(tester, true),
                    ) {
                        out.push(clause);
                        self.rule_transfer += 1;
                    }
                    if let Some(clause) = self.entailed_clause_with_extra(
                        euf,
                        verifier,
                        pivot_arg,
                        arg,
                        TheoryLit::new(tester, false),
                        TheoryLit::new(pivot, true),
                    ) {
                        out.push(clause);
                        self.rule_transfer += 1;
                    }
                } else {
                    // Exclusion: is-C(x) ∧ x~y ⇒ ¬is-D(y)  (C ≠ D).
                    if let Some(clause) = self.entailed_clause_with_extra(
                        euf,
                        verifier,
                        pivot_arg,
                        arg,
                        TheoryLit::new(pivot, false),
                        TheoryLit::new(tester, false),
                    ) {
                        out.push(clause);
                        self.rule_transfer += 1;
                    }
                }
            }
        }

        self.emitted_total += out.len() as u64;
        if self.emitted_total >= D1_MAX_LEMMAS_TOTAL {
            tracing::warn!(
                total = self.emitted_total,
                "dt-d1: total lemma budget exhausted; propagator going inert (fail-open)"
            );
        }
        out
    }

    /// Build the entailed clause `¬explain(a, w) ∨ lit` after independently
    /// re-deriving `a ~ w` from its own explanation on the fresh verifier.
    fn entailed_clause(
        &mut self,
        euf: &mut EufSolver<'_>,
        verifier: &mut EufSolver<'_>,
        a: TermId,
        w: TermId,
        lit: TheoryLit,
    ) -> Option<TheoryLemma> {
        self.entailed_clause_impl(euf, verifier, a, w, None, lit)
    }

    /// Build the entailed clause `extra_neg ∨ ¬explain(a, w) ∨ lit`.
    ///
    /// `extra_neg` is an additional clause literal (already in clause
    /// polarity, e.g. `¬is-C(x)` for the transfer/exclusion rules).
    fn entailed_clause_with_extra(
        &mut self,
        euf: &mut EufSolver<'_>,
        verifier: &mut EufSolver<'_>,
        a: TermId,
        w: TermId,
        extra_neg: TheoryLit,
        lit: TheoryLit,
    ) -> Option<TheoryLemma> {
        self.entailed_clause_impl(euf, verifier, a, w, Some(extra_neg), lit)
    }

    /// Shared clause builder. Returns `None` (dropped, fail-open) when the
    /// explanation is empty or fails the independent fresh-EUF re-derivation
    /// of `a ~ w`.
    fn entailed_clause_impl(
        &mut self,
        euf: &mut EufSolver<'_>,
        verifier: &mut EufSolver<'_>,
        a: TermId,
        w: TermId,
        extra_neg: Option<TheoryLit>,
        lit: TheoryLit,
    ) -> Option<TheoryLemma> {
        let mut reason = euf.explain(a, w);
        reason.sort_unstable_by_key(|l| (l.term.0, l.value));
        reason.dedup_by_key(|l| (l.term.0, l.value));
        if reason.is_empty() {
            // A non-syntactic merge the proof forest cannot justify: never
            // emit an unconditional clause from this pass.
            tracing::warn!("dt-d1: empty explanation for e-graph merge; propagation dropped");
            self.rederive_failures += 1;
            return None;
        }
        // Independent re-derivation: exactly the reason literals on a fresh
        // closure must re-derive a ~ w.
        verifier.push();
        for l in &reason {
            verifier.assert_literal(l.term, l.value);
        }
        let verdict = verifier.check();
        let rederived = match verdict {
            // A conflict from the reason set alone is an even stronger
            // certificate: the clause `¬reason ∨ lit` is then EUF-tautological.
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => true,
            _ => verifier.are_equal(a, w),
        };
        verifier.pop();
        if !rederived {
            tracing::warn!(
                lit_count = reason.len(),
                "dt-d1: explanation failed independent fresh-EUF re-derivation; dropped"
            );
            self.rederive_failures += 1;
            return None;
        }
        let mut clause: Vec<TheoryLit> = Vec::with_capacity(reason.len() + 2);
        if let Some(extra) = extra_neg {
            clause.push(extra);
        }
        for l in reason {
            clause.push(TheoryLit::new(l.term, !l.value));
        }
        // The propagated literal may coincide with a clause literal already
        // present; keep the clause duplicate-free with `lit` last (tests and
        // debuggability rely on the propagated literal's position).
        clause.retain(|c| !(c.term == lit.term && c.value == lit.value));
        clause.push(lit);
        Some(TheoryLemma::new(clause))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;

    /// tower = stack(top: enum, rest: tower) | empty, with an `enum` sort of
    /// nullary constructors A | B. Mirrors the blocksworld shape.
    struct Fixture {
        terms: TermStore,
        prop: DtLazyPropagator,
    }

    fn fixture() -> Fixture {
        let terms = TermStore::new();
        let mut prop = DtLazyPropagator::new();
        prop.register_datatype("tower", &["stack".to_string(), "empty".to_string()]);
        prop.register_datatype("enum", &["A".to_string(), "B".to_string()]);
        prop.register_ctor_selectors("stack", &["top".to_string(), "rest".to_string()]);
        Fixture { terms, prop }
    }

    fn tower_sort() -> Sort {
        Sort::Uninterpreted("tower".to_string())
    }
    fn enum_sort() -> Sort {
        Sort::Uninterpreted("enum".to_string())
    }

    fn verify_clause_is_dt_tautology(
        terms: &TermStore,
        prop_reg: &DtLazyPropagator,
        clause: &[TheoryLit],
    ) {
        // Independent oracle: assert the NEGATION of the clause (every literal
        // flipped) into a fresh DtSolver+EUF stack and require inconsistency.
        // Here we re-derive with EUF + the registered DT semantics manually:
        // the clause must have the shape ¬r₁ ∨ ... ∨ ¬rₖ ∨ lit where the rᵢ
        // are equality/tester atoms; asserting all rᵢ and ¬lit must produce a
        // datatype-inconsistent e-graph. We check via crate::DtSolver.
        let mut dt = crate::DtSolver::new(terms);
        dt.register_datatype("tower", &["stack".to_string(), "empty".to_string()]);
        dt.register_datatype("enum", &["A".to_string(), "B".to_string()]);
        dt.register_ctor_selectors("stack", &["top".to_string(), "rest".to_string()]);
        let _ = prop_reg; // registration mirrored above
        for l in clause {
            // negation of the clause: flip each literal
            dt.assert_literal(l.term, !l.value);
        }
        let mut euf = EufSolver::new(terms);
        for l in clause {
            euf.assert_literal(l.term, !l.value);
        }
        // Two DT checks: selector projection merges land in the first call,
        // and the disequality re-check that refutes them runs in the second.
        let dt_verdict1 = dt.check();
        let dt_verdict2 = dt.check();
        let euf_verdict = euf.check();
        assert!(
            matches!(dt_verdict1, TheoryResult::Unsat(_))
                || matches!(dt_verdict2, TheoryResult::Unsat(_))
                || matches!(euf_verdict, TheoryResult::Unsat(_)),
            "emitted clause is not refuted by the independent DT/EUF oracles: {clause:?}"
        );
    }

    /// Rule 1: a DERIVED merge (x = y, y = stack(a, r)) evaluates both testers
    /// on x with a two-literal explanation.
    #[test]
    fn tester_evaluation_through_derived_merge() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let a = terms.mk_var("a", enum_sort());
        let r = terms.mk_var("r", tower_sort());
        let x = terms.mk_var("x", tower_sort());
        let y = terms.mk_var("y", tower_sort());
        let stack_ar = terms.mk_app(Symbol::Named("stack".to_string()), [a, r], tower_sort());
        let is_stack_x = terms.mk_app(Symbol::Named("is-stack".to_string()), [x], Sort::Bool);
        let is_empty_x = terms.mk_app(Symbol::Named("is-empty".to_string()), [x], Sort::Bool);
        let eq1 = terms.mk_eq(x, y);
        let eq2 = terms.mk_eq(y, stack_ar);

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        let mut verifier = EufSolver::new(&terms).verify_only();

        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        // is-stack(x) := true and is-empty(x) := false.
        let mut saw_pos = false;
        let mut saw_neg = false;
        for lemma in &lemmas {
            verify_clause_is_dt_tautology(&terms, &prop, &lemma.clause);
            let last = lemma.clause.last().unwrap();
            if last.term == is_stack_x {
                assert!(last.value);
                saw_pos = true;
            }
            if last.term == is_empty_x {
                assert!(!last.value);
                saw_neg = true;
            }
            // Reasons must be exactly (negations of) the asserted equalities.
            for l in &lemma.clause[..lemma.clause.len() - 1] {
                assert!(
                    [eq1, eq2].contains(&l.term),
                    "unexpected reason literal {l:?}"
                );
                assert!(!l.value);
            }
        }
        assert!(saw_pos, "positive tester propagation missing: {lemmas:?}");
        assert!(saw_neg, "negative tester propagation missing: {lemmas:?}");
    }

    /// Rule 1 skip cases: syntactic (same-term) tester and unmerged classes
    /// produce no lemmas.
    #[test]
    fn tester_evaluation_skips_syntactic_and_unmerged() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let a = terms.mk_var("a", enum_sort());
        let r = terms.mk_var("r", tower_sort());
        let x = terms.mk_var("x", tower_sort());
        let stack_ar = terms.mk_app(Symbol::Named("stack".to_string()), [a, r], tower_sort());
        // Syntactic: tester directly on the constructor application.
        let _is_stack_app = terms.mk_app(
            Symbol::Named("is-stack".to_string()),
            [stack_ar],
            Sort::Bool,
        );
        // Unmerged: tester on x, but x never merged with stack_ar.
        let _is_stack_x = terms.mk_app(Symbol::Named("is-stack".to_string()), [x], Sort::Bool);

        let mut euf = EufSolver::new(&terms);
        let _ = euf.check();
        let mut verifier = EufSolver::new(&terms).verify_only();
        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        assert!(lemmas.is_empty(), "no propagation expected: {lemmas:?}");
    }

    /// Rule 3: selector evaluation `top(x) = a` from the derived commitment
    /// `x ~ stack(a, r)`, emitted only when the equality atom exists.
    #[test]
    fn selector_evaluation_through_derived_merge() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let a = terms.mk_var("a", enum_sort());
        let r = terms.mk_var("r", tower_sort());
        let x = terms.mk_var("x", tower_sort());
        let stack_ar = terms.mk_app(Symbol::Named("stack".to_string()), [a, r], tower_sort());
        let top_x = terms.mk_app(Symbol::Named("top".to_string()), [x], enum_sort());
        let eq = terms.mk_eq(x, stack_ar);
        let eq_atom = terms.mk_eq(top_x, a); // the propagated equality atom

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        let mut verifier = EufSolver::new(&terms).verify_only();
        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        let found = lemmas.iter().find(|l| {
            l.clause
                .last()
                .is_some_and(|last| last.term == eq_atom && last.value)
        });
        let lemma = found.expect("selector propagation lemma missing");
        // Clause: ¬(x = stack(a,r)) ∨ (top(x) = a)
        assert_eq!(lemma.clause.len(), 2);
        assert_eq!(lemma.clause[0].term, eq);
        assert!(!lemma.clause[0].value);
    }

    /// Rule 3 total-selector semantics: a WRONG-constructor selector
    /// (`top` on an `empty`-committed class) is never propagated.
    #[test]
    fn wrong_constructor_selector_is_unconstrained() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let x = terms.mk_var("x", tower_sort());
        let empty = terms.mk_var("empty", tower_sort());
        let a = terms.mk_var("a", enum_sort());
        let top_x = terms.mk_app(Symbol::Named("top".to_string()), [x], enum_sort());
        let eq = terms.mk_eq(x, empty);
        let _eq_atom = terms.mk_eq(top_x, a);

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        let _ = euf.check();
        let mut verifier = EufSolver::new(&terms).verify_only();
        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        assert!(
            !lemmas
                .iter()
                .any(|l| { l.clause.last().is_some_and(|last| last.term == _eq_atom) }),
            "wrong-constructor selector must stay unconstrained: {lemmas:?}"
        );
        // The tester evaluation on the committed class may still fire — but
        // only if tester atoms exist, which they don't here.
        assert!(lemmas.is_empty(), "{lemmas:?}");
    }

    /// Rule 2: tester transfer + exclusion across a merged, uncommitted class.
    #[test]
    fn tester_transfer_and_exclusion_across_merge() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let x = terms.mk_var("x", tower_sort());
        let y = terms.mk_var("y", tower_sort());
        let is_stack_x = terms.mk_app(Symbol::Named("is-stack".to_string()), [x], Sort::Bool);
        let is_stack_y = terms.mk_app(Symbol::Named("is-stack".to_string()), [y], Sort::Bool);
        let is_empty_y = terms.mk_app(Symbol::Named("is-empty".to_string()), [y], Sort::Bool);
        let eq = terms.mk_eq(x, y);

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        let mut verifier = EufSolver::new(&terms).verify_only();
        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);

        // Transfer: is-stack(x) → is-stack(y) (and converse); exclusion:
        // is-stack(x) → ¬is-empty(y). The pivot is the smallest tester term.
        let has = |neg: TermId, pos: TermId, pos_val: bool| {
            lemmas.iter().any(|l| {
                l.clause.iter().any(|c| c.term == neg && !c.value)
                    && l.clause.iter().any(|c| c.term == eq && !c.value)
                    && l.clause.iter().any(|c| c.term == pos && c.value == pos_val)
            })
        };
        assert!(
            has(is_stack_x, is_stack_y, true),
            "transfer x→y missing: {lemmas:?}"
        );
        assert!(
            has(is_stack_y, is_stack_x, true),
            "transfer y→x missing: {lemmas:?}"
        );
        assert!(
            has(is_stack_x, is_empty_y, false),
            "exclusion is-stack(x) → ¬is-empty(y) missing: {lemmas:?}"
        );
        // Oracle-check the transfer clauses (their negation is refutable by
        // pure EUF tester congruence). The exclusion clause's DT step
        // (distinct constructors are mutually exclusive) is definitional and
        // covered by the structural assertion above.
        for lemma in &lemmas {
            if lemma.clause.last().is_some_and(|c| c.value) {
                verify_clause_is_dt_tautology(&terms, &prop, &lemma.clause);
            }
        }
    }

    /// Explanation validity under conflict: the propagated literal's clause,
    /// with reasons TRUE and the propagated literal FALSE, is refuted by an
    /// independent solver — i.e. the learned clause the SAT core would derive
    /// from this propagation is sound.
    #[test]
    fn forced_conflict_learned_clause_is_sound() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let a = terms.mk_var("a", enum_sort());
        let r = terms.mk_var("r", tower_sort());
        let x = terms.mk_var("x", tower_sort());
        let y = terms.mk_var("y", tower_sort());
        let stack_ar = terms.mk_app(Symbol::Named("stack".to_string()), [a, r], tower_sort());
        let is_empty_x = terms.mk_app(Symbol::Named("is-empty".to_string()), [x], Sort::Bool);
        let eq1 = terms.mk_eq(x, y);
        let eq2 = terms.mk_eq(y, stack_ar);

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        let _ = euf.check();
        let mut verifier = EufSolver::new(&terms).verify_only();
        let lemmas = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        let lemma = lemmas
            .iter()
            .find(|l| {
                l.clause
                    .last()
                    .is_some_and(|c| c.term == is_empty_x && !c.value)
            })
            .expect("negative tester propagation expected");

        // Force the conflict: assert every reason true and the propagated
        // literal's opposite (is-empty(x) = true). The independent DtSolver
        // must refute this assignment — the SAT core's learned clause
        // (exactly `lemma.clause`) is therefore a sound theory lemma.
        let mut dt = crate::DtSolver::new(&terms);
        dt.register_datatype("tower", &["stack".to_string(), "empty".to_string()]);
        dt.register_datatype("enum", &["A".to_string(), "B".to_string()]);
        for l in &lemma.clause[..lemma.clause.len() - 1] {
            dt.assert_literal(l.term, !l.value); // reasons at asserted polarity
        }
        dt.assert_literal(is_empty_x, true);
        assert!(
            matches!(dt.check(), TheoryResult::Unsat(_)),
            "independent DT oracle failed to refute reasons ∧ ¬propagated"
        );
    }

    /// Dedup: a second run over the same e-graph emits nothing new.
    #[test]
    fn second_run_is_deduplicated() {
        let Fixture {
            mut terms,
            mut prop,
        } = fixture();
        let a = terms.mk_var("a", enum_sort());
        let r = terms.mk_var("r", tower_sort());
        let x = terms.mk_var("x", tower_sort());
        let stack_ar = terms.mk_app(Symbol::Named("stack".to_string()), [a, r], tower_sort());
        let _is_stack_x = terms.mk_app(Symbol::Named("is-stack".to_string()), [x], Sort::Bool);
        let eq = terms.mk_eq(x, stack_ar);

        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        let _ = euf.check();
        let mut verifier = EufSolver::new(&terms).verify_only();
        let first = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        assert!(!first.is_empty());
        let second = prop.propagate_lemmas(&terms, &mut euf, &mut verifier, None);
        assert!(second.is_empty(), "dedup failed: {second:?}");
    }
}
