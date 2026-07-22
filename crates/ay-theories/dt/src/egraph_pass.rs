// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D0: read-only datatype rule pass over the EUF e-graph (final check).
//!
//! Stage D0 of the development design notes: a
//! final-check pass over the *existing* EUF congruence closure that applies the
//! two conflict-only Barrett–Shikanian–Tinelli datatype rules the eager DtAx
//! axiom encoding cannot express over **derived** (non-syntactic) equalities:
//!
//! - **Clash**: two applications of *distinct* constructors in one e-class
//!   (`C(u⃗) ~ D(v⃗)`, `C != D`) contradict constructor distinctness.
//! - **Ground structural disequality** (rule 1b, stage D2): two *ground*
//!   constructor terms (every leaf a constructor) in one e-class that are
//!   structurally different denote distinct datatype values (repeated
//!   injectivity + distinctness), so their merge is a conflict. This is the
//!   bounded, term-creation-free reduct of the injectivity rule: instead of
//!   propagating argument equalities (whose atoms may not exist), it descends
//!   the two ground terms directly and refutes the merge in one clause. The
//!   lazy (no-unroll) DT lane depends on it: there the eager injectivity
//!   axiom family is absent, and e.g. BMC goal equalities merge two ground
//!   towers that differ only below the top constructor.
//! - **Cycle** (acyclicity / well-foundedness): an e-class reachable from
//!   itself through constructor-*argument* edges would have to contain a value
//!   that is a proper structural subvalue of itself, which no inductive
//!   datatype value is. The eager lane's occurs-check only sees *asserted*
//!   equalities; cycles closed through EUF merges of tester-instantiated
//!   constructor shapes (axiom (C): `is-C(t) => t = C(sel_1(t), ...)`) were
//!   invisible and produced wrong-SAT (the `min-pred` shape: `x5 != zero`,
//!   `x5 = pred(pred(x5))` forces `x5 = succ(succ(x5))` in the e-graph).
//!
//! ## Soundness
//!
//! The pass is read-only over the e-graph and CONFLICT-ONLY: it never merges,
//! never propagates, and never influences a Sat verdict other than by blocking
//! it with an entailed datatype tautology. Each detected conflict is:
//!
//! 1. **Explained** through the e-graph proof forest
//!    ([`ay_euf::EufSolver::explain`]) into a set of asserted theory literals
//!    whose conjunction entails the clash/cycle;
//! 2. **Independently re-derived** on a *fresh* [`ay_euf::EufSolver`] seeded
//!    with exactly those literals (congruence closure from scratch, then this
//!    pass's own detection over the fresh closure). A conflict that cannot be
//!    re-derived from its own explanation is DROPPED (fail-open for that
//!    conflict — the always-on model gates remain the backstop), so an
//!    under-explained conflict can never become a learned clause (the classic
//!    lazy-solver wrong-UNSAT hazard);
//! 3. Emitted as a [`TheoryLemma`] clause (the negation of the explanation) via
//!    `TheoryResult::NeedLemmas` — the same permanent-clause conduit the array
//!    ROW2 batching uses (#6546). The clause is a datatype-theory tautology
//!    (true in every model), so adding it can only prune models that violate
//!    datatype semantics; it can never manufacture a false-UNSAT.
//!
//! The `NeedLemmas` channel is used deliberately instead of
//! `TheoryResult::Unsat`: the fail-closed conflict-verification gate
//! (`verify_conflict_semantic`, #8123) re-derives `Unsat` conflicts with a
//! fresh *pure-EUF* solver, which cannot see datatype distinctness or
//! well-foundedness and would reject every genuine DT conflict, degrading the
//! solve to Unknown. Lemma clauses carry their own justification (step 2) and
//! flow through the SAT core as ordinary permanent clauses.
//!
//! ## Scope
//!
//! Selector projection and constructor injectivity are NOT re-implemented
//! here: in the eager DtAx lane those rules are already pre-instantiated as
//! axiom families (A)/(F) over the unrolled selector frontier, and the merges
//! they force are exactly what this pass reads back out of the e-graph. This
//! is the smallest sound slice that closes the derived-cycle/clash gap; the
//! full lazy propagation lane is design stage D1.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::{TheoryLemma, TheoryLit, TheoryResult, TheorySolver};
use ay_euf::EufSolver;

/// Outcome of one [`DtEgraphPass::check`] invocation.
#[derive(Debug)]
pub enum DtPassOutcome {
    /// No datatype clash/cycle in the current e-graph: the candidate model is
    /// consistent with the rules this pass implements.
    Ok,
    /// A verified datatype conflict, packaged as tautology lemma clauses to
    /// inject via `TheoryResult::NeedLemmas`.
    Lemmas(Vec<TheoryLemma>),
    /// A datatype clash/cycle EXISTS in the e-graph, but no new clause can be
    /// emitted (its clause was already emitted this solve, or its explanation
    /// failed independent re-derivation). The candidate model MUST NOT be
    /// accepted; the caller returns a sound `Unknown` (fail-closed).
    Inconclusive,
}

/// Read-only datatype clash/acyclicity pass over an EUF e-graph.
///
/// Construct once per solve (it memoizes an append-only scan of the term
/// store), register the problem's datatypes, then call
/// [`check`](Self::check) from the theory's final check.
#[derive(Debug, Default)]
pub struct DtEgraphPass {
    /// Constructor name -> datatype name.
    ctor_to_dt: HashMap<String, String>,
    /// Term-store scan frontier (the store is append-only).
    scanned_len: usize,
    /// Constructor application terms discovered so far. Nullary constructors
    /// are `TermData::Var` terms whose name is a registered constructor.
    ctor_apps: Vec<TermId>,
    /// Clauses already emitted this solve (dedup; clauses are permanent).
    emitted: HashSet<Vec<TheoryLit>>,
    /// Memo: term -> is a GROUND constructor term (every leaf a registered
    /// constructor). Sound to cache forever: term structure is immutable.
    ground_memo: HashMap<TermId, bool>,
}

impl DtEgraphPass {
    /// Create an empty pass (no datatypes registered; `check` is a no-op).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a datatype and its constructor names (internal, possibly
    /// instance-mangled names — the same names the term store uses).
    pub fn register_datatype(&mut self, dt_name: &str, constructors: &[String]) {
        for ctor in constructors {
            self.ctor_to_dt.insert(ctor.clone(), dt_name.to_string());
        }
    }

    /// True when no datatypes are registered (pass is inert).
    #[must_use]
    pub fn is_inert(&self) -> bool {
        self.ctor_to_dt.is_empty()
    }

    /// The constructor name of a scanned constructor application/constant.
    fn ctor_name_of<'t>(&self, terms: &'t TermStore, term: TermId) -> Option<&'t str> {
        match terms.get(term) {
            TermData::App(Symbol::Named(name), _) if self.ctor_to_dt.contains_key(name) => {
                Some(name.as_str())
            }
            TermData::Var(name, _) if self.ctor_to_dt.contains_key(name) => Some(name.as_str()),
            _ => None,
        }
    }

    /// True when `term` is a GROUND constructor term: a registered nullary
    /// constructor constant, or a registered constructor application whose
    /// arguments are all ground constructor terms. Memoized (term structure
    /// is immutable). Iterative worklist to stay stack-safe on deep chains.
    fn is_ground_ctor_term(&mut self, terms: &TermStore, term: TermId) -> bool {
        if let Some(&g) = self.ground_memo.get(&term) {
            return g;
        }
        // Post-order worklist: (term, children_pushed).
        let mut stack: Vec<(TermId, bool)> = vec![(term, false)];
        while let Some((t, expanded)) = stack.pop() {
            if self.ground_memo.contains_key(&t) {
                continue;
            }
            match terms.get(t) {
                TermData::Var(name, _) => {
                    let g = self.ctor_to_dt.contains_key(name);
                    self.ground_memo.insert(t, g);
                }
                TermData::App(Symbol::Named(name), args) => {
                    if !self.ctor_to_dt.contains_key(name) {
                        self.ground_memo.insert(t, false);
                        continue;
                    }
                    if expanded {
                        let g = args
                            .iter()
                            .all(|a| self.ground_memo.get(a).copied().unwrap_or(false));
                        self.ground_memo.insert(t, g);
                    } else {
                        stack.push((t, true));
                        for &a in args {
                            stack.push((a, false));
                        }
                    }
                }
                _ => {
                    self.ground_memo.insert(t, false);
                }
            }
        }
        self.ground_memo.get(&term).copied().unwrap_or(false)
    }

    /// Structural equality of two GROUND constructor terms (callers must have
    /// checked [`Self::is_ground_ctor_term`] for both). Iterative pairwise
    /// descent; no memo needed (hash-consing makes equal subtrees compare by
    /// id at the first level in practice, this is the correctness backstop).
    fn ground_struct_eq(terms: &TermStore, a: TermId, b: TermId) -> bool {
        let mut stack: Vec<(TermId, TermId)> = vec![(a, b)];
        while let Some((x, y)) = stack.pop() {
            if x == y {
                continue;
            }
            match (terms.get(x), terms.get(y)) {
                (TermData::Var(nx, _), TermData::Var(ny, _)) => {
                    if nx != ny {
                        return false;
                    }
                }
                (TermData::App(Symbol::Named(nx), ax), TermData::App(Symbol::Named(ny), ay)) => {
                    if nx != ny || ax.len() != ay.len() {
                        return false;
                    }
                    for (&px, &py) in ax.iter().zip(ay.iter()) {
                        stack.push((px, py));
                    }
                }
                // Var vs App: a nullary constructor vs an application — the
                // constructor names necessarily differ (arities differ).
                _ => return false,
            }
        }
        true
    }

    /// Extend the memoized constructor-application list over newly created
    /// terms (the term store is append-only, so old entries stay valid).
    fn scan_new_terms(&mut self, terms: &TermStore) {
        let len = terms.len();
        for raw in self.scanned_len..len {
            let tid = TermId(raw as u32);
            if self.ctor_name_of(terms, tid).is_some() {
                self.ctor_apps.push(tid);
            }
        }
        self.scanned_len = len;
    }

    /// Run the clash + cycle rules over `euf`'s current e-graph.
    ///
    /// Read-only on the e-graph (aside from `explain`'s internal memo);
    /// conflict-only (see module docs for the soundness argument).
    pub fn check(&mut self, terms: &TermStore, euf: &mut EufSolver<'_>) -> DtPassOutcome {
        if self.is_inert() {
            return DtPassOutcome::Ok;
        }
        self.scan_new_terms(terms);
        if self.ctor_apps.is_empty() {
            return DtPassOutcome::Ok;
        }

        // Group constructor applications by e-class root.
        let mut class_apps: HashMap<u32, Vec<TermId>> = HashMap::default();
        for &t in &self.ctor_apps {
            class_apps
                .entry(euf.enode_find_const(t.0))
                .or_default()
                .push(t);
        }

        let mut found_unemittable = false;

        // ---- Rule 1: constructor clash --------------------------------------
        // Deterministic order: iterate classes by root id (#8529).
        let mut roots: Vec<u32> = class_apps.keys().copied().collect();
        roots.sort_unstable();
        for &root in &roots {
            let apps = &class_apps[&root];
            if apps.len() < 2 {
                continue;
            }
            let first = apps[0];
            let first_name = self.ctor_name_of(terms, first);
            for &other in &apps[1..] {
                if self.ctor_name_of(terms, other) == first_name {
                    continue;
                }
                let lits = euf.explain(first, other);
                match self.package_conflict(terms, lits, "clash") {
                    ConflictPackage::Lemma(l) => return DtPassOutcome::Lemmas(vec![l]),
                    ConflictPackage::Unemittable => {
                        found_unemittable = true;
                    }
                }
            }
        }

        // ---- Rule 1b: ground structural disequality --------------------------
        // Two structurally-different GROUND constructor terms in one class
        // denote distinct datatype values (injectivity + distinctness,
        // applied recursively), so the merge is a conflict. Linear per class:
        // in a rule-consistent class all ground members are structurally
        // equal, so comparing everything against the first ground member
        // finds any violation.
        for &root in &roots {
            let apps = &class_apps[&root];
            if apps.len() < 2 {
                continue;
            }
            let mut first_ground: Option<TermId> = None;
            for &t in apps {
                if !self.is_ground_ctor_term(terms, t) {
                    continue;
                }
                let Some(g0) = first_ground else {
                    first_ground = Some(t);
                    continue;
                };
                if !Self::ground_struct_eq(terms, g0, t) {
                    let lits = euf.explain(g0, t);
                    match self.package_conflict(terms, lits, "ground-diseq") {
                        ConflictPackage::Lemma(l) => return DtPassOutcome::Lemmas(vec![l]),
                        ConflictPackage::Unemittable => {
                            found_unemittable = true;
                        }
                    }
                }
            }
        }

        // ---- Rule 2: acyclicity over constructor-argument edges -------------
        // Edge R -> root(arg) for every argument `arg` of every constructor
        // application in class R, restricted to targets that themselves
        // contain a constructor application (only those can extend a cycle).
        // An edge means: every value of class R properly contains the value
        // of the target class, so any cycle is a well-foundedness violation.
        let mut adj: HashMap<u32, Vec<(TermId, TermId, u32)>> = HashMap::default();
        for &root in &roots {
            for &app in &class_apps[&root] {
                if let TermData::App(_, args) = terms.get(app) {
                    for &arg in args {
                        let target = euf.enode_find_const(arg.0);
                        if class_apps.contains_key(&target) {
                            adj.entry(root).or_default().push((app, arg, target));
                        }
                    }
                }
            }
        }
        // Deterministic DFS order.
        for edges in adj.values_mut() {
            edges.sort_unstable_by_key(|&(app, arg, _)| (app.0, arg.0));
        }

        // Iterative tri-color DFS. `frames` holds (root, next_edge_index);
        // `path_edges[i]` is the (app, arg) edge taken from frames[i] to
        // frames[i+1] (invariant: path_edges.len() == frames.len() - 1).
        let mut color: HashMap<u32, u8> = HashMap::default(); // 1 = gray, 2 = black
        for &start in &roots {
            if color.contains_key(&start) {
                continue;
            }
            let mut frames: Vec<(u32, usize)> = vec![(start, 0)];
            let mut path_edges: Vec<(TermId, TermId)> = Vec::new();
            color.insert(start, 1);
            while let Some(&(root, edge_idx)) = frames.last() {
                let edge = adj.get(&root).and_then(|es| es.get(edge_idx).copied());
                let Some((app, arg, target)) = edge else {
                    // Class exhausted: blacken and pop.
                    color.insert(root, 2);
                    frames.pop();
                    if !frames.is_empty() {
                        path_edges.pop();
                    }
                    continue;
                };
                frames.last_mut().expect("nonempty: just read").1 += 1;
                match color.get(&target) {
                    Some(1) => {
                        // Back edge: cycle through constructor-argument edges.
                        let pos = frames
                            .iter()
                            .position(|&(r, _)| r == target)
                            .expect("gray target is on the current DFS path");
                        let mut cycle: Vec<(TermId, TermId)> = path_edges[pos..].to_vec();
                        cycle.push((app, arg));
                        // Premises: consecutive edges are linked by the arg of
                        // one being e-equal to the app of the next (wrapping).
                        let mut lits: Vec<TheoryLit> = Vec::new();
                        for i in 0..cycle.len() {
                            let (_, arg_i) = cycle[i];
                            let (app_next, _) = cycle[(i + 1) % cycle.len()];
                            if arg_i != app_next {
                                lits.extend(euf.explain(arg_i, app_next));
                            }
                        }
                        match self.package_conflict(terms, lits, "cycle") {
                            ConflictPackage::Lemma(l) => return DtPassOutcome::Lemmas(vec![l]),
                            ConflictPackage::Unemittable => {
                                found_unemittable = true;
                                // Keep searching other cycles from this state:
                                // treat the back edge as explored.
                            }
                        }
                    }
                    Some(_) => {} // black: fully explored, no cycle through it
                    None => {
                        color.insert(target, 1);
                        path_edges.push((app, arg));
                        frames.push((target, 0));
                    }
                }
            }
        }

        if found_unemittable {
            DtPassOutcome::Inconclusive
        } else {
            DtPassOutcome::Ok
        }
    }

    /// Validate + dedup a detected conflict and package it as a lemma clause.
    fn package_conflict(
        &mut self,
        terms: &TermStore,
        mut lits: Vec<TheoryLit>,
        rule: &'static str,
    ) -> ConflictPackage {
        lits.sort_unstable_by_key(|l| (l.term.0, l.value));
        lits.dedup_by_key(|l| (l.term.0, l.value));
        // An empty explanation for a non-syntactic fact means the proof forest
        // could not justify the merges — never emit an empty (unconditional)
        // clause from this pass.
        if lits.is_empty() {
            tracing::warn!(rule, "dt-egraph-pass: empty explanation; conflict dropped");
            return ConflictPackage::Unemittable;
        }
        if self.emitted.contains(&lits) {
            // The SAT layer already holds this clause yet re-produced an
            // assignment violating it (e.g. a literal it could not map).
            // Fail closed rather than looping.
            return ConflictPackage::Unemittable;
        }
        if !self.rederive_on_fresh_euf(terms, &lits) {
            tracing::warn!(
                rule,
                lit_count = lits.len(),
                "dt-egraph-pass: conflict failed independent fresh-EUF re-derivation; dropped"
            );
            return ConflictPackage::Unemittable;
        }
        self.emitted.insert(lits.clone());
        tracing::debug!(
            rule,
            lit_count = lits.len(),
            "dt-egraph-pass: emitting tautology lemma"
        );
        // Clause = negation of the jointly-inconsistent literal set.
        let clause: Vec<TheoryLit> = lits
            .into_iter()
            .map(|l| TheoryLit::new(l.term, !l.value))
            .collect();
        ConflictPackage::Lemma(TheoryLemma::new(clause))
    }

    /// Independently re-derive the conflict: assert exactly `lits` into a
    /// fresh EUF solver, run congruence closure from scratch, and re-run this
    /// pass's clash/ground-diseq/cycle detection over the fresh closure.
    /// Returns `true` only when the fresh derivation confirms the literal set
    /// entails a datatype clash, ground structural disequality, or cycle
    /// (i.e. the emitted clause is a DT tautology).
    fn rederive_on_fresh_euf(&mut self, terms: &TermStore, lits: &[TheoryLit]) -> bool {
        let mut fresh = EufSolver::new(terms).verify_only();
        for lit in lits {
            fresh.assert_literal(lit.term, lit.value);
        }
        // A fresh-EUF conflict on the literal set alone is an even stronger
        // certificate (the set is EUF-inconsistent), which also validates the
        // clause as a tautology.
        if matches!(
            fresh.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            return true;
        }

        // Group the known constructor applications by the FRESH closure's
        // classes and re-run detection (no allocation reuse needed here —
        // conflicts are rare).
        let mut class_apps: HashMap<u32, Vec<TermId>> = HashMap::default();
        for &t in &self.ctor_apps {
            class_apps
                .entry(fresh.enode_find_const(t.0))
                .or_default()
                .push(t);
        }
        // Clash.
        for apps in class_apps.values() {
            if apps.len() < 2 {
                continue;
            }
            let first_name = self.ctor_name_of(terms, apps[0]);
            if apps[1..]
                .iter()
                .any(|&o| self.ctor_name_of(terms, o) != first_name)
            {
                return true;
            }
        }
        // Ground structural disequality (rule 1b).
        for apps in class_apps.values() {
            if apps.len() < 2 {
                continue;
            }
            let mut first_ground: Option<TermId> = None;
            for &t in apps {
                if !self.is_ground_ctor_term(terms, t) {
                    continue;
                }
                let Some(g0) = first_ground else {
                    first_ground = Some(t);
                    continue;
                };
                if !Self::ground_struct_eq(terms, g0, t) {
                    return true;
                }
            }
        }
        // Cycle (plain tri-color DFS; no explanations needed).
        let mut adj: HashMap<u32, Vec<u32>> = HashMap::default();
        for (&root, apps) in &class_apps {
            for &app in apps {
                if let TermData::App(_, args) = terms.get(app) {
                    for &arg in args {
                        let target = fresh.enode_find_const(arg.0);
                        if class_apps.contains_key(&target) {
                            adj.entry(root).or_default().push(target);
                        }
                    }
                }
            }
        }
        let mut color: HashMap<u32, u8> = HashMap::default();
        for &start in class_apps.keys() {
            if color.contains_key(&start) {
                continue;
            }
            let mut frames: Vec<(u32, usize)> = vec![(start, 0)];
            color.insert(start, 1);
            while let Some(&(root, edge_idx)) = frames.last() {
                let next = adj.get(&root).and_then(|es| es.get(edge_idx).copied());
                let Some(target) = next else {
                    color.insert(root, 2);
                    frames.pop();
                    continue;
                };
                frames.last_mut().expect("nonempty: just read").1 += 1;
                match color.get(&target) {
                    Some(1) => return true, // back edge: cycle re-derived
                    Some(_) => {}
                    None => {
                        color.insert(target, 1);
                        frames.push((target, 0));
                    }
                }
            }
        }
        false
    }
}

enum ConflictPackage {
    Lemma(TheoryLemma),
    Unemittable,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;

    /// nat = succ(pred: nat) | zero, plus constants and the selector chain
    /// used by the tests. Returns (store, pass, x, px, ppx, zero, succ_px,
    /// succ_ppx).
    #[allow(clippy::type_complexity)]
    fn nat_setup() -> (
        TermStore,
        DtEgraphPass,
        TermId,
        TermId,
        TermId,
        TermId,
        TermId,
        TermId,
    ) {
        let mut terms = TermStore::new();
        let nat = Sort::Uninterpreted("nat".to_string());
        let x = terms.mk_var("x", nat.clone());
        let px = terms.mk_app(Symbol::Named("pred".to_string()), [x], nat.clone());
        let ppx = terms.mk_app(Symbol::Named("pred".to_string()), [px], nat.clone());
        let zero = terms.mk_var("zero", nat.clone());
        let succ_px = terms.mk_app(Symbol::Named("succ".to_string()), [px], nat.clone());
        let succ_ppx = terms.mk_app(Symbol::Named("succ".to_string()), [ppx], nat.clone());
        let mut pass = DtEgraphPass::new();
        pass.register_datatype("nat", &["succ".to_string(), "zero".to_string()]);
        (terms, pass, x, px, ppx, zero, succ_px, succ_ppx)
    }

    /// The min-pred shape as pure e-graph input: `x = succ(pred x)`,
    /// `pred x = succ(pred (pred x))`, `x = pred(pred x)` — a derived
    /// two-class constructor-argument cycle that plain congruence accepts.
    #[test]
    fn cycle_through_derived_merges_is_detected_and_explained() {
        let (mut terms, mut pass, x, px, ppx, _zero, succ_px, succ_ppx) = nat_setup();
        let eq1 = terms.mk_eq(x, succ_px);
        let eq2 = terms.mk_eq(px, succ_ppx);
        let eq3 = terms.mk_eq(x, ppx);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        euf.assert_literal(eq3, true);
        assert!(
            matches!(euf.check(), TheoryResult::Sat),
            "plain EUF congruence must accept the cycle (that is the gap)"
        );
        match pass.check(&terms, &mut euf) {
            DtPassOutcome::Lemmas(lemmas) => {
                assert_eq!(lemmas.len(), 1);
                let clause = &lemmas[0].clause;
                assert!(!clause.is_empty(), "cycle lemma must be conditional");
                // The clause is the negation of asserted equalities only.
                for lit in clause {
                    assert!(
                        !lit.value,
                        "cycle lemma literals must negate asserted-true equalities"
                    );
                    assert!(
                        [eq1, eq2, eq3].contains(&lit.term),
                        "cycle explanation must consist of the asserted equalities"
                    );
                }
            }
            other => panic!("expected cycle lemma, got {other:?}"),
        }
    }

    /// Constructor clash through a derived merge: `x = succ(pred x)` and
    /// `x = zero` put a `succ` application and the `zero` constant in one
    /// e-class.
    #[test]
    fn clash_through_derived_merge_is_detected() {
        let (mut terms, mut pass, x, _px, _ppx, zero, succ_px, _succ_ppx) = nat_setup();
        let eq1 = terms.mk_eq(x, succ_px);
        let eq2 = terms.mk_eq(x, zero);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        match pass.check(&terms, &mut euf) {
            DtPassOutcome::Lemmas(lemmas) => {
                let clause = &lemmas[0].clause;
                assert!(!clause.is_empty());
                for lit in clause {
                    assert!([eq1, eq2].contains(&lit.term));
                    assert!(!lit.value);
                }
            }
            other => panic!("expected clash lemma, got {other:?}"),
        }
    }

    /// A standard (acyclic) selector-chain model must pass: `x = succ(pred x)`,
    /// `pred x = zero` — no clash, no cycle.
    #[test]
    fn acyclic_constructor_chain_is_accepted() {
        let (mut terms, mut pass, x, px, _ppx, zero, succ_px, _succ_ppx) = nat_setup();
        let eq1 = terms.mk_eq(x, succ_px);
        let eq2 = terms.mk_eq(px, zero);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        assert!(
            matches!(pass.check(&terms, &mut euf), DtPassOutcome::Ok),
            "acyclic chain must not be flagged"
        );
    }

    /// Rule 1b: two structurally different GROUND constructor terms merged
    /// into one class through a variable chain is a conflict, explained by
    /// the asserted equalities; structurally EQUAL ground terms are not.
    #[test]
    fn ground_structural_disequality_is_detected() {
        let mut terms = TermStore::new();
        let nat = Sort::Uninterpreted("nat".to_string());
        let zero = terms.mk_var("zero", nat.clone());
        let s_zero = terms.mk_app(Symbol::Named("succ".to_string()), [zero], nat.clone());
        let ss_zero = terms.mk_app(Symbol::Named("succ".to_string()), [s_zero], nat.clone());
        let x = terms.mk_var("x", nat.clone());
        let y = terms.mk_var("y", nat.clone());
        let mut pass = DtEgraphPass::new();
        pass.register_datatype("nat", &["succ".to_string(), "zero".to_string()]);

        // x = succ(zero), y = succ(succ(zero)), x = y: same top constructor
        // (no clash), but the ground values differ at depth 1.
        let eq1 = terms.mk_eq(x, s_zero);
        let eq2 = terms.mk_eq(y, ss_zero);
        let eq3 = terms.mk_eq(x, y);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        euf.assert_literal(eq3, true);
        assert!(
            matches!(euf.check(), TheoryResult::Sat),
            "plain EUF congruence must accept the merge (that is the gap)"
        );
        match pass.check(&terms, &mut euf) {
            DtPassOutcome::Lemmas(lemmas) => {
                let clause = &lemmas[0].clause;
                assert!(!clause.is_empty());
                for lit in clause {
                    assert!([eq1, eq2, eq3].contains(&lit.term));
                    assert!(!lit.value);
                }
            }
            other => panic!("expected ground-diseq lemma, got {other:?}"),
        }

        // Control: merging x with a structurally EQUAL ground term (a second
        // path to succ(zero)) must NOT conflict.
        let mut terms2 = TermStore::new();
        let zero2 = terms2.mk_var("zero", nat.clone());
        let s_zero2 = terms2.mk_app(Symbol::Named("succ".to_string()), [zero2], nat.clone());
        let w = terms2.mk_var("w", nat.clone());
        let eq_a = terms2.mk_eq(w, s_zero2);
        let mut pass2 = DtEgraphPass::new();
        pass2.register_datatype("nat", &["succ".to_string(), "zero".to_string()]);
        let mut euf2 = EufSolver::new(&terms2);
        euf2.assert_literal(eq_a, true);
        let _ = euf2.check();
        assert!(
            matches!(pass2.check(&terms2, &mut euf2), DtPassOutcome::Ok),
            "equal ground terms must not be flagged"
        );
    }

    /// Rule 1b stays silent for NON-ground same-constructor merges (the
    /// injectivity consequences there are the eager lane's / D1's job).
    #[test]
    fn non_ground_same_ctor_merge_is_not_flagged() {
        let (mut terms, mut pass, x, px, _ppx, _zero, succ_px, _succ_ppx) = nat_setup();
        // succ(pred x) merged with succ(v): non-ground arguments — no rule
        // 1b conflict even though the args are not known equal.
        let v = terms.mk_var("v", Sort::Uninterpreted("nat".to_string()));
        let succ_v = terms.mk_app(
            Symbol::Named("succ".to_string()),
            [v],
            Sort::Uninterpreted("nat".to_string()),
        );
        let eq = terms.mk_eq(succ_px, succ_v);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        let _ = euf.check();
        let _ = (x, px);
        assert!(
            matches!(pass.check(&terms, &mut euf), DtPassOutcome::Ok),
            "non-ground same-constructor merge must not be flagged"
        );
    }

    /// Re-emitting the same conflict is refused (fail-closed Inconclusive
    /// instead of an emission loop).
    #[test]
    fn repeated_conflict_is_inconclusive_not_looping() {
        let (mut terms, mut pass, x, _px, _ppx, zero, succ_px, _succ_ppx) = nat_setup();
        let eq1 = terms.mk_eq(x, succ_px);
        let eq2 = terms.mk_eq(x, zero);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq1, true);
        euf.assert_literal(eq2, true);
        let _ = euf.check();
        assert!(matches!(
            pass.check(&terms, &mut euf),
            DtPassOutcome::Lemmas(_)
        ));
        assert!(matches!(
            pass.check(&terms, &mut euf),
            DtPassOutcome::Inconclusive
        ));
    }
}
