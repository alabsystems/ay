// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 demand-driven-instantiation FAMILY CLASSIFIER (shadow, zero-behavior).
//!
//! A pure-observation classifier for the demand-driven-instantiation campaign
//! (`demand-driven-instantiation-campaign` memory). It buckets each registered
//! `forall` into one of three families that the M2/M3 frontier-gated instantiation
//! lane will treat differently. It is consulted by NOTHING that steers a verdict:
//! its output feeds only the `quantifier.demand.family.*` statistics keys (M0'
//! plumbing) and the M1 unit tests. Deleting this module changes no solve result.
//!
//! The three families (per the campaign blueprint's two-minter disease map):
//!
//! - [`FamilyClass::SelfChainingDefinitional`] — a recursive defining equation
//!   whose instantiation mints a ground term that re-triggers ITSELF one level
//!   deeper (the `tsum`/`logic_sum` shape: `forall x:DT. f(x) = ... f(sel(x)) ...`
//!   with trigger `f(x)`). This is the first minter — the round-chaining that mints
//!   the depth-4/5 free-var chains before search. Recognized by MIRRORING the
//!   defining-equation head extraction of [`super::super::mbqi`]'s
//!   the UF-definition head recognizer
//!   (same completable-UF-head-over-bound-vars discipline, reusing
//!   `is_mbqi_completable_uf_symbol` + `symbol_is_datatype_selector_or_constructor`)
//!   and EXTENDING with the recursive-descent check those recognizers deliberately
//!   forbid (they require an `f`-free value side): here the value side must apply
//!   `f` to a datatype selector chain rooted at a bound variable.
//!
//!   REALITY CHECK (demand-driven-instantiation campaign diagnosis): this family is
//!   EMPTY on the real verification-consumer `rusthorn/inc_some_list`-class VCs. verification-consumer emits a
//!   datatype-recursive logic fn (`logic_sum`) as GROUND `ite` assertions per
//!   occurrence, NOT as a quantified `forall x. f(x) = ... f(sel(x)) ...`
//!   (`skip_global_quantified_logic_axioms`). The hand-written `freevar_takesome`
//!   repro presents that recursion AS a self-chaining forall, which is why it flips
//!   under the demand lane while the real obligation does not: the real residual is
//!   the ground DT/EUF/LIA combiner, downstream of this classifier. See
//!   `real_inc_some_list_ground_recursion_has_no_self_chaining` in `tests`.
//!
//! - [`FamilyClass::BridgeCycle`] — a SET of foralls forming a cross-vocabulary
//!   instantiation cycle: instantiating A mints a term that triggers B, whose
//!   instance mints a term that triggers A (the `list_cons_1` <->
//!   `enum_payload_get_1_1` dual-vocabulary shape — the second minter). Detected on
//!   a head-symbol graph over the foralls: an edge `A -> B` exists when a
//!   body-minted application head of A (an application over binder-derived
//!   arguments) is a trigger head of B. A strongly-connected component of >= 2
//!   foralls whose internal edges carry >= 2 DISTINCT bridging head symbols is a
//!   bridge cycle (the cross-vocabulary requirement — a mono-vocabulary coupling
//!   such as a recursive definition plus its own nonneg lemma, both keyed on the
//!   same head, is NOT a bridge and stays `Other`).
//!
//! - [`FamilyClass::Other`] — everything else, including quantifier_consumer seq-prelude
//!   axioms, UF-completion candidates, and plain bounded finite-table foralls.
//!   Classification alone grants no SAT authority. This is the fall-through,
//!   and it is deliberately the majority class.
//!
//! PRECEDENCE: `SelfChainingDefinitional` wins over `BridgeCycle` for a single
//! forall's tag (a recursive definition that also happens to sit in a cross-vocab
//! cycle is charged to its dominant self-chaining budget in M2/M3); `BridgeCycle`
//! wins over `Other`. The three population counts therefore partition the foralls.

use ay_core::{TermData, TermId};

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use std::collections::BTreeMap;

use super::super::mbqi::is_mbqi_completable_uf_symbol;
use super::super::Executor;
use crate::ematching::DemandStats;
use crate::Statistics;

/// Shadow classification of a registered `forall` for the demand-driven campaign.
/// Pure observation — never read to steer any instantiation or verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FamilyClass {
    /// A recursive defining equation `forall x:DT. f(x) = ... f(sel(x)) ...`.
    SelfChainingDefinitional,
    /// A member of a >= 2-forall cross-vocabulary instantiation cycle.
    BridgeCycle,
    /// Everything else (certificate-path shapes, bounded foralls, lemmas).
    Other,
}

impl FamilyClass {
    /// The `quantifier.demand.family.<suffix>` statistics-key suffix.
    pub(crate) fn stat_suffix(self) -> &'static str {
        match self {
            Self::SelfChainingDefinitional => "self_chaining",
            Self::BridgeCycle => "bridge_cycle",
            Self::Other => "other",
        }
    }
}

/// Shadow-perf guard: beyond this many foralls the O(F^2) bridge-graph edge build
/// is skipped (self-chaining/other classification still runs; bridge cycles report
/// none). Purely a cost ceiling on the observation pass; it can only move a forall
/// from `BridgeCycle` to `Other`, never affect a verdict.
const MAX_BRIDGE_GRAPH_FORALLS: usize = 400;

impl Executor {
    /// Classify every registered `forall` in `foralls` into its demand-campaign
    /// family. Pure over the term store (reads only); the returned map is consumed
    /// solely by [`write_family_class_statistics`] and the M1 unit tests.
    ///
    /// `foralls` should be the positive top-level foralls the E-matcher sees (see
    /// [`Self::collect_classifiable_foralls`]). Non-`Forall` term ids are ignored.
    pub(crate) fn classify_quantifier_families(
        &self,
        foralls: &[TermId],
    ) -> BTreeMap<TermId, FamilyClass> {
        // Deduplicate while preserving a deterministic node order for the graph.
        let mut nodes: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &q in foralls {
            if matches!(self.ctx.terms.get(q), TermData::Forall(..)) && seen.insert(q) {
                nodes.push(q);
            }
        }

        // Pass 1 — per-forall self-chaining recognition (independent).
        let self_chaining: Vec<bool> = nodes
            .iter()
            .map(|&q| self.quantifier_is_self_chaining_definition(q).is_some())
            .collect();

        // Pass 2 — bridge cycles on the head-symbol graph over the foralls.
        let bridge: Vec<bool> = self.detect_bridge_cycles(&nodes);

        // Fuse with the SelfChaining > BridgeCycle > Other precedence.
        let mut out = BTreeMap::new();
        for (idx, &q) in nodes.iter().enumerate() {
            let class = if self_chaining[idx] {
                FamilyClass::SelfChainingDefinitional
            } else if bridge[idx] {
                FamilyClass::BridgeCycle
            } else {
                FamilyClass::Other
            };
            out.insert(q, class);
        }
        out
    }

    /// Collect the positive top-level `forall` term ids reachable from the current
    /// assertions — the population the E-matcher instantiates. READ ONLY: unlike
    /// [`crate::ematching::collect_quantifiers`] it never NNF-converts (never
    /// mutates the store), so it introduces no new terms and cannot perturb any
    /// solve. A `forall` directly under a `not` (a negated universal = existential)
    /// is skipped: it is not an instantiable universal family.
    pub(crate) fn collect_classifiable_foralls(&self) -> Vec<TermId> {
        let mut out = Vec::new();
        // `seen` records collected foralls (dedup); `visited` memoizes every node so
        // a heavily-shared assertion DAG is walked in linear time.
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for a in assertions {
            self.collect_foralls_rec(a, &mut out, &mut seen, &mut visited);
        }
        out
    }

    fn collect_foralls_rec(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::Forall(..) => {
                if seen.insert(term) {
                    out.push(term);
                }
            }
            TermData::App(_, args) => {
                let args: Vec<TermId> = args.clone();
                for a in args {
                    self.collect_foralls_rec(a, out, seen, visited);
                }
            }
            TermData::Not(inner) => {
                let inner = *inner;
                // A `forall`/`exists` directly under `not` is a negated universal /
                // existential — not a plain instantiable universal family. Skip it;
                // recurse through any other negated structure.
                if !matches!(
                    self.ctx.terms.get(inner),
                    TermData::Forall(..) | TermData::Exists(..)
                ) {
                    self.collect_foralls_rec(inner, out, seen, visited);
                }
            }
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                self.collect_foralls_rec(c, out, seen, visited);
                self.collect_foralls_rec(t, out, seen, visited);
                self.collect_foralls_rec(e, out, seen, visited);
            }
            TermData::Let(bindings, body) => {
                let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                let body = *body;
                for v in vals {
                    self.collect_foralls_rec(v, out, seen, visited);
                }
                self.collect_foralls_rec(body, out, seen, visited);
            }
            TermData::Const(_) | TermData::Var(_, _) | TermData::Exists(..) => {}
            _ => {}
        }
    }

    // ----- SelfChainingDefinitional --------------------------------------------

    /// `Some(head)` when `quant` is a recursive defining equation
    /// `forall x⃗:DT. f(x⃗) = ... f(<selector-chain over a bound var>) ...`,
    /// where `head` is the defined symbol `f`.
    ///
    /// Head recognition mirrors the MBQI UF-definition discipline: `f` is a
    /// completable free UF (not a datatype selector/constructor) applied to exactly
    /// the distinct bound variables. It DIVERGES on the value side: those
    /// recognizers require the value to be `f`-free (a pointwise definition), whereas
    /// the self-chaining family is precisely the recursive complement — the value
    /// side re-applies `f` to a strictly-smaller structural projection of a bound
    /// variable.
    ///
    /// The defining equality is SEARCHED for through the body's connective
    /// structure, because ay's elaborator ite-lifts an `(= (f x⃗) (ite g a b))`
    /// definition into `(ite g (= (f x⃗) a) (= (f x⃗) b))` — the equality no longer
    /// sits at the body root. The search descends through `ite`/`and`/`=>`/`not` and
    /// tries each `(= .. ..)` atom it reaches (the `tsum`/`sum` axioms surface the
    /// recursive branch this way; verification-consumer's `=>`-guarded form is reached the same
    /// way).
    pub(crate) fn quantifier_is_self_chaining_definition(&self, quant: TermId) -> Option<String> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return None;
        };
        let vars = vars.clone();
        let body = *body;
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        self.find_self_chaining_eq(body, &vars, &bound)
    }

    /// Search `term` for a self-chaining defining equality, descending through the
    /// connective structure the elaborator may have lifted the definition into.
    fn find_self_chaining_eq(
        &self,
        term: TermId,
        vars: &[(String, ay_core::Sort)],
        bound: &HashSet<String>,
    ) -> Option<String> {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "=" && args.len() == 2 {
                    let (a0, a1) = (args[0], args[1]);
                    if let Some(f) = self
                        .self_chaining_oriented(vars, bound, a0, a1)
                        .or_else(|| self.self_chaining_oriented(vars, bound, a1, a0))
                    {
                        return Some(f);
                    }
                }
                let args: Vec<TermId> = args.clone();
                args.iter()
                    .find_map(|&a| self.find_self_chaining_eq(a, vars, bound))
            }
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                self.find_self_chaining_eq(c, vars, bound)
                    .or_else(|| self.find_self_chaining_eq(t, vars, bound))
                    .or_else(|| self.find_self_chaining_eq(e, vars, bound))
            }
            TermData::Not(inner) => self.find_self_chaining_eq(*inner, vars, bound),
            TermData::Let(bindings, b) => {
                let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                let b = *b;
                vals.iter()
                    .find_map(|&v| self.find_self_chaining_eq(v, vars, bound))
                    .or_else(|| self.find_self_chaining_eq(b, vars, bound))
            }
            _ => None,
        }
    }

    /// One orientation of the defining equation: `head` is `f(x⃗)`, `value` is the
    /// other side. Returns the defined head symbol `f` when `head` is a completable
    /// UF applied to exactly the distinct bound variables AND `value` re-applies
    /// `f` to a selector chain rooted at a bound variable.
    fn self_chaining_oriented(
        &self,
        vars: &[(String, ay_core::Sort)],
        bound: &HashSet<String>,
        head: TermId,
        value: TermId,
    ) -> Option<String> {
        let TermData::App(f, hargs) = self.ctx.terms.get(head) else {
            return None;
        };
        // Same head discipline as the MBQI UF-definition recognizer: a completable
        // free UF, not a datatype selector/constructor.
        if hargs.is_empty()
            || !is_mbqi_completable_uf_symbol(f.name())
            || self.symbol_is_datatype_selector_or_constructor(f.name())
        {
            return None;
        }
        // Head args: exactly the bound variables, each used once (a total
        // definition over the binders).
        let hargs = hargs.clone();
        let mut used: HashSet<String> = HashSet::default();
        for arg in &hargs {
            let TermData::Var(name, _) = self.ctx.terms.get(*arg) else {
                return None;
            };
            if !bound.contains(name) || !used.insert(name.clone()) {
                return None;
            }
        }
        if used.len() != vars.len() {
            return None;
        }
        let fname = f.name().to_string();
        if self.term_has_recursive_selector_application(value, &fname, bound) {
            Some(fname)
        } else {
            None
        }
    }

    /// True when `term` contains, anywhere, an application `f(a)` whose argument
    /// `a` is a datatype-selector chain rooted at a bound variable (the recursive
    /// descent of a defining equation). Descends through the whole value side
    /// (`ite`/`+`/... included).
    fn term_has_recursive_selector_application(
        &self,
        term: TermId,
        f: &str,
        bound: &HashSet<String>,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                let args: Vec<TermId> = args.clone();
                if sym.name() == f
                    && args
                        .iter()
                        .any(|&a| self.is_selector_chain_over_binder(a, bound))
                {
                    return true;
                }
                args.iter()
                    .any(|&a| self.term_has_recursive_selector_application(a, f, bound))
            }
            TermData::Not(inner) => self.term_has_recursive_selector_application(*inner, f, bound),
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                self.term_has_recursive_selector_application(c, f, bound)
                    || self.term_has_recursive_selector_application(t, f, bound)
                    || self.term_has_recursive_selector_application(e, f, bound)
            }
            TermData::Let(bindings, body) => {
                let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                let body = *body;
                vals.iter()
                    .any(|&v| self.term_has_recursive_selector_application(v, f, bound))
                    || self.term_has_recursive_selector_application(body, f, bound)
            }
            TermData::Const(_)
            | TermData::Var(_, _)
            | TermData::Forall(..)
            | TermData::Exists(..) => false,
            _ => false,
        }
    }

    /// True when `term` is a chain of >= 1 datatype selectors/constructors that
    /// bottoms out at a bound variable — e.g. `tl(l)`, `left(t)`, `tl(tl(l))`. A
    /// bare bound variable is NOT a chain (the recursion must descend at least one
    /// structural step); a chain bottoming at a free constant is rejected (it is
    /// not recursion over the binder).
    fn is_selector_chain_over_binder(&self, term: TermId, bound: &HashSet<String>) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        if args.is_empty() || !self.symbol_is_datatype_selector_or_constructor(sym.name()) {
            return false;
        }
        let args: Vec<TermId> = args.clone();
        args.iter().any(|&a| match self.ctx.terms.get(a) {
            TermData::Var(name, _) => bound.contains(name),
            _ => self.is_selector_chain_over_binder(a, bound),
        })
    }

    // ----- BridgeCycle ---------------------------------------------------------

    /// For each forall in `nodes`, whether it is a member of a cross-vocabulary
    /// instantiation cycle (a >= 2-forall SCC of the head-symbol graph whose
    /// internal edges carry >= 2 distinct bridging head symbols).
    fn detect_bridge_cycles(&self, nodes: &[TermId]) -> Vec<bool> {
        let n = nodes.len();
        let mut result = vec![false; n];
        if !(2..=MAX_BRIDGE_GRAPH_FORALLS).contains(&n) {
            return result;
        }

        let trigger: Vec<HashSet<String>> = nodes
            .iter()
            .map(|&q| self.trigger_head_symbols(q))
            .collect();
        let minted: Vec<HashSet<String>> = nodes
            .iter()
            .map(|&q| self.minted_application_heads(q))
            .collect();

        // Directed adjacency: u -> v when a minted head of u triggers v. The edge
        // is labelled by the shared bridging symbols (used for the cross-vocabulary
        // test on each SCC's internal edges).
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        // Edge label lookup keyed by (u, v).
        let mut labels: HashMap<(usize, usize), Vec<String>> = HashMap::default();
        for u in 0..n {
            for (v, trigger_v) in trigger.iter().enumerate() {
                if u == v {
                    continue;
                }
                let shared: Vec<String> = minted[u]
                    .iter()
                    .filter(|s| trigger_v.contains(*s))
                    .cloned()
                    .collect();
                if !shared.is_empty() {
                    adj[u].push(v);
                    labels.insert((u, v), shared);
                }
            }
        }

        // Strongly-connected components (Tarjan).
        let sccs = tarjan_sccs(n, &adj);
        for comp in sccs {
            if comp.len() < 2 {
                continue;
            }
            let members: HashSet<usize> = comp.iter().copied().collect();
            let mut bridging: HashSet<String> = HashSet::default();
            for &u in &comp {
                for &v in &adj[u] {
                    if members.contains(&v) {
                        if let Some(syms) = labels.get(&(u, v)) {
                            for s in syms {
                                bridging.insert(s.clone());
                            }
                        }
                    }
                }
            }
            if bridging.len() >= 2 {
                for &u in &comp {
                    result[u] = true;
                }
            }
        }
        result
    }

    /// The head symbols the E-matcher would key `quant` on: the head symbol of each
    /// declared `:pattern` trigger term. Falls back to the body-minted heads when a
    /// forall carries no usable declared trigger (auto-trigger approximation).
    fn trigger_head_symbols(&self, quant: TermId) -> HashSet<String> {
        let mut heads: HashSet<String> = HashSet::default();
        let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(quant) else {
            return heads;
        };
        let body = *body;
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        for group in triggers {
            for &t in group {
                if let TermData::App(sym, _) = self.ctx.terms.get(t) {
                    heads.insert(sym.name().to_string());
                }
            }
        }
        if heads.is_empty() {
            self.collect_minted_heads(body, &bound, &mut heads);
        }
        heads
    }

    /// The application head symbols `quant`'s body mints over binder-derived
    /// arguments: an instantiation substitutes ground terms for the binders, so
    /// every application whose argument subtree mentions a bound variable becomes a
    /// fresh ground term that can re-trigger E-matching. These are the heads on the
    /// outgoing edges of `quant` in the bridge graph.
    fn minted_application_heads(&self, quant: TermId) -> HashSet<String> {
        let mut heads: HashSet<String> = HashSet::default();
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return heads;
        };
        let body = *body;
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        self.collect_minted_heads(body, &bound, &mut heads);
        heads
    }

    /// DFS helper: insert into `out` the head of every application whose argument
    /// subtree mentions a bound variable. Returns whether `term`'s subtree mentions
    /// a bound variable.
    fn collect_minted_heads(
        &self,
        term: TermId,
        bound: &HashSet<String>,
        out: &mut HashSet<String>,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => bound.contains(name),
            TermData::Const(_) => false,
            TermData::App(sym, args) => {
                let name = sym.name().to_string();
                let args: Vec<TermId> = args.clone();
                let mut has_bound = false;
                for a in args {
                    if self.collect_minted_heads(a, bound, out) {
                        has_bound = true;
                    }
                }
                if has_bound {
                    out.insert(name);
                }
                has_bound
            }
            TermData::Not(inner) => self.collect_minted_heads(*inner, bound, out),
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                let x = self.collect_minted_heads(c, bound, out);
                let y = self.collect_minted_heads(t, bound, out);
                let z = self.collect_minted_heads(e, bound, out);
                x || y || z
            }
            TermData::Let(bindings, body) => {
                let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                let body = *body;
                let mut has_bound = false;
                for v in vals {
                    if self.collect_minted_heads(v, bound, out) {
                        has_bound = true;
                    }
                }
                if self.collect_minted_heads(body, bound, out) {
                    has_bound = true;
                }
                has_bound
            }
            // Nested quantifier: recurse into the body (its own binders shadow ours
            // and are absent from `bound`, so they contribute no minted heads).
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                self.collect_minted_heads(*body, bound, out)
            }
            _ => false,
        }
    }
}

/// Tarjan's strongly-connected-components over the small forall graph. Returns the
/// SCCs (each a list of node indices). Iterative to stay stack-safe even though the
/// graph is bounded by [`MAX_BRIDGE_GRAPH_FORALLS`].
fn tarjan_sccs(n: usize, adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    #[derive(Clone, Copy)]
    struct NodeState {
        index: u32,
        lowlink: u32,
        on_stack: bool,
        visited: bool,
    }
    let mut state = vec![
        NodeState {
            index: 0,
            lowlink: 0,
            on_stack: false,
            visited: false,
        };
        n
    ];
    let mut stack: Vec<usize> = Vec::new();
    let mut sccs: Vec<Vec<usize>> = Vec::new();
    let mut next_index: u32 = 0;

    // Explicit DFS work stack of (node, next-adjacency-cursor).
    for start in 0..n {
        if state[start].visited {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, ci)) = work.last() {
            if ci == 0 {
                state[v].visited = true;
                state[v].index = next_index;
                state[v].lowlink = next_index;
                next_index += 1;
                stack.push(v);
                state[v].on_stack = true;
            }
            if ci < adj[v].len() {
                let w = adj[v][ci];
                work.last_mut().unwrap().1 += 1;
                if !state[w].visited {
                    work.push((w, 0));
                } else if state[w].on_stack {
                    state[v].lowlink = state[v].lowlink.min(state[w].index);
                }
            } else {
                if state[v].lowlink == state[v].index {
                    let mut comp = Vec::new();
                    loop {
                        let w = stack.pop().unwrap();
                        state[w].on_stack = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    sccs.push(comp);
                }
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    state[parent].lowlink = state[parent].lowlink.min(state[v].lowlink);
                }
            }
        }
    }
    sccs
}

/// Surface the M1 family classification into `stats` under
/// `quantifier.demand.family.*`. PURE OUTPUT: reads the classification map + the
/// M0' per-family demand tallies; writes only statistics. Two views:
///
/// - Population: `quantifier.demand.family.{self_chaining,bridge_cycle,other}` —
///   how many registered foralls fell in each class (the classes partition, so
///   these sum to the classified-forall count).
/// - Activity: `quantifier.demand.family.<class>.{asserted,parked,blocked}` — the
///   M0' cost-gate tallies re-aggregated by the class of each family's source
///   quantifier (joined on the quantifier `TermId`). A family whose quantifier was
///   not classified — e.g. one materialized by preprocessing after the shadow
///   population snapshot — folds into `other`.
pub(in crate::executor) fn write_family_class_statistics(
    demand: &DemandStats,
    classes: &BTreeMap<TermId, FamilyClass>,
    stats: &mut Statistics,
) {
    // Population counts over every classified forall.
    let mut pop = [0u64; 3];
    for class in classes.values() {
        pop[class_index(*class)] += 1;
    }
    // Activity re-aggregated by the class of each family's source quantifier.
    // The M0' family key stores the quantifier's raw `TermId.0`; index the classes
    // by the same raw id for the join.
    let mut by_raw: HashMap<u32, FamilyClass> = HashMap::default();
    for (tid, class) in classes {
        by_raw.insert(tid.0, *class);
    }
    let mut activity = [(0u64, 0u64, 0u64); 3];
    for ((quant_raw, _head), fd) in &demand.families {
        let class = by_raw.get(quant_raw).copied().unwrap_or(FamilyClass::Other);
        let slot = &mut activity[class_index(class)];
        slot.0 += fd.asserted;
        slot.1 += fd.parked;
        slot.2 += fd.blocked;
    }

    for class in [
        FamilyClass::SelfChainingDefinitional,
        FamilyClass::BridgeCycle,
        FamilyClass::Other,
    ] {
        let suffix = class.stat_suffix();
        let i = class_index(class);
        stats.set_int(&format!("quantifier.demand.family.{suffix}"), pop[i]);
        stats.set_int(
            &format!("quantifier.demand.family.{suffix}.asserted"),
            activity[i].0,
        );
        stats.set_int(
            &format!("quantifier.demand.family.{suffix}.parked"),
            activity[i].1,
        );
        stats.set_int(
            &format!("quantifier.demand.family.{suffix}.blocked"),
            activity[i].2,
        );
    }
}

fn class_index(class: FamilyClass) -> usize {
    match class {
        FamilyClass::SelfChainingDefinitional => 0,
        FamilyClass::BridgeCycle => 1,
        FamilyClass::Other => 2,
    }
}

#[cfg(test)]
mod tests;
