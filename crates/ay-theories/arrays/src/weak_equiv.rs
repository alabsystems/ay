// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Weak-equivalence graph over array terms (Christ/Hoenicke), M1 shadow build.
//!
//! Two arrays are *weakly equivalent* if they differ only at a finite set of
//! store indices. The graph has array terms as nodes and two edge kinds:
//!
//! - **Strong edges** from asserted/external equalities: the arrays are equal
//!   everywhere. Reason-carrying variants record the SAT-visible literals that
//!   justify the edge (same discipline as `extend_eq_path` in store_chain.rs);
//!   reason-free sentinel edges and `array_vars` merge-log edges participate in
//!   connectivity queries only and are excluded from reason-carrying paths.
//! - **Store edges** labeled with the store index: for `store(a, i, v)` the
//!   store term and `a` differ at most at `i`.
//!
//! M1 is a *shadow* structure: it changes no solving behavior. It backs
//! `#[cfg(debug_assertions)]` invariants on the existing store-chain walkers
//! and lazy ROW2 generation, plus unit tests. M2/M3 build the conflict-driven
//! filter and read-over-weak-path lemma instantiation on top of it.
//!
//! Invalidation mirrors `build_equiv_class_cache` (equality.rs): the cached
//! graph is rebuilt when `eq_adj_version` bumps or when `store_cache`,
//! `external_eqs`, `external_eq_reasons`, or `array_var_merge_log` grow.
//! Within one `eq_adj_version`, `eq_adj` may gain/lose parallel edges inside a
//! component; connectivity answers are stable under that, which is all the
//! debug asserts rely on.

use super::*;

/// Cache key: (eq_adj_version, store_cache.len(), external_eqs.len(),
/// external_eq_reasons.len(), array_var_merge_log.len()).
type WeakGraphKey = (u64, usize, usize, usize, usize);

/// One edge of the weak-equivalence graph.
#[derive(Debug, Clone, PartialEq, Eq)]
// M1 shadow structure: fully exercised under cfg(test)/debug_assertions;
// M2/M3 add the production consumers. Lint stays active in test builds.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) enum WeakEdgeKind {
    /// Strong equality edge with SAT-visible reason literals.
    Strong { reasons: Vec<TheoryLit> },
    /// Strong equality edge without reasons (reason-free external sentinel or
    /// `array_vars` merge-log edge). Connectivity only; never on a
    /// reason-carrying `weak_path`.
    StrongUnreasoned,
    /// Store edge: endpoints differ at most at `label` (the store index).
    Store { label: TermId },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WeakEdge {
    pub(crate) to: TermId,
    pub(crate) kind: WeakEdgeKind,
}

/// Immutable snapshot of the weak-equivalence graph.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct WeakEquivGraph {
    adj: HashMap<TermId, Vec<WeakEdge>>,
}

/// Edge filter for graph traversals.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(test), allow(dead_code))]
enum TraversalMode {
    /// All edges (strong, unreasoned, store).
    All,
    /// Only reason-carrying edges (Strong + Store); paths can justify lemmas.
    Reasoned,
    /// Only strong edges (reasoned or not); no store hops.
    Strong,
}

impl WeakEquivGraph {
    fn edge_allowed(kind: &WeakEdgeKind, mode: TraversalMode) -> bool {
        match mode {
            TraversalMode::All => true,
            TraversalMode::Reasoned => !matches!(kind, WeakEdgeKind::StrongUnreasoned),
            TraversalMode::Strong => !matches!(kind, WeakEdgeKind::Store { .. }),
        }
    }

    /// BFS from `a` to `b` under `mode`. Returns the edge sequence of a
    /// shortest path, or `None` if unreachable. `a == b` yields `Some(vec![])`.
    fn bfs_path(&self, a: TermId, b: TermId, mode: TraversalMode) -> Option<Vec<&WeakEdge>> {
        if a == b {
            return Some(vec![]);
        }
        // parent: node -> (predecessor, edge taken into node)
        let mut parent: HashMap<TermId, (TermId, &WeakEdge)> = HashMap::default();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(a);
        while let Some(current) = queue.pop_front() {
            let Some(edges) = self.adj.get(&current) else {
                continue;
            };
            for edge in edges {
                if !Self::edge_allowed(&edge.kind, mode) {
                    continue;
                }
                if edge.to == a || parent.contains_key(&edge.to) {
                    continue;
                }
                parent.insert(edge.to, (current, edge));
                if edge.to == b {
                    let mut path = Vec::new();
                    let mut node = b;
                    while node != a {
                        let (pred, edge) = parent[&node];
                        path.push(edge);
                        node = pred;
                    }
                    path.reverse();
                    return Some(path);
                }
                queue.push_back(edge.to);
            }
        }
        None
    }

    /// Whether `a` and `b` are weakly connected (any edges, including
    /// reason-free strong edges).
    pub(crate) fn weakly_connected(&self, a: TermId, b: TermId) -> bool {
        self.bfs_path(a, b, TraversalMode::All).is_some()
    }

    /// Whether `a` and `b` are strongly connected (equality edges only,
    /// including reason-free ones; no store hops).
    // Consumed only by `#[cfg(debug_assertions)]` invariants (the ROW2 length-1
    // weak-path assert + the M5 `weq5_shadow` M6-feasibility telemetry); dead in
    // release non-test builds.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn strongly_connected(&self, a: TermId, b: TermId) -> bool {
        self.bfs_path(a, b, TraversalMode::Strong).is_some()
    }

    /// Shortest reason-carrying weak path from `a` to `b`.
    ///
    /// Returns `(labels, reasons)` where `labels` are the store indices along
    /// the path (the arrays may differ only at these indices) and `reasons`
    /// are the canonicalized SAT-visible literals justifying every strong edge
    /// used. Reason-free strong edges are never traversed.
    // M1 shadow API: exercised by unit tests now; M3's read-over-weak-path
    // lemma instantiation is the production consumer.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn weak_path(&self, a: TermId, b: TermId) -> Option<(Vec<TermId>, Vec<TheoryLit>)> {
        let path = self.bfs_path(a, b, TraversalMode::Reasoned)?;
        let mut labels = Vec::new();
        let mut reasons = Vec::new();
        for edge in path {
            match &edge.kind {
                WeakEdgeKind::Strong { reasons: r } => reasons.extend(r.iter().copied()),
                WeakEdgeKind::Store { label } => labels.push(*label),
                WeakEdgeKind::StrongUnreasoned => {
                    unreachable!("filtered by TraversalMode::Reasoned")
                }
            }
        }
        ArraySolver::canonicalize_theory_lits(&mut reasons);
        Some((labels, reasons))
    }
}

/// Version-keyed cache entry stored on the solver.
pub(crate) struct WeakEquivCacheEntry {
    key: WeakGraphKey,
    graph: Rc<WeakEquivGraph>,
    /// Pairs already verified weakly connected under this key (debug asserts
    /// are hot in the store-chain walkers; avoid re-running BFS per call).
    #[cfg(debug_assertions)]
    verified_weak: HashSet<(TermId, TermId)>,
    /// Pairs already verified strongly connected under this key.
    #[cfg(debug_assertions)]
    verified_strong: HashSet<(TermId, TermId)>,
}

impl ArraySolver<'_> {
    fn weak_graph_key(&self) -> WeakGraphKey {
        (
            self.eq_adj_version,
            self.store_cache.len(),
            self.external_eqs.len(),
            self.external_eq_reasons.len(),
            self.array_var_merge_log.len(),
        )
    }

    fn is_array_term(&self, term: TermId) -> bool {
        matches!(self.terms.sort(term), Sort::Array(_))
    }

    /// Build the weak-equivalence graph from the current equality indices and
    /// term caches. Deterministic: edges are gathered in sorted order.
    fn build_weak_equiv_graph(&self) -> WeakEquivGraph {
        let mut graph = WeakEquivGraph::default();

        // Strong edges from the equality adjacency list (array-sorted terms).
        // eq_adj holds each edge in both directions; take each once (t < other)
        // and insert both directions ourselves for a canonical adjacency.
        let mut eq_nodes: Vec<TermId> = self.eq_adj.keys().copied().collect();
        eq_nodes.sort_unstable_by_key(|t| t.0);
        let mut strong_seen: HashSet<(TermId, TermId)> = HashSet::default();
        for t in eq_nodes {
            if !self.is_array_term(t) {
                continue;
            }
            let Some(neighbors) = self.eq_adj.get(&t) else {
                continue;
            };
            let mut sorted_neighbors: Vec<(TermId, TermId)> = neighbors.clone();
            sorted_neighbors.sort_unstable_by_key(|&(other, eq)| (other.0, eq.0));
            for (other, eq_term) in sorted_neighbors {
                if !self.is_array_term(other) {
                    continue;
                }
                if !strong_seen.insert(Self::ordered_pair(t, other)) {
                    continue;
                }
                let kind = if eq_term.is_sentinel() {
                    match self.external_eq_reasons.get(&Self::ordered_pair(t, other)) {
                        Some(reasons) if !reasons.is_empty() => WeakEdgeKind::Strong {
                            reasons: reasons.clone(),
                        },
                        // Reason-free sentinel: connectivity only
                        // (store_chain.rs `SentinelEdgeMode::Skip` discipline).
                        _ => WeakEdgeKind::StrongUnreasoned,
                    }
                } else {
                    WeakEdgeKind::Strong {
                        reasons: vec![TheoryLit::new(eq_term, true)],
                    }
                };
                Self::push_undirected_edge(&mut graph, t, other, kind);
            }
        }

        // Equality-driven array_vars merges (notify_equality) may connect
        // arrays without a matching eq_adj edge; mirror them for connectivity
        // so cache-derived pairs (e.g. ROW2 candidates) stay explainable by
        // the graph.
        let mut merges = self.array_var_merge_log.clone();
        merges.sort_unstable_by_key(|&(a, b)| (a.0, b.0));
        for (a, b) in merges {
            if a == b || !self.is_array_term(a) || !self.is_array_term(b) {
                continue;
            }
            if !strong_seen.insert(Self::ordered_pair(a, b)) {
                continue;
            }
            Self::push_undirected_edge(&mut graph, a, b, WeakEdgeKind::StrongUnreasoned);
        }

        // Store edges: store(a, i, v) —[i]— a.
        let mut stores: Vec<(TermId, (TermId, TermId, TermId))> = self
            .store_cache
            .iter()
            .map(|(&s, &triple)| (s, triple))
            .collect();
        stores.sort_unstable_by_key(|&(s, _)| s.0);
        for (store_term, (base, index, _value)) in stores {
            Self::push_undirected_edge(
                &mut graph,
                store_term,
                base,
                WeakEdgeKind::Store { label: index },
            );
        }

        graph
    }

    fn push_undirected_edge(graph: &mut WeakEquivGraph, a: TermId, b: TermId, kind: WeakEdgeKind) {
        graph.adj.entry(a).or_default().push(WeakEdge {
            to: b,
            kind: kind.clone(),
        });
        graph
            .adj
            .entry(b)
            .or_default()
            .push(WeakEdge { to: a, kind });
    }

    /// Current weak-equivalence graph, rebuilt when the equality graph
    /// connectivity or the store/external-edge caches change.
    pub(crate) fn weak_equiv_graph(&self) -> Rc<WeakEquivGraph> {
        let key = self.weak_graph_key();
        {
            let cache = self.weak_equiv_cache.borrow();
            if let Some(entry) = cache.as_ref() {
                if entry.key == key {
                    return Rc::clone(&entry.graph);
                }
            }
        }
        let graph = self.build_weak_equiv_graph();
        // M1 invariant: the rebuild is deterministic — the same solver state
        // must always produce the same graph.
        #[cfg(debug_assertions)]
        {
            let rebuilt = self.build_weak_equiv_graph();
            debug_assert_eq!(
                graph, rebuilt,
                "weak-equivalence graph rebuild must be deterministic"
            );
        }
        let graph = Rc::new(graph);
        *self.weak_equiv_cache.borrow_mut() = Some(WeakEquivCacheEntry {
            key,
            graph: Rc::clone(&graph),
            #[cfg(debug_assertions)]
            verified_weak: HashSet::default(),
            #[cfg(debug_assertions)]
            verified_strong: HashSet::default(),
        });
        graph
    }

    /// Whether `a` and `b` are weakly connected in the current graph.
    ///
    /// M5 production consumer: the near-linear no-conflict verdict at the
    /// SingletonOnly store-chain-witness (`check_store_chain_select_difference_
    /// witness_with_mode`). `!weakly_connected(array1, array2)` authoritatively
    /// decides *no conflict* — the two select arrays are in different weak-eq
    /// components, so they cannot share a common base, so the witness's legacy
    /// `base_eq` (`explain_equal_if_provable`, over `eq_adj`) provably fails and
    /// no witness can fire. Pruning here replaces the up-front per-pair
    /// store-chain collection (the O(selects²×aliases²) scan) with one cached-
    /// graph BFS. Sound because `build_weak_equiv_graph` ingests every `eq_adj`
    /// edge the legacy prover can traverse (a superset), so
    /// `base_eq ⟹ weakly_connected` by construction (enforced corpus-wide by the
    /// `weq5_shadow` differential assert in the witness).
    pub(crate) fn weakly_connected(&self, a: TermId, b: TermId) -> bool {
        self.weak_equiv_graph().weakly_connected(a, b)
    }

    /// Weak-equivalence-**modulo-`j`**: whether `select(a, j) = select(b, j)` is
    /// FORCED by the current array structure — i.e. `a` and `b` are connected in
    /// the weak-equivalence graph by a path whose store edges are ALL provably at
    /// an index distinct from `j`, so none of them can affect the value at `j`.
    /// This is the near-linear read-over-write query (de Moura–Bjørner weak
    /// equivalence) that replaces the O(selects²×aliases²) store-chain BFS.
    ///
    /// The store-edge crossability is decided **LIVE** per query via
    /// `explain_distinct_if_provable(label, j)` and is deliberately **NOT
    /// memoized at graph lifetime**: the cached graph is diseq-independent
    /// (`weak_graph_key` has no disequality component), but this answer depends
    /// on `diseq_set`, which mutates on false-assign / backtrack-retract /
    /// external-diseq injection WITHOUT bumping the graph key — so any
    /// graph-lifetime distinctness memo would be stale-by-construction across a
    /// diseq retraction (the incremental-correctness wrong-verdict vector).
    ///
    /// Soundness (the direction that matters): a `true` answer means every store
    /// on the connecting path is provably distinct from `j`, so the two reads
    /// must coincide — a valid array tautology. A `false` answer is conservative
    /// (it never fabricates a forced equality). M1 SHADOW primitive: no authority
    /// change; validated against the legacy store-chain witness before any flip.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn weakly_equiv_mod_j(&self, a: TermId, b: TermId, j: TermId) -> bool {
        if a == b {
            return true;
        }
        let graph = self.weak_equiv_graph();
        let mut visited: HashSet<TermId> = HashSet::default();
        visited.insert(a);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(a);
        while let Some(current) = queue.pop_front() {
            let Some(edges) = graph.adj.get(&current) else {
                continue;
            };
            for edge in edges {
                // Store edges are crossable-modulo-`j` ONLY when the store index
                // is provably distinct from `j` (the store cannot touch index
                // `j`). Strong / StrongUnreasoned edges are always crossable (the
                // arrays are equal everywhere). Distinctness is computed LIVE.
                if let WeakEdgeKind::Store { label } = &edge.kind {
                    if self.explain_distinct_if_provable(*label, j).is_none() {
                        continue;
                    }
                }
                if visited.insert(edge.to) {
                    if edge.to == b {
                        return true;
                    }
                    queue.push_back(edge.to);
                }
            }
        }
        false
    }

    /// Shortest reason-carrying weak path between `a` and `b`:
    /// `(store-index labels, strong-equality reason literals)`.
    // M1 shadow API: see `weakly_connected`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn weak_path(&self, a: TermId, b: TermId) -> Option<(Vec<TermId>, Vec<TheoryLit>)> {
        self.weak_equiv_graph().weak_path(a, b)
    }

    /// Debug invariant: a store-chain walk from `term` that found a store with
    /// base `base` implies `term` and `base` are weakly connected. The walker
    /// traverses a subset of the graph's edges, so this must always hold.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_walk_endpoints_weakly_connected(&self, term: TermId, base: TermId) {
        let pair = Self::ordered_pair(term, base);
        let graph = self.weak_equiv_graph();
        {
            let cache = self.weak_equiv_cache.borrow();
            if let Some(entry) = cache.as_ref() {
                if entry.verified_weak.contains(&pair) {
                    return;
                }
            }
        }
        debug_assert!(
            graph.weakly_connected(term, base),
            "store-chain walk endpoints must be weakly connected: {term:?} -> {base:?}"
        );
        if let Some(entry) = self.weak_equiv_cache.borrow_mut().as_mut() {
            entry.verified_weak.insert(pair);
        }
    }

    /// Debug invariant: a lazy ROW2-down candidate pairs a select on `array`
    /// with a `store` in `array`'s strong class — i.e. the pair lies on a
    /// length-1 weak path `array ≈ store —[i]— base`.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_row2_pair_on_length1_weak_path(&self, array: TermId, store: TermId) {
        let pair = Self::ordered_pair(array, store);
        let graph = self.weak_equiv_graph();
        {
            let cache = self.weak_equiv_cache.borrow();
            if let Some(entry) = cache.as_ref() {
                if entry.verified_strong.contains(&pair) {
                    return;
                }
            }
        }
        debug_assert!(
            graph.strongly_connected(array, store),
            "ROW2-down candidate must pair a select array with a store in its \
             strong class (length-1 weak path): array {array:?}, store {store:?}"
        );
        if let Some(entry) = self.weak_equiv_cache.borrow_mut().as_mut() {
            entry.verified_strong.insert(pair);
        }
    }
}

/// M5 verdict-only authority-flip differential (shadow, debug-only).
///
/// The M5 flip promotes the weak-equivalence graph to authoritatively decide
/// *no conflict* at the SingletonOnly store-chain-witness: `!weakly_connected`
/// prunes a candidate pair before the expensive legacy store-chain collection,
/// while legacy (`collect_complete_effective_stores` / `store_chain_difference_
/// support`) stays the SOLE producer of `(support, reasons)` on surviving pairs
/// — so reasons remain byte-identical.
///
/// This module accumulates the corpus-wide differential proving the flip sound:
///
///  * SOUNDNESS GATE (wrong-SAT direction): a graph *no-conflict* verdict must
///    never drop a pair the legacy witness would fire on. Because the witness
///    fires only when its `base_eq` (`explain_equal_if_provable`) holds, and
///    `base_eq ⟹ weakly_connected` by construction (the graph ingests a
///    superset of `eq_adj`), we enforce the contrapositive live: every pair
///    whose `base_eq` holds MUST be weakly connected. `DISAGREE_BASE_EQ_NOT_WC`
///    is that counter and the `debug_assert` fires on any violation (the M3
///    extensionality-derived-base-equality vector — held on the whole corpus).
///
///  * The wrong-UNSAT direction is vacuous: the graph only ever *prunes*
///    (verdict-only, never fabricates a conflict), and legacy produces every
///    reason, so a kept-but-uninteresting pair merely wastes work.
///
/// Telemetry counters (`SC_*` / `MJ_*`) measure whether a *stronger* prune
/// (`strongly_connected`, or `weakly_equiv_mod_j` at the read index) could
/// soundly filter same-component pairs — the M6 latency lever's feasibility.
///
/// Counters are process-global (they must aggregate across the fresh-
/// `ArraySolver`-per-round recreation and across a whole serial test binary)
/// and compiled only under `debug_assertions`; release builds carry none of it.
#[cfg(debug_assertions)]
pub(crate) mod weq5_shadow {
    use std::cell::Cell;
    use std::thread::LocalKey;

    // Per-thread counters. The cargo test harness runs unit tests on many
    // threads in parallel, so a process-global counter would let a concurrent
    // array test bump these between a reader test's `reset()` and `snapshot()`.
    // These are pure diagnostics (never consulted for a solver decision), so
    // per-thread accumulation is exactly right: each solve reports its own
    // thread's tally and `maybe_dump` runs on the solve's thread.
    thread_local! {
        /// Total candidate pairs examined at the SingletonOnly witness.
        pub(crate) static PAIRS: Cell<u64> = const { Cell::new(0) };
        /// Pairs the graph pruned as no-conflict (`!weakly_connected`).
        pub(crate) static GRAPH_PRUNED: Cell<u64> = const { Cell::new(0) };
        /// Pairs whose legacy common-base equality holds (reached the support step).
        pub(crate) static BASE_EQ_HOLDS: Cell<u64> = const { Cell::new(0) };
        /// SOUNDNESS GATE: base-eq holds yet the pair is NOT weakly connected — a
        /// dropped-witness (wrong-SAT) vector. MUST stay 0.
        pub(crate) static DISAGREE_BASE_EQ_NOT_WC: Cell<u64> = const { Cell::new(0) };
        /// Among base-eq pairs: legacy difference support is non-empty (would-fire).
        pub(crate) static SUPPORT_NONEMPTY: Cell<u64> = const { Cell::new(0) };
        /// Among base-eq pairs: legacy difference support is empty (no witness).
        pub(crate) static SUPPORT_EMPTY: Cell<u64> = const { Cell::new(0) };
        /// M6-feasibility contingency for a `strongly_connected`-based prune:
        /// strongly connected AND support non-empty = a would-be-unsound prune.
        pub(crate) static SC_AND_SUPPORT_NONEMPTY: Cell<u64> = const { Cell::new(0) };
        pub(crate) static SC_AND_SUPPORT_EMPTY: Cell<u64> = const { Cell::new(0) };
        /// M6-feasibility contingency for a `weakly_equiv_mod_j`-based prune at the
        /// read index, cross-tabbed against support (non-)emptiness.
        pub(crate) static MJ_TRUE_SUPPORT_NONEMPTY: Cell<u64> = const { Cell::new(0) };
        pub(crate) static MJ_TRUE_SUPPORT_EMPTY: Cell<u64> = const { Cell::new(0) };
        pub(crate) static MJ_FALSE_SUPPORT_NONEMPTY: Cell<u64> = const { Cell::new(0) };
        pub(crate) static MJ_FALSE_SUPPORT_EMPTY: Cell<u64> = const { Cell::new(0) };
    }

    /// Increment a thread-local counter by 1.
    fn bump(counter: &'static LocalKey<Cell<u64>>) {
        counter.with(|c| c.set(c.get() + 1));
    }
    /// Read a thread-local counter.
    fn get(counter: &'static LocalKey<Cell<u64>>) -> u64 {
        counter.with(Cell::get)
    }

    /// Record a pair the SingletonOnly flip pruned as no-conflict.
    pub(crate) fn record_graph_pruned() {
        bump(&PAIRS);
        bump(&GRAPH_PRUNED);
    }

    /// Record a base-eq pair that survived to the support computation.
    ///
    /// `wc` / `sc` / `mj` are the graph predicates (weakly / strongly connected,
    /// weakly-equiv-modulo the read index); `support_empty` is the legacy
    /// verdict. Asserts the wrong-SAT soundness gate (`base_eq ⟹ wc`).
    pub(crate) fn record_base_eq(wc: bool, sc: bool, mj: bool, support_empty: bool) {
        bump(&PAIRS);
        bump(&BASE_EQ_HOLDS);
        if !wc {
            bump(&DISAGREE_BASE_EQ_NOT_WC);
            debug_assert!(
                wc,
                "M5 wrong-SAT vector: legacy base-eq holds but the pair is NOT \
                 weakly connected (extensionality-derived base equality escaped \
                 the weak-eq graph) — the no-conflict flip would drop a witness"
            );
        }
        if support_empty {
            bump(&SUPPORT_EMPTY);
        } else {
            bump(&SUPPORT_NONEMPTY);
        }
        match (sc, support_empty) {
            (true, false) => bump(&SC_AND_SUPPORT_NONEMPTY),
            (true, true) => bump(&SC_AND_SUPPORT_EMPTY),
            _ => {}
        }
        match (mj, support_empty) {
            (true, false) => bump(&MJ_TRUE_SUPPORT_NONEMPTY),
            (true, true) => bump(&MJ_TRUE_SUPPORT_EMPTY),
            (false, false) => bump(&MJ_FALSE_SUPPORT_NONEMPTY),
            (false, true) => bump(&MJ_FALSE_SUPPORT_EMPTY),
        }
    }

    /// Snapshot of every counter, for the differential harness / unit tests.
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub(crate) struct Snapshot {
        pub pairs: u64,
        pub graph_pruned: u64,
        pub base_eq_holds: u64,
        pub disagree_base_eq_not_wc: u64,
        pub support_nonempty: u64,
        pub support_empty: u64,
        pub sc_and_support_nonempty: u64,
        pub sc_and_support_empty: u64,
        pub mj_true_support_nonempty: u64,
        pub mj_true_support_empty: u64,
        pub mj_false_support_nonempty: u64,
        pub mj_false_support_empty: u64,
    }

    pub(crate) fn snapshot() -> Snapshot {
        Snapshot {
            pairs: get(&PAIRS),
            graph_pruned: get(&GRAPH_PRUNED),
            base_eq_holds: get(&BASE_EQ_HOLDS),
            disagree_base_eq_not_wc: get(&DISAGREE_BASE_EQ_NOT_WC),
            support_nonempty: get(&SUPPORT_NONEMPTY),
            support_empty: get(&SUPPORT_EMPTY),
            sc_and_support_nonempty: get(&SC_AND_SUPPORT_NONEMPTY),
            sc_and_support_empty: get(&SC_AND_SUPPORT_EMPTY),
            mj_true_support_nonempty: get(&MJ_TRUE_SUPPORT_NONEMPTY),
            mj_true_support_empty: get(&MJ_TRUE_SUPPORT_EMPTY),
            mj_false_support_nonempty: get(&MJ_FALSE_SUPPORT_NONEMPTY),
            mj_false_support_empty: get(&MJ_FALSE_SUPPORT_EMPTY),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn reset() {
        for counter in [
            &PAIRS,
            &GRAPH_PRUNED,
            &BASE_EQ_HOLDS,
            &DISAGREE_BASE_EQ_NOT_WC,
            &SUPPORT_NONEMPTY,
            &SUPPORT_EMPTY,
            &SC_AND_SUPPORT_NONEMPTY,
            &SC_AND_SUPPORT_EMPTY,
            &MJ_TRUE_SUPPORT_NONEMPTY,
            &MJ_TRUE_SUPPORT_EMPTY,
            &MJ_FALSE_SUPPORT_NONEMPTY,
            &MJ_FALSE_SUPPORT_EMPTY,
        ] {
            counter.with(|c| c.set(0));
        }
    }

    /// `--weq5-shadow-dump` (B73): one-line stderr dump of the totals,
    /// so a standalone `ay` debug run over a repro reports the differential.
    /// Registered via `atexit`-style `Drop` is overkill; callers invoke it.
    pub(crate) fn maybe_dump() {
        if !ay_core::misc_cli_flags().weq5_shadow_dump {
            return;
        }
        let s = snapshot();
        eprintln!(
            "[weq5-shadow] pairs={} graph_pruned={} base_eq_holds={} \
             DISAGREE_base_eq_not_wc={} support(nonempty={},empty={}) \
             sc(nonempty={},empty={}) \
             mj(T:ne={},T:e={},F:ne={},F:e={})",
            s.pairs,
            s.graph_pruned,
            s.base_eq_holds,
            s.disagree_base_eq_not_wc,
            s.support_nonempty,
            s.support_empty,
            s.sc_and_support_nonempty,
            s.sc_and_support_empty,
            s.mj_true_support_nonempty,
            s.mj_true_support_empty,
            s.mj_false_support_nonempty,
            s.mj_false_support_empty,
        );
    }
}
