// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental difference-logic feasibility under a backtracking trail.
//!
//! [`crate::graph::DiffGraph`] re-runs a full `O(|V|·|E|)` Bellman-Ford on every
//! [`crate::graph::DiffGraph::check`]. That is the right shape for a one-shot
//! conjunctive query, but it is the wrong shape for DPLL(T), where the search
//! asserts and retracts one atom at a time and calls the theory after *every*
//! propagation. This module is the DPLL(T)-shaped engine: assert an edge, keep a
//! feasible potential function incrementally, and answer in time proportional to
//! the part of the graph the new edge actually disturbs.
//!
//! # The invariant
//!
//! An edge `from → to : w` encodes `to − from <= w` (the convention of
//! [`crate::atom`]). We maintain a *potential* `π` that is feasible for every
//! ACTIVE edge:
//!
//! ```text
//!     π(to) <= π(from) + w        for every active edge (from → to : w)
//! ```
//!
//! `π` is therefore a satisfying assignment at all times — a feasible `π` is
//! exactly a model, so SAT needs no extra work. Define an edge's **slack**
//!
//! ```text
//!     s(from → to : w) = π(from) + w − π(to)
//! ```
//!
//! The invariant says `s(e) >= 0` for every active `e`.
//!
//! # Asserting an edge (Cotton–Maler)
//!
//! To activate `e₀ = (a → b : w)`:
//!
//! * If `s(e₀) >= 0`, `π` is already feasible for it. Activation is **free** —
//!   no graph work at all. On these benchmarks most asserts take this path.
//! * Otherwise `π(b)` must decrease. Run a Dijkstra from `b` whose edge lengths
//!   are the *slacks* `s(·)`, which are non-negative by the invariant, seeded
//!   with the single negative value `D(b) = s(e₀) < 0`. Dijkstra is valid: only
//!   the source carries a negative value, every relaxation weight is `>= 0`.
//!   Settling a vertex `x` with `D(x) < 0` means `π(x)` must drop by `D(x)`.
//!
//! Around any cycle the potentials telescope away, so the summed slack equals
//! the summed edge weight. A path `b ⇝ a` of slack `S` therefore closes a cycle
//! through `e₀` of total weight `s(e₀) + S = D(a)`. Hence:
//!
//! > **the graph has a negative cycle through `e₀` iff Dijkstra settles `a` with
//! > `D(a) < 0`.**
//!
//! That is the conflict test, and the predecessor chain from `a` back to `b`
//! plus `e₀` is the cycle itself — the conflict's explanation.
//!
//! Once no unsettled vertex has `D < 0`, apply `π(x) += D(x)` to the settled
//! negative vertices; the result is feasible for every active edge including
//! `e₀`.
//!
//! # Retraction is free
//!
//! Backtracking only ever *removes* constraints, and a `π` feasible for a set of
//! edges stays feasible for any subset. So [`pop`](IncrementalDiffGraph::pop)
//! merely deactivates edges and never restores potentials — the invariant cannot
//! be violated by deletion. This is why the trail stores edge ids and nothing
//! else.
//!
//! # Soundness posture
//!
//! Every verdict is self-certified behind `debug_assert!`, matching the sibling
//! [`crate::graph`] engine: a reported conflict is re-walked and its weight
//! summed to confirm it is a genuine negative cycle, and the feasibility
//! invariant is re-checked across all active edges after each assert.

use crate::atom::Negate;
use crate::weight::Weight;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

/// One edge `from → to : weight`, i.e. the constraint `to − from <= weight`,
/// tagged with a caller-supplied identifier (in DPLL(T), the literal that
/// asserted it) so a conflict can be reported in the caller's vocabulary.
#[derive(Clone, Debug)]
pub struct IncEdge<W> {
    pub from: usize,
    pub to: usize,
    pub weight: W,
    /// Opaque caller tag, echoed back in conflict explanations.
    pub tag: u64,
}

/// Result of [`IncrementalDiffGraph::assert_edge`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssertOutcome {
    /// The edge was activated and the constraint system remains feasible.
    Consistent,
    /// Activating the edge closed a negative cycle. Carries the tags of the
    /// edges forming that cycle — a sound, and by construction cycle-minimal,
    /// explanation. The edge just asserted is included.
    Conflict(Vec<u64>),
}

/// Difference-logic constraint graph with incremental feasibility maintenance.
#[derive(Clone, Debug)]
pub struct IncrementalDiffGraph<W> {
    n: usize,
    /// Feasible potential for every active edge; doubles as the model.
    pot: Vec<W>,
    edges: Vec<IncEdge<W>>,
    /// `out[v]` = ids of edges leaving `v` (active or not).
    out: Vec<Vec<usize>>,
    /// `inc[v]` = ids of edges entering `v` (active or not); the reverse
    /// adjacency the backward Dijkstra of theory propagation walks.
    inc: Vec<Vec<usize>>,
    active: Vec<bool>,
    /// Activated edge ids, in activation order.
    trail: Vec<usize>,
    /// `trail.len()` captured at each `push`.
    level_marks: Vec<usize>,
    /// Scratch reused across asserts to avoid per-assert allocation.
    dist: Vec<Option<W>>,
    settled: Vec<bool>,
    pred: Vec<Option<usize>>,
    touched: Vec<usize>,
    /// Scratch for theory propagation: forward distances from the new edge's
    /// head, backward distances to its tail, each with predecessors so a
    /// propagation can name the path that justifies it.
    fwd: Vec<Option<W>>,
    fwd_pred: Vec<Option<usize>>,
    fwd_done: Vec<bool>,
    fwd_touched: Vec<usize>,
    bwd: Vec<Option<W>>,
    bwd_pred: Vec<Option<usize>>,
    bwd_done: Vec<bool>,
    bwd_touched: Vec<usize>,
}

/// An atom the current constraint set ENTAILS, discovered by theory
/// propagation, together with the asserted edges that justify it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entailment {
    /// The registered (currently inactive) edge that is implied.
    pub edge_id: usize,
    /// Tags of the asserted edges whose conjunction implies it. Sound by
    /// construction: they form a concrete path no longer than the atom's bound.
    pub reason: Vec<u64>,
}

impl<W: Weight + Negate> IncrementalDiffGraph<W> {
    /// An empty graph over `n_vars` vertices, all potentials zero (feasible for
    /// the empty edge set).
    pub fn new(n_vars: usize) -> Self {
        Self {
            n: n_vars,
            pot: vec![W::zero(); n_vars],
            edges: Vec::new(),
            out: vec![Vec::new(); n_vars],
            inc: vec![Vec::new(); n_vars],
            active: Vec::new(),
            trail: Vec::new(),
            level_marks: Vec::new(),
            dist: vec![None; n_vars],
            settled: vec![false; n_vars],
            pred: vec![None; n_vars],
            touched: Vec::new(),
            fwd: vec![None; n_vars],
            fwd_pred: vec![None; n_vars],
            fwd_done: vec![false; n_vars],
            fwd_touched: Vec::new(),
            bwd: vec![None; n_vars],
            bwd_pred: vec![None; n_vars],
            bwd_done: vec![false; n_vars],
            bwd_touched: Vec::new(),
        }
    }

    /// Number of vertices.
    pub fn num_vars(&self) -> usize {
        self.n
    }

    /// Grow the vertex set so index `v` exists.
    pub fn ensure_var(&mut self, v: usize) {
        if v >= self.n {
            let new_n = v + 1;
            self.pot.resize(new_n, W::zero());
            self.out.resize(new_n, Vec::new());
            self.inc.resize(new_n, Vec::new());
            self.dist.resize(new_n, None);
            self.settled.resize(new_n, false);
            self.pred.resize(new_n, None);
            self.fwd.resize(new_n, None);
            self.fwd_pred.resize(new_n, None);
            self.fwd_done.resize(new_n, false);
            self.bwd.resize(new_n, None);
            self.bwd_pred.resize(new_n, None);
            self.bwd_done.resize(new_n, false);
            self.n = new_n;
        }
    }

    /// Register the edge `to − from <= weight` WITHOUT activating it, returning
    /// its id. Registration is what makes an atom known to the engine; a
    /// registered-but-inactive edge constrains nothing.
    pub fn register_edge(&mut self, from: usize, to: usize, weight: W, tag: u64) -> usize {
        self.ensure_var(from);
        self.ensure_var(to);
        let id = self.edges.len();
        self.edges.push(IncEdge {
            from,
            to,
            weight,
            tag,
        });
        self.active.push(false);
        self.out[from].push(id);
        self.inc[to].push(id);
        id
    }

    /// The registered edges.
    pub fn edges(&self) -> &[IncEdge<W>] {
        &self.edges
    }

    /// The current potential assignment. Feasible for every active edge, hence a
    /// model of the asserted constraints.
    pub fn model(&self) -> &[W] {
        &self.pot
    }

    /// Is this edge already satisfied by the current potential, i.e. would
    /// activating it require no work?
    ///
    /// Exposed for theory-aware branching: the polarity whose edges are already
    /// satisfied is the one that keeps the constraint graph feasible, so it is
    /// the polarity a DPLL(T) search should try first.
    pub fn edge_is_satisfied(&self, id: usize) -> bool {
        debug_assert!(id < self.edges.len(), "unregistered edge id");
        self.slack(id) >= W::zero()
    }

    /// Open a backtracking level.
    pub fn push(&mut self) {
        self.level_marks.push(self.trail.len());
    }

    /// Close the innermost backtracking level, deactivating every edge asserted
    /// within it. Potentials are deliberately left alone: dropping constraints
    /// cannot invalidate a feasible potential.
    pub fn pop(&mut self) {
        let Some(mark) = self.level_marks.pop() else {
            return;
        };
        while self.trail.len() > mark {
            let id = self.trail.pop().expect("trail longer than mark");
            self.active[id] = false;
        }
    }

    /// Current backtracking depth.
    pub fn level(&self) -> usize {
        self.level_marks.len()
    }

    /// Deactivate every edge and reset to the empty state (potentials kept —
    /// still feasible for the now-empty active set).
    pub fn clear_assertions(&mut self) {
        for id in self.trail.drain(..) {
            self.active[id] = false;
        }
        self.level_marks.clear();
    }

    #[inline]
    fn sub(a: &W, b: &W) -> W {
        a.add(&b.negate())
    }

    /// Slack of edge `id` under the current potential: `π(from) + w − π(to)`.
    /// The invariant is that this is `>= 0` for every active edge.
    #[inline]
    fn slack(&self, id: usize) -> W {
        let e = &self.edges[id];
        Self::sub(&self.pot[e.from].add(&e.weight), &self.pot[e.to])
    }

    /// Activate a registered edge, restoring feasibility or reporting the
    /// negative cycle it closes.
    ///
    /// On [`AssertOutcome::Conflict`] the edge is left INACTIVE and the
    /// potentials are unchanged, so the engine stays in a consistent state that
    /// the caller may keep using after it has processed the conflict.
    pub fn assert_edge(&mut self, id: usize) -> AssertOutcome {
        debug_assert!(id < self.edges.len(), "unregistered edge id");
        if self.active[id] {
            return AssertOutcome::Consistent;
        }

        let zero = W::zero();
        let s0 = self.slack(id);
        if s0 >= zero {
            // Already satisfied by the current potential: nothing to do.
            self.active[id] = true;
            self.trail.push(id);
            debug_assert!(self.invariant_holds(), "feasibility invariant broken");
            return AssertOutcome::Consistent;
        }

        let (a, b) = {
            let e = &self.edges[id];
            (e.from, e.to)
        };

        // Dijkstra from `b` over slacks, seeded with the single negative value
        // s0. Settling `a` with a negative distance means a negative cycle.
        self.reset_scratch();
        self.dist[b] = Some(s0);
        self.touched.push(b);
        let mut heap: BinaryHeap<Reverse<(W, usize)>> = BinaryHeap::new();
        heap.push(Reverse((self.dist[b].clone().expect("just set"), b)));

        let mut cycle_at: Option<usize> = None;

        while let Some(Reverse((dx, x))) = heap.pop() {
            if self.settled[x] {
                continue;
            }
            // Stale heap entry (a better key was pushed later).
            match &self.dist[x] {
                Some(best) if *best == dx => {}
                _ => continue,
            }
            // Everything from here on is >= 0: no potential needs to move.
            if dx >= zero {
                break;
            }
            self.settled[x] = true;

            if x == a {
                // Closed a negative cycle through the new edge.
                cycle_at = Some(a);
                break;
            }

            // Walk the adjacency by index: cloning it per settled vertex costs
            // an allocation on the hottest path in the engine.
            for k in 0..self.out[x].len() {
                let eid = self.out[x][k];
                if !self.active[eid] {
                    continue;
                }
                let y = self.edges[eid].to;
                if self.settled[y] {
                    continue;
                }
                // Relax with the NON-NEGATIVE slack of the active edge, computed
                // from disjoint field borrows so no `&self` method call blocks
                // the `&mut self.dist` write below.
                let cand = {
                    let e = &self.edges[eid];
                    dx.add(
                        &self.pot[e.from]
                            .add(&e.weight)
                            .add(&self.pot[e.to].negate()),
                    )
                };
                let better = match &self.dist[y] {
                    Some(d) => &cand < d,
                    None => true,
                };
                if better {
                    if self.dist[y].is_none() {
                        self.touched.push(y);
                    }
                    self.dist[y] = Some(cand.clone());
                    self.pred[y] = Some(eid);
                    heap.push(Reverse((cand, y)));
                }
            }
        }

        if let Some(a_vertex) = cycle_at {
            // Recover the cycle as EDGE IDS and self-certify on those, THEN map
            // to tags. Certifying on tags would be wrong: tags are opaque
            // caller labels and are explicitly allowed to repeat (`x − y = c`
            // registers both of its halves under one literal), so a tag does
            // not identify an edge and its weight cannot be recovered from it.
            let cycle = self.recover_cycle_edges(a_vertex, b, id);
            debug_assert!(
                self.cycle_is_negative(&cycle),
                "reported conflict is not a negative cycle"
            );
            let tags = self.tags_of(&cycle);
            self.reset_scratch();
            return AssertOutcome::Conflict(tags);
        }

        // No conflict: apply the required decreases.
        for i in 0..self.touched.len() {
            let v = self.touched[i];
            if let Some(d) = self.dist[v].clone() {
                if d < zero {
                    self.pot[v] = self.pot[v].add(&d);
                }
            }
        }
        self.reset_scratch();

        self.active[id] = true;
        self.trail.push(id);
        debug_assert!(
            self.invariant_holds(),
            "feasibility invariant broken after assert"
        );
        AssertOutcome::Consistent
    }

    /// Clear only what this assert actually touched. A vertex is `settled` only
    /// after being popped from the heap, which requires `dist` to have been set,
    /// which requires it to be in `touched` — so `touched` covers every dirty
    /// slot and the reset stays proportional to the disturbed region rather than
    /// to `|V|`. That distinction matters: these instances have >5000 vertices
    /// and most asserts disturb a handful of them.
    fn reset_scratch(&mut self) {
        for v in self.touched.drain(..) {
            self.dist[v] = None;
            self.pred[v] = None;
            self.settled[v] = false;
        }
    }

    /// Walk predecessors from `a` back to `b` and add the closing edge `e0`,
    /// yielding the EDGE IDS of the negative cycle (`e0` first).
    fn recover_cycle_edges(&self, a: usize, b: usize, e0: usize) -> Vec<usize> {
        let mut ids = vec![e0];
        let mut cur = a;
        let mut guard = 0usize;
        while cur != b {
            let Some(eid) = self.pred[cur] else { break };
            ids.push(eid);
            cur = self.edges[eid].from;
            guard += 1;
            if guard > self.edges.len() {
                break;
            }
        }
        ids
    }

    /// The caller-visible explanation for a cycle: its edges' tags, sorted and
    /// deduplicated (several edges may legitimately carry the same tag).
    fn tags_of(&self, edge_ids: &[usize]) -> Vec<u64> {
        let mut tags: Vec<u64> = edge_ids.iter().map(|&i| self.edges[i].tag).collect();
        tags.sort_unstable();
        tags.dedup();
        tags
    }

    /// `debug_assert` support: these edges really do form a cycle of negative
    /// total weight.
    ///
    /// Weights are summed over the EDGES, never looked up by tag: tags are not
    /// unique (an `=` atom registers two edges under one tag), so a tag-keyed
    /// lookup would sum some other edge's weight and could both raise a false
    /// alarm and — worse — certify a cycle that is not actually negative.
    fn cycle_is_negative(&self, edge_ids: &[usize]) -> bool {
        if edge_ids.is_empty() {
            return false;
        }
        // 1. It must really be a CLOSED walk. In a closed walk every vertex is
        //    entered exactly as often as it is left, so in-degree equals
        //    out-degree everywhere. Checking degrees rather than the edge order
        //    keeps this independent of how the cycle happened to be recovered.
        let mut balance: std::collections::BTreeMap<usize, i64> = std::collections::BTreeMap::new();
        for &i in edge_ids {
            let e = &self.edges[i];
            *balance.entry(e.from).or_insert(0) -= 1;
            *balance.entry(e.to).or_insert(0) += 1;
        }
        if balance.values().any(|&b| b != 0) {
            return false;
        }
        // 2. And its total weight must be negative — that is what makes it a
        //    proof of infeasibility, since potentials telescope away around any
        //    cycle leaving exactly the summed edge weights.
        let mut sum = W::zero();
        for &i in edge_ids {
            sum = sum.add(&self.edges[i].weight);
        }
        sum < W::zero()
    }

    /// Theory propagation: which registered-but-unasserted atoms does the
    /// current constraint set now ENTAIL?
    ///
    /// This is the piece whose absence dominates the QF_RDL profile — 62 theory
    /// propagations against 68,138 decisions means the SAT search is
    /// rediscovering by branching what the theory could have told it outright.
    ///
    /// # Why potentials cannot answer this
    ///
    /// `π` is a *feasible* potential, not a shortest-path distance. It only
    /// guarantees `π(u) − π(v) <= δ(v,u)`, which is necessary but NOT sufficient
    /// for `δ(v,u) <= d`. Testing `model[u] − model[v] <= d` would therefore
    /// claim entailments that do not hold — an unsound propagation, and the
    /// worst possible bug. Real distances are required, so we compute them.
    ///
    /// # What is computed
    ///
    /// After asserting `e₀ = (a → b : w)`, any newly implied bound must use
    /// `e₀`, so every new path has the shape `v ⇝ a → b ⇝ u`. Two Dijkstras
    /// suffice: forward from `b`, and backward to `a` over reversed edges. Both
    /// run on SLACKS, which are `>= 0` by the invariant.
    ///
    /// Working in reduced space keeps this exact. With
    /// `Dr(x)` the forward slack-distance from `b` and `Dr'(v)` the backward
    /// slack-distance to `a`, the telescoping identities
    /// `δ(b,x) = Dr(x) − π(b) + π(x)` and `δ(v,a) = Dr'(v) − π(v) + π(a)`
    /// combine with `w = s(e₀) − π(a) + π(b)` so that the path length
    /// `δ(v,a) + w + δ(b,u)` reduces to `Dr'(v) + s(e₀) + Dr(u) − π(v) + π(u)`.
    /// The atom `u − v <= d` is therefore entailed when
    ///
    /// ```text
    ///     Dr'(v) + s(e₀) + Dr(u)  <=  d + π(v) − π(u)
    /// ```
    ///
    /// That is a *sufficient* test: it exhibits a concrete path of length `<= d`,
    /// so `δ(v,u) <= d` and the atom holds in every model of the asserted set.
    /// Missing an entailment only costs search; claiming a false one would be
    /// unsound, so the test is deliberately one-directional.
    ///
    /// `budget` caps how many vertices each Dijkstra settles. Only SETTLED
    /// distances are used — Dijkstra finalizes in nondecreasing order, so a
    /// settled value is exact while a tentative one is merely an upper bound
    /// that has not converged. Cutting the search short therefore loses
    /// propagations but can never produce a wrong one.
    pub fn entailed_after_assert(&mut self, e0: usize, budget: usize) -> Vec<Entailment> {
        debug_assert!(e0 < self.edges.len(), "unregistered edge id");
        if !self.active[e0] {
            return Vec::new();
        }
        let (a, b) = {
            let e = &self.edges[e0];
            (e.from, e.to)
        };
        let s0 = self.slack(e0);

        self.dijkstra_forward(b, budget);
        self.dijkstra_backward(a, budget);

        let mut out = Vec::new();
        for f in 0..self.edges.len() {
            if self.active[f] {
                continue;
            }
            let (v, u, d) = {
                let e = &self.edges[f];
                (e.from, e.to, e.weight.clone())
            };
            if !self.bwd_done[v] || !self.fwd_done[u] {
                continue;
            }
            let (Some(bv), Some(fu)) = (self.bwd[v].clone(), self.fwd[u].clone()) else {
                continue;
            };
            let lhs = bv.add(&s0).add(&fu);
            let rhs = d.add(&self.pot[v]).add(&self.pot[u].negate());
            if lhs <= rhs {
                let reason = self.entailment_reason(e0, v, u, a, b);
                out.push(Entailment { edge_id: f, reason });
            }
        }

        self.reset_prop_scratch();
        out
    }

    /// Tags of the concrete path `v ⇝ a → b ⇝ u` that justifies an entailment.
    fn entailment_reason(&self, e0: usize, v: usize, u: usize, a: usize, b: usize) -> Vec<u64> {
        let mut tags = vec![self.edges[e0].tag];
        // backward leg: v ⇝ a
        let mut cur = v;
        let mut guard = 0usize;
        while cur != a {
            let Some(eid) = self.bwd_pred[cur] else { break };
            tags.push(self.edges[eid].tag);
            cur = self.edges[eid].to;
            guard += 1;
            if guard > self.edges.len() {
                break;
            }
        }
        // forward leg: b ⇝ u
        let mut cur = u;
        guard = 0;
        while cur != b {
            let Some(eid) = self.fwd_pred[cur] else { break };
            tags.push(self.edges[eid].tag);
            cur = self.edges[eid].from;
            guard += 1;
            if guard > self.edges.len() {
                break;
            }
        }
        tags.sort_unstable();
        tags.dedup();
        tags
    }

    /// Dijkstra over slacks from `src`, following ACTIVE out-edges.
    fn dijkstra_forward(&mut self, src: usize, budget: usize) {
        let mut heap: BinaryHeap<Reverse<(W, usize)>> = BinaryHeap::new();
        self.fwd[src] = Some(W::zero());
        self.fwd_touched.push(src);
        heap.push(Reverse((W::zero(), src)));
        let mut settled = 0usize;
        while let Some(Reverse((dx, x))) = heap.pop() {
            if self.fwd_done[x] {
                continue;
            }
            match &self.fwd[x] {
                Some(best) if *best == dx => {}
                _ => continue,
            }
            self.fwd_done[x] = true;
            settled += 1;
            if settled > budget {
                break;
            }
            for k in 0..self.out[x].len() {
                let eid = self.out[x][k];
                if !self.active[eid] {
                    continue;
                }
                let y = self.edges[eid].to;
                if self.fwd_done[y] {
                    continue;
                }
                let cand = {
                    let e = &self.edges[eid];
                    dx.add(
                        &self.pot[e.from]
                            .add(&e.weight)
                            .add(&self.pot[e.to].negate()),
                    )
                };
                let better = match &self.fwd[y] {
                    Some(d) => &cand < d,
                    None => true,
                };
                if better {
                    if self.fwd[y].is_none() {
                        self.fwd_touched.push(y);
                    }
                    self.fwd[y] = Some(cand.clone());
                    self.fwd_pred[y] = Some(eid);
                    heap.push(Reverse((cand, y)));
                }
            }
        }
    }

    /// Dijkstra over slacks to `dst`, following ACTIVE in-edges (reverse graph).
    fn dijkstra_backward(&mut self, dst: usize, budget: usize) {
        let mut heap: BinaryHeap<Reverse<(W, usize)>> = BinaryHeap::new();
        self.bwd[dst] = Some(W::zero());
        self.bwd_touched.push(dst);
        heap.push(Reverse((W::zero(), dst)));
        let mut settled = 0usize;
        while let Some(Reverse((dx, x))) = heap.pop() {
            if self.bwd_done[x] {
                continue;
            }
            match &self.bwd[x] {
                Some(best) if *best == dx => {}
                _ => continue,
            }
            self.bwd_done[x] = true;
            settled += 1;
            if settled > budget {
                break;
            }
            for k in 0..self.inc[x].len() {
                let eid = self.inc[x][k];
                if !self.active[eid] {
                    continue;
                }
                let y = self.edges[eid].from;
                if self.bwd_done[y] {
                    continue;
                }
                let cand = {
                    let e = &self.edges[eid];
                    dx.add(
                        &self.pot[e.from]
                            .add(&e.weight)
                            .add(&self.pot[e.to].negate()),
                    )
                };
                let better = match &self.bwd[y] {
                    Some(d) => &cand < d,
                    None => true,
                };
                if better {
                    if self.bwd[y].is_none() {
                        self.bwd_touched.push(y);
                    }
                    self.bwd[y] = Some(cand.clone());
                    self.bwd_pred[y] = Some(eid);
                    heap.push(Reverse((cand, y)));
                }
            }
        }
    }

    fn reset_prop_scratch(&mut self) {
        for v in self.fwd_touched.drain(..) {
            self.fwd[v] = None;
            self.fwd_pred[v] = None;
            self.fwd_done[v] = false;
        }
        for v in self.bwd_touched.drain(..) {
            self.bwd[v] = None;
            self.bwd_pred[v] = None;
            self.bwd_done[v] = false;
        }
    }

    /// `debug_assert` support: `π` is feasible for every active edge.
    fn invariant_holds(&self) -> bool {
        let zero = W::zero();
        (0..self.edges.len())
            .filter(|i| self.active[*i])
            .all(|i| self.slack(i) >= zero)
    }
}
