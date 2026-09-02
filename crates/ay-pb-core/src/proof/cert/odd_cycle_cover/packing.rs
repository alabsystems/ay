// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Odd-cycle separation and the vertex-disjoint PACKING that supplies the
//! certificate's cuts.
//!
//! # What this computes, and why nothing here can make a proof unsound
//!
//! The emitted certificate is `Σ_C (odd-cycle cut C) + Σ_M (edge row) + literal
//! axioms`. **Any vertex-disjoint family of odd cycles and edges yields a VALID
//! proof** — the cutting-planes derivation is checked line by line either way,
//! and the literal-axiom fill lifts every objective coefficient to exactly 1
//! whatever the packing chose. A bad packing produces a WEAKER bound, and a
//! bound below the optimum is declined by the caller. So this module is an
//! OPTIMIZER, not part of the trusted core.
//!
//! What it does have to be is DETERMINISTIC, because the proof bytes are. There
//! is no wall clock, no randomness and no hash iteration order anywhere below;
//! every cap is a COUNT and every scan is in ascending vertex order. Two runs on
//! the same instance emit the same bytes, under any load.
//!
//! # The loop
//!
//! An odd closed walk through `v` is exactly a path `(v,0) -> (v,1)` in the
//! PARITY DOUBLE COVER (two copies of every vertex; every edge crosses copies),
//! so breadth-first search from `(v,0)` finds the SHORTEST one — and a shortest
//! odd closed walk is automatically simple, because a repeated vertex would
//! split it into two closed walks one of which is odd and shorter. That is a
//! proof, not an assumption, and [`shortest_odd_cycle`] still re-checks
//! simplicity before returning: this module fails closed.
//!
//! Cycles are taken greedily from the RESIDUAL graph, so disjointness is
//! structural rather than tested afterwards. Two facts keep the cost linear-ish
//! in practice:
//!
//! * a successful search deletes at least three vertices, so there are at most
//!   `V/3` successes; and
//! * a failed search proves no odd cycle passes through `v`, and deleting
//!   vertices can only destroy cycles, so that stays true forever and `v` is
//!   never searched again.
//!
//! Every pass is preceded by a 2-COLOURING of the residual, which costs
//! `O(V+E)` and skips the whole scan when no odd cycle remains at all. That is
//! what makes the BIPARTITE members of this family (`evenrowevencol...`) cost
//! zero searches instead of `V` failed ones.
//!
//! # Why the residual matching is bipartite matching
//!
//! When the odd-cycle phase stops because the residual 2-coloured, the residual
//! has no odd cycle — i.e. it IS bipartite — so Hopcroft-Karp is not a heuristic
//! there, it is the maximum matching, and König's theorem says that maximum is
//! exactly the residual's own vertex-cover optimum. Every matched edge row
//! contributes `1` to the floor with load `1` on each endpoint, which is the
//! same shape as a cycle cut and is combined identically.

use std::collections::VecDeque;

use super::CoverGraph;

/// Deterministic work caps. Every one of them is a COUNT, never a duration: a
/// clock-based cap would make the emitted bytes depend on machine load, and
/// these proofs are byte-deterministic.
#[derive(Clone, Copy, Debug)]
pub(super) struct Limits {
    /// Maximum vertices. Bounds the `O(V)` allocations the double-cover search
    /// needs, and declines a graph too large to pay for after `O(1)` recovery.
    pub(super) max_vertices: usize,
    /// Maximum separation passes (a pass is one ascending scan of the residual).
    pub(super) max_passes: usize,
    /// Maximum double-cover searches across the whole run.
    pub(super) max_searches: usize,
    /// Maximum EDGE RELAXATIONS across every double-cover search. This is the
    /// load-bearing budget: it is the currency the search actually spends, it
    /// is identical on every machine, and it bounds the pathological case (a
    /// graph with many odd cycles that the per-vertex bounds do not catch)
    /// without bounding the family this route exists for.
    pub(super) max_relaxations: u64,
}

impl Limits {
    /// The caps production runs under.
    ///
    /// `max_relaxations` is sized from measurement, not taste: the largest
    /// member of the family this route closes (`evenrowoddcol_dim_160`, 25,760
    /// vertices and 51,520 edges) spends 16.5 M relaxations, so `1 << 29` leaves
    /// 32x of headroom. Raising any of these cannot make a proof wrong, only
    /// slower; lowering them turns a certificate into a decline.
    pub(super) fn production() -> Self {
        Self {
            max_vertices: 1 << 21,
            max_passes: 64,
            max_searches: 1 << 20,
            max_relaxations: 1 << 29,
        }
    }
}

/// The packing this module produces. Cycles and matched edges are pairwise
/// VERTEX-DISJOINT by construction, so every load is `0` or `1` and the emitted
/// derivation needs no final division.
pub(super) struct Packing {
    /// One entry per cut: the VeriPB input row ids of the cycle's edges, in
    /// walk order. `ids.len()` is the cycle length and is always odd and `>= 3`.
    pub(super) cycles: Vec<Vec<u64>>,
    /// VeriPB input row ids of the matched residual edges.
    pub(super) matched: Vec<u64>,
    /// `true` for a vertex carried by some cycle or matched edge (0-indexed).
    pub(super) loaded: Vec<bool>,
    /// `Σ (L_i + 1)/2 + |matched|` — the floor this packing derives.
    pub(super) bound: i128,
    /// Edge relaxations actually spent. Diagnostics and budget reporting only;
    /// read by the tests, which assert the family's cost is well inside the cap.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) relaxations: u64,
}

/// 2-colours the residual graph. Returns `(colour, is_bipartite)`.
///
/// `colour[v]` is `0`/`1` for a live vertex and `u8::MAX` for a deleted one.
fn two_colour(graph: &CoverGraph, alive: &[bool]) -> (Vec<u8>, bool) {
    const UNSET: u8 = u8::MAX;
    let mut colour = vec![UNSET; graph.order()];
    let mut bipartite = true;
    let mut queue: VecDeque<u32> = VecDeque::new();
    for start in 0..graph.order() {
        if !alive[start] || colour[start] != UNSET {
            continue;
        }
        colour[start] = 0;
        queue.clear();
        queue.push_back(start as u32);
        while let Some(v) = queue.pop_front() {
            let here = colour[v as usize];
            for &(other, _edge) in graph.neighbours(v) {
                let other = other as usize;
                if !alive[other] {
                    continue;
                }
                if colour[other] == UNSET {
                    colour[other] = here ^ 1;
                    queue.push_back(other as u32);
                } else if colour[other] == here {
                    bipartite = false;
                }
            }
        }
    }
    (colour, bipartite)
}

/// Scratch reused across every double-cover search, so a pass allocates nothing.
struct Search {
    /// Visit stamp per double-cover node, avoiding an `O(V)` clear per search.
    stamp: Vec<u32>,
    /// Predecessor double-cover node, or `u32::MAX` at the source.
    prev: Vec<u32>,
    queue: VecDeque<u32>,
    token: u32,
    relaxations: u64,
}

impl Search {
    fn new(order: usize) -> Self {
        Self {
            stamp: vec![0; order * 2],
            prev: vec![u32::MAX; order * 2],
            queue: VecDeque::new(),
            token: 0,
            relaxations: 0,
        }
    }
}

/// Breadth-first search from `(source, 0)` to `(source, 1)` in the parity double
/// cover of the RESIDUAL graph.
///
/// Returns the cycle as an ordered vertex list, or `None` when no odd cycle
/// passes through `source` — which, because deletion only ever destroys cycles,
/// is a permanent fact about `source` and lets the caller retire it.
///
/// Fails closed: the returned walk is re-checked to be closed at `source`, of
/// ODD length `>= 3`, and SIMPLE. Shortest odd closed walks are simple as a
/// theorem, but a certifier does not run on theorems it has not checked.
fn shortest_odd_cycle(
    graph: &CoverGraph,
    alive: &[bool],
    source: u32,
    search: &mut Search,
    budget: u64,
) -> Option<Vec<u32>> {
    let start = source * 2;
    let target = source * 2 + 1;
    search.token = search.token.wrapping_add(1);
    if search.token == 0 {
        // Stamps are u32 and this run would alias them; restart the epoch.
        search.stamp.iter_mut().for_each(|s| *s = 0);
        search.token = 1;
    }
    let token = search.token;
    search.stamp[start as usize] = token;
    search.prev[start as usize] = u32::MAX;
    search.queue.clear();
    search.queue.push_back(start);
    let mut reached = false;
    while let Some(node) = search.queue.pop_front() {
        if node == target {
            reached = true;
            break;
        }
        let vertex = node >> 1;
        let parity = node & 1;
        for &(other, _edge) in graph.neighbours(vertex) {
            if !alive[other as usize] {
                continue;
            }
            search.relaxations += 1;
            if search.relaxations > budget {
                return None;
            }
            let next = other * 2 + (parity ^ 1);
            if search.stamp[next as usize] != token {
                search.stamp[next as usize] = token;
                search.prev[next as usize] = node;
                search.queue.push_back(next);
            }
        }
    }
    if !reached {
        return None;
    }
    let mut walk: Vec<u32> = Vec::new();
    let mut node = target;
    loop {
        walk.push(node >> 1);
        let parent = search.prev[node as usize];
        if parent == u32::MAX {
            break;
        }
        node = parent;
        if walk.len() > graph.order() * 2 + 2 {
            return None;
        }
    }
    walk.reverse();
    // `walk` is `[source, ..., source]`: drop the closing repeat.
    if walk.len() < 4 || walk[0] != source || *walk.last()? != source {
        return None;
    }
    walk.pop();
    if !walk.len().is_multiple_of(2) {
        // Length is odd, as an odd closed walk must be.
    } else {
        return None;
    }
    let mut sorted = walk.clone();
    sorted.sort_unstable();
    sorted.dedup();
    if sorted.len() != walk.len() {
        return None;
    }
    Some(walk)
}

/// Maximum matching on the residual, which the caller has established is
/// BIPARTITE, by Hopcroft-Karp.
///
/// The augmenting search is an EXPLICIT-STACK depth-first search rather than a
/// recursive one: a recursive Hopcroft-Karp augments to depth `O(V)`, and `V`
/// here reaches 25,760 on the family this route closes, which overflows the
/// stack on every platform this ships to.
///
/// SPENDS THE SAME RELAXATION BUDGET as the cycle search, and stops when it is
/// exhausted. Hopcroft-Karp is `O(E·sqrt(V))`, which is a different growth rate
/// from everything above it, so leaving it outside the budget would have made
/// `max_relaxations` a bound on part of the work and nothing else — and the
/// floor rungs of the OPT-LIN chain are NOT scheduled, so an unbudgeted phase
/// here has no outer deadline to stop it either. Stopping early is sound: the
/// matching is only ever a lower bound on itself, so the packing gets WEAKER,
/// and a packing that falls short of the optimum is declined by the caller.
fn hopcroft_karp(
    graph: &CoverGraph,
    alive: &[bool],
    colour: &[u8],
    spent: &mut u64,
    budget: u64,
) -> Vec<(u32, u32)> {
    const NONE: u32 = u32::MAX;
    const FAR: u32 = u32::MAX;
    let order = graph.order();
    let mut mate = vec![NONE; order];
    let left: Vec<u32> = (0..order as u32)
        .filter(|&v| alive[v as usize] && colour[v as usize] == 0)
        .collect();
    let mut dist = vec![FAR; order];
    let mut queue: VecDeque<u32> = VecDeque::new();
    // (vertex, cursor into its adjacency, the neighbour chosen at this level)
    let mut stack: Vec<(u32, u32, u32)> = Vec::new();
    loop {
        queue.clear();
        for &u in &left {
            if mate[u as usize] == NONE {
                dist[u as usize] = 0;
                queue.push_back(u);
            } else {
                dist[u as usize] = FAR;
            }
        }
        let mut augmentable = false;
        while let Some(u) = queue.pop_front() {
            for &(w, _edge) in graph.neighbours(u) {
                if !alive[w as usize] {
                    continue;
                }
                *spent += 1;
                let partner = mate[w as usize];
                if partner == NONE {
                    augmentable = true;
                } else if dist[partner as usize] == FAR {
                    dist[partner as usize] = dist[u as usize] + 1;
                    queue.push_back(partner);
                }
            }
        }
        if !augmentable || *spent > budget {
            break;
        }
        for &root in &left {
            if mate[root as usize] != NONE {
                continue;
            }
            stack.clear();
            stack.push((root, graph.adjacency_start(root), NONE));
            while let Some(&mut (u, ref mut cursor, _)) = stack.last_mut() {
                if *cursor >= graph.adjacency_end(u) {
                    dist[u as usize] = FAR;
                    stack.pop();
                    continue;
                }
                let (w, _edge) = graph.adjacency_at(*cursor);
                *cursor += 1;
                if !alive[w as usize] {
                    continue;
                }
                *spent += 1;
                let partner = mate[w as usize];
                if partner == NONE {
                    // Free vertex: re-pair every level of the alternating path.
                    if let Some(top) = stack.last_mut() {
                        top.2 = w;
                    }
                    for &(level, _cursor, chosen) in &stack {
                        mate[level as usize] = chosen;
                        mate[chosen as usize] = level;
                    }
                    stack.clear();
                    break;
                }
                if dist[partner as usize] == dist[u as usize] + 1 {
                    if let Some(top) = stack.last_mut() {
                        top.2 = w;
                    }
                    stack.push((partner, graph.adjacency_start(partner), NONE));
                }
            }
        }
    }
    let mut out: Vec<(u32, u32)> = Vec::new();
    for &u in &left {
        let w = mate[u as usize];
        if w != NONE {
            out.push((u, w));
        }
    }
    out
}

/// Builds the vertex-disjoint packing: odd cycles to exhaustion, then a maximum
/// matching on the (now bipartite) residual.
pub(super) fn build(graph: &CoverGraph, limits: Limits) -> Option<Packing> {
    let order = graph.order();
    if order == 0 || order > limits.max_vertices {
        return None;
    }
    let mut alive = vec![true; order];
    // `retired[v]` records a PROVED fact: no odd cycle passes through `v` in the
    // residual. Deletion only destroys cycles, so it never becomes false again.
    let mut retired = vec![false; order];
    let mut search = Search::new(order);
    let mut cycles: Vec<Vec<u64>> = Vec::new();
    let mut searches: usize = 0;

    for _pass in 0..limits.max_passes {
        let (_colour, bipartite) = two_colour(graph, &alive);
        if bipartite {
            break;
        }
        let mut accepted = 0usize;
        for source in 0..order as u32 {
            if !alive[source as usize] || retired[source as usize] {
                continue;
            }
            if searches >= limits.max_searches || search.relaxations >= limits.max_relaxations {
                break;
            }
            searches += 1;
            let Some(walk) =
                shortest_odd_cycle(graph, &alive, source, &mut search, limits.max_relaxations)
            else {
                retired[source as usize] = true;
                continue;
            };
            let Some(ids) = graph.walk_row_ids(&walk) else {
                // The walk is not a closed cycle of real edges. Cannot happen
                // for a BFS path, so treat it as corruption and retire rather
                // than emit anything derived from it.
                retired[source as usize] = true;
                continue;
            };
            for &v in &walk {
                alive[v as usize] = false;
            }
            cycles.push(ids);
            accepted += 1;
        }
        if accepted == 0 {
            break;
        }
    }

    let (colour, bipartite) = two_colour(graph, &alive);
    let mut matched: Vec<u64> = Vec::new();
    let mut loaded = vec![false; order];
    if bipartite {
        for (u, w) in hopcroft_karp(
            graph,
            &alive,
            &colour,
            &mut search.relaxations,
            limits.max_relaxations,
        ) {
            let id = graph.edge_row_between(u, w)?;
            matched.push(id);
            loaded[u as usize] = true;
            loaded[w as usize] = true;
        }
    }
    // Cycle vertices carry load 1 too; recovered from `alive` so the load vector
    // and the emitted cuts cannot disagree.
    for v in 0..order {
        if !alive[v] {
            loaded[v] = true;
        }
    }
    let mut bound: i128 = 0;
    for ids in &cycles {
        let length = i128::try_from(ids.len()).ok()?;
        bound = bound.checked_add(length.checked_add(1)? / 2)?;
    }
    bound = bound.checked_add(i128::try_from(matched.len()).ok()?)?;
    Some(Packing {
        cycles,
        matched,
        loaded,
        bound,
        relaxations: search.relaxations,
    })
}
