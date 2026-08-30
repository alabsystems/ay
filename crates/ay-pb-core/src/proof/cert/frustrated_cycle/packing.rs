// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frustrated-cycle separation and the fractional cycle PACKING that supplies
//! the certificate's multipliers.
//!
//! # What this computes, and why nothing here can make a proof unsound
//!
//! The emitted certificate is `Σ_C λ_C · (cycle cut C)` plus literal-axiom slack
//! fill, divided by the common denominator. **Any non-negative λ with edge loads
//! bounded by the denominator yields a VALID proof** — the cutting-planes
//! derivation is checked line by line either way. A bad packing produces a
//! WEAKER bound, and a bound below the optimum is declined by the caller. So
//! this module is an OPTIMIZER, not part of the trusted core: it is allowed to
//! use floating point, and it does.
//!
//! What it does have to be is DETERMINISTIC, because the proof bytes are. There
//! is no wall clock, no randomness from the environment and no hash iteration
//! order anywhere below; the diversification jitter is a fixed LCG. Two runs on
//! the same instance emit the same bytes.
//!
//! # The loop
//!
//! Frustrated cycles are separated exactly in the signed DOUBLE COVER: two
//! copies of every node, a DIFFER edge crosses copies and an EQUAL edge does
//! not, so a frustrated closed walk through `v` is exactly a path
//! `(v,0) -> (v,1)`. Dijkstra under the current edge prices finds the cheapest
//! one per source; a violated closed walk is decomposed into simple cycles and
//! the frustrated ones are kept.
//!
//! The prices come from the PACKING LP itself. `max Σ λ_C  s.t. Σ_{C ∋ e} λ_C
//! <= 1` has one row per edge and one column per pooled cycle; its DUAL is the
//! fractional cycle COVER `min Σ x_e  s.t. x(C) >= 1`, and the dual vector is
//! precisely the next round's separation weights. So one revised simplex serves
//! both halves of the column-generation loop and the pool converges when
//! separation finds nothing new.
//!
//! # Why a simplex and not a multiplicative-weights scheme
//!
//! Measured, on `macrophage`: the converged cycle relaxation is `1120/3 =
//! 373.333…` against an optimum of `374`, so a packing must land in
//! `(373, 373.334]` — a relative accuracy of 0.09 %. Garg-Könemann and friends
//! need `O(m log m / ε²)` oracle calls for that, which is `~10^10` shortest-path
//! computations here. There is nothing to spare in this family and an
//! approximation scheme cannot pay for it.

use std::cmp::Ordering;
use std::collections::BinaryHeap;

use super::SignedGraph;

/// Deterministic work caps. Every one of them is a COUNT, never a duration:
/// a clock-based cap would make the emitted bytes depend on machine load, and
/// these proofs are byte-deterministic.
#[derive(Clone, Copy, Debug)]
pub(super) struct Limits {
    /// Maximum number of 2-core edges, i.e. rows of the packing LP. The revised
    /// simplex carries an explicit `m × m` basis inverse, so this is what bounds
    /// its memory and its per-pivot cost.
    pub(super) max_rows: usize,
    /// Maximum number of separated cycles kept (columns of the packing LP).
    pub(super) max_pool: usize,
    /// Maximum column-generation rounds.
    pub(super) max_rounds: usize,
    /// Maximum simplex pivots across the whole run.
    pub(super) max_pivots: usize,
}

impl Limits {
    /// The caps production runs under.
    ///
    /// `max_rows` is the load-bearing one. It is set so the family member this
    /// route CAN close (`macrophage`, 1,582 edges) fits with headroom, and the
    /// one it cannot (`methanosarcina`, 7,302 edges, where the same cut family
    /// reaches 540 against an incumbent of 2,730) is declined after O(rows)
    /// recovery instead of after minutes of simplex that would end in a decline
    /// anyway. Raising it does not make a proof wrong, only slower.
    pub(super) fn production() -> Self {
        Self {
            max_rows: 4096,
            max_pool: 24_000,
            max_rounds: 600,
            max_pivots: 200_000,
        }
    }
}

/// A simple frustrated cycle, as an ordered walk `(edge index, node it is
/// entered from)`. The order is what the derivation walks; the edge SET is what
/// the packing constrains.
pub(super) type Walk = Vec<(usize, usize)>;

/// The packing this module produces: cycles with integer numerators over a
/// common denominator, already checked to load no edge above the denominator.
pub(super) struct Packing {
    pub(super) walks: Vec<Walk>,
    pub(super) numerators: Vec<i128>,
    pub(super) denominator: i128,
    /// `Σ numerators`; the derived floor is `ceil(total / denominator)`.
    pub(super) total: i128,
    /// Per-edge load `Σ_{C ∋ e} numerator_C`, indexed by edge.
    pub(super) load: Vec<i128>,
}

// ---------------------------------------------------------------------------
// The 2-core: the only edges that can carry a cycle.
// ---------------------------------------------------------------------------

/// Edges that survive iterated removal of degree-1 nodes.
///
/// A bridge lies on no cycle, so it can appear in no cut and its packing dual is
/// zero. Dropping bridges is a pure speed reduction — it removes rows the LP
/// would leave at their slack — and on signal-transduction networks, which hang
/// long trees off a small core, it removes most of them.
pub(super) fn two_core(graph: &SignedGraph) -> Vec<bool> {
    let mut degree = vec![0usize; graph.nodes.len()];
    for edge in &graph.edges {
        degree[edge.u] += 1;
        degree[edge.v] += 1;
    }
    let mut alive = vec![true; graph.edges.len()];
    let mut queue: Vec<usize> = (0..graph.nodes.len()).filter(|&n| degree[n] <= 1).collect();
    let mut incident: Vec<Vec<usize>> = vec![Vec::new(); graph.nodes.len()];
    for (index, edge) in graph.edges.iter().enumerate() {
        incident[edge.u].push(index);
        incident[edge.v].push(index);
    }
    while let Some(node) = queue.pop() {
        for &index in &incident[node] {
            if !alive[index] {
                continue;
            }
            alive[index] = false;
            let edge = &graph.edges[index];
            for endpoint in [edge.u, edge.v] {
                degree[endpoint] -= 1;
                if degree[endpoint] == 1 {
                    queue.push(endpoint);
                }
            }
        }
    }
    alive
}

// ---------------------------------------------------------------------------
// Separation in the signed double cover.
// ---------------------------------------------------------------------------

/// A heap entry ordered by distance then by node then by layer, so ties break
/// identically on every run.
#[derive(PartialEq)]
struct Entry(f64, usize, u8);

impl Eq for Entry {}

impl Ord for Entry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reversed: `BinaryHeap` is a max-heap and this is a shortest-path queue.
        other
            .0
            .partial_cmp(&self.0)
            .unwrap_or(Ordering::Equal)
            .then_with(|| other.1.cmp(&self.1))
            .then_with(|| other.2.cmp(&self.2))
    }
}

impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Adjacency of the signed double cover, built once.
struct Cover {
    /// `adj[2*node + layer]` -> `(other node, other layer, edge index)`.
    adj: Vec<Vec<(usize, u8, usize)>>,
}

impl Cover {
    fn build(graph: &SignedGraph, alive: &[bool]) -> Self {
        let mut adj = vec![Vec::new(); graph.nodes.len() * 2];
        for (index, edge) in graph.edges.iter().enumerate() {
            if !alive[index] {
                continue;
            }
            let cross = u8::from(edge.differ);
            for layer in 0u8..2 {
                adj[edge.u * 2 + usize::from(layer)].push((edge.v, layer ^ cross, index));
                adj[edge.v * 2 + usize::from(layer)].push((edge.u, layer ^ cross, index));
            }
        }
        Self { adj }
    }
}

/// Decomposes a closed walk into simple cycles and keeps the FRUSTRATED ones.
///
/// A shortest violated closed walk need not be simple, but every violated closed
/// walk of non-negative weight contains a violated simple frustrated cycle: the
/// walk's frustration is the parity sum of its pieces, so an odd walk has an odd
/// piece, and that piece is no heavier than the walk.
fn decompose(seq: &[(usize, usize)], graph: &SignedGraph, out: &mut Vec<Vec<usize>>) {
    let mut position: Vec<Option<usize>> = vec![None; graph.nodes.len()];
    let mut current: Vec<(usize, usize)> = Vec::new();
    let mut pieces: Vec<Vec<(usize, usize)>> = Vec::new();
    for &(edge, node) in seq {
        if let Some(start) = position[node] {
            let piece: Vec<(usize, usize)> = current.split_off(start);
            for &(_, visited) in &piece {
                position[visited] = None;
            }
            if !piece.is_empty() {
                pieces.push(piece);
            }
        }
        position[node] = Some(current.len());
        current.push((edge, node));
    }
    if !current.is_empty() {
        pieces.push(current);
    }
    for piece in pieces {
        let edges: Vec<usize> = piece.iter().map(|&(edge, _)| edge).collect();
        if edges.len() < 2 {
            continue;
        }
        let mut sorted = edges.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != edges.len() {
            continue;
        }
        if edges.iter().filter(|&&e| graph.edges[e].differ).count() % 2 == 1 {
            out.push(edges);
        }
    }
}

/// One separation sweep: the cheapest frustrated closed walk through each node
/// under prices `x`, decomposed into simple frustrated cycles.
fn separate(graph: &SignedGraph, cover: &Cover, x: &[f64], out: &mut Vec<Vec<usize>>) {
    const LIMIT: f64 = 1.0 - 1e-7;
    let nodes = graph.nodes.len();
    let mut dist = vec![f64::INFINITY; nodes * 2];
    let mut prev: Vec<Option<(usize, u8, usize)>> = vec![None; nodes * 2];
    let mut touched: Vec<usize> = Vec::new();
    for source in 0..nodes {
        if cover.adj[source * 2].is_empty() {
            continue;
        }
        for &slot in &touched {
            dist[slot] = f64::INFINITY;
            prev[slot] = None;
        }
        touched.clear();
        let start = source * 2;
        let target = source * 2 + 1;
        dist[start] = 0.0;
        touched.push(start);
        let mut heap = BinaryHeap::new();
        heap.push(Entry(0.0, source, 0));
        let mut reached = false;
        while let Some(Entry(d, node, layer)) = heap.pop() {
            let slot = node * 2 + usize::from(layer);
            if d > dist[slot] {
                continue;
            }
            if slot == target {
                reached = true;
                break;
            }
            if d >= LIMIT {
                break;
            }
            for &(other, other_layer, edge) in &cover.adj[slot] {
                let next = d + x[edge];
                let other_slot = other * 2 + usize::from(other_layer);
                if next < dist[other_slot] - 1e-12 {
                    if dist[other_slot].is_infinite() {
                        touched.push(other_slot);
                    }
                    dist[other_slot] = next;
                    prev[other_slot] = Some((node, layer, edge));
                    heap.push(Entry(next, other, other_layer));
                }
            }
        }
        if !reached || dist[target] >= LIMIT {
            continue;
        }
        let mut seq: Vec<(usize, usize)> = Vec::new();
        let mut slot = target;
        while slot != start {
            let Some((from, from_layer, edge)) = prev[slot] else {
                break;
            };
            seq.push((edge, from));
            slot = from * 2 + usize::from(from_layer);
        }
        seq.reverse();
        decompose(&seq, graph, out);
    }
}

/// Orders a cycle given as an unordered edge set into the walk the derivation
/// needs, or `None` if the set is not a simple frustrated cycle.
///
/// This is a REJECTING re-check, not a convenience: the derivation is only valid
/// for a closed walk in which every node has degree exactly two and the DIFFER
/// count is odd, so anything the separator produced that does not satisfy that
/// is dropped here rather than emitted.
pub(super) fn order_cycle(graph: &SignedGraph, edges: &[usize]) -> Option<Walk> {
    if edges.len() < 2 {
        return None;
    }
    let mut degree: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for &edge in edges {
        let e = &graph.edges[edge];
        for end in [e.u, e.v] {
            *degree.entry(end).or_insert(0) += 1;
        }
    }
    if degree.values().any(|&d| d != 2) {
        return None;
    }
    if edges.iter().filter(|&&e| graph.edges[e].differ).count() % 2 == 0 {
        return None;
    }
    let start = graph.edges[edges[0]].u;
    let mut used = vec![false; edges.len()];
    let mut walk: Walk = Vec::with_capacity(edges.len());
    let mut current = start;
    loop {
        let mut advanced = false;
        for (slot, &edge) in edges.iter().enumerate() {
            if used[slot] {
                continue;
            }
            let e = &graph.edges[edge];
            let other = if e.u == current {
                e.v
            } else if e.v == current {
                e.u
            } else {
                continue;
            };
            used[slot] = true;
            walk.push((edge, current));
            current = other;
            advanced = true;
            break;
        }
        if !advanced || current == start {
            break;
        }
    }
    if walk.len() != edges.len() || current != start {
        return None;
    }
    Some(walk)
}

// ---------------------------------------------------------------------------
// The packing LP: a revised simplex with an explicit basis inverse.
// ---------------------------------------------------------------------------

/// `max 1ᵀλ  s.t.  Aλ + s = 1,  λ,s >= 0`, with columns generated on the fly.
///
/// Explicit `B⁻¹` rather than an LU factorization: the basis is `m × m` with
/// `m <= max_rows`, columns are extremely sparse (a cycle has a handful of
/// edges) and the whole solve is one-shot.
///
/// AN EXPLICIT INVERSE DRIFTS, AND ON THIS INSTANCE IT DOES. Measured on
/// `macrophage` (1,551 rows): with a naive ratio test the packing climbed
/// cleanly to 371.03 over 47 column-generation rounds in 7.5 s, then a pivot on
/// an element of order `1e-9` amplified `B⁻¹` until the reported LP value was
/// `7.25e52`, and the run spent its remaining 395,726 pivots there. Two things
/// keep that from mattering:
///
/// * the ratio test breaks near-ties by the LARGEST pivot element, which is what
///   stops the amplification happening in the first place; and
/// * [`Simplex::health`] re-derives `x_B = B⁻¹·1` from the inverse every few
///   dozen pivots and stops the solve when it disagrees with the incrementally
///   maintained values, so a drifting basis is DETECTED rather than trusted.
///
/// The caller keeps the last verified-feasible primal as a snapshot, so the
/// packing that reaches the emitter is always one whose loads were checked. And
/// even if all of that failed, drift could still only produce a WORSE packing:
/// the numerators are re-verified in exact integer arithmetic afterwards and a
/// violated edge load declines.
struct Simplex {
    rows: usize,
    /// Column supports (row indices), one per generated cycle.
    columns: Vec<Vec<usize>>,
    /// Basic column per row: `Some(j)` for cycle `j`, `None` for that row's slack.
    basis: Vec<Option<usize>>,
    /// Row-major `rows × rows` basis inverse.
    binv: Vec<f64>,
    /// Basic variable values, maintained incrementally.
    xb: Vec<f64>,
    pivots: usize,
    /// Set once the basis inverse has been caught drifting; no further pivot is
    /// taken and the caller falls back on its last verified snapshot.
    unhealthy: bool,
}

impl Simplex {
    fn new(rows: usize) -> Self {
        let mut binv = vec![0.0; rows * rows];
        for i in 0..rows {
            binv[i * rows + i] = 1.0;
        }
        Self {
            rows,
            columns: Vec::new(),
            basis: vec![None; rows],
            binv,
            xb: vec![1.0; rows],
            pivots: 0,
            unhealthy: false,
        }
    }

    /// Dual prices `y = c_Bᵀ B⁻¹`. `c_B` is 1 on basic cycle columns and 0 on
    /// basic slacks, so this is a sum of the corresponding `B⁻¹` rows.
    fn duals(&self) -> Vec<f64> {
        let mut y = vec![0.0; self.rows];
        for (row, basic) in self.basis.iter().enumerate() {
            if basic.is_none() {
                continue;
            }
            let base = row * self.rows;
            for (slot, value) in y.iter_mut().enumerate() {
                *value += self.binv[base + slot];
            }
        }
        y
    }

    /// `B⁻¹ A_q` for a cycle column (sum of `B⁻¹` columns over its support).
    fn column_direction(&self, support: &[usize], out: &mut [f64]) {
        out.fill(0.0);
        for row in 0..self.rows {
            let base = row * self.rows;
            let mut acc = 0.0;
            for &slot in support {
                acc += self.binv[base + slot];
            }
            out[row] = acc;
        }
    }

    /// `B⁻¹ e_slot` for a slack column.
    fn slack_direction(&self, slot: usize, out: &mut [f64]) {
        for row in 0..self.rows {
            out[row] = self.binv[row * self.rows + slot];
        }
    }

    /// Re-derives `x_B = B⁻¹ · 1` straight from the inverse and compares it with
    /// the incrementally maintained vector. They are the same quantity computed
    /// two ways, so a disagreement is exactly the accumulated round-off — the
    /// signal that the inverse can no longer be trusted.
    fn health(&mut self) -> bool {
        const DRIFT_TOL: f64 = 1e-6;
        for row in 0..self.rows {
            let base = row * self.rows;
            let mut sum = 0.0;
            for slot in 0..self.rows {
                sum += self.binv[base + slot];
            }
            if !sum.is_finite() || sum < -DRIFT_TOL || (sum - self.xb[row]).abs() > DRIFT_TOL {
                self.unhealthy = true;
                return false;
            }
            self.xb[row] = sum;
        }
        true
    }

    fn pivot(&mut self, leaving_row: usize, entering: Option<usize>, direction: &[f64]) {
        let rows = self.rows;
        let scale = direction[leaving_row];
        let base = leaving_row * rows;
        for slot in 0..rows {
            self.binv[base + slot] /= scale;
        }
        let theta = self.xb[leaving_row] / scale;
        for row in 0..rows {
            if row == leaving_row {
                continue;
            }
            let factor = direction[row];
            if factor == 0.0 {
                continue;
            }
            let target = row * rows;
            for slot in 0..rows {
                self.binv[target + slot] -= factor * self.binv[base + slot];
            }
            self.xb[row] -= factor * theta;
        }
        self.xb[leaving_row] = theta;
        self.basis[leaving_row] = entering;
        self.pivots += 1;
    }

    /// Runs primal simplex to optimality, pricing every generated column plus
    /// every slack. Stops at the global `max_pivots`, at this call's own
    /// `budget`, or the moment the basis inverse fails its health check.
    fn solve(&mut self, max_pivots: usize, budget: usize) {
        const PRICE_TOL: f64 = 1e-9;
        // Well above the `1e-9` element that destroyed the inverse in the
        // measurement recorded on this type.
        const PIVOT_TOL: f64 = 1e-7;
        const HEALTH_EVERY: usize = 64;
        let deadline = self.pivots.saturating_add(budget);
        let mut direction = vec![0.0; self.rows];
        let mut in_basis: Vec<bool> = Vec::new();
        loop {
            if self.unhealthy || self.pivots >= max_pivots || self.pivots >= deadline {
                return;
            }
            in_basis.clear();
            in_basis.resize(self.columns.len(), false);
            let mut slack_basic = vec![false; self.rows];
            for (row, basic) in self.basis.iter().enumerate() {
                match basic {
                    Some(j) => in_basis[*j] = true,
                    None => slack_basic[row] = true,
                }
            }
            let y = self.duals();
            let mut best: Option<(f64, Option<usize>, usize)> = None;
            for (j, support) in self.columns.iter().enumerate() {
                if in_basis[j] {
                    continue;
                }
                let mut reduced = 1.0;
                for &slot in support {
                    reduced -= y[slot];
                }
                if reduced > PRICE_TOL && best.as_ref().is_none_or(|(b, _, _)| reduced > *b) {
                    best = Some((reduced, Some(j), j));
                }
            }
            for (slot, &basic) in slack_basic.iter().enumerate() {
                if basic {
                    continue;
                }
                let reduced = -y[slot];
                if reduced > PRICE_TOL && best.as_ref().is_none_or(|(b, _, _)| reduced > *b) {
                    best = Some((reduced, None, slot));
                }
            }
            let Some((_, entering, key)) = best else {
                return;
            };
            match entering {
                Some(j) => {
                    let support = self.columns[j].clone();
                    self.column_direction(&support, &mut direction);
                }
                None => self.slack_direction(key, &mut direction),
            }
            // TWO-PASS RATIO TEST. The first pass finds the limiting ratio; the
            // second picks, among the rows within `TIE_TOL` of it, the one with
            // the LARGEST pivot element. Dividing a row of `B⁻¹` by a pivot of
            // order `1e-9` is what destroyed the inverse in the measurement
            // above, and every degenerate vertex here offers a choice — so
            // taking the biggest available pivot costs one extra pass and buys
            // the whole solve.
            const TIE_TOL: f64 = 1e-9;
            let mut limit = f64::INFINITY;
            for row in 0..self.rows {
                if direction[row] <= PIVOT_TOL {
                    continue;
                }
                let ratio = (self.xb[row] / direction[row]).max(0.0);
                if ratio < limit {
                    limit = ratio;
                }
            }
            if !limit.is_finite() {
                // Unbounded is impossible here (`λ_C <= 1` for every column);
                // treat it as a numerical failure and stop with what we have.
                return;
            }
            let mut leaving: Option<(f64, usize)> = None;
            for row in 0..self.rows {
                if direction[row] <= PIVOT_TOL {
                    continue;
                }
                let ratio = (self.xb[row] / direction[row]).max(0.0);
                if ratio <= limit + TIE_TOL && leaving.is_none_or(|(best, _)| direction[row] > best)
                {
                    leaving = Some((direction[row], row));
                }
            }
            let Some((_, row)) = leaving else {
                return;
            };
            self.pivot(row, entering, &direction);
            if self.pivots.is_multiple_of(HEALTH_EVERY) && !self.health() {
                return;
            }
        }
    }

    /// The primal solution over the cycle columns, but ONLY if it is finite and
    /// genuinely feasible for the packing constraints when re-checked directly
    /// against the columns. This is the gate the caller's snapshot is taken
    /// through, so a basis that has drifted can never be the one that reaches
    /// the emitter.
    fn verified_primal(&self) -> Option<(Vec<f64>, f64)> {
        const FEAS_TOL: f64 = 1e-6;
        let lambda = self.primal();
        let mut load = vec![0.0f64; self.rows];
        let mut value = 0.0f64;
        for (j, weight) in lambda.iter().enumerate() {
            if !weight.is_finite() || *weight < -FEAS_TOL {
                return None;
            }
            value += weight;
            for &slot in &self.columns[j] {
                load[slot] += weight;
            }
        }
        if !value.is_finite() || load.iter().any(|&v| v > 1.0 + FEAS_TOL) {
            return None;
        }
        Some((lambda, value))
    }

    /// The primal solution over the cycle columns.
    fn primal(&self) -> Vec<f64> {
        let mut lambda = vec![0.0; self.columns.len()];
        for (row, basic) in self.basis.iter().enumerate() {
            if let Some(j) = basic {
                lambda[*j] = self.xb[row].max(0.0);
            }
        }
        lambda
    }
}

// ---------------------------------------------------------------------------
// Driver: column generation, then rounding onto a 1/D grid.
// ---------------------------------------------------------------------------

/// The denominators tried, in order. The first that reaches the target bound
/// wins, so the ladder is a determinism-preserving way to keep the proof small
/// when a coarse grid suffices and still close the instance when it does not.
///
/// Every entry is highly composite: rounding loss is at most `support / D`, and
/// a packing basis here has a few hundred nonzeros.
const DENOMINATORS: [i128; 6] = [12, 60, 360, 2520, 20_160, 720_720];

/// Rounds `lambda` onto a `1/denominator` grid and repairs greedily.
///
/// Rounding DOWN is what keeps this sound: the load of the rounded packing is
/// pointwise below the fractional one, hence below the denominator. The repair
/// then raises numerators while every incident edge stays within budget, which
/// recovers most of the loss and can only increase the bound.
fn round_and_repair(
    lambda: &[f64],
    columns: &[Vec<usize>],
    rows: usize,
    denominator: i128,
) -> Option<(Vec<i128>, Vec<i128>, i128)> {
    // `numerators` is indexed by column below; a caller that hands over a
    // shorter weight vector gets a decline, not an out-of-bounds panic.
    if lambda.len() != columns.len() {
        return None;
    }
    let scale = denominator as f64;
    let mut numerators: Vec<i128> = Vec::with_capacity(lambda.len());
    for &value in lambda {
        let scaled = (value * scale).floor();
        if !scaled.is_finite() || scaled < 0.0 {
            numerators.push(0);
        } else {
            numerators.push(scaled as i128);
        }
    }
    let mut load = vec![0i128; rows];
    for (j, support) in columns.iter().enumerate() {
        if numerators[j] == 0 {
            continue;
        }
        for &slot in support {
            load[slot] = load[slot].checked_add(numerators[j])?;
        }
    }
    // Rounding down cannot overshoot, but a numerically drifted `lambda` can:
    // shed the offenders rather than trust the LP.
    for j in 0..numerators.len() {
        if numerators[j] == 0 {
            continue;
        }
        let over = columns[j].iter().any(|&slot| load[slot] > denominator);
        if over {
            for &slot in &columns[j] {
                load[slot] -= numerators[j];
            }
            numerators[j] = 0;
        }
    }
    if load.iter().any(|&value| value > denominator) {
        return None;
    }
    loop {
        let mut improved = false;
        for (j, support) in columns.iter().enumerate() {
            let room = support
                .iter()
                .map(|&slot| denominator - load[slot])
                .min()
                .unwrap_or(0);
            if room > 0 {
                numerators[j] = numerators[j].checked_add(room)?;
                for &slot in support {
                    load[slot] += room;
                }
                improved = true;
            }
        }
        if !improved {
            break;
        }
    }
    if load.iter().any(|&value| value > denominator) {
        return None;
    }
    let mut total: i128 = 0;
    for &value in &numerators {
        total = total.checked_add(value)?;
    }
    Some((numerators, load, total))
}

/// Separates frustrated cycles to convergence and returns the rounded packing
/// whose floor is `>= target`, or the best one found if none reaches it.
///
/// `target` is the optimum the caller wants certified; the denominator ladder
/// stops at the first grid that reaches it.
pub(super) fn build(graph: &SignedGraph, target: i128, limits: Limits) -> Option<Packing> {
    let alive = two_core(graph);
    let active: Vec<usize> = (0..graph.edges.len()).filter(|&e| alive[e]).collect();
    if active.is_empty() || active.len() > limits.max_rows {
        return None;
    }
    let mut slot_of = vec![usize::MAX; graph.edges.len()];
    for (slot, &edge) in active.iter().enumerate() {
        slot_of[edge] = slot;
    }
    let rows = active.len();

    let cover = Cover::build(graph, &alive);
    let mut simplex = Simplex::new(rows);
    let mut walks: Vec<Walk> = Vec::new();
    let mut seen: std::collections::BTreeSet<Vec<usize>> = std::collections::BTreeSet::new();
    let mut prices = vec![0.0f64; graph.edges.len()];
    // A fixed LCG, used only to diversify separation. Deterministic by
    // construction: same instance, same jitter, same proof bytes.
    let mut lcg: u64 = 0x2545_f491_4f6c_dd1d;
    // The last primal that passed [`Simplex::verified_primal`]. Column
    // generation only ever moves this UP, so a late numerical failure costs the
    // improvement of one round rather than the whole run.
    let mut best_lambda: Vec<f64> = Vec::new();
    let mut best_value = 0.0f64;
    // Per-call pivot budget. The observed worst round on `macrophage` needed
    // 470 pivots; this leaves an order of magnitude of headroom while making it
    // impossible for one stalled solve to consume the global budget.
    let per_solve = 4_000 + rows;

    for round in 0..limits.max_rounds {
        let mut found: Vec<Vec<usize>> = Vec::new();
        separate(graph, &cover, &prices, &mut found);
        if round % 3 == 2 {
            let mut jittered = prices.clone();
            for value in &mut jittered {
                lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let unit = ((lcg >> 11) as f64) / ((1u64 << 53) as f64);
                *value = (*value + (unit - 0.5) * 0.5).clamp(0.0, 1.0);
            }
            separate(graph, &cover, &jittered, &mut found);
        }
        let mut added = 0usize;
        for cycle in found {
            if walks.len() >= limits.max_pool {
                break;
            }
            if cycle.iter().any(|&e| !alive[e]) {
                continue;
            }
            let mut key = cycle.clone();
            key.sort_unstable();
            if seen.contains(&key) {
                continue;
            }
            let Some(walk) = order_cycle(graph, &cycle) else {
                continue;
            };
            seen.insert(key);
            let support: Vec<usize> = {
                let mut support: Vec<usize> = cycle.iter().map(|&e| slot_of[e]).collect();
                support.sort_unstable();
                support
            };
            simplex.columns.push(support);
            walks.push(walk);
            added += 1;
        }
        if added == 0 {
            break;
        }
        simplex.solve(limits.max_pivots, per_solve);
        match simplex.verified_primal() {
            Some((lambda, value)) if value > best_value => {
                best_value = value;
                best_lambda = lambda;
            }
            Some(_) => {}
            None => {
                // The basis inverse is no longer trustworthy. Stop generating
                // and emit from the last snapshot that WAS verified feasible.
                break;
            }
        }
        let y = simplex.duals();
        for (edge, price) in prices.iter_mut().enumerate() {
            *price = if slot_of[edge] == usize::MAX {
                1.0
            } else {
                y[slot_of[edge]].max(0.0)
            };
        }
        if simplex.pivots >= limits.max_pivots || simplex.unhealthy {
            break;
        }
    }
    // One last solve after the final round's columns, then the snapshot rule one
    // more time: the packing that reaches the emitter is always one whose loads
    // were re-checked directly against the columns.
    simplex.solve(limits.max_pivots, per_solve);
    if let Some((lambda, value)) = simplex.verified_primal() {
        if value > best_value {
            best_lambda = lambda;
        }
    }

    // The snapshot was taken at some earlier round, so it can be SHORTER than
    // the column set that later rounds grew — a column generated after the last
    // verified solve simply carries weight zero. Padding here is what keeps
    // `numerators` and `columns` index-parallel; without it `round_and_repair`
    // indexes past the end of the numerators the moment a late solve fails
    // verification, which is exactly the run that most needs to fall back
    // gracefully.
    let mut lambda = best_lambda;
    lambda.resize(simplex.columns.len(), 0.0);
    let mut best: Option<Packing> = None;
    for &denominator in &DENOMINATORS {
        let Some((numerators, load_active, total)) =
            round_and_repair(&lambda, &simplex.columns, rows, denominator)
        else {
            continue;
        };
        let floor = total.div_euclid(denominator) + i128::from(total.rem_euclid(denominator) != 0);
        let mut load = vec![0i128; graph.edges.len()];
        for (slot, &edge) in active.iter().enumerate() {
            load[edge] = load_active[slot];
        }
        let packing = Packing {
            walks: walks.clone(),
            numerators,
            denominator,
            total,
            load,
        };
        let better = best
            .as_ref()
            .is_none_or(|current| floor_of(current) < floor);
        if better {
            best = Some(packing);
        }
        if floor >= target {
            break;
        }
    }
    best
}

/// `ceil(total / denominator)` — the bound a packing derives.
pub(super) fn floor_of(packing: &Packing) -> i128 {
    packing.total.div_euclid(packing.denominator)
        + i128::from(packing.total.rem_euclid(packing.denominator) != 0)
}
