// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact polynomial-time optimum for the MINIMUM VERTEX COVER class via König's
//! theorem (bipartite graphs only), with a self-certifying soundness gate.
//!
//! # The class
//!
//! A PB optimization instance is recognised as minimum vertex cover when:
//! - the objective is `min sum_v x_v` with every term a single *positive*
//!   literal of coefficient `1` (uniform unit weights), and
//! - every constraint is an edge clause `+1 x_i +1 x_j >= 1` (two distinct
//!   positive literals, `>=`, rhs `1`), and
//! - every edge endpoint appears in the objective (so picking it has unit cost —
//!   otherwise a free vertex would trivialise the problem and break the
//!   reduction).
//!
//! That is exactly: choose a minimum-weight set of vertices covering every edge.
//!
//! # Why this is an *optimum* (and why it is sound regardless of bugs here)
//!
//! For a bipartite graph König's theorem gives `|min vertex cover| = |max
//! matching|`. We compute a maximum matching `M` (Hopcroft–Karp) and the König
//! cover `C`. We then return `OptimumFound` ONLY when three independently
//! checkable facts hold:
//!
//! 1. `C` satisfies every ORIGINAL constraint (`verify_all_constraints`) — `C`
//!    is a genuine feasible vertex cover, so `|C|` is a valid UPPER bound.
//! 2. `M` is a genuine matching: its edges are pairwise vertex-disjoint and each
//!    is an actual edge of the instance — so every vertex cover must take at
//!    least one endpoint of each (disjoint) edge, making `|M|` a valid LOWER
//!    bound on the optimum.
//! 3. `eval_objective(C) == |M|`.
//!
//! `LB = |M| <= optimum <= |C| = UB` together with `|C| == |M|` forces
//! `optimum == |M|`. None of this trusts the matching/König code: a bug there
//! simply fails one of the three checks and we return `None` (fall through to the
//! general portfolio). An empty/unverified result is never a discharge — only the
//! three-way certificate is. This makes the path 0-wrong by construction.

use std::collections::VecDeque;

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// A detected min-vertex-cover instance: the edge list (as 0-indexed variable
/// pairs) plus the set of vertices that carry unit objective cost.
struct VertexCoverShape {
    /// Edges as pairs of 0-indexed variable ids (`var - 1`).
    edges: Vec<(u32, u32)>,
    /// Vertices (0-indexed) that appear in at least one edge.
    vertices: Vec<u32>,
}

/// Recognises the minimum-vertex-cover class. Returns `None` for any instance
/// that is not *exactly* this shape (the detection is intentionally strict; a
/// mismatch costs only the cheap scan and falls through to the portfolio).
fn detect_vertex_cover(instance: &PbInstance, objective: &PbObjective) -> Option<VertexCoverShape> {
    if instance.constraints.is_empty() || objective.terms.is_empty() {
        return None;
    }

    // Objective: every term is `+1 * x_v` (positive literal, coeff 1, distinct).
    let mut in_objective = vec![false; instance.num_vars as usize];
    for term in &objective.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > instance.num_vars {
            return None;
        }
        let idx = (lit.var - 1) as usize;
        if in_objective[idx] {
            // Repeated objective variable -> not the canonical unit shape.
            return None;
        }
        in_objective[idx] = true;
    }

    let mut edges: Vec<(u32, u32)> = Vec::with_capacity(instance.constraints.len());
    let mut seen = vec![false; instance.num_vars as usize];
    let mut vertices: Vec<u32> = Vec::new();

    for constraint in &instance.constraints {
        let edge = edge_of_constraint(constraint, instance.num_vars)?;
        let (a, b) = edge;
        // Both endpoints must be objective vertices (unit cost). A free endpoint
        // would let us cover edges at zero cost, breaking the VC reduction.
        if !in_objective[a as usize] || !in_objective[b as usize] {
            return None;
        }
        for v in [a, b] {
            if !seen[v as usize] {
                seen[v as usize] = true;
                vertices.push(v);
            }
        }
        edges.push(edge);
    }

    Some(VertexCoverShape { edges, vertices })
}

/// Returns the `(a, b)` 0-indexed endpoints if `constraint` is an edge clause
/// `+1 x_a +1 x_b >= 1` with two distinct positive literals; otherwise `None`.
fn edge_of_constraint(constraint: &PbConstraint, num_vars: u32) -> Option<(u32, u32)> {
    if constraint.rel != PbRel::Ge || constraint.rhs != 1 || constraint.terms.len() != 2 {
        return None;
    }
    let mut ends = [0u32; 2];
    for (slot, term) in ends.iter_mut().zip(&constraint.terms) {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > num_vars {
            return None;
        }
        *slot = lit.var - 1;
    }
    if ends[0] == ends[1] {
        return None;
    }
    Some((ends[0], ends[1]))
}

/// Attempts to solve `instance` as a bipartite minimum vertex cover. Returns a
/// certified `OptimumFound` solution, or `None` if the instance is not of the
/// class, the graph is not bipartite, or the soundness certificate fails.
pub(crate) fn try_solve(instance: &PbInstance, objective: &PbObjective) -> Option<PbSolution> {
    let shape = detect_vertex_cover(instance, objective)?;
    let n = instance.num_vars as usize;

    // Two-colour each connected component (BFS). Non-bipartite -> bail.
    let mut adjacency: Vec<Vec<u32>> = vec![Vec::new(); n];
    for &(a, b) in &shape.edges {
        adjacency[a as usize].push(b);
        adjacency[b as usize].push(a);
    }
    // color: -1 unvisited, 0 = left side, 1 = right side.
    let mut color = vec![-1i8; n];
    for &start in &shape.vertices {
        if color[start as usize] != -1 {
            continue;
        }
        color[start as usize] = 0;
        let mut queue = VecDeque::new();
        queue.push_back(start);
        while let Some(u) = queue.pop_front() {
            let cu = color[u as usize];
            for &w in &adjacency[u as usize] {
                if color[w as usize] == -1 {
                    color[w as usize] = 1 - cu;
                    queue.push_back(w);
                } else if color[w as usize] == cu {
                    // Odd cycle -> not bipartite. König does not apply.
                    return None;
                }
            }
        }
    }

    // Maximum matching via Hopcroft–Karp on the (left=color 0, right=color 1)
    // bipartition. `match_of[v]` = the partner of `v`, or `u32::MAX` if free.
    let matching = hopcroft_karp(n, &adjacency, &color);

    // König cover: Z = vertices reachable from UNMATCHED left vertices via
    // alternating paths (non-matching edges L->R, matching edges R->L). The
    // minimum vertex cover is `(L \ Z) ∪ (R ∩ Z)`.
    let mut in_z = vec![false; n];
    let mut queue = VecDeque::new();
    for &v in &shape.vertices {
        if color[v as usize] == 0 && matching[v as usize] == u32::MAX {
            in_z[v as usize] = true;
            queue.push_back(v);
        }
    }
    while let Some(u) = queue.pop_front() {
        if color[u as usize] == 0 {
            // Left vertex: follow NON-matching edges to the right.
            for &w in &adjacency[u as usize] {
                if matching[u as usize] != w && !in_z[w as usize] {
                    in_z[w as usize] = true;
                    queue.push_back(w);
                }
            }
        } else {
            // Right vertex: follow its single MATCHING edge back to the left.
            let m = matching[u as usize];
            if m != u32::MAX && !in_z[m as usize] {
                in_z[m as usize] = true;
                queue.push_back(m);
            }
        }
    }

    // Build the cover assignment: cover vertices true, everything else false.
    let mut assignment = vec![false; n];
    for &v in &shape.vertices {
        let vi = v as usize;
        let cover = (color[vi] == 0 && !in_z[vi]) || (color[vi] == 1 && in_z[vi]);
        if cover {
            assignment[vi] = true;
        }
    }

    // --- SOUNDNESS CERTIFICATE (three independent checks) ---
    // 1. The cover is feasible against the ORIGINAL constraints.
    if !verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    // 2. The matching is genuine: pairwise disjoint, symmetric, real edges.
    let matching_size = certified_matching_size(&matching, &adjacency, &color)?;
    // 3. Cover value equals the matching lower bound -> optimum.
    let value = eval_objective(objective, &assignment);
    if value != matching_size {
        return None;
    }

    Some(PbSolution {
        status: PbStatus::OptimumFound,
        assignment,
        objective: Some(value),
    })
}

/// Validates that `matching` is a real matching and returns its size, or `None`
/// if any invariant fails (symmetry, disjointness, edges that exist, left/right
/// orientation). This is the trusted check behind the `|M|` lower bound; it does
/// NOT trust how the matching was produced.
fn certified_matching_size(matching: &[u32], adjacency: &[Vec<u32>], color: &[i8]) -> Option<i128> {
    let mut count: i128 = 0;
    for (v, &partner) in matching.iter().enumerate() {
        if partner == u32::MAX {
            continue;
        }
        let vu = v as u32;
        // Symmetric pairing.
        if matching[partner as usize] != vu {
            return None;
        }
        // A real edge of the graph.
        if !adjacency[v].contains(&partner) {
            return None;
        }
        // Proper bipartite orientation (one endpoint per side).
        if color[v] == color[partner as usize] {
            return None;
        }
        // Count each undirected matched pair once.
        if vu < partner {
            count += 1;
        }
    }
    Some(count)
}

/// Hopcroft–Karp maximum bipartite matching. `color[v] == 0` denotes the left
/// side, `1` the right side; isolated/uncoloured vertices (`-1`) are ignored.
/// Returns `match_of`, where `match_of[v]` is `v`'s partner or `u32::MAX`.
fn hopcroft_karp(n: usize, adjacency: &[Vec<u32>], color: &[i8]) -> Vec<u32> {
    const NIL: u32 = u32::MAX;
    let mut match_of = vec![NIL; n];
    let mut dist = vec![0u32; n];

    loop {
        // BFS layering from all free left vertices.
        let mut queue = VecDeque::new();
        for v in 0..n {
            if color[v] == 0 {
                if match_of[v] == NIL {
                    dist[v] = 0;
                    queue.push_back(v as u32);
                } else {
                    dist[v] = u32::MAX;
                }
            }
        }
        let mut found_augmenting = false;
        while let Some(u) = queue.pop_front() {
            let du = dist[u as usize];
            for &w in &adjacency[u as usize] {
                // w is on the right; step across the matching edge to its left
                // partner (or detect a free right vertex => augmenting path).
                let m = match_of[w as usize];
                if m == NIL {
                    found_augmenting = true;
                } else if dist[m as usize] == u32::MAX {
                    dist[m as usize] = du + 1;
                    queue.push_back(m);
                }
            }
        }
        if !found_augmenting {
            break;
        }
        // DFS augment along shortest alternating paths from each free left vertex.
        for v in 0..n {
            if color[v] == 0 && match_of[v] == NIL {
                hk_dfs(v as u32, adjacency, &mut match_of, &mut dist);
            }
        }
    }
    match_of
}

/// Iterative DFS for one augmenting path in Hopcroft–Karp. Returns whether the
/// left vertex `start` was successfully matched along a shortest alternating
/// path under the current `dist` layering.
fn hk_dfs(start: u32, adjacency: &[Vec<u32>], match_of: &mut [u32], dist: &mut [u32]) -> bool {
    const NIL: u32 = u32::MAX;
    // Manual stack of (left-vertex, next adjacency index) frames.
    let mut stack: Vec<(u32, usize)> = vec![(start, 0)];
    // Parent right-vertex used to reach each frame's left vertex, for relinking.
    let mut via: Vec<u32> = vec![NIL];

    while let Some(&(u, idx)) = stack.last() {
        if idx >= adjacency[u as usize].len() {
            dist[u as usize] = u32::MAX;
            stack.pop();
            via.pop();
            continue;
        }
        // Advance this frame's cursor.
        let frame = stack.len() - 1;
        stack[frame].1 = idx + 1;
        let w = adjacency[u as usize][idx];
        let m = match_of[w as usize];
        if m == NIL {
            // Augmenting path found: relink the whole stack with right vertex w.
            let mut child_right = w;
            for k in (0..stack.len()).rev() {
                let lv = stack[k].0;
                match_of[lv as usize] = child_right;
                match_of[child_right as usize] = lv;
                child_right = via[k];
            }
            return true;
        } else if dist[m as usize] == dist[u as usize] + 1 {
            stack.push((m, 0));
            via.push(w);
        }
    }
    false
}

#[cfg(test)]
mod tests;
