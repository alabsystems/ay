// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact UNSAT for the bipartite VERTEX-COVER DECISION class via a SELF-CHECKED
//! matching / cardinality cutting-planes contradiction.
//!
//! # The class
//!
//! A PB decision instance is recognised when every constraint is either
//! - an *edge* clause `+1 x_u +1 x_v >= 1` (cover at least one endpoint), or
//! - the single *cardinality* row `-1 x_1 -1 x_2 ... -1 x_n >= -k`
//!   (equivalently `sum_v x_v <= k`: take at most `k` vertices).
//!
//! That is exactly: "is there a vertex cover of size `<= k`?". When the edge
//! graph is bipartite, König's theorem makes the minimum vertex cover equal the
//! maximum matching, so a matching of size `m > k` already PROVES no cover of
//! size `<= k` exists — the instance is UNSAT.
//!
//! # The refutation (and why it is sound regardless of bugs here)
//!
//! Let `M` be a matching with `|M| = m` (pairwise vertex-disjoint edges). Each
//! matched edge contributes `x_u + x_v >= 1`. Summing the `m` matched-edge rows
//! (all variables distinct, because `M` is a matching) yields
//! `sum_{v in V(M)} x_v >= m`. Adding the cardinality row `-sum_v x_v >= -k`
//! cancels every matched variable to coefficient `0` and leaves every *unmatched*
//! variable with coefficient `-1`; cancelling each of those with the boolean
//! axiom `x_v >= 0` produces `0 >= m - k`. When `m > k` this is `0 >= c` with
//! `c >= 1` — a contradiction.
//!
//! This derivation is assembled over the ORIGINAL rows and handed to the
//! kernel-algebra checker [`crate::proof::Refutation::check`], which recomputes
//! every step. We emit UNSAT ONLY if that replay reaches `0 >= c` (`c >= 1`).
//! Soundness therefore does NOT depend on the matching/2-colouring code: if the
//! proposed edges are not actually disjoint, or the proposed `m` is wrong, the
//! summed leftover does not reduce to a contradiction and the checker REJECTS it
//! (we then return `None` and the normal engine runs). The path is 0-wrong by
//! construction — exactly the pigeonhole pattern in [`super::pigeonhole`].

use std::collections::{HashMap, VecDeque};

use crate::proof::{pb_ge, LinConstraint, RefStep, Refutation};
use crate::types::{PbConstraint, PbRel};

/// Fail-closed size guards (the derivation is linear in these).
const MAX_ROWS: usize = 2_000_000;
const MAX_NNZ: u128 = 64_000_000;

/// An edge `+1 x_u +1 x_v >= 1` recovered from a constraint: the 0-indexed
/// endpoints plus the originating constraint index (so the refutation can cite
/// the genuine original row).
struct Edge {
    u: u32,
    v: u32,
    ci: usize,
}

/// The recognised shape: the edge list, the cardinality row's constraint index,
/// its bound `k`, and the variable count.
struct Shape {
    edges: Vec<Edge>,
    cardinality_ci: usize,
    cardinality_vars: Vec<u32>,
    k: i128,
    num_vars: u32,
}

/// Public, SELF-CHECKED entry point (mirrors
/// [`crate::optimize::pigeonhole::pigeonhole_unsat_cp_checked`]): returns `true`
/// iff `constraints` is the bipartite VC decision class with `m > k` AND the
/// reconstructed matching/cardinality derivation replays to `0 >= m-k >= 1`.
pub fn matching_cardinality_unsat_cp_checked(constraints: &[PbConstraint]) -> bool {
    matching_cardinality_refutation(constraints).is_some()
}

/// Builds the checked matching/cardinality [`Refutation`], or `None` if the
/// instance is not of the class, the edge graph is not bipartite, the maximum
/// matching does not exceed `k`, or the derivation fails to self-check.
pub(crate) fn matching_cardinality_refutation(constraints: &[PbConstraint]) -> Option<Refutation> {
    let shape = detect(constraints)?;
    if shape.k < 0 {
        return None;
    }
    let n = shape.num_vars as usize;

    // Adjacency over 0-indexed variables (only edge endpoints are touched).
    let mut adjacency: Vec<Vec<u32>> = vec![Vec::new(); n];
    // Map an unordered endpoint pair to a genuine edge constraint index, so the
    // refutation cites a real original row for each matched edge.
    let mut edge_index: HashMap<(u32, u32), usize> = HashMap::with_capacity(shape.edges.len());
    for e in &shape.edges {
        adjacency[e.u as usize].push(e.v);
        adjacency[e.v as usize].push(e.u);
        let key = if e.u < e.v { (e.u, e.v) } else { (e.v, e.u) };
        edge_index.entry(key).or_insert(e.ci);
    }

    // Two-colour each component by BFS. A non-bipartite (odd-cycle) graph means
    // Hopcroft–Karp does not apply and König gives no |VC|=|M| identity, so we
    // decline (the matching argument would be unsound to maximise here).
    let mut color = vec![-1i8; n];
    for e in &shape.edges {
        for start in [e.u, e.v] {
            if color[start as usize] != -1 {
                continue;
            }
            color[start as usize] = 0;
            let mut queue = VecDeque::new();
            queue.push_back(start);
            while let Some(node) = queue.pop_front() {
                let cu = color[node as usize];
                for &w in &adjacency[node as usize] {
                    if color[w as usize] == -1 {
                        color[w as usize] = 1 - cu;
                        queue.push_back(w);
                    } else if color[w as usize] == cu {
                        return None; // odd cycle -> not bipartite
                    }
                }
            }
        }
    }

    // Maximum matching (Hopcroft–Karp). Only the SIZE / disjointness matter for
    // the derivation; soundness is the checker, not this routine.
    let matching = hopcroft_karp(n, &adjacency, &color);

    // Collect matched pairs (each undirected edge once) and their citing rows.
    let mut matched_rows: Vec<usize> = Vec::new();
    let mut matched_vars: Vec<u32> = Vec::new();
    for v in 0..n {
        let p = matching[v];
        if p == u32::MAX {
            continue;
        }
        if (v as u32) < p {
            let key = (v as u32, p);
            let ci = *edge_index.get(&key)?; // must be a real edge
            matched_rows.push(ci);
            matched_vars.push(v as u32);
            matched_vars.push(p);
        }
    }
    let m = matched_rows.len() as i128;
    // Only a matching strictly larger than the budget refutes `sum x <= k`.
    if m <= shape.k {
        return None;
    }

    // --- Assemble the checkable refutation over the ORIGINAL rows. ---
    // inputs: [matched edge rows..., cardinality row, x_v>=0 axioms...].
    let mut matched_set = vec![false; n];
    for &v in &matched_vars {
        matched_set[v as usize] = true;
    }
    // Unmatched variables of the cardinality row carry a leftover `-1` after the
    // summation; each is cancelled by one `x_v >= 0` axiom.
    let mut leftover: Vec<u32> = Vec::new();
    for &v in &shape.cardinality_vars {
        if !matched_set[v as usize] {
            leftover.push(v);
        }
    }

    let mut inputs: Vec<LinConstraint> =
        Vec::with_capacity(matched_rows.len() + 1 + leftover.len());
    for &ci in &matched_rows {
        inputs.push(pb_ge(&constraints[ci])?);
    }
    let cardinality_input = inputs.len();
    inputs.push(pb_ge(&constraints[shape.cardinality_ci])?);
    let first_axiom = inputs.len();
    for &v in &leftover {
        // `v` is 0-indexed internally; `var_geq_zero` wants the 1-indexed id.
        inputs.push(LinConstraint::var_geq_zero(v + 1));
    }

    // Steps: sum the matched edges, add the cardinality row, then cancel each
    // leftover negative variable with its `x_v >= 0` axiom.
    let mut steps: Vec<RefStep> = Vec::new();
    let mut next = inputs.len();
    let row_indices: Vec<usize> = (0..matched_rows.len()).collect();
    let mut acc = tree_add(&row_indices, &mut steps, &mut next);
    steps.push(RefStep::Add(acc, cardinality_input));
    acc = next;
    next += 1;
    for (j, _) in leftover.iter().enumerate() {
        steps.push(RefStep::Add(acc, first_axiom + j));
        acc = next;
        next += 1;
    }
    let _ = acc;

    let refutation = Refutation { inputs, steps };
    // SOUNDNESS GATE: accept only a derivation the kernel-algebra checker replays
    // to `0 >= c` (`c >= 1`). A mis-detected matching/bound is rejected here.
    refutation.check().ok()?;
    Some(refutation)
}

/// Balanced-tree summation of the database entries `idxs`, appending `Add` steps
/// and advancing `next`; returns the index of the accumulated constraint.
/// `idxs` must be non-empty. (Mirror of the helper in [`super::pigeonhole`].)
fn tree_add(idxs: &[usize], steps: &mut Vec<RefStep>, next: &mut usize) -> usize {
    let mut level: Vec<usize> = idxs.to_vec();
    while level.len() > 1 {
        let mut nxt = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            steps.push(RefStep::Add(level[i], level[i + 1]));
            nxt.push(*next);
            *next += 1;
            i += 2;
        }
        if i < level.len() {
            nxt.push(level[i]);
        }
        level = nxt;
    }
    level[0]
}

/// Recognises the bipartite VC decision class: every row is an edge clause or the
/// SINGLE cardinality row. Returns `None` for any other shape (intentionally
/// strict; a mismatch costs only the cheap scan).
fn detect(constraints: &[PbConstraint]) -> Option<Shape> {
    if constraints.is_empty() {
        return None;
    }
    let mut edges: Vec<Edge> = Vec::new();
    let mut cardinality: Option<(usize, Vec<u32>, i128)> = None;
    let mut num_vars: u32 = 0;
    let mut nnz: u128 = 0;

    for (ci, c) in constraints.iter().enumerate() {
        if ci > MAX_ROWS {
            return None;
        }
        nnz = nnz.saturating_add(c.terms.len() as u128);
        if nnz > MAX_NNZ {
            return None;
        }
        if let Some((u, v, hi)) = as_edge(c) {
            num_vars = num_vars.max(hi);
            edges.push(Edge { u, v, ci });
        } else if let Some((vars, k, hi)) = as_cardinality(c) {
            if cardinality.is_some() {
                return None; // more than one cardinality row: not the class
            }
            num_vars = num_vars.max(hi);
            cardinality = Some((ci, vars, k));
        } else {
            return None; // an unmodeled row: decline
        }
    }

    let (cardinality_ci, cardinality_vars, k) = cardinality?;
    if edges.is_empty() {
        return None;
    }
    Some(Shape {
        edges,
        cardinality_ci,
        cardinality_vars,
        k,
        num_vars,
    })
}

/// Returns `(u, v, max_var)` 0-indexed endpoints if `c` is `+1 x_u +1 x_v >= 1`
/// (two distinct positive unit literals, `>=`, rhs `1`); otherwise `None`.
fn as_edge(c: &PbConstraint) -> Option<(u32, u32, u32)> {
    if c.rel != PbRel::Ge || c.rhs != 1 || c.terms.len() != 2 {
        return None;
    }
    let mut ends = [0u32; 2];
    let mut hi = 0u32;
    for (slot, term) in ends.iter_mut().zip(&c.terms) {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 {
            return None;
        }
        hi = hi.max(lit.var);
        *slot = lit.var - 1;
    }
    if ends[0] == ends[1] {
        return None;
    }
    Some((ends[0], ends[1], hi))
}

/// Returns `(vars_0indexed, k, max_var)` if `c` is `-1 x_1 ... -1 x_t >= -k`
/// (every term a `-1` positive unit literal, `>=`, rhs `<= 0`, distinct vars):
/// the cardinality bound `sum_v x_v <= k`. Otherwise `None`.
fn as_cardinality(c: &PbConstraint) -> Option<(Vec<u32>, i128, u32)> {
    if c.rel != PbRel::Ge || c.rhs > 0 || c.terms.len() < 2 {
        return None;
    }
    let mut vars: Vec<u32> = Vec::with_capacity(c.terms.len());
    let mut hi = 0u32;
    for term in &c.terms {
        if term.coeff != -1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 {
            return None;
        }
        hi = hi.max(lit.var);
        vars.push(lit.var - 1);
    }
    vars.sort_unstable();
    vars.dedup();
    if vars.len() != c.terms.len() {
        return None; // a repeated variable: not the canonical cardinality row
    }
    let k = c.rhs.checked_neg()?;
    Some((vars, k, hi))
}

/// Hopcroft–Karp maximum bipartite matching (`color[v]==0` left, `1` right).
/// Returns `match_of`, where `match_of[v]` is `v`'s partner or `u32::MAX`.
/// (Independent reimplementation; the checker — not this code — is the soundness
/// anchor.)
fn hopcroft_karp(n: usize, adjacency: &[Vec<u32>], color: &[i8]) -> Vec<u32> {
    const NIL: u32 = u32::MAX;
    let mut match_of = vec![NIL; n];
    let mut dist = vec![0u32; n];
    loop {
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
        let mut found = false;
        while let Some(u) = queue.pop_front() {
            let du = dist[u as usize];
            for &w in &adjacency[u as usize] {
                let mw = match_of[w as usize];
                if mw == NIL {
                    found = true;
                } else if dist[mw as usize] == u32::MAX {
                    dist[mw as usize] = du + 1;
                    queue.push_back(mw);
                }
            }
        }
        if !found {
            break;
        }
        for v in 0..n {
            if color[v] == 0 && match_of[v] == NIL {
                hk_dfs(v as u32, adjacency, &mut match_of, &mut dist);
            }
        }
    }
    match_of
}

/// Iterative DFS for one Hopcroft–Karp augmenting path under the `dist` layering.
fn hk_dfs(start: u32, adjacency: &[Vec<u32>], match_of: &mut [u32], dist: &mut [u32]) -> bool {
    const NIL: u32 = u32::MAX;
    let mut stack: Vec<(u32, usize)> = vec![(start, 0)];
    let mut via: Vec<u32> = vec![NIL];
    while let Some(&(u, idx)) = stack.last() {
        if idx >= adjacency[u as usize].len() {
            dist[u as usize] = u32::MAX;
            stack.pop();
            via.pop();
            continue;
        }
        let frame = stack.len() - 1;
        stack[frame].1 = idx + 1;
        let w = adjacency[u as usize][idx];
        let mw = match_of[w as usize];
        if mw == NIL {
            let mut child_right = w;
            for k in (0..stack.len()).rev() {
                let lv = stack[k].0;
                match_of[lv as usize] = child_right;
                match_of[child_right as usize] = lv;
                child_right = via[k];
            }
            return true;
        } else if dist[mw as usize] == dist[u as usize] + 1 {
            stack.push((mw, 0));
            via.push(w);
        }
    }
    false
}

#[cfg(test)]
mod tests;
