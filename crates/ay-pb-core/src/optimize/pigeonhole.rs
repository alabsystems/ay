// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact pigeonhole / Hall-violation UNSAT detector, certified by the
//! kernel-verified cutting-planes self-check ([`crate::proof::refutation_check`]).
//!
//! # The gap this closes
//!
//! The canonical pigeonhole instance (`n` pigeons, `m = n-1` holes) is UNSAT by
//! a one-line counting argument, yet generic CP/resolution search blows up on it:
//! AY returns `s UNKNOWN` at the cutoff on `php_220_219` (220 pigeons, 219 holes,
//! ~48k vars). The refutation, however, is `O(n+m)`:
//!
//! * Sum the `n` per-pigeon **demand** rows (each `sum_h x[p,h] >= 1`) to get
//!   `TotalAssigned >= n`.
//! * Sum the `m` per-hole **capacity** rows (each `sum_p x[p,h] <= 1`, i.e. in
//!   `>=` form `-sum_p x[p,h] >= -1`) to get `TotalAssigned <= m`.
//! * Add the two: `0 >= n - m >= 1` — a contradiction.
//!
//! # Soundness model (NEVER a wrong UNSAT)
//!
//! This module is **only a heuristic that proposes a candidate certificate**. It
//! recognizes the demand/capacity structure, then *constructs* the explicit
//! cutting-planes summation [`Refutation`] over the ORIGINAL constraints and
//! hands it to the proven checker. We emit UNSAT **only if**
//! [`Refutation::check`] certifies the derivation actually replays to `0 >= c`
//! with `c >= 1`. A mis-detection produces a derivation that fails to certify, so
//! it can never yield a wrong UNSAT — soundness is inherited from the checker,
//! which mirrors the Lean-kernel-verified PB algebra (`impliedGe_add`,
//! `var_geq_zero`, `pb_unsat_of_contradictory_bounds`).
//!
//! The inputs we cite are faithful normalizations of the instance's own rows
//! (via the checker's own [`pb_ge`]) plus the universally-true boolean
//! lower-bound axiom `x_v >= 0` ([`LinConstraint::var_geq_zero`]). Both are
//! trusted-as-given by the checker, so a passing self-check proves UNSAT of the
//! original instance.
//!
//! # Scope
//!
//! The **pure global path** ([`pigeonhole_cp_refutation`]) targets the pure
//! pigeonhole shape (and the `php-exit` v1 variants), where the demand rows and
//! capacity rows globally **cancel** when summed: every variable that appears
//! positively in a demand row appears with matching negative weight across the
//! capacity rows. Any leftover *negative*-coefficient variable is cancelled
//! soundly with the `x_v >= 0` axiom (this also handles a class of Hall
//! sub-instances where capacity rows range over more pigeons than the demand
//! rows). A leftover *positive*-coefficient variable cannot be cancelled by a
//! free boolean axiom, so the pure path fails closed.
//!
//! # General Hall extension (`php-exit` v2 "multi-exit")
//!
//! The pure global sum DECLINES `php-exit` v2: each PHP block carries a shared
//! **exit** variable `e_b` appearing in *every* demand row of the block, and a
//! single coupling row bounds the exits (`sum_b e_b <= N-1`). A naive global sum
//! leaves a *positive* leftover `(k-1)*e_b` per block, which is satisfiable on its
//! own. The general path ([`hall_cp_refutation`]) recovers the refutation:
//!
//! 1. Decompose demand rows into connected **blocks** by their shared hole
//!    variables, and find a Hall-deficient pigeon subset `T` per block via
//!    Hopcroft–Karp + König alternating-reachability (the deficient set is the
//!    pigeons reachable from an unmatched pigeon).
//! 2. Sum `T`'s demand rows + `N(T)`'s capacity rows. After cancelling the
//!    matched holes (and any negative leftover with `x_v >= 0`), the surviving
//!    positive terms are exactly the block's exit variables:
//!    `sum_e c_e e >= d` with deficiency `d = |T| - cap(N(T)) >= 1`.
//!    * No exit terms (pure Hall subset): this is already `0 >= d` — a
//!      contradiction, emitted directly.
//!    * Exit terms present: **divide** by `max_e c_e` (the proven ceil-division
//!      rule) to get `sum_e e >= ceil(d / max_c) >= 1` — a forced-exit bound.
//! 3. Sum the per-block forced-exit bounds (`sum_all e >= N`) and add the coupling
//!    row (`-sum_all e >= -(N-1)`) to reach `0 >= 1`.
//!
//! Every step is an `Add`/`Scale`/`Divide` arrow of the kernel-verified algebra,
//! cited over the ORIGINAL rows plus the `x_v >= 0` axiom, and the assembled
//! [`Refutation`] is replayed by [`Refutation::check`] before any UNSAT is
//! emitted. The Hopcroft–Karp/König search is *only a heuristic that proposes the
//! subset* `T`: a wrong `T` yields a derivation that does not reduce to `0 >= c`
//! and is rejected by the checker — never a false UNSAT.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::proof::{pb_ge, RefStep, Refutation};
use crate::types::{PbConstraint, PbRel};

/// Largest number of (demand + capacity) rows we will fold into a single
/// refutation. Fail-closed beyond this: the candidate is abandoned (the normal
/// engine still runs). Generous — real php families top out in the low thousands
/// of rows.
const MAX_PH_ROWS: usize = 200_000;

/// Largest total number of non-zero coefficients across the summed rows. Caps the
/// checker's replay cost; beyond it we decline (fail-closed `None`).
const MAX_PH_NNZ: u128 = 64_000_000;

/// A locally-normalized `>=` constraint used only for *classification* and for
/// the pre-check cancellation arithmetic. This mirrors the checker's own
/// `from_ge` normalization (negated literal `a*~x = a - a*x` contributes `-a` to
/// the coefficient and `-a` to the rhs); it is a heuristic view only — the
/// soundness-critical normalization is the checker's [`pb_ge`], recomputed
/// independently inside [`Refutation::check`].
struct NormView {
    coeff: BTreeMap<u32, i128>,
    rhs: i128,
}

/// How a constraint was classified for the pigeonhole construction.
enum RowKind {
    /// All coefficients `> 0` and `rhs >= 1`: a "demand" row (`sum x >= k`).
    Demand,
    /// All coefficients `< 0` and `rhs <= -1`: a "capacity" row (`-sum x >= -k`,
    /// i.e. `sum x <= k`).
    Capacity,
    /// Neither shape (objective-bound rows, mixed-sign rows, equalities, etc.):
    /// not part of the counting argument.
    Other,
}

/// Locally normalizes a `>=` PB constraint into a [`NormView`], or `None` if the
/// constraint is not a plain linear `>=` row the construction can use (non-`Ge`
/// relation, non-linear term, zero var id, or `i128` overflow). This is the
/// heuristic classifier's normalizer; failures simply mean "skip this row".
fn norm_view(c: &PbConstraint) -> Option<NormView> {
    if c.rel != PbRel::Ge {
        return None;
    }
    let mut coeff: BTreeMap<u32, i128> = BTreeMap::new();
    let mut rhs = c.rhs;
    for term in &c.terms {
        if term.lits.len() != 1 {
            return None; // non-linear term: not modeled here
        }
        let lit = term.lits[0];
        if lit.var == 0 {
            return None;
        }
        let delta = if lit.negated {
            // a*~x = a - a*x : coeff[x] -= a, rhs -= a.
            rhs = rhs.checked_sub(term.coeff)?;
            term.coeff.checked_neg()?
        } else {
            term.coeff
        };
        let entry = coeff.entry(lit.var).or_insert(0);
        *entry = entry.checked_add(delta)?;
        if *entry == 0 {
            coeff.remove(&lit.var);
        }
    }
    Some(NormView { coeff, rhs })
}

/// Classifies a normalized row as a demand row, a capacity row, or neither.
fn classify(v: &NormView) -> RowKind {
    if v.coeff.is_empty() {
        return RowKind::Other;
    }
    if v.rhs >= 1 && v.coeff.values().all(|&c| c > 0) {
        RowKind::Demand
    } else if v.rhs <= -1 && v.coeff.values().all(|&c| c < 0) {
        RowKind::Capacity
    } else {
        RowKind::Other
    }
}

/// Balanced pairwise `Add` reduction of database indices `idxs` into a single
/// index holding their sum. Appends `Add` steps to `steps` and advances `next`
/// (the index the next derived constraint will occupy). A balanced tree keeps the
/// checker's replay cost `O(N log N)` instead of the `O(N^2)` of a linear fold
/// (each [`RefStep::Add`] clones its larger operand). `idxs` must be non-empty.
fn tree_add(idxs: &[usize], steps: &mut Vec<RefStep>, next: &mut usize) -> usize {
    let mut level: Vec<usize> = idxs.to_vec();
    while level.len() > 1 {
        let mut up: Vec<usize> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            steps.push(RefStep::Add(level[i], level[i + 1]));
            up.push(*next);
            *next += 1;
            i += 2;
        }
        if i < level.len() {
            up.push(level[i]); // odd element carries up unchanged
        }
        level = up;
    }
    level[0]
}

/// Builds a kernel-algebra cutting-planes [`Refutation`] for the pigeonhole /
/// Hall counting contradiction in `constraints`, or `None` if no such structure
/// is present (or it cannot be reconstructed as a checkable derivation).
///
/// Strategy: classify every row as a demand row (`sum x >= k`, all `+` coeffs) or
/// a capacity row (`-sum x >= -k`, all `-` coeffs). Sum *all* demand and capacity
/// rows. If the variable terms globally cancel (or leave only negative-coefficient
/// terms, removable with the `x >= 0` axiom) and the summed rhs is `>= 1`, the
/// summation reduces to `0 >= c` (`c >= 1`) — a refutation. The returned
/// refutation cites the ORIGINAL rows (via [`pb_ge`]) and the boolean axiom, and
/// is self-checked before return.
///
/// Fail-closed: `None` on size limits, an unrepresentable row, a positive leftover
/// term, `rhs < 1`, or any arithmetic edge — never a spurious refutation.
pub(crate) fn pigeonhole_cp_refutation(constraints: &[PbConstraint]) -> Option<Refutation> {
    if constraints.is_empty() {
        return None;
    }

    // Pass 1: classify and accumulate the global sum (heuristic arithmetic, used
    // only to decide whether a contradiction is reachable and which axioms to add).
    let mut demand_idx: Vec<usize> = Vec::new();
    let mut capacity_idx: Vec<usize> = Vec::new();
    let mut total: BTreeMap<u32, i128> = BTreeMap::new();
    let mut total_rhs: i128 = 0i128;
    let mut nnz: u128 = 0;

    for (ci, c) in constraints.iter().enumerate() {
        let Some(view) = norm_view(c) else {
            continue; // unmodeled row: not part of the counting argument
        };
        let kind = classify(&view);
        match kind {
            RowKind::Demand => demand_idx.push(ci),
            RowKind::Capacity => capacity_idx.push(ci),
            RowKind::Other => continue,
        }
        nnz = nnz.saturating_add(view.coeff.len() as u128);
        if nnz > MAX_PH_NNZ || demand_idx.len() + capacity_idx.len() > MAX_PH_ROWS {
            return None; // fail-closed on size
        }
        total_rhs = total_rhs.checked_add(view.rhs)?;
        for (&var, &c) in &view.coeff {
            let entry = total.entry(var).or_insert(0);
            *entry = entry.checked_add(c)?;
            if *entry == 0 {
                total.remove(&var);
            }
        }
    }

    // Need both halves of the counting argument, and demand must over-subscribe
    // capacity (the global rhs `sum(demand_rhs) + sum(capacity_rhs) >= 1`).
    if demand_idx.is_empty() || capacity_idx.is_empty() {
        return None;
    }
    if total_rhs < 1 {
        return None;
    }

    // The leftover variable terms must all be NEGATIVE: a `-k*x_v` term is
    // cancelled soundly by `k * (x_v >= 0)` without changing the rhs. A positive
    // leftover term cannot be cancelled by a free boolean axiom (it would need an
    // upper bound, which lowers the rhs), so we fail-closed.
    let mut negatives: Vec<(u32, i128)> = Vec::new();
    for (&var, &c) in &total {
        if c > 0 {
            return None; // positive leftover (e.g. php-exit v2 multi-exit): decline
        }
        // c < 0 (zeros are never stored); record magnitude to cancel.
        negatives.push((var, c.checked_neg()?));
    }

    // Pass 2: assemble the checkable refutation over the ORIGINAL rows.
    // Inputs layout: [demand rows..., capacity rows..., x_v>=0 axioms...].
    let mut inputs = Vec::with_capacity(demand_idx.len() + capacity_idx.len() + negatives.len());
    for &ci in demand_idx.iter().chain(capacity_idx.iter()) {
        inputs.push(pb_ge(&constraints[ci])?); // faithful normalization, fail-closed
    }
    let row_input_count = inputs.len(); // indices [0, row_input_count) are demand+capacity
    for &(var, _) in &negatives {
        inputs.push(crate::proof::LinConstraint::var_geq_zero(var));
    }

    let mut steps: Vec<RefStep> = Vec::new();
    let mut next = inputs.len();

    // Sum all demand + capacity rows via a balanced tree.
    let row_indices: Vec<usize> = (0..row_input_count).collect();
    let mut acc = tree_add(&row_indices, &mut steps, &mut next);

    // Cancel each negative leftover `-k*x_v` by adding `k*(x_v>=0)`.
    for (pos, &(_, k)) in negatives.iter().enumerate() {
        let axiom_idx = row_input_count + pos;
        let to_add = if k == 1 {
            axiom_idx
        } else {
            steps.push(RefStep::Scale(axiom_idx, k));
            let s = next;
            next += 1;
            s
        };
        steps.push(RefStep::Add(acc, to_add));
        acc = next;
        next += 1;
    }
    // `acc` now holds the final derived constraint (should be `0 >= total_rhs`).
    let _ = acc;

    let refutation = Refutation { inputs, steps };
    // SOUNDNESS GATE: only return a refutation the kernel-algebra checker accepts
    // as actually replaying to `0 >= c`, `c >= 1`. A mis-built candidate is
    // rejected here and yields `None` (the normal engine then runs).
    refutation.check().ok()?;
    Some(refutation)
}

// ===========================================================================
// GENERAL HALL extension: per-block deficiency + forced-exit + coupling.
// ===========================================================================

/// One Hall-deficient block's forced-exit bound, as a *plan* (original-row
/// indices + the arithmetic needed to rebuild the derivation). The actual
/// checkable steps are emitted later in [`hall_cp_refutation`]'s build phase so
/// that every cited input is registered before any derived step references it.
struct BlockPlan {
    /// Original constraint indices of the deficient subset `T`'s demand rows.
    demand_cis: Vec<usize>,
    /// Original constraint indices of `N(T)`'s capacity (hole) rows.
    cap_cis: Vec<usize>,
    /// Negative leftover terms `(var, magnitude)` to cancel with `var >= 0`
    /// before dividing (matched holes cancel exactly; over-ranged holes leave a
    /// `-k` term removed by `k * (var >= 0)`).
    neg_axioms: Vec<(u32, i128)>,
    /// Divisor `max_e c_e` applied to normalize the exit coefficients to `1`
    /// (`1` means no `Divide` step is needed).
    divide_by: i128,
    /// The block's exit variables (each carries post-division coefficient `1`).
    exit_vars: Vec<u32>,
}

/// Disjoint-set union over a fixed node space, for grouping demand rows and hole
/// rows into connected blocks by shared variables.
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
        }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

/// Hopcroft–Karp maximum bipartite matching. `np` left (pigeon) vertices, `nh`
/// right (hole) vertices, `adj[p]` listing the holes adjacent to pigeon `p`.
/// Returns `(match_p, match_h)`: `match_p[p]` is `p`'s matched hole or
/// `usize::MAX`, and symmetrically for `match_h`. (Mirrors the proven
/// Hopcroft–Karp in [`crate::optimize::bipartite_vertex_cover`]; used here only
/// as a heuristic to PROPOSE a Hall-deficient subset — soundness is the checker.)
fn hk_matching(np: usize, nh: usize, adj: &[Vec<usize>]) -> (Vec<usize>, Vec<usize>) {
    const NIL: usize = usize::MAX;
    let mut match_p = vec![NIL; np];
    let mut match_h = vec![NIL; nh];
    let mut dist = vec![0u32; np];
    loop {
        // BFS layering from all free pigeons.
        let mut queue = VecDeque::new();
        for p in 0..np {
            if match_p[p] == NIL {
                dist[p] = 0;
                queue.push_back(p);
            } else {
                dist[p] = u32::MAX;
            }
        }
        let mut found = false;
        while let Some(p) = queue.pop_front() {
            for &h in &adj[p] {
                let m = match_h[h];
                if m == NIL {
                    found = true;
                } else if dist[m] == u32::MAX {
                    dist[m] = dist[p] + 1;
                    queue.push_back(m);
                }
            }
        }
        if !found {
            break;
        }
        for p in 0..np {
            if match_p[p] == NIL {
                hk_dfs(p, adj, &mut match_p, &mut match_h, &mut dist);
            }
        }
    }
    (match_p, match_h)
}

/// One augmenting-path DFS for Hopcroft–Karp under the current `dist` layering.
fn hk_dfs(
    p: usize,
    adj: &[Vec<usize>],
    match_p: &mut [usize],
    match_h: &mut [usize],
    dist: &mut [u32],
) -> bool {
    const NIL: usize = usize::MAX;
    for i in 0..adj[p].len() {
        let h = adj[p][i];
        let m = match_h[h];
        if m == NIL || (dist[m] == dist[p] + 1 && hk_dfs(m, adj, match_p, match_h, dist)) {
            match_p[p] = h;
            match_h[h] = p;
            return true;
        }
    }
    dist[p] = u32::MAX;
    false
}

/// Cancels each negative leftover `-k * x_var` of `acc` by adding `k * (var>=0)`,
/// appending the `Scale`/`Add` steps and advancing `next`. Returns the index of
/// the resulting (cleaned) derived constraint. `axiom_idx` maps a variable to the
/// input index of its `x_var >= 0` axiom.
fn cancel_negs(
    mut acc: usize,
    negs: &[(u32, i128)],
    axiom_idx: &BTreeMap<u32, usize>,
    steps: &mut Vec<RefStep>,
    next: &mut usize,
) -> Option<usize> {
    for &(var, k) in negs {
        let aidx = *axiom_idx.get(&var)?;
        let to_add = if k == 1 {
            aidx
        } else {
            steps.push(RefStep::Scale(aidx, k));
            let s = *next;
            *next += 1;
            s
        };
        steps.push(RefStep::Add(acc, to_add));
        acc = *next;
        *next += 1;
    }
    Some(acc)
}

/// Builds a kernel-algebra cutting-planes [`Refutation`] for a GENERAL Hall
/// violation with shared "exit" variables and a coupling row — the `php-exit` v2
/// shape the pure global path declines — or `None` if no such structure refutes
/// (the normal engine then runs).
///
/// See the module docs for the three-phase strategy. Fail-closed in every branch;
/// the assembled derivation is replayed by [`Refutation::check`] before return, so
/// a mis-proposed subset can never yield a wrong UNSAT.
pub(crate) fn hall_cp_refutation(constraints: &[PbConstraint]) -> Option<Refutation> {
    if constraints.is_empty() {
        return None;
    }

    // --- Pass 1: classify rows into demand (all +, rhs>=1) and negative
    // (all -, rhs<=-1) rows. The negative class holds BOTH block-capacity rows
    // and the coupling row(s). ---
    let mut demand: Vec<(usize, NormView)> = Vec::new();
    let mut negs: Vec<(usize, NormView)> = Vec::new();
    let mut nnz: u128 = 0;
    for (ci, c) in constraints.iter().enumerate() {
        let Some(view) = norm_view(c) else {
            continue;
        };
        match classify(&view) {
            RowKind::Demand => {
                nnz = nnz.saturating_add(view.coeff.len() as u128);
                demand.push((ci, view));
            }
            RowKind::Capacity => {
                nnz = nnz.saturating_add(view.coeff.len() as u128);
                negs.push((ci, view));
            }
            RowKind::Other => continue,
        }
        if nnz > MAX_PH_NNZ || demand.len() + negs.len() > MAX_PH_ROWS {
            return None; // fail-closed on size
        }
    }
    if demand.is_empty() || negs.is_empty() {
        return None;
    }

    // --- exit variables: those appearing in >= 2 demand rows. (Pure pigeonhole
    // hole vars appear in exactly one demand row; only the cross-cutting exits
    // repeat.) Without any exit var the pure global path already covers it. ---
    let mut demand_deg: BTreeMap<u32, u32> = BTreeMap::new();
    for (_, v) in &demand {
        for &var in v.coeff.keys() {
            *demand_deg.entry(var).or_insert(0) += 1;
        }
    }
    let exit_set: BTreeSet<u32> = demand_deg
        .iter()
        .filter(|&(_, &d)| d >= 2)
        .map(|(&v, _)| v)
        .collect();
    if exit_set.is_empty() {
        return None;
    }

    // --- split negative rows: block-capacity (no exit var) vs coupling (has an
    // exit var). Coupling rows bound the exits; they are NOT used to cancel holes. ---
    let mut blockcaps: Vec<usize> = Vec::new(); // indices into `negs`
    let mut coupling: Vec<usize> = Vec::new(); // indices into `negs`
    for (i, (_, v)) in negs.iter().enumerate() {
        if v.coeff.keys().any(|var| exit_set.contains(var)) {
            coupling.push(i);
        } else {
            blockcaps.push(i);
        }
    }
    if coupling.is_empty() {
        return None; // nothing bounds the exits -> no contradiction reachable
    }

    // --- pigeon(demand)->hole(blockcap) bipartite incidence. ---
    let np = demand.len();
    let nh = blockcaps.len();
    let mut var_to_holes: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
    for (hloc, &neg_i) in blockcaps.iter().enumerate() {
        for &var in negs[neg_i].1.coeff.keys() {
            var_to_holes.entry(var).or_default().push(hloc);
        }
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); np];
    for (p, (_, v)) in demand.iter().enumerate() {
        let mut hs: Vec<usize> = Vec::new();
        for &var in v.coeff.keys() {
            if let Some(list) = var_to_holes.get(&var) {
                hs.extend_from_slice(list);
            }
        }
        hs.sort_unstable();
        hs.dedup();
        adj[p] = hs;
    }

    // --- global maximum matching, then König alternating-reachability Z from the
    // unmatched pigeons. T = pigeons in Z, N(T) = holes in Z. ---
    let (match_p, match_h) = hk_matching(np, nh, &adj);
    let mut in_z_p = vec![false; np];
    let mut in_z_h = vec![false; nh];
    let mut queue = VecDeque::new();
    for p in 0..np {
        if match_p[p] == usize::MAX {
            in_z_p[p] = true;
            queue.push_back(p);
        }
    }
    while let Some(p) = queue.pop_front() {
        for &h in &adj[p] {
            if match_p[p] == h || in_z_h[h] {
                continue; // skip the matching edge; already-visited holes
            }
            in_z_h[h] = true;
            let q = match_h[h];
            if q != usize::MAX && !in_z_p[q] {
                in_z_p[q] = true;
                queue.push_back(q);
            }
        }
    }

    // --- connected blocks of pigeons+holes (shared hole variables). ---
    let mut uf = UnionFind::new(np + nh);
    for p in 0..np {
        for &h in &adj[p] {
            uf.union(p, np + h);
        }
    }
    let mut comp_pigeons: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut comp_holes: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for p in 0..np {
        comp_pigeons.entry(uf.find(p)).or_default().push(p);
    }
    for h in 0..nh {
        comp_holes.entry(uf.find(np + h)).or_default().push(h);
    }

    // --- per-component deficiency analysis. ---
    let mut blocks: Vec<BlockPlan> = Vec::new();
    for (root, pigeons) in &comp_pigeons {
        // Deficient subset of this component: T = component pigeons in Z.
        let td: Vec<usize> = pigeons.iter().copied().filter(|&p| in_z_p[p]).collect();
        if td.is_empty() {
            continue; // matching saturates this block -> no deficiency
        }
        let empty: Vec<usize> = Vec::new();
        let holes = comp_holes.get(root).unwrap_or(&empty);
        let nt: Vec<usize> = holes.iter().copied().filter(|&h| in_z_h[h]).collect();

        // Sum T's demand rows + N(T)'s capacity rows (heuristic arithmetic).
        let mut sum: BTreeMap<u32, i128> = BTreeMap::new();
        let mut rhs: i128 = 0;
        let mut demand_cis: Vec<usize> = Vec::with_capacity(td.len());
        let mut cap_cis: Vec<usize> = Vec::with_capacity(nt.len());
        for &p in &td {
            let (ci, view) = &demand[p];
            demand_cis.push(*ci);
            rhs = rhs.checked_add(view.rhs)?;
            for (&var, &c) in &view.coeff {
                let e = sum.entry(var).or_insert(0);
                *e = e.checked_add(c)?;
                if *e == 0 {
                    sum.remove(&var);
                }
            }
        }
        for &h in &nt {
            let (ci, view) = &negs[blockcaps[h]];
            cap_cis.push(*ci);
            rhs = rhs.checked_add(view.rhs)?;
            for (&var, &c) in &view.coeff {
                let e = sum.entry(var).or_insert(0);
                *e = e.checked_add(c)?;
                if *e == 0 {
                    sum.remove(&var);
                }
            }
        }
        if rhs < 1 {
            continue; // not a deficiency after all
        }

        // Partition the leftover: positives must be exit vars; negatives cancel
        // with the boolean axiom. A positive NON-exit term means the proposed
        // subset is malformed -> skip this block (fail-closed).
        let mut exit_terms: Vec<(u32, i128)> = Vec::new();
        let mut neg_axioms: Vec<(u32, i128)> = Vec::new();
        let mut positive_nonexit = false;
        for (&var, &c) in &sum {
            if c > 0 {
                if exit_set.contains(&var) {
                    exit_terms.push((var, c));
                } else {
                    positive_nonexit = true;
                    break;
                }
            } else {
                neg_axioms.push((var, c.checked_neg()?));
            }
        }
        if positive_nonexit {
            continue;
        }

        if exit_terms.is_empty() {
            // Pure Hall subset: T's demand + N(T)'s capacity already give 0 >= d.
            // Build and return this single-block contradiction directly.
            return build_direct_refutation(constraints, &demand_cis, &cap_cis, &neg_axioms);
        }

        let maxc = exit_terms.iter().map(|&(_, c)| c).max()?; // >= 1
        blocks.push(BlockPlan {
            demand_cis,
            cap_cis,
            neg_axioms,
            divide_by: maxc,
            exit_vars: exit_terms.into_iter().map(|(v, _)| v).collect(),
        });
    }

    if blocks.is_empty() {
        return None;
    }

    // --- coupling phase: sum the per-block forced-exit bounds and add the
    // coupling rows; the result must reduce to 0 >= c (c >= 1). ---
    let mut acc: BTreeMap<u32, i128> = BTreeMap::new();
    let mut acc_rhs: i128 = 0;
    for bp in &blocks {
        // post-division bound: `sum_e e >= ceil(deficiency / divide_by)`.
        // Recompute the bound's rhs from the block's demand/cap rows.
        let mut d: i128 = 0;
        for &ci in bp.demand_cis.iter() {
            d = d.checked_add(pb_ge(&constraints[ci])?.rhs())?;
        }
        for &ci in bp.cap_cis.iter() {
            d = d.checked_add(pb_ge(&constraints[ci])?.rhs())?;
        }
        // Cancelling negatives leaves the rhs unchanged; division ceils it.
        let bound_rhs = ceil_div_pos(d, bp.divide_by)?;
        for &e in &bp.exit_vars {
            let x = acc.entry(e).or_insert(0);
            *x = x.checked_add(1)?;
            if *x == 0 {
                acc.remove(&e);
            }
        }
        acc_rhs = acc_rhs.checked_add(bound_rhs)?;
    }
    for &i in &coupling {
        let (_, view) = &negs[i];
        acc_rhs = acc_rhs.checked_add(view.rhs)?;
        for (&var, &c) in &view.coeff {
            let x = acc.entry(var).or_insert(0);
            *x = x.checked_add(c)?;
            if *x == 0 {
                acc.remove(&var);
            }
        }
    }
    // Final leftover: positives are fatal (cannot reach 0 >= c); negatives cancel.
    let mut final_negs: Vec<(u32, i128)> = Vec::new();
    for (&var, &c) in &acc {
        if c > 0 {
            return None;
        }
        final_negs.push((var, c.checked_neg()?));
    }
    if acc_rhs < 1 {
        return None;
    }

    // --- BUILD PHASE: register every cited row + axiom as an input first, then
    // emit the replayable steps (block sums -> divisions -> coupling sum). ---
    let mut cited: BTreeMap<usize, usize> = BTreeMap::new();
    let mut axiom_vars: BTreeSet<u32> = BTreeSet::new();
    let mut order: Vec<usize> = Vec::new();
    let cite = |ci: usize, order: &mut Vec<usize>, cited: &mut BTreeMap<usize, usize>| {
        if let std::collections::btree_map::Entry::Vacant(e) = cited.entry(ci) {
            e.insert(order.len());
            order.push(ci);
        }
    };
    for bp in &blocks {
        for &ci in bp.demand_cis.iter().chain(bp.cap_cis.iter()) {
            cite(ci, &mut order, &mut cited);
        }
        for &(v, _) in &bp.neg_axioms {
            axiom_vars.insert(v);
        }
    }
    for &i in &coupling {
        cite(negs[i].0, &mut order, &mut cited);
    }
    for &(v, _) in &final_negs {
        axiom_vars.insert(v);
    }

    let mut inputs: Vec<crate::proof::LinConstraint> =
        Vec::with_capacity(order.len() + axiom_vars.len());
    for &ci in &order {
        inputs.push(pb_ge(&constraints[ci])?);
    }
    let mut axiom_idx: BTreeMap<u32, usize> = BTreeMap::new();
    for &v in &axiom_vars {
        axiom_idx.insert(v, inputs.len());
        inputs.push(crate::proof::LinConstraint::var_geq_zero(v));
    }

    let mut steps: Vec<RefStep> = Vec::new();
    let mut next = inputs.len();

    // Per-block: sum demand+cap, cancel negatives, divide to a unit exit bound.
    let mut bound_idxs: Vec<usize> = Vec::with_capacity(blocks.len());
    for bp in &blocks {
        let row_idxs: Vec<usize> = bp
            .demand_cis
            .iter()
            .chain(bp.cap_cis.iter())
            .map(|ci| cited[ci])
            .collect();
        let sum_idx = tree_add(&row_idxs, &mut steps, &mut next);
        let cleaned = cancel_negs(sum_idx, &bp.neg_axioms, &axiom_idx, &mut steps, &mut next)?;
        let bound = if bp.divide_by > 1 {
            steps.push(RefStep::Divide(cleaned, bp.divide_by));
            let s = next;
            next += 1;
            s
        } else {
            cleaned
        };
        bound_idxs.push(bound);
    }

    // Coupling: sum the bounds + the coupling rows, then cancel any negatives.
    let mut combine: Vec<usize> = bound_idxs;
    for &i in &coupling {
        combine.push(cited[&negs[i].0]);
    }
    let comb_idx = tree_add(&combine, &mut steps, &mut next);
    let _final_idx = cancel_negs(comb_idx, &final_negs, &axiom_idx, &mut steps, &mut next)?;

    let refutation = Refutation { inputs, steps };
    // SOUNDNESS GATE: the kernel-algebra checker must independently certify that
    // this derivation replays to `0 >= c` (c >= 1). A mis-proposed subset / wrong
    // coupling is rejected here and yields `None` (the normal engine then runs).
    refutation.check().ok()?;
    Some(refutation)
}

/// `ceil(a / d)` for `a >= 0`, `d >= 1` (the only regime used by the Hall
/// builder). `None` on `i128` overflow (fail-closed).
fn ceil_div_pos(a: i128, d: i128) -> Option<i128> {
    if d < 1 || a < 0 {
        return None;
    }
    a.checked_add(d - 1)?.checked_div(d)
}

/// Builds the single-block (pure Hall subset) contradiction `0 >= d`: sum the
/// subset's demand + capacity rows, cancel negative leftovers with `x>=0`, and
/// self-check. Returns the certified [`Refutation`] or `None`.
fn build_direct_refutation(
    constraints: &[PbConstraint],
    demand_cis: &[usize],
    cap_cis: &[usize],
    neg_axioms: &[(u32, i128)],
) -> Option<Refutation> {
    let mut inputs: Vec<crate::proof::LinConstraint> = Vec::new();
    for &ci in demand_cis.iter().chain(cap_cis.iter()) {
        inputs.push(pb_ge(&constraints[ci])?);
    }
    let row_count = inputs.len();
    let mut axiom_idx: BTreeMap<u32, usize> = BTreeMap::new();
    for &(v, _) in neg_axioms {
        if let std::collections::btree_map::Entry::Vacant(e) = axiom_idx.entry(v) {
            e.insert(inputs.len());
            inputs.push(crate::proof::LinConstraint::var_geq_zero(v));
        }
    }
    let mut steps: Vec<RefStep> = Vec::new();
    let mut next = inputs.len();
    let row_idxs: Vec<usize> = (0..row_count).collect();
    let sum_idx = tree_add(&row_idxs, &mut steps, &mut next);
    let _final = cancel_negs(sum_idx, neg_axioms, &axiom_idx, &mut steps, &mut next)?;
    let refutation = Refutation { inputs, steps };
    refutation.check().ok()?;
    Some(refutation)
}

/// Detects pigeonhole/Hall UNSAT and SELF-CHECKS the reconstructed cutting-planes
/// derivation against the kernel-verified algebra
/// (`crate::proof::refutation_check`).
///
/// Returns `true` ONLY when a checked `0 >= c` (`c >= 1`) cutting-planes
/// refutation over the ORIGINAL constraints exists. Tries the pure global
/// counting path first (`pigeonhole_cp_refutation`), then the general Hall
/// extension (`hall_cp_refutation`) for the `php-exit` v2 multi-exit shape. The
/// caller may then emit `s UNSATISFIABLE` without trusting this detector: a `true`
/// here means the verdict carries a kernel-algebra-checked refutation. Returns
/// `false` otherwise (no structure, size limits, or a candidate that fails the
/// check) — never a false positive.
pub fn pigeonhole_unsat_cp_checked(constraints: &[PbConstraint]) -> bool {
    pigeonhole_cp_refutation(constraints).is_some() || hall_cp_refutation(constraints).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbTerm};

    /// `sum_{v in vars} (+1) x_v >= rhs` — a demand row.
    fn demand(vars: &[u32], rhs: i128) -> PbConstraint {
        PbConstraint {
            terms: vars
                .iter()
                .map(|&v| PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: v,
                        negated: false,
                    }],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// `sum_{v in vars} (-1) x_v >= -cap` — a capacity row (`sum x <= cap`).
    fn capacity(vars: &[u32], cap: i128) -> PbConstraint {
        PbConstraint {
            terms: vars
                .iter()
                .map(|&v| PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: v,
                        negated: false,
                    }],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: -cap,
        }
    }

    /// Builds a pure pigeonhole instance: `pigeons` demand rows over disjoint
    /// hole-slots, `holes` capacity rows. Variable for (pigeon p, hole h),
    /// `p,h` 0-based, is `p*holes + h + 1`.
    fn pigeonhole_instance(pigeons: u32, holes: u32) -> Vec<PbConstraint> {
        let mut cs = Vec::new();
        for p in 0..pigeons {
            let vars: Vec<u32> = (0..holes).map(|h| p * holes + h + 1).collect();
            cs.push(demand(&vars, 1));
        }
        for h in 0..holes {
            let vars: Vec<u32> = (0..pigeons).map(|p| p * holes + h + 1).collect();
            cs.push(capacity(&vars, 1));
        }
        cs
    }

    #[test]
    fn pure_pigeonhole_php_5_4_emits_checked_refutation() {
        let cs = pigeonhole_instance(5, 4); // 5 pigeons, 4 holes: UNSAT
        let refutation = pigeonhole_cp_refutation(&cs).expect("must build a refutation");
        // The proven checker must independently certify it (0 >= 1).
        assert_eq!(refutation.check(), Ok(()));
        assert!(pigeonhole_unsat_cp_checked(&cs));
    }

    #[test]
    fn small_php_2_1_emits_checked_refutation() {
        // 2 pigeons, 1 hole: x1>=1, x2>=1, -x1-x2>=-1  ==>  0 >= 1.
        let cs = pigeonhole_instance(2, 1);
        let refutation = pigeonhole_cp_refutation(&cs).expect("must build a refutation");
        assert_eq!(refutation.check(), Ok(()));
    }

    #[test]
    fn satisfiable_equal_pigeons_and_holes_is_not_refuted() {
        // n pigeons, n holes: a perfect matching exists, so SATISFIABLE.
        // Demand+capacity sum cancels to 0 >= 0, which is NOT a contradiction.
        let cs = pigeonhole_instance(4, 4);
        assert!(
            pigeonhole_cp_refutation(&cs).is_none(),
            "must NOT fabricate UNSAT for a satisfiable equal-size instance"
        );
        assert!(!pigeonhole_unsat_cp_checked(&cs));
    }

    #[test]
    fn satisfiable_more_holes_than_pigeons_is_not_refuted() {
        // 3 pigeons, 5 holes: trivially satisfiable. rhs sum = 3 - 5 = -2 < 1.
        let cs = pigeonhole_instance(3, 5);
        assert!(pigeonhole_cp_refutation(&cs).is_none());
    }

    #[test]
    fn near_pigeonhole_with_enough_capacity_is_not_refuted() {
        // 5 pigeons, 4 holes BUT each hole has capacity 2 (`sum x <= 2`). Then
        // total capacity 8 >= 5 demand: SATISFIABLE. rhs sum = 5 - 8 = -3 < 1.
        let mut cs = Vec::new();
        for p in 0..5u32 {
            let vars: Vec<u32> = (0..4).map(|h| p * 4 + h + 1).collect();
            cs.push(demand(&vars, 1));
        }
        for h in 0..4u32 {
            let vars: Vec<u32> = (0..5).map(|p| p * 4 + h + 1).collect();
            cs.push(capacity(&vars, 2)); // capacity 2 per hole
        }
        assert!(
            pigeonhole_cp_refutation(&cs).is_none(),
            "enough total capacity for all pigeons: must not be refuted"
        );
    }

    #[test]
    fn negated_literal_capacity_rows_are_handled() {
        // Capacity expressed with negated literals: sum_p ~x[p,h] >= pigeons-1
        // is equivalent to sum_p x[p,h] <= 1. Build php_3_2 that way and confirm
        // the detector still certifies UNSAT.
        let pigeons = 3u32;
        let holes = 2u32;
        let mut cs = Vec::new();
        for p in 0..pigeons {
            let vars: Vec<u32> = (0..holes).map(|h| p * holes + h + 1).collect();
            cs.push(demand(&vars, 1));
        }
        for h in 0..holes {
            // sum_p ~x[p,h] >= pigeons - 1
            let terms: Vec<PbTerm> = (0..pigeons)
                .map(|p| PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: p * holes + h + 1,
                        negated: true,
                    }],
                })
                .collect();
            cs.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: i128::from(pigeons) - 1,
            });
        }
        let refutation =
            pigeonhole_cp_refutation(&cs).expect("negated-literal capacity must be recognized");
        assert_eq!(refutation.check(), Ok(()));
    }

    #[test]
    fn hall_subset_with_negative_leftover_uses_boolean_axiom() {
        // A Hall-style violation where capacity rows span MORE pigeons than the
        // demand rows, leaving a negative leftover term cancelled by x>=0.
        //   pigeons {1,2,3} each need a hole among {A,B} (demand >= 1).
        //   hole A capacity over pigeons {1,2,3,4}: -x1A-x2A-x3A-x4A >= -1.
        //   hole B capacity over pigeons {1,2,3,4}: -x1B-x2B-x3B-x4B >= -1.
        // Vars: x1A=1,x2A=2,x3A=3,x4A=4, x1B=5,x2B=6,x3B=7,x4B=8.
        // 3 pigeons into 2 holes -> UNSAT; summing leaves -x4A - x4B >= 1, then
        // +(x4A>=0)+(x4B>=0) -> 0 >= 1.
        let cs = vec![
            demand(&[1, 5], 1),         // pigeon 1: hole A or B
            demand(&[2, 6], 1),         // pigeon 2
            demand(&[3, 7], 1),         // pigeon 3
            capacity(&[1, 2, 3, 4], 1), // hole A over pigeons 1..4
            capacity(&[5, 6, 7, 8], 1), // hole B over pigeons 1..4
        ];
        let refutation =
            pigeonhole_cp_refutation(&cs).expect("Hall violation with neg leftover must certify");
        assert_eq!(refutation.check(), Ok(()));
    }

    #[test]
    fn positive_leftover_is_declined() {
        // Mirror of php-exit v2: an extra "exit" variable appears only in a demand
        // row (positive leftover), never in a capacity row. The global sum leaves
        // +x_exit >= 1, which is satisfiable; we must decline (no false UNSAT).
        let cs = vec![
            demand(&[1, 2, 99], 1), // pigeon 1 with an exit var 99
            demand(&[3, 4], 1),
            demand(&[5, 6], 1),
            capacity(&[1, 3, 5], 1),
            capacity(&[2, 4, 6], 1),
        ];
        assert!(
            pigeonhole_cp_refutation(&cs).is_none(),
            "positive leftover (exit var) must be declined, not refuted"
        );
    }

    // ----- GENERAL HALL extension (php-exit v2 multi-exit) tests -----

    /// Builds a `php-exit` v2-shaped instance: `blocks` PHP blocks each with
    /// `pigeons` demand rows over `pigeons-1` holes plus one shared exit var that
    /// appears in every demand row of the block, and a single coupling row
    /// `sum_b exit_b <= blocks-1`. UNSAT: each block forces its exit to 1, but the
    /// coupling allows at most `blocks-1` exits.
    fn phpexit_v2_instance(blocks: u32, pigeons: u32) -> Vec<PbConstraint> {
        let holes = pigeons - 1;
        let mut cs = Vec::new();
        let mut next_var = 1u32;
        let mut exits: Vec<u32> = Vec::new();
        for _b in 0..blocks {
            // hole variable for (pigeon p, hole h): contiguous block of ids.
            let base = next_var;
            next_var += pigeons * holes;
            let exit = next_var;
            next_var += 1;
            exits.push(exit);
            let var = |p: u32, h: u32| base + p * holes + h;
            for p in 0..pigeons {
                let mut vars: Vec<u32> = (0..holes).map(|h| var(p, h)).collect();
                vars.push(exit); // shared exit in every demand row
                cs.push(demand(&vars, 1));
            }
            for h in 0..holes {
                let vars: Vec<u32> = (0..pigeons).map(|p| var(p, h)).collect();
                cs.push(capacity(&vars, 1));
            }
        }
        // coupling: -sum exits >= -(blocks-1)  (i.e. sum exits <= blocks-1).
        let terms: Vec<PbTerm> = exits
            .iter()
            .map(|&e| PbTerm {
                coeff: -1,
                lits: vec![PbLit {
                    var: e,
                    negated: false,
                }],
            })
            .collect();
        cs.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: -(i128::from(blocks) - 1),
        });
        cs
    }

    #[test]
    fn phpexit_v2_small_emits_checked_hall_refutation() {
        // 2 blocks, 3 pigeons / 2 holes each, exits coupled to <= 1.
        let cs = phpexit_v2_instance(2, 3);
        // The pure global path MUST decline (positive exit leftover).
        assert!(
            pigeonhole_cp_refutation(&cs).is_none(),
            "pure path must decline php-exit v2 (positive leftover)"
        );
        // The Hall extension must build a kernel-checked refutation.
        let refutation =
            hall_cp_refutation(&cs).expect("Hall extension must certify php-exit v2 UNSAT");
        assert_eq!(refutation.check(), Ok(()));
        assert!(pigeonhole_unsat_cp_checked(&cs));
    }

    #[test]
    fn phpexit_v2_six_blocks_49_pigeons_certifies() {
        // Mirrors normalized-phpexit_v2_06_048: 6 blocks of 49 pigeons / 48 holes.
        let cs = phpexit_v2_instance(6, 49);
        assert!(pigeonhole_cp_refutation(&cs).is_none());
        let refutation = hall_cp_refutation(&cs).expect("v2_06-shape must certify");
        assert_eq!(refutation.check(), Ok(()));
    }

    #[test]
    fn phpexit_v2_satisfiable_when_coupling_allows_all_exits_is_not_refuted() {
        // Same blocks, but coupling allows ALL exits (sum exits <= blocks): then
        // every block can take its exit -> SATISFIABLE. Must NOT be refuted.
        let mut cs = phpexit_v2_instance(2, 3);
        // Replace the coupling row (last) with a non-binding one: sum exits <= 2.
        let last = cs.len() - 1;
        cs[last].rhs = -2; // -e1 - e2 >= -2  (sum exits <= 2): satisfiable.
        assert!(
            hall_cp_refutation(&cs).is_none(),
            "non-binding coupling: each block can exit, must not be refuted"
        );
        assert!(!pigeonhole_unsat_cp_checked(&cs));
    }

    #[test]
    fn hall_deficient_subset_within_a_mixed_block_certifies() {
        // Each block has a Hall-deficient TRIPLE {p1,p2,p3} mapping only to holes
        // A,B (3 into 2) PLUS a saturable pigeon p4 sharing holes A,B,C. König
        // alternating-reachability must isolate T = {p1,p2,p3}, N(T) = {A,B} and
        // EXCLUDE p4 (matched to C). The exit sits only in the triple; a coupling
        // row `e1 + e2 <= 1` then contradicts the two forced exits. This exercises
        // subset isolation + negative-leftover (p4's A,B slots) cancellation +
        // division + coupling all at once.
        // Block 1 vars: aPi (A-slot of pi)=1..4, bPi (B-slot)=5..8, c4=9, e1=10.
        // Block 2 vars: 11..20 analogously.
        let mut cs = vec![
            // --- block 1 ---
            demand(&[1, 5, 10], 1),     // p1: A1 | B1 | e1
            demand(&[2, 6, 10], 1),     // p2: A2 | B2 | e1
            demand(&[3, 7, 10], 1),     // p3: A3 | B3 | e1
            demand(&[4, 8, 9], 1),      // p4 (saturable): A4 | B4 | C4 (no exit)
            capacity(&[1, 2, 3, 4], 1), // hole A over p1..p4
            capacity(&[5, 6, 7, 8], 1), // hole B over p1..p4
            capacity(&[9], 1),          // hole C (p4 only)
            // --- block 2 ---
            demand(&[11, 15, 20], 1),
            demand(&[12, 16, 20], 1),
            demand(&[13, 17, 20], 1),
            demand(&[14, 18, 19], 1),
            capacity(&[11, 12, 13, 14], 1),
            capacity(&[15, 16, 17, 18], 1),
            capacity(&[19], 1),
        ];
        // coupling: -e1 - e2 >= -1  (sum exits <= 1): both forced -> 0 >= 1.
        cs.push(PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: 10,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: 20,
                        negated: false,
                    }],
                },
            ],
            rel: PbRel::Ge,
            rhs: -1,
        });
        let refutation = hall_cp_refutation(&cs)
            .expect("deficient triples isolated by Hopcroft-Karp must certify");
        assert_eq!(refutation.check(), Ok(()));
    }

    #[test]
    fn empty_instance_is_declined() {
        assert!(pigeonhole_cp_refutation(&[]).is_none());
        assert!(hall_cp_refutation(&[]).is_none());
    }

    #[test]
    fn only_demand_rows_is_declined() {
        let cs = vec![demand(&[1, 2], 1), demand(&[3, 4], 1)];
        assert!(pigeonhole_cp_refutation(&cs).is_none());
    }
}
