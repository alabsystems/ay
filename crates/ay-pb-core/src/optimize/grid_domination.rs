// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact certified optimum for BOUNDED-FRONTIER MINIMUM DOMINATING SET (the
//! grid/hexgrid/cylinder family) via a transfer-matrix dynamic program with a
//! self-certifying shortest-path-dual lower-bound witness.
//!
//! # Why the plain 2-packing / LP dual is not enough (the honest negative)
//!
//! The sibling [`crate::optimize::dominating_set`] path certifies a dominating
//! set only when a 2-PACKING (pairwise-disjoint closed neighbourhoods) matches
//! the incumbent. For the regular hexgrid/grid family every closed neighbourhood
//! has the same size `d+1`, so:
//!
//! * The all-`1/(d+1)` weighting is a FEASIBLE fractional dominating set (each
//!   covering row sums to exactly `1`), giving `gamma_f <= n/(d+1)`.
//! * Symmetrically `y_v = 1/(d+1)` is a FEASIBLE fractional 2-packing dual (each
//!   vertex's incident dual weights sum to `1`), giving `gamma_f >= n/(d+1)`.
//!
//! Hence the domination LP is *exactly* `n/(d+1)` on these instances, and any
//! 2-packing is `<= n/(d+1)`. But for the NON-perfect members `gamma` is
//! strictly larger (e.g. the real `r6_c50` hexgrid: `n/(d+1) = 75` yet
//! `gamma = 76`). So NO feasible LP dual — fractional or integral — can ever
//! reach `gamma`; the integrality gap is real. The 2-packing / LP-dual cert is
//! provably stuck one short. Closing these instances needs an *integral* lower
//! bound, which is what the DP below provides.
//!
//! # The integral lower bound, made self-certifying
//!
//! These instances have small *bandwidth* in the natural variable order (a hex
//! cylinder of `R` rows has frontier width `~2R`). We sweep the vertices in
//! order, maintaining a frontier state that records, per active vertex, whether
//! it is `SELECTED`, `DOMINATED` (by an already-decided neighbour) or still
//! `UNDOMINATED`. This is the standard path-decomposition domination DP; its
//! value is exactly `gamma`.
//!
//! The DP is a shortest-path problem on a layered DAG (layers = sweep steps,
//! nodes = frontier states, edge cost = `1` iff the new vertex is selected). We
//! make the lower bound RE-CHECKABLE the way König makes the matching bound
//! re-checkable — by exhibiting a feasible LP dual:
//!
//! * A **forward sweep** computes `gamma_fwd` = min selections of any complete
//!   sweep (cost-to-reach the empty accept state).
//! * A **backward cost-to-go potential** `pi[layer][state]` (a shortest-path
//!   dual): by construction `pi[i][s] = min over transitions (i,s)-c->(i+1,s')
//!   of c + pi[i+1][s']` and `pi[n][accept] = 0`, so it is a FEASIBLE potential
//!   (`pi[i][s] <= c + pi[i+1][s']` for every transition). Any feasible
//!   potential gives `pi[0][start] <= cost of every complete sweep = gamma`, so
//!   `pi[0][start]` is a VALID lower bound on `gamma`.
//! * A **dominating set `D`** reconstructed along a `pi`-optimal path, re-checked
//!   feasible against the ORIGINAL constraints (`verify_all_constraints`), so
//!   `|D|` is a valid UPPER bound.
//!
//! We return `OptimumFound` ONLY when:
//! 1. the forward sweep value and the backward potential value agree
//!    (`gamma_fwd == pi[0][start]`) — two independent DP directions cross-check
//!    the lower bound;
//! 2. `D` is feasible (`verify_all_constraints`) and `eval_objective(D) ==
//!    gamma_fwd` — a genuine upper bound equal to the lower bound.
//!
//! `LB <= gamma <= UB` with `LB == UB` forces `gamma == LB`. A bug in the DP
//! search makes the forward/backward cross-check or the UB re-verification fail
//! and we return `None` (fall through to the portfolio); a too-large frontier or
//! state count declines up front. This makes the path 0-wrong by construction,
//! exactly like the König / 2-packing certs.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::time::Instant;

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// Frontier-state status of one active vertex.
const UND: u8 = 0; // not selected, not yet dominated (needs a future neighbour)
const DOM: u8 = 1; // not selected, already dominated by a decided neighbour/self
const SEL: u8 = 2; // selected (dominates itself and its neighbours)

/// Largest frontier width we attempt. States are packed 2 bits per active vertex
/// into a `u32` key, so the ceiling is 16. Beyond a hex cylinder of ~7 rows the
/// reachable-state count explodes past the budget anyway; larger instances
/// decline up front.
const MAX_FRONTIER_WIDTH: usize = 16;
/// Per-layer reachable-state cap (defends runtime + the `u32` cost range).
const MAX_STATES_PER_LAYER: usize = 8_000_000;
/// Total reachable-state cap across all layers (defends memory: each retained
/// state is one `u32` in `layer_states` plus one decision bit, ~4.1 bytes).
const MAX_TOTAL_STATES: usize = 520_000_000;

/// Fast hasher for the small integer (`u32`) frontier-state keys used by the
/// forward sweep: a single multiplicative mix. Avoids SipHash overhead on the
/// hot inner loop without pulling in an external dependency.
#[derive(Default)]
struct IntHasher(u64);
impl Hasher for IntHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }
    fn write_u32(&mut self, i: u32) {
        self.0 = u64::from(i).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}
type IntMap = HashMap<u32, u32, BuildHasherDefault<IntHasher>>;

/// A detected min-dominating-set instance with its symmetric adjacency.
struct DomShape {
    /// `adj[v]` = the open neighbourhood of vertex `v` (0-indexed, excludes `v`),
    /// sorted ascending. The closed neighbourhood is `{v} ∪ adj[v]`.
    adj: Vec<Vec<u32>>,
}

/// Recognises `min sum_{v} x_v` subject to one closed-neighbourhood covering row
/// per vertex, with a SYMMETRIC neighbourhood family (so domination via the
/// undirected graph matches the constraints exactly). Returns `None` otherwise.
fn detect(instance: &PbInstance, objective: &PbObjective) -> Option<DomShape> {
    let n = instance.num_vars as usize;
    if n == 0 || objective.terms.len() != n || instance.constraints.len() != n {
        return None;
    }

    // Objective must be EXACTLY `min sum_{v=1..n} +1 x_v`: every variable once,
    // unit positive coefficient. Then `eval_objective(D) == |D|`.
    let mut seen = vec![false; n];
    for term in &objective.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > instance.num_vars {
            return None;
        }
        let idx = (lit.var - 1) as usize;
        if seen[idx] {
            return None;
        }
        seen[idx] = true;
    }
    if seen.iter().any(|&s| !s) {
        return None;
    }

    // Closed neighbourhood per vertex from constraint `i` (= row of vertex `i`).
    let mut closed: Vec<Vec<u32>> = Vec::with_capacity(n);
    for (i, constraint) in instance.constraints.iter().enumerate() {
        let row = closed_neighborhood(constraint, instance.num_vars)?;
        if !row.contains(&(i as u32)) {
            return None; // self-membership: vertex `i` must dominate itself
        }
        closed.push(row);
    }

    // Build open adjacency and verify the family is symmetric: the constraint row
    // of `v` must equal `{v} ∪ adj[v]`, and every neighbour lists `v` back.
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (v, row) in closed.iter().enumerate() {
        for &u in row {
            if u as usize != v {
                adj[v].push(u);
            }
        }
    }
    for nb in &mut adj {
        nb.sort_unstable();
        nb.dedup();
    }
    for (v, row) in closed.iter().enumerate() {
        let mut rebuilt: Vec<u32> = adj[v].clone();
        rebuilt.push(v as u32);
        rebuilt.sort_unstable();
        let mut orig = row.clone();
        orig.sort_unstable();
        orig.dedup();
        if rebuilt != orig {
            return None;
        }
        for &u in &adj[v] {
            if adj[u as usize].binary_search(&(v as u32)).is_err() {
                return None;
            }
        }
    }

    Some(DomShape { adj })
}

/// Returns the sorted, deduplicated 0-indexed variable set of a closed-
/// neighbourhood covering row `+1 x_a +1 x_b ... >= 1` (distinct positive unit
/// literals), or `None` if `constraint` is not of that shape.
fn closed_neighborhood(constraint: &PbConstraint, num_vars: u32) -> Option<Vec<u32>> {
    if constraint.rel != PbRel::Ge || constraint.rhs != 1 || constraint.terms.is_empty() {
        return None;
    }
    let mut vars = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > num_vars {
            return None;
        }
        vars.push(lit.var - 1);
    }
    vars.sort_unstable();
    let len = vars.len();
    vars.dedup();
    if vars.len() != len {
        return None; // repeated variable in a row
    }
    Some(vars)
}

/// Per-step transition data, precomputed once for sweeping vertex `i`
/// (layer `i` -> layer `i+1`). All positions index the *sorted active list*.
struct Trans {
    /// Positions in `active[i]` of `i`'s already-decided neighbours `j < i`.
    en_pos: Vec<u32>,
    /// Positions in `active[i]` of vertices retiring at this step (their last
    /// neighbour is `i`): each must be `DOM`/`SEL` or the branch is infeasible.
    retire_pos: Vec<u32>,
    /// Whether vertex `i` itself stays active after this step (has a later
    /// neighbour). If not, it retires now and must be dominated immediately.
    i_stays: bool,
    /// For each position in `active[i+1]`: the source position in `active[i]`, or
    /// `u32::MAX` meaning "this is the freshly added vertex `i`".
    b_src: Vec<u32>,
}

/// Attempts to solve `instance` as a bounded-frontier minimum dominating set,
/// returning a certified `OptimumFound` solution, or `None` if it is not of the
/// class, the frontier is too wide, the state budget is exceeded, the optional
/// `deadline` is reached, or the soundness certificate fails.
///
/// `deadline` (when `Some`) bounds the wall-clock spent here: the sweep polls it
/// per layer and DECLINES (returns `None`) rather than overrun, so the path never
/// blows past the solve budget. Declining is always sound — the caller keeps
/// whatever incumbent it had.
pub(crate) fn try_solve(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<Instant>,
) -> Option<PbSolution> {
    let shape = detect(instance, objective)?;
    let n = instance.num_vars as usize;
    let adj = &shape.adj;

    // `last[v]` = max index touched by `v` (itself or a neighbour): the sweep
    // step after which `v` can no longer change. `v` is active during layers
    // `(v, last[v]]`.
    let mut last = vec![0u32; n];
    for v in 0..n {
        let mut m = v as u32;
        for &u in &adj[v] {
            m = m.max(u);
        }
        last[v] = m;
    }

    // Cheap O(n) frontier-width precheck BEFORE materialising the per-layer
    // active lists (which would be O(n^2) on a dense, non-grid instance): vertex
    // `v` is active during layers `(v, last[v]]`, so a difference array gives the
    // width of every layer in linear time. Decline early if any layer is too wide.
    let mut diff = vec![0i64; n + 2];
    for v in 0..n {
        diff[v + 1] += 1;
        diff[last[v] as usize + 1] -= 1;
    }
    let mut widths = vec![0usize; n + 1];
    let mut running = 0i64;
    for (i, slot) in widths.iter_mut().enumerate() {
        running += diff[i];
        *slot = running as usize;
    }
    if widths.iter().copied().max().unwrap_or(0) > MAX_FRONTIER_WIDTH {
        return None;
    }

    // Active frontier per layer: `active[i] = { v : v < i <= last[v] }`, sorted.
    // Total size is now bounded by `(MAX_FRONTIER_WIDTH + 1) * (n + 1)`.
    let mut active: Vec<Vec<u32>> = vec![Vec::new(); n + 1];
    for v in 0..n {
        for slot in active.iter_mut().take(last[v] as usize + 1).skip(v + 1) {
            slot.push(v as u32);
        }
    }
    debug_assert!(active.iter().zip(&widths).all(|(a, &w)| a.len() == w));

    // Precompute the transition data for every step.
    let mut pos_of = vec![u32::MAX; n]; // scratch: vertex -> position in active[i]
    let mut trans: Vec<Trans> = Vec::with_capacity(n);
    for i in 0..n {
        let a = &active[i];
        for (k, &v) in a.iter().enumerate() {
            pos_of[v as usize] = k as u32;
        }
        let mut en_pos = Vec::new();
        for &u in &adj[i] {
            if (u as usize) < i {
                debug_assert_ne!(pos_of[u as usize], u32::MAX);
                en_pos.push(pos_of[u as usize]);
            }
        }
        let mut retire_pos = Vec::new();
        for (k, &v) in a.iter().enumerate() {
            if last[v as usize] == i as u32 {
                retire_pos.push(k as u32);
            }
        }
        let i_stays = last[i] > i as u32;
        let mut b_src = Vec::with_capacity(active[i + 1].len());
        for &v in &active[i + 1] {
            if v as usize == i {
                b_src.push(u32::MAX);
            } else {
                debug_assert_ne!(pos_of[v as usize], u32::MAX);
                b_src.push(pos_of[v as usize]);
            }
        }
        for &v in a {
            pos_of[v as usize] = u32::MAX;
        }
        trans.push(Trans {
            en_pos,
            retire_pos,
            i_stays,
            b_src,
        });
    }

    // ---- Forward sweep: min selections to reach each frontier state. ----
    // `layer_states[i]` = sorted reachable state codes at layer `i` (retained for
    // the backward potential pass). State code = 2 bits/active-vertex in a `u32`.
    let mut layer_states: Vec<Vec<u32>> = vec![Vec::new(); n + 1];
    layer_states[0] = vec![0];
    let mut prev: IntMap = IntMap::default();
    prev.insert(0, 0);
    let mut total_states = 1usize;
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_FRONTIER_WIDTH);

    for i in 0..n {
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            return None;
        }
        let t = &trans[i];
        let wi = widths[i];
        let mut cur: IntMap = IntMap::default();
        for (&code, &cost) in &prev {
            decode(code, wi, &mut buf);
            for sel in [false, true] {
                if let Some((bcode, dcost)) = step(&buf, t, sel) {
                    let e = cur.entry(bcode).or_insert(u32::MAX);
                    *e = (*e).min(cost + dcost);
                }
            }
        }
        if cur.len() > MAX_STATES_PER_LAYER {
            return None;
        }
        total_states += cur.len();
        if total_states > MAX_TOTAL_STATES {
            return None;
        }
        let mut keys: Vec<u32> = cur.keys().copied().collect();
        keys.sort_unstable();
        layer_states[i + 1] = keys;
        prev = cur;
    }
    // Layer `n` has the single empty (accept) state `0`.
    let gamma_fwd = *prev.get(&0)?;

    // ---- Backward cost-to-go potential (streamed: keep two layers). ----
    // `pi_next` is aligned to `layer_states[i+1]`; `decision[i][si]` records the
    // optimal choice for state `si` at layer `i` (bit-packed) for reconstruction.
    let mut decision: Vec<Vec<u64>> = (0..n)
        .map(|i| vec![0u64; layer_states[i].len().div_ceil(64)])
        .collect();
    let mut pi_next: Vec<i64> = vec![i64::MAX; layer_states[n].len()];
    match layer_states[n].binary_search(&0) {
        Ok(idx) => pi_next[idx] = 0,
        Err(_) => return None,
    }
    for i in (0..n).rev() {
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            return None;
        }
        let t = &trans[i];
        let wi = widths[i];
        let next = &layer_states[i + 1];
        let states_i = &layer_states[i];
        let mut pi_cur = vec![i64::MAX; states_i.len()];
        for (si, &code) in states_i.iter().enumerate() {
            decode(code, wi, &mut buf);
            let mut best = i64::MAX;
            let mut best_sel = false;
            for sel in [false, true] {
                if let Some((bcode, dcost)) = step(&buf, t, sel) {
                    if let Ok(j) = next.binary_search(&bcode) {
                        let pj = pi_next[j];
                        if pj != i64::MAX {
                            let cand = pj + i64::from(dcost);
                            if cand < best {
                                best = cand;
                                best_sel = sel;
                            }
                        }
                    }
                }
            }
            pi_cur[si] = best;
            if best != i64::MAX && best_sel {
                decision[i][si / 64] |= 1u64 << (si % 64);
            }
        }
        pi_next = pi_cur;
    }
    // Start layer has the single empty state at index 0.
    let gamma_bwd = pi_next[0];
    if gamma_bwd != i64::from(gamma_fwd) {
        return None; // forward/backward disagree -> decline (defensive cross-check)
    }

    // ---- Reconstruct a dominating set along the recorded optimal path. ----
    let mut assignment = vec![false; n];
    let mut code = 0u32; // start state (empty frontier)
    for i in 0..n {
        let si = layer_states[i].binary_search(&code).ok()?;
        let sel = (decision[i][si / 64] >> (si % 64)) & 1 == 1;
        decode(code, widths[i], &mut buf);
        let (bcode, _) = step(&buf, &trans[i], sel)?;
        assignment[i] = sel;
        code = bcode;
    }

    // ---- Soundness gate: UB feasible and equal to the certified LB. ----
    if !verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    let value = eval_objective(objective, &assignment);
    if value != i128::from(gamma_fwd) {
        return None;
    }

    Some(PbSolution {
        status: PbStatus::OptimumFound,
        assignment,
        objective: Some(value),
    })
}

/// Applies the domination transition for sweeping one vertex given the decoded
/// frontier statuses `st` (over `active[i]`) and decision `sel`. Returns the
/// successor state code over `active[i+1]` and the cost delta (`1` iff selected),
/// or `None` if the branch is infeasible (a retiring vertex stays undominated).
///
/// This is the single trusted local relation: it enumerates BOTH decisions for
/// every vertex and prunes ONLY a provably-undominatable vertex, so it never
/// drops a valid dominating set (completeness) — the basis of the lower bound.
fn step(st: &[u8], t: &Trans, sel: bool) -> Option<(u32, u32)> {
    let mut cur: [u8; MAX_FRONTIER_WIDTH] = [0; MAX_FRONTIER_WIDTH];
    let w = st.len();
    cur[..w].copy_from_slice(st);

    let i_status = if sel {
        for &p in &t.en_pos {
            let p = p as usize;
            if cur[p] == UND {
                cur[p] = DOM;
            }
        }
        SEL
    } else if t.en_pos.iter().any(|&p| st[p as usize] == SEL) {
        DOM
    } else {
        UND
    };

    // Retiring active vertices must be dominated.
    for &p in &t.retire_pos {
        if cur[p as usize] == UND {
            return None;
        }
    }
    // If `i` retires immediately it must be dominated now.
    if !t.i_stays && i_status == UND {
        return None;
    }

    // Build the successor state over `active[i+1]`.
    let mut bcode = 0u32;
    for (q, &src) in t.b_src.iter().enumerate() {
        let s = if src == u32::MAX {
            i_status
        } else {
            cur[src as usize]
        };
        bcode |= u32::from(s) << (2 * q);
    }
    Some((bcode, u32::from(sel)))
}

/// Decodes a 2-bit-packed state `code` of width `w` into `out`.
fn decode(code: u32, w: usize, out: &mut Vec<u8>) {
    out.clear();
    for k in 0..w {
        out.push(((code >> (2 * k)) & 0b11) as u8);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbObjective, PbTerm};

    fn pos(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn unit_term(var: u32) -> PbTerm {
        PbTerm {
            coeff: 1,
            lits: vec![pos(var)],
        }
    }

    /// Builds a min-dominating-set instance from an undirected graph (0-indexed
    /// `edges`): constraint `i` is `N[i+1] = {i+1} ∪ neighbours`.
    fn domset_instance(n: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
        let mut adj: Vec<std::collections::BTreeSet<u32>> = (0..n)
            .map(|v| std::collections::BTreeSet::from([v]))
            .collect();
        for &(a, b) in edges {
            adj[a as usize].insert(b);
            adj[b as usize].insert(a);
        }
        let constraints: Vec<PbConstraint> = (0..n)
            .map(|v| PbConstraint {
                terms: adj[v as usize].iter().map(|&u| unit_term(u + 1)).collect(),
                rel: PbRel::Ge,
                rhs: 1,
            })
            .collect();
        let objective = PbObjective {
            terms: (1..=n).map(unit_term).collect(),
        };
        let instance = PbInstance {
            num_vars: n,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    /// Brute-force domination number over all 2^n subsets (tiny graphs only).
    fn brute_force_gamma(instance: &PbInstance) -> i128 {
        let n = instance.num_vars as usize;
        let mut best = i128::MAX;
        for mask in 0u32..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|v| (mask >> v) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &assignment) {
                best = best.min(i128::from(mask.count_ones()));
            }
        }
        best
    }

    /// Hexagonal cylinder: `R` rows, `C` columns, column-major numbering, the
    /// brick vertical pairing alternating by column parity, horizontal edges
    /// between same-row adjacent columns with column wraparound. This is exactly
    /// the shape of the real `dominating_set_hexgrid` corpus instances.
    fn hex_cylinder(rows: u32, cols: u32) -> (PbInstance, PbObjective) {
        let n = rows * cols;
        let vid = |c: u32, r: u32| c * rows + r;
        let mut edges = Vec::new();
        for c in 0..cols {
            // Vertical brick pairing: even columns pair (0-1,2-3,...), odd
            // columns pair (1-2,3-4,...,R-1-0).
            for r in 0..rows {
                let partner = if c % 2 == 0 {
                    if r % 2 == 0 {
                        Some(r + 1)
                    } else {
                        None
                    }
                } else if r % 2 == 1 {
                    Some((r + 1) % rows)
                } else {
                    None
                };
                if let Some(p) = partner {
                    let p = p % rows;
                    if p != r {
                        edges.push((vid(c, r), vid(c, p)));
                    }
                }
            }
            // Horizontal edges to the next column (wrap at the last column).
            let nc = (c + 1) % cols;
            for r in 0..rows {
                edges.push((vid(c, r), vid(nc, r)));
            }
        }
        domset_instance(n, &edges)
    }

    #[test]
    fn triangle_certifies_gamma_one() {
        let (inst, obj) = domset_instance(3, &[(0, 1), (1, 2), (2, 0)]);
        let sol = try_solve(&inst, &obj, None).expect("triangle certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(1));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
    }

    #[test]
    fn five_cycle_certifies_gamma_two_where_packing_fails() {
        // C_5: 2-packing/LP dual caps at 1 (< gamma 2). The integral DP certifies
        // the true gamma = 2, which the sibling 2-packing cert cannot reach.
        let (inst, obj) = domset_instance(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
        assert_eq!(brute_force_gamma(&inst), 2);
        let sol = try_solve(&inst, &obj, None).expect("C5 certifies via DP");
        assert_eq!(sol.objective, Some(2));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn paths_and_cycles_match_brute_force() {
        // A spread of small graphs; the DP optimum must equal brute force every
        // time (validates transition completeness + the certificate gate).
        let cases: Vec<(u32, Vec<(u32, u32)>)> = vec![
            (4, vec![(0, 1), (1, 2), (2, 3)]),                 // P4
            (6, vec![(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]), // P6
            (7, (0..7).map(|v| (v, (v + 1) % 7)).collect()),   // C7
            (8, (0..8).map(|v| (v, (v + 1) % 8)).collect()),   // C8
            (6, vec![(0, 1), (1, 2), (3, 4), (4, 5)]),         // 2x P3
            (
                9,
                vec![
                    (0, 1),
                    (1, 2),
                    (2, 0),
                    (3, 4),
                    (4, 5),
                    (5, 3),
                    (6, 7),
                    (7, 8),
                    (8, 6),
                ],
            ), // 3 triangles
        ];
        for (n, edges) in cases {
            let (inst, obj) = domset_instance(n, &edges);
            let g = brute_force_gamma(&inst);
            let sol =
                try_solve(&inst, &obj, None).unwrap_or_else(|| panic!("n={n} should certify"));
            assert_eq!(sol.objective, Some(g), "n={n} edges={edges:?}");
            assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
            assert_eq!(sol.status, PbStatus::OptimumFound);
        }
    }

    #[test]
    fn small_hex_cylinder_matches_brute_force() {
        // Tiny hex cylinders small enough to brute-force; the DP must agree.
        for cols in [2u32, 3, 4] {
            let rows = 4u32;
            if rows * cols > 22 {
                continue;
            }
            let (inst, obj) = hex_cylinder(rows, cols);
            let g = brute_force_gamma(&inst);
            let sol = try_solve(&inst, &obj, None)
                .unwrap_or_else(|| panic!("hex r{rows} c{cols} should certify"));
            assert_eq!(sol.objective, Some(g), "hex r{rows} c{cols}");
            assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        }
    }

    #[test]
    fn hex_r6_c50_certifies_seventy_six() {
        // The flagship open instance: AY's incumbent is 78, the true gamma is 76,
        // and the LP/2-packing bound is only n/4 = 75. The DP certifies 76.
        let (inst, obj) = hex_cylinder(6, 50);
        let sol = try_solve(&inst, &obj, None).expect("r6_c50 certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(76));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn hex_r6_perfect_codes_certify_n_over_four() {
        // c60, c80 are efficient (perfect) codes: gamma = n/4. The DP agrees with
        // the sibling 2-packing cert (90 and 120 respectively).
        for (cols, expect) in [(60u32, 90i128), (80, 120)] {
            let (inst, obj) = hex_cylinder(6, cols);
            let sol = try_solve(&inst, &obj, None).expect("perfect code certifies");
            assert_eq!(sol.objective, Some(expect), "c{cols}");
            assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        }
    }

    #[test]
    fn lp_dual_is_loose_honest_negative() {
        // Honest-negative evidence for the fractional-dual approach (option 1):
        // on the 3-regular hex cylinder the all-`1/4` dual `y_v = 1/4` is FEASIBLE
        // (each vertex's incident weights sum to 4*(1/4) = 1) and OPTIMAL, so the
        // LP optimum is exactly n/4. Yet the true gamma is strictly larger, so no
        // feasible dual reaches gamma. We demonstrate the gap numerically.
        let (inst, obj) = hex_cylinder(6, 50);
        for c in &inst.constraints {
            assert_eq!(c.terms.len(), 4, "3-regular: closed nbhd size 4");
        }
        let n = inst.num_vars as i128;
        let lp_opt = n / 4; // 4 * (n * 1/4) = n  ->  lp_opt = n/4 = 75
        assert_eq!(lp_opt, 75);
        // The DP-certified gamma exceeds the LP optimum: the integrality gap is
        // real and option 1 (any LP dual) is provably one short.
        let sol = try_solve(&inst, &obj, None).expect("certifies");
        assert!(sol.objective.unwrap() > lp_opt, "gamma > n/4");
        assert_eq!(sol.objective, Some(76));
    }

    #[test]
    fn non_domset_rejected() {
        // Weighted objective: not the unit min-dominating-set shape.
        let (mut inst, _obj) = domset_instance(3, &[(0, 1), (1, 2), (2, 0)]);
        let weighted = PbObjective {
            terms: vec![
                PbTerm {
                    coeff: 2,
                    lits: vec![pos(1)],
                },
                unit_term(2),
                unit_term(3),
            ],
        };
        inst.objective = Some(weighted.clone());
        assert!(try_solve(&inst, &weighted, None).is_none());
    }

    #[test]
    fn wide_frontier_declines() {
        // A complete graph K_n has every vertex adjacent to every other, so the
        // frontier never narrows: width n-1. For n beyond the cap we decline
        // (fall through to the portfolio) rather than blow up.
        let n = 30u32;
        let mut edges = Vec::new();
        for a in 0..n {
            for b in (a + 1)..n {
                edges.push((a, b));
            }
        }
        let (inst, obj) = domset_instance(n, &edges);
        assert!(try_solve(&inst, &obj, None).is_none());
    }
}
