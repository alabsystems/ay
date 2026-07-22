// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Staged groundwork (5feea5ab): recognizer + violating-pair BnB are tested but
// not yet wired into the portfolio; drop this allow when the caller lands.
#![allow(dead_code)]

//! Exact maximum 2-CLUB solver for the standard PB encoding — the `2club*`
//! OPT-LIN family.
//!
//! # The encoding this recognizes
//!
//! A maximum 2-club instance over a graph `G = (V, E)`: maximize `Σ x_v`
//! (objective `min Σ -x_v`, every vertex, coefficient −1) subject to one row per
//! NON-adjacent pair `{i, j}`:
//!
//! ```text
//!   -x_i - x_j + Σ_{k ∈ N(i) ∩ N(j)} x_k >= -1
//! ```
//!
//! i.e. *if both `i` and `j` are selected, some common neighbour is selected* —
//! exactly "the induced subgraph has diameter ≤ 2".
//!
//! # Soundness (the recognizer IS the proof obligation)
//!
//! The solver's verdict is only meaningful if the PB rows are EXACTLY the 2-club
//! constraints of a single reconstructed graph. The recognizer therefore:
//! 1. parses every row into `(i, j, CN)` with coefficients ±1 / rhs −1 and plain
//!    positive literals only — anything else DECLINES;
//! 2. reconstructs `E` = all pairs that do NOT appear as a row's (i, j);
//! 3. **re-derives every row from `E`**: the row's `CN` must equal
//!    `N(i) ∩ N(j)` computed from the reconstructed adjacency, every pair must
//!    appear at most once, and every non-adjacent pair must have exactly one row.
//!    Any mismatch DECLINES.
//! Under (3), the feasible sets of the PB instance are exactly the 2-clubs of
//! `G`, so the branch-and-bound's exhaustive optimum is the instance's optimum.
//!
//! On top of that, the returned witness is independently re-verified against the
//! ORIGINAL constraints by the caller-side checks (`verify_all_constraints` +
//! `eval_objective`) before any status is emitted, and `OptimumFound` is claimed
//! ONLY when the search ran to exhaustion (never on a node/deadline cut).
//!
//! # Algorithm (Bourjolly-style violating-pair branch-and-bound)
//!
//! State = candidate set `C` (vertices still allowed). If some non-adjacent pair
//! `{i, j} ⊆ C` has no surviving common neighbour (`CN ∩ C = ∅`), no 2-club
//! within `C` contains both — branch `C \ {i}` / `C \ {j}`. If no violating pair
//! exists, `C` itself is a 2-club (update incumbent with WHOLE `C`). Prune when
//! `|C| <= incumbent`. Each branch removes a vertex, so the tree is finite; with
//! the pair lists precomputed from the rows the violating-pair check is a cheap
//! counter scan.

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Hard ceiling on vertices (the family is ~200; the recognizer is O(rows·arity)).
const MAX_VERTICES: usize = 512;
/// Node budget: exhaustion within this many nodes or the solver declines.
const MAX_NODES: u64 = 20_000_000;

/// Node budget for the exhaustive search. `TWO_CLUB_MAX_NODES` overrides the
/// default for manual hours-scale probe runs (measured 337k nodes/s on the
/// real 2club200v15p5scn — the field-calibrated 5-8e9 nodes is single-digit
/// HOURS at that rate, not the 550 core-hours Gurobi's MILP tree needed).
fn max_nodes() -> u64 {
    std::env::var("TWO_CLUB_MAX_NODES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_NODES)
}
/// Poll the stop signal every this many nodes.
const STOP_POLL_MASK: u64 = (1 << 12) - 1;

/// LP node-bound configuration for the exact search — **incremental dual
/// snapshots** (the fast form of LP-based node pruning).
///
/// The only *sound* optimistic bound the search had was the cardinality bound
/// `|C|`, which collapses on the field-hard `2club200v15p5scn` (root LP `121.22`
/// vs IP optimum `70`, gap `51`), so exhaustion is astronomical. The stronger
/// sound bound is the LP relaxation of the 2-club polytope **restricted to the
/// node's candidate set `C`**: every 2-club `S ⊆ C` is LP-feasible, so the LP
/// optimum bounds `|S|` from above and prunes exactly like (only tighter than)
/// `|C|`.
///
/// **Why snapshots.** Solving an LP *per node* costs ~ms — 3 orders of
/// magnitude above the raw node rate. Instead we exploit the NS/weak-duality
/// form of the bound: for ANY fixed dual vector `y ≥ 0` priced on rows valid
/// for the current subtree,
///
/// ```text
///   min Σ_{v∈C} -x_v  ≥  base(y) + Σ_{v∈C} min(0, d_v(y))
/// ```
///
/// where `base = y·b` and `d_v = c_v − (Aᵀy)_v` are **constants of `y`**. So a
/// node's bound differs from its parent's by exactly the removed vertex's term
/// `min(0, d_v)` — an **O(1) exact-integer update** per remove/undo (we store
/// `base`/`d` as integers scaled by `DUAL_SCALE`; rounding duals *down* keeps
/// `y ≥ 0` hence soundness, it only weakens the bound). Every node gets the LP
/// prune test for free; actual LP *solves* happen only as cadenced **refreshes**
/// (re-pricing `y` against the current cell), pushed on a stack at the refresh
/// node and popped when its subtree unwinds — descendants inherit the tightest
/// ancestor pricing automatically, and the bound *tightens* as `C` shrinks
/// (each removed `d_v < 0` term raises the floor), unlike a scalar inherited
/// bound which stays fixed.
///
/// Validity of a snapshot for its whole subtree: the refresh prices the rows
/// `-x_a - x_b + Σ_{k∈CN∩C} x_k ≥ -1` (active pairs, CN restricted to `C`).
/// For any descendant set `C' ⊆ C`, vertices in `C \ C'` are fixed to 0, under
/// which each restricted row coincides with the original (always-valid) 2-club
/// row — so the priced rows remain valid inequalities and weak duality gives a
/// sound bound at every descendant. `enabled == false` is byte-for-byte the
/// validated cardinality-only prover.
#[derive(Clone, Copy)]
pub(crate) struct LpNodeBound {
    /// Master switch. `false` ⇒ the validated cardinality-only baseline.
    pub enabled: bool,
    /// Do not run any refresh LP until this many nodes have been searched. The
    /// pre-refresh snapshot is `y = 0`, whose bound IS the cardinality bound —
    /// so easy instances that finish inside the warmup pay nothing.
    pub warmup: u64,
    /// Run a refresh LP at most once per this many search nodes.
    pub cadence: u64,
    /// Refresh only when `c_size <= best_floor + window` — above that the LP
    /// rarely dips below the floor and only costs time.
    pub window: usize,
    /// Skip a refresh whose restricted model would exceed this many rows
    /// (active pairs): a per-refresh cost guard. `0` = unlimited.
    pub max_rows: usize,
    /// Do not SOLVE any refresh when `c_size <= best_floor + low_margin` — the
    /// measured sweep shows refreshes just above the floor are ~0.5 s each and
    /// almost never prune (paths there are cardinality-tight, UB ≈ |C|), so
    /// the deep-solve budget is pure waste. The free O(1) test still applies.
    pub low_margin: usize,
    /// CEILING ATTACK: at a cascade's top failed rung — and only when that top
    /// is within 2 levels of the highest LP-kill c seen so far (the frontier)
    /// and under a ≤¼-of-wall-time budget — escalate to a full float solve and
    /// then the exact rational LP+cut loop (clique/cover cuts over the 2-club
    /// rows, hard per-call deadline). Each success extends the cascade one
    /// level ≈ halves the remaining skeleton; the 6h campaign showed the
    /// ceiling (not the kill rate) is the binding exponent.
    pub ceiling: bool,
    /// When a refresh bound lands within this many units above the floor,
    /// escalate to the exact LP+cuts bound (`lp_lower_bound_with_target`, whose
    /// clique/cover cutting-plane loop is at least as tight) for a decisive
    /// prune. `0` disables the escalation.
    pub exact_margin: i128,
}

impl LpNodeBound {
    /// The cardinality-only baseline: no LP bound (existing, validated behaviour).
    pub(crate) const fn disabled() -> Self {
        Self {
            enabled: false,
            warmup: 0,
            cadence: 0,
            window: 0,
            max_rows: 0,
            low_margin: 0,
            ceiling: false,
            exact_margin: 0,
        }
    }
    /// Production defaults: LP bound on. Refreshes fire in a band above the
    /// incumbent (`c_size <= floor + window`) — where a re-priced dual can flip
    /// a non-prune into a prune — on a cadence that amortizes the ~ms solve over
    /// many O(1) snapshot tests. The warmup means instances that finish under
    /// cardinality pruning never pay for a single LP.
    pub(crate) const fn standard() -> Self {
        Self {
            enabled: true,
            warmup: 20_000,
            cadence: 64,
            window: 75,
            max_rows: 60_000,
            low_margin: 6,
            ceiling: true,
            // Exact escalation OFF: on multi-thousand-row restricted models the
            // exact rational LP+cuts tier costs SECONDS per call, and in
            // cardinality-tight regions (float UB just above the floor) every
            // refresh triggers it — measured 70 refreshes consuming 150 s. The
            // float refresh already prunes ~99% of thin-path refreshes.
            exact_margin: 0,
        }
    }
}

struct TwoClub {
    n: usize,
    /// Non-adjacent pairs: (i, j, common-neighbour list), 0-based vertices.
    pairs: Vec<(u32, u32, Vec<u32>)>,
    /// G-adjacency bitset: `adj_bits[v]` bit `u` set iff `{u,v} in E`
    /// (complement of `pairs`, no self-loops). Used by the 2-domination
    /// separator (independence tests + neighbourhood scans).
    adj_bits: Vec<Vec<u64>>,
    /// For each vertex, the indices into `pairs` where it appears as i or j.
    pair_of_vertex: Vec<Vec<u32>>,
    /// For each vertex, the indices into `pairs` whose CN list contains it.
    cn_of_vertex: Vec<Vec<u32>>,
}

/// Recognize the 2-club encoding; decline (None) on ANY deviation.
fn recognize(instance: &PbInstance, objective: &PbObjective) -> Option<TwoClub> {
    let n = instance.num_vars as usize;
    if n == 0 || n > MAX_VERTICES {
        return None;
    }
    // Objective: exactly -1 per vertex, every vertex, plain positive literal.
    let mut seen = vec![false; n + 1];
    for t in &objective.terms {
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || lit.var as usize > n || t.coeff != -1 {
            return None;
        }
        if seen[lit.var as usize] {
            return None;
        }
        seen[lit.var as usize] = true;
    }
    if !seen[1..=n].iter().all(|&b| b) {
        return None;
    }

    // Parse rows into (i, j, CN).
    let mut pairs: Vec<(u32, u32, Vec<u32>)> = Vec::with_capacity(instance.constraints.len());
    let mut pair_seen = std::collections::HashSet::with_capacity(instance.constraints.len());
    for c in &instance.constraints {
        if c.rel != PbRel::Ge || c.rhs != -1 {
            return None;
        }
        let mut neg: Vec<u32> = Vec::with_capacity(2);
        let mut pos: Vec<u32> = Vec::new();
        for t in &c.terms {
            let [lit] = t.lits.as_slice() else {
                return None;
            };
            if lit.negated || lit.var == 0 || lit.var as usize > n {
                return None;
            }
            match t.coeff {
                -1 => neg.push(lit.var - 1),
                1 => pos.push(lit.var - 1),
                _ => return None,
            }
        }
        if neg.len() != 2 {
            return None;
        }
        let (a, b) = (neg[0].min(neg[1]), neg[0].max(neg[1]));
        if a == b || !pair_seen.insert((a, b)) {
            return None; // self-pair or duplicate row
        }
        pos.sort_unstable();
        pos.dedup();
        pairs.push((a, b, pos));
    }

    // Reconstruct adjacency: edges = pairs WITHOUT a row.
    let mut non_adj = vec![vec![false; n]; n];
    for &(a, b, _) in &pairs {
        non_adj[a as usize][b as usize] = true;
        non_adj[b as usize][a as usize] = true;
    }
    // adjacency[v] = neighbours of v under the reconstruction.
    let mut adj = vec![vec![false; n]; n];
    for a in 0..n {
        for b in (a + 1)..n {
            if !non_adj[a][b] {
                adj[a][b] = true;
                adj[b][a] = true;
            }
        }
    }
    // RE-DERIVE every row: CN(i, j) from the reconstruction must equal the row's
    // CN list exactly. This pins rows <-> 2-club constraints of THIS graph.
    for (a, b, cn) in &pairs {
        let (a, b) = (*a as usize, *b as usize);
        let derived: Vec<u32> = (0..n)
            .filter(|&k| adj[a][k] && adj[b][k])
            .map(|k| k as u32)
            .collect();
        if derived != *cn {
            return None;
        }
    }
    // Every non-adjacent pair must HAVE a row (else the instance is not the full
    // 2-club encoding and our optimum claim would be over the wrong polytope).
    let expected_rows: usize = (0..n)
        .map(|a| ((a + 1)..n).filter(|&b| non_adj[a][b]).count())
        .sum();
    if expected_rows != pairs.len() {
        return None;
    }

    let mut pair_of_vertex = vec![Vec::new(); n];
    let mut cn_of_vertex = vec![Vec::new(); n];
    for (idx, (a, b, cn)) in pairs.iter().enumerate() {
        pair_of_vertex[*a as usize].push(idx as u32);
        pair_of_vertex[*b as usize].push(idx as u32);
        for &k in cn {
            cn_of_vertex[k as usize].push(idx as u32);
        }
    }
    let words = n.div_ceil(64);
    let mut adj_bits = vec![vec![u64::MAX; words]; n];
    for (v, row) in adj_bits.iter_mut().enumerate() {
        row[v / 64] &= !(1u64 << (v % 64));
        let tail = n % 64;
        if tail != 0 {
            row[words - 1] &= (1u64 << tail) - 1;
        }
    }
    for &(a, b, _) in &pairs {
        let (a, b) = (a as usize, b as usize);
        adj_bits[a][b / 64] &= !(1u64 << (b % 64));
        adj_bits[b][a / 64] &= !(1u64 << (a % 64));
    }

    Some(TwoClub {
        n,
        pairs,
        adj_bits,
        pair_of_vertex,
        cn_of_vertex,
    })
}

/// DFS node: the set of removed vertices along this path (undo log driven).
struct SearchState {
    in_c: Vec<bool>,
    c_size: usize,
    /// pairs[idx] surviving common-neighbour count within C.
    cn_alive: Vec<u32>,
    /// pair is "active" iff both endpoints in C.
    both_in: Vec<bool>,
}

impl SearchState {
    fn remove(&mut self, v: usize, tc: &TwoClub, undo: &mut Vec<(u32, u8)>) {
        debug_assert!(self.in_c[v]);
        self.in_c[v] = false;
        self.c_size -= 1;
        for &pi in &tc.pair_of_vertex[v] {
            if self.both_in[pi as usize] {
                self.both_in[pi as usize] = false;
                undo.push((pi, 0));
            }
        }
        for &pi in &tc.cn_of_vertex[v] {
            self.cn_alive[pi as usize] -= 1;
            undo.push((pi, 1));
        }
    }
    fn undo(&mut self, v: usize, log: &[(u32, u8)]) {
        for &(pi, kind) in log.iter().rev() {
            match kind {
                0 => self.both_in[pi as usize] = true,
                _ => self.cn_alive[pi as usize] += 1,
            }
        }
        self.in_c[v] = true;
        self.c_size += 1;
    }
    /// A violating pair: both endpoints in C and zero surviving common neighbours.
    fn find_violating(&self) -> Option<usize> {
        // Prefer the pair with the smallest surviving CN count overall — but a
        // simple first-active-zero scan is O(pairs) and sufficient at this size.
        self.both_in
            .iter()
            .enumerate()
            .position(|(idx, &active)| active && self.cn_alive[idx] == 0)
    }
}

/// Greedy CLIQUE COVER over the ACTIVE VIOLATING pairs (both endpoints in
/// `C`, zero surviving common neighbours). Any pairwise-violating set `Q`
/// admits at most ONE member in any 2-club `S ⊆ C`, so `S` excludes at least
/// `|Q|−1` distinct vertices per clique of a vertex-disjoint cover:
///
/// ```text
///   |S| ≤ c_size − Σ_i (|Q_i| − 1)
/// ```
///
/// — a sound, LP-free upper bound that strictly dominates the maximal-matching
/// bound (matching = the all-cliques-size-2 special case) wherever the
/// violating-pair graph has triangles. Returns the excluded count
/// `Σ (|Q_i|−1)`; callers prune when `c_size − ret ≤ floor`.
fn greedy_viol_matching(tc: &TwoClub, state: &SearchState) -> usize {
    // Collect the active violating pairs and per-vertex adjacency (the graph is
    // tiny relative to `pairs`: tens to a few hundred edges deep in the tree).
    let mut adj: std::collections::HashMap<u32, Vec<u32>> = std::collections::HashMap::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        if state.both_in[pi] && state.cn_alive[pi] == 0 {
            adj.entry(*a).or_default().push(*b);
            adj.entry(*b).or_default().push(*a);
        }
    }
    if adj.is_empty() {
        return 0;
    }
    // Highest-degree-first greedy: grow a clique from each unused vertex by
    // repeatedly adding an unused viol-neighbour adjacent to ALL members.
    let mut order: Vec<u32> = adj.keys().copied().collect();
    order.sort_unstable_by_key(|v| std::cmp::Reverse(adj[v].len()));
    let mut used = vec![false; tc.n];
    let mut excluded = 0usize;
    for &v in &order {
        if used[v as usize] {
            continue;
        }
        let mut clique: Vec<u32> = vec![v];
        // Candidates: v's unused viol-neighbours, tried in arbitrary order.
        for &u in &adj[&v] {
            if used[u as usize] {
                continue;
            }
            let ua = &adj[&u];
            if clique.iter().all(|&q| q == u || ua.contains(&q)) {
                clique.push(u);
            }
        }
        if clique.len() >= 2 {
            for &q in &clique {
                used[q as usize] = true;
            }
            excluded += clique.len() - 1;
        }
    }
    excluded
}

/// Violating-pair CLIQUES of size ≥ 3 for use as LP cut rows
/// `Σ_{v∈Q} x_v ≤ 1`. Every pairwise-violating set admits at most one member
/// in any 2-club ⊆ C, so each clique is a valid row of the restricted
/// polytope. Unlike the combinatorial cover bound, LP rows need NOT be
/// disjoint — one maximal clique is grown greedily from every vertex of the
/// violating-pair graph (deduplicated, capped). Size-2 cliques are omitted:
/// a violating pair's ORIGINAL row already reads `-x_a - x_b ≥ -1` (its CN∩C
/// is empty), so the LP always knew the 2-cliques — size ≥ 3 is the new
/// information.
fn viol_clique_rows(tc: &TwoClub, state: &SearchState, cap: usize) -> Vec<Vec<u32>> {
    // Adjacency of the violating-pair graph, plus the edge list as clique
    // seeds: EVERY violating pair seeds a growth attempt, so triangle-rich
    // regions are mined systematically instead of once per vertex.
    let mut adj: std::collections::HashMap<u32, Vec<u32>> = std::collections::HashMap::new();
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        if state.both_in[pi] && state.cn_alive[pi] == 0 {
            adj.entry(*a).or_default().push(*b);
            adj.entry(*b).or_default().push(*a);
            edges.push((*a, *b));
        }
    }
    if edges.is_empty() {
        return Vec::new();
    }
    // Process dense endpoints first; grow with candidates in descending
    // viol-degree so the densest extensions are tried before sparse ones.
    let deg = |v: &u32| adj[v].len();
    edges.sort_unstable_by_key(|(a, b)| std::cmp::Reverse(deg(a) + deg(b)));
    let mut seen: std::collections::HashSet<Vec<u32>> = std::collections::HashSet::new();
    let mut out: Vec<Vec<u32>> = Vec::new();
    for &(a, b) in &edges {
        if out.len() >= cap {
            break;
        }
        let mut clique: Vec<u32> = vec![a, b];
        // Candidates: common viol-neighbours of the seed edge, densest first.
        let ba = &adj[&b];
        let mut cands: Vec<u32> = adj[&a].iter().copied().filter(|u| ba.contains(u)).collect();
        cands.sort_unstable_by_key(|u| std::cmp::Reverse(deg(u)));
        for u in cands {
            let ua = &adj[&u];
            if clique.iter().all(|&q| ua.contains(&q)) {
                clique.push(u);
            }
        }
        if clique.len() >= 3 {
            clique.sort_unstable();
            if seen.insert(clique.clone()) {
                out.push(clique);
            }
        }
    }
    out
}

/// Violating-pair 5-CYCLE rows `Σ_{v∈H} x_v ≤ 2`: an odd cycle H in the
/// violating-pair graph admits at most ⌊|H|/2⌋ = 2 members in any 2-club ⊆ C
/// (its vertices form an odd cycle of mutual-exclusion constraints — a stable
/// set in C_5 has ≤ 2 vertices). Chordless-ness is NOT required for validity
/// (any 5 vertices whose cycle edges are all violating admit ≤ 2), so a cheap
/// greedy walk suffices: from each high-degree vertex, try to close a 5-walk
/// v→a→b→c→d→v with distinct vertices. These carry information neither pair
/// rows (2-cliques) nor clique rows express.
fn viol_odd_hole_rows(tc: &TwoClub, state: &SearchState, cap: usize) -> Vec<Vec<u32>> {
    // OFF — root-caused and A/B-measured 2026-07: the original "collapse"
    // (front 145→126, subs=0, ceiling 0-for-N) was NOT the hole rows
    // themselves but a row-count plumbing bug — `refresh_dual_snapshot`
    // checked `duals.len() != n_pair_rows + cliques.len()` while the solver
    // (correctly) returned one dual per row INCLUDING the appended hole rows,
    // so every Solve/Support refresh with holes > 0 was silently discarded on
    // an untraced None path. That check and the hole-dual pricing are fixed
    // below (holes: b = -2 ⇒ base -= 2m; ay[v] -= m), and with the fix the
    // engine is fully healthy with holes on (front=145, subs populated,
    // ceiling kill rate ~55%). But a same-load A/B (300 s, seed70,
    // 2club200v15p5scn) measured holes as a pure throughput tax with no
    // frontier or kill-rate benefit: 38,220 prunes / 726 refreshes WITH holes
    // vs 50,710 prunes / 989 refreshes WITHOUT (~25% fewer solves for the
    // same per-solve kill quality). Keep OFF; the pricing below stays correct
    // if re-enabled.
    if true {
        return Vec::new();
    }
    use std::collections::{HashMap, HashSet};
    let mut adj: HashMap<u32, HashSet<u32>> = HashMap::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        if state.both_in[pi] && state.cn_alive[pi] == 0 {
            adj.entry(*a).or_default().insert(*b);
            adj.entry(*b).or_default().insert(*a);
        }
    }
    if adj.len() < 5 {
        return Vec::new();
    }
    let mut order: Vec<u32> = adj.keys().copied().collect();
    order.sort_unstable_by_key(|v| std::cmp::Reverse(adj[v].len()));
    let mut seen: HashSet<Vec<u32>> = HashSet::new();
    let mut out: Vec<Vec<u32>> = Vec::new();
    // HARD WORK BUDGET: the naive 5-walk enumeration is O(deg^4)-ish per seed
    // vertex and the violating graph at band entries is dense — an unbudgeted
    // scan measured MINUTES per refresh (starving every solve). ~300k steps
    // keeps the generator well under a millisecond-scale budget.
    let mut steps = 0usize;
    const STEP_BUDGET: usize = 300_000;
    'outer: for &v in &order {
        if out.len() >= cap {
            break;
        }
        let va = &adj[&v];
        for &a in va.iter() {
            for &b in adj[&a].iter() {
                steps += 1;
                if steps > STEP_BUDGET {
                    break 'outer;
                }
                if b == v || va.contains(&b) {
                    continue;
                }
                for &cnd in adj[&b].iter() {
                    steps += 1;
                    if steps > STEP_BUDGET {
                        break 'outer;
                    }
                    if cnd == v || cnd == a || va.contains(&cnd) {
                        continue;
                    }
                    for &d in adj[&cnd].iter() {
                        steps += 1;
                        if steps > STEP_BUDGET {
                            break 'outer;
                        }
                        if d != a && d != b && d != v && va.contains(&d) {
                            let mut hole = vec![v, a, b, cnd, d];
                            hole.sort_unstable();
                            if seen.insert(hole.clone()) {
                                out.push(hole);
                                if out.len() >= cap {
                                    break 'outer;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    out
}

/// Violated independent-set 2-DOMINATION cuts at the fractional point `x*`
/// (exact over triples of the top-80 x*-mass candidates — see the diagnostic
/// history in the development design notes*). Returns up to `cap` cuts
/// `(I = [a,b,c], hubs = [(v, coeff)])` with violation > 0.03, meaning
/// `Σ_I x − Σ_hubs coeff·x_v > 1 + 0.03` at x*. Validity of each cut for every
/// 2-club `S ⊆ C` (and every descendant C' — removed members/hubs only relax/
/// re-derive the same proof): the witness-clique spanning-tree argument of
/// Mahdavi Pajouh–Balasundaram–Hicks 2016.
fn indep_2dom_cuts(
    tc: &TwoClub,
    state: &SearchState,
    x: &[f64],
    cap: usize,
) -> Vec<(Vec<u32>, Vec<(u32, u8)>)> {
    let n = tc.n;
    let words = n.div_ceil(64);
    let mut order: Vec<u32> = (0..n as u32).filter(|&v| state.in_c[v as usize]).collect();
    order.sort_unstable_by(|&a, &b| {
        x[b as usize]
            .partial_cmp(&x[a as usize])
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    order.truncate(80);
    let k = order.len();
    if k < 3 {
        return Vec::new();
    }
    let mut cmask = vec![0u64; words];
    for v in 0..n {
        if state.in_c[v] {
            cmask[v / 64] |= 1u64 << (v % 64);
        }
    }
    let nb: Vec<Vec<u64>> = order
        .iter()
        .map(|&u| {
            tc.adj_bits[u as usize]
                .iter()
                .zip(cmask.iter())
                .map(|(&a, &c)| a & c)
                .collect::<Vec<u64>>()
        })
        .collect();
    let mass = |bits: &[u64]| -> f64 {
        let mut s = 0.0;
        for (w, &b0) in bits.iter().enumerate() {
            let mut b = b0;
            while b != 0 {
                let v = w * 64 + b.trailing_zeros() as usize;
                b &= b - 1;
                s += x[v];
            }
        }
        s
    };
    let adj = |i: usize, j: usize| -> bool {
        let vj = order[j] as usize;
        tc.adj_bits[order[i] as usize][vj / 64] & (1u64 << (vj % 64)) != 0
    };
    let mut pair_mass = vec![f64::NAN; k * k];
    let mut buf = vec![0u64; words];
    for i in 0..k {
        for j in (i + 1)..k {
            if adj(i, j) {
                continue;
            }
            for w in 0..words {
                buf[w] = nb[i][w] & nb[j][w];
            }
            pair_mass[i * k + j] = mass(&buf);
        }
    }
    // Collect violated triples.
    let mut found: Vec<(f64, usize, usize, usize)> = Vec::new();
    for i in 0..k {
        for j in (i + 1)..k {
            let mij = pair_mass[i * k + j];
            if mij.is_nan() {
                continue;
            }
            for l in (j + 1)..k {
                let mil = pair_mass[i * k + l];
                let mjl = pair_mass[j * k + l];
                if mil.is_nan() || mjl.is_nan() {
                    continue;
                }
                let mut m3 = 0.0;
                for w in 0..words {
                    let mut b = nb[i][w] & nb[j][w] & nb[l][w];
                    while b != 0 {
                        let v = w * 64 + b.trailing_zeros() as usize;
                        b &= b - 1;
                        m3 += x[v];
                    }
                }
                let viol = x[order[i] as usize] + x[order[j] as usize] + x[order[l] as usize]
                    - (mij + mil + mjl - m3)
                    - 1.0;
                if viol > 0.03 {
                    found.push((viol, i, j, l));
                }
            }
        }
    }
    found.sort_unstable_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    found.truncate(cap);
    // Materialize hub coefficient lists: coeff = cover-1 for cover in {2,3}.
    let mut out = Vec::with_capacity(found.len());
    for &(_, i, j, l) in &found {
        let members = vec![order[i], order[j], order[l]];
        let mut hubs: Vec<(u32, u8)> = Vec::new();
        for w in 0..words {
            let bi = nb[i][w];
            let bj = nb[j][w];
            let bl = nb[l][w];
            let mut two = (bi & bj) | (bi & bl) | (bj & bl);
            let three = bi & bj & bl;
            two &= !three;
            let mut b = two;
            while b != 0 {
                let v = (w * 64 + b.trailing_zeros() as usize) as u32;
                b &= b - 1;
                hubs.push((v, 1));
            }
            let mut b = three;
            while b != 0 {
                let v = (w * 64 + b.trailing_zeros() as usize) as u32;
                b &= b - 1;
                hubs.push((v, 2));
            }
        }
        out.push((members, hubs));
    }
    out
}

/// VIOLATED-CLIQUE separation at the fractional point `x*`: cliques `Q` in
/// the violating-pair graph with `Σ_{v∈Q} x*_v > 1 + 0.03`. The blind family
/// (viol_clique_rows) grows by degree and misses exactly the x*-heavy
/// cliques; violated cliques of size ≥ 4 are also outside the exact-triple
/// 2-domination scan. Greedy growth by descending x* from each x*-heavy
/// violating edge; emitted in the 2-domination cut format with empty hub
/// lists (a clique is the all-pairs-violating, zero-hub special case).
fn violated_cliques_at_x(
    tc: &TwoClub,
    state: &SearchState,
    x: &[f64],
    cap: usize,
) -> Vec<(Vec<u32>, Vec<(u32, u8)>)> {
    use std::collections::{HashMap, HashSet};
    let mut adj: HashMap<u32, HashSet<u32>> = HashMap::new();
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        if state.both_in[pi] && state.cn_alive[pi] == 0 {
            adj.entry(*a).or_default().insert(*b);
            adj.entry(*b).or_default().insert(*a);
            edges.push((*a, *b));
        }
    }
    if edges.is_empty() {
        return Vec::new();
    }
    // Heaviest edges first; only x*-support endpoints are worth seeding.
    edges.retain(|&(a, b)| x[a as usize] + x[b as usize] > 0.4);
    edges.sort_unstable_by(|&(a1, b1), &(a2, b2)| {
        (x[a2 as usize] + x[b2 as usize])
            .partial_cmp(&(x[a1 as usize] + x[b1 as usize]))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    edges.truncate(400);
    let mut seen: HashSet<Vec<u32>> = HashSet::new();
    let mut out = Vec::new();
    for &(a, b) in &edges {
        if out.len() >= cap {
            break;
        }
        let mut clique = vec![a, b];
        let mut weight = x[a as usize] + x[b as usize];
        let ba = &adj[&b];
        let mut cands: Vec<u32> = adj[&a]
            .iter()
            .copied()
            .filter(|u| ba.contains(u) && x[*u as usize] > 1e-6)
            .collect();
        cands.sort_unstable_by(|&u, &v| {
            x[v as usize]
                .partial_cmp(&x[u as usize])
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        for u in cands {
            let ua = &adj[&u];
            if clique.iter().all(|&q| ua.contains(&q)) {
                weight += x[u as usize];
                clique.push(u);
            }
        }
        if weight > 1.03 && clique.len() >= 3 {
            clique.sort_unstable();
            if seen.insert(clique.clone()) {
                out.push((clique, Vec::new()));
            }
        }
    }
    out
}

/// Builds the Solve-mode model rows: pair rows (CN restricted to `C`, sorted
/// merge of endpoints into the CN stream) followed by clique-cut rows.
/// Returns `(rows_raw, pair_of_row, cliques)`; `None` if over `cfg.max_rows`.
#[allow(clippy::type_complexity)]
fn build_solve_rows(
    tc: &TwoClub,
    state: &SearchState,
    cfg: &LpNodeBound,
) -> Option<(Vec<(Vec<(usize, f64)>, f64)>, Vec<u32>, Vec<Vec<u32>>)> {
    let mut rows_raw: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
    let mut pair_of_row: Vec<u32> = Vec::new();
    for (pi, (a, b, cn)) in tc.pairs.iter().enumerate() {
        if !state.both_in[pi] {
            continue;
        }
        let (a, b) = (*a as usize, *b as usize);
        let mut coeffs: Vec<(usize, f64)> = Vec::with_capacity(cn.len() + 2);
        let mut placed_a = false;
        let mut placed_b = false;
        for &k in cn {
            let k = k as usize;
            if state.in_c[k] {
                if !placed_a && a < k {
                    coeffs.push((a, -1.0));
                    placed_a = true;
                }
                if !placed_b && b < k {
                    if !placed_a {
                        coeffs.push((a, -1.0));
                        placed_a = true;
                    }
                    coeffs.push((b, -1.0));
                    placed_b = true;
                }
                coeffs.push((k, 1.0));
            }
        }
        if !placed_a {
            coeffs.push((a, -1.0));
        }
        if !placed_b {
            coeffs.push((b, -1.0));
        }
        rows_raw.push((coeffs, -1.0));
        pair_of_row.push(pi as u32);
        if cfg.max_rows != 0 && rows_raw.len() > cfg.max_rows {
            return None;
        }
    }
    let cliques = viol_clique_rows(tc, state, 2000);
    for q in &cliques {
        let coeffs: Vec<(usize, f64)> = q.iter().map(|&v| (v as usize, -1.0)).collect();
        rows_raw.push((coeffs, -1.0));
    }
    Some((rows_raw, pair_of_row, cliques))
}

/// Fixed-point scale for the exact-integer dual arithmetic. Duals are rounded
/// DOWN onto this grid (`m = ⌊y·SCALE⌋ ≥ 0`), which preserves `y ≥ 0` and hence
/// soundness — rounding only weakens the bound, never inflates it.
const DUAL_SCALE: i128 = 1 << 20;
/// Per-row dual clamp on the scaled grid (≈ `y ≤ 2^20`); any clamped value is
/// still a valid `y ≥ 0`, and the cap keeps every downstream sum well inside
/// i128 (see the overflow audit at [`refresh_dual_snapshot`]).
const DUAL_M_MAX: i128 = 1 << 40;

/// One priced dual state, valid for the entire subtree of the node it was
/// refreshed at. `d[v]` is the scaled reduced cost `c_v − (Aᵀy)_v`; `base` is
/// the scaled `y·b`. The node bound is `base + Σ_{v∈C} min(0, d_v)` (a scaled
/// lower bound on `min Σ_{v∈C} −x_v`), maintained incrementally: remove(v) ⇒
/// `sum −= min(0, d_v)`, undo(v) ⇒ `sum += min(0, d_v)` — O(1) exact integers.
///
/// On the snapshot *stack* an entry stores the PREVIOUS state (the one to
/// restore when the refresh node's subtree unwinds); `saved_sum` is the
/// previous state's running sum at push time, which is exactly its value again
/// when the subtree has fully unwound (every remove pairs with its undo).
struct DualSnapshot {
    base: i128,
    d: Vec<i128>,
    saved_sum: i128,
}

/// Builds the LP relaxation of the 2-club IP restricted to the candidate set
/// `C = { v : state.in_c[v] }`:
///
/// ```text
///   min  Σ_{v∈C} -x_v
///   s.t. -x_a - x_b + Σ_{k∈CN(a,b)∩C} x_k ≥ -1   for every active pair (a,b)⊆C
///        0 ≤ x ≤ 1
/// ```
///
/// Returns `(objective, rows, pair_of_row)` where `pair_of_row[i]` is the index
/// into `tc.pairs` for row `i` (needed to re-derive reduced costs from duals),
/// or `None` when the model exceeds `cfg.max_rows` (fail-closed: no prune).
/// Rows for pairs with an endpoint outside `C` are dropped — with that endpoint
/// fixed to 0 they are implied by the box — so this is an exact relaxation of
/// "max 2-club within `C`".
fn build_restricted_lp(
    tc: &TwoClub,
    state: &SearchState,
    cfg: &LpNodeBound,
) -> Option<(PbObjective, Vec<PbConstraint>, Vec<u32>)> {
    let mut obj_terms = Vec::with_capacity(state.c_size);
    for v in 0..tc.n {
        if state.in_c[v] {
            obj_terms.push(PbTerm {
                coeff: -1,
                lits: vec![PbLit {
                    var: (v + 1) as u32,
                    negated: false,
                }],
            });
        }
    }
    let objective = PbObjective { terms: obj_terms };

    let mut rows: Vec<PbConstraint> = Vec::new();
    let mut pair_of_row: Vec<u32> = Vec::new();
    for (pi, (a, b, cn)) in tc.pairs.iter().enumerate() {
        if !state.both_in[pi] {
            continue;
        }
        let mut terms = Vec::with_capacity(cn.len() + 2);
        terms.push(PbTerm {
            coeff: -1,
            lits: vec![PbLit {
                var: a + 1,
                negated: false,
            }],
        });
        terms.push(PbTerm {
            coeff: -1,
            lits: vec![PbLit {
                var: b + 1,
                negated: false,
            }],
        });
        for &k in cn {
            if state.in_c[k as usize] {
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: k + 1,
                        negated: false,
                    }],
                });
            }
        }
        rows.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: -1,
        });
        pair_of_row.push(pi as u32);
        if cfg.max_rows != 0 && rows.len() > cfg.max_rows {
            return None; // too heavy at this node — decline (no prune).
        }
    }
    Some((objective, rows, pair_of_row))
}

/// Refresh: solve the `C`-restricted LP, convert its duals into an exact
/// scaled-integer snapshot `(base, d, sum-at-C)`, and report `prune` if the
/// fresh bound (or, within `exact_margin`, the exact LP+cuts bound) already
/// proves no 2-club in `C` beats `best_floor`.
///
/// # Soundness
///
/// The float duals `y` are clamped to `≥ 0` and floored onto the `DUAL_SCALE`
/// grid — the resulting `y' = m/SCALE` satisfies `0 ≤ y' ` componentwise, and
/// weak duality holds for ANY nonnegative multiplier vector on valid rows, so
/// `base + Σ_{v∈C} min(0, d_v)` is a sound scaled lower bound on
/// `min Σ_{v∈C} −x_v` regardless of how (in)accurate the simplex was. All
/// post-rounding arithmetic is exact i128.
///
/// # Overflow audit
///
/// `m ≤ 2^40`, rows ≤ `MAX_VERTICES²/2 < 2^17` ⇒ `|base| ≤ 2^57`; per-vertex
/// pair memberships < 2^17 ⇒ `|Ay_v| ≤ 2^57`, `|d_v| ≤ 2^58`; `|sum| ≤ n·2^58 ≤
/// 2^67`. All far inside i128.
struct RefreshOutcome {
    base: i128,
    d: Vec<i128>,
    sum: i128,
    /// The fresh bound already proves `⌊UB⌋ ≤ best_floor`: prune immediately.
    prune: bool,
}

/// How a refresh obtains its dual vector.
enum RefreshMode<'a> {
    /// Full float LP solve (~100s of ms on multi-thousand-row boundary models).
    /// On success the caller receives the support pair set for caching.
    Solve,
    /// Solve ONLY the cached dual-support rows (pair indices with `y > 0` at
    /// the last full solve — a vertex optimum has ≤ #cols ≈ 200 of them, vs
    /// ~7,000 total rows), then price exactly with `y = 0` on every omitted
    /// row — sound, and ~100× cheaper than the full model. Unlike freezing the
    /// stale duals, this RE-OPTIMIZES y on the rows that carry the bound, so
    /// it stays sharp across the few-vertex C changes between nearby refreshes
    /// (cascade rungs, sibling band entries). Fallback on a non-prune is the
    /// full solve.
    Support(&'a [u32]),
}

fn refresh_dual_snapshot(
    tc: &TwoClub,
    state: &SearchState,
    cfg: &LpNodeBound,
    best_floor: i128,
    mode: RefreshMode<'_>,
    should_stop: &dyn Fn() -> bool,
) -> Option<(RefreshOutcome, Option<Vec<u32>>)> {
    let n = tc.n;
    // Support mode: build + solve ONLY the cached support rows (those active at
    // the current C), then price exactly with y = 0 on every omitted row.
    if let RefreshMode::Support(support) = mode {
        let mut rows_raw: Vec<(Vec<(usize, f64)>, f64)> = Vec::with_capacity(support.len());
        let mut pair_of_row: Vec<u32> = Vec::with_capacity(support.len());
        for &pi in support {
            if !state.both_in[pi as usize] {
                continue;
            }
            let (a, b, cn) = &tc.pairs[pi as usize];
            let (a, b) = (*a as usize, *b as usize);
            let mut coeffs: Vec<(usize, f64)> = Vec::with_capacity(cn.len() + 2);
            let mut placed_a = false;
            let mut placed_b = false;
            for &k in cn {
                let k = k as usize;
                if state.in_c[k] {
                    if !placed_a && a < k {
                        coeffs.push((a, -1.0));
                        placed_a = true;
                    }
                    if !placed_b && b < k {
                        if !placed_a {
                            coeffs.push((a, -1.0));
                            placed_a = true;
                        }
                        coeffs.push((b, -1.0));
                        placed_b = true;
                    }
                    coeffs.push((k, 1.0));
                }
            }
            if !placed_a {
                coeffs.push((a, -1.0));
            }
            if !placed_b {
                coeffs.push((b, -1.0));
            }
            rows_raw.push((coeffs, -1.0));
            pair_of_row.push(pi);
        }
        let c: Vec<f64> = (0..n)
            .map(|v| if state.in_c[v] { -1.0 } else { 0.0 })
            .collect();
        // Fresh clique-cut rows here too (regenerated per node — a cached
        // clique can go INVALID on unwind when a restored common neighbour
        // un-violates one of its pairs; regeneration is cheap and valid by
        // construction). This is what lets the ~3ms support rungs kill at the
        // heights the wall-breaking full solves reach.
        let n_pair_rows = rows_raw.len();
        let cliques = viol_clique_rows(tc, state, 600);
        for q in &cliques {
            let coeffs: Vec<(usize, f64)> = q.iter().map(|&v| (v as usize, -1.0)).collect();
            rows_raw.push((coeffs, -1.0));
        }
        let holes = viol_odd_hole_rows(tc, state, 150);
        for h in &holes {
            let coeffs: Vec<(usize, f64)> = h.iter().map(|&v| (v as usize, -1.0)).collect();
            rows_raw.push((coeffs, -2.0));
        }
        let duals = crate::optimize::safe_lp_bound::safe_lp_duals_from_raw(
            n,
            c,
            rows_raw,
            // Early-exit threshold: stop the simplex as soon as its quick-NS
            // bound already proves the prune (+0.5 covers grid-floor loss so
            // the exact re-check almost surely passes).
            Some(-(best_floor as f64) + 0.5),
            should_stop,
        )?;
        if duals.len() != n_pair_rows + cliques.len() + holes.len() {
            if std::env::var_os("TWO_CLUB_TRACE").is_some() {
                eprintln!(
                    "  [support-none-len] duals={} pair={} cliques={} holes={}",
                    duals.len(),
                    n_pair_rows,
                    cliques.len(),
                    holes.len()
                );
            }
            return None;
        }
        let mut base: i128 = 0;
        let mut ay = vec![0i128; n];
        for (row_i, &pi) in pair_of_row.iter().enumerate() {
            let m = ((duals[row_i] * DUAL_SCALE as f64).floor() as i128).clamp(0, DUAL_M_MAX);
            if m == 0 {
                continue;
            }
            base -= m;
            let (a, b, cn) = &tc.pairs[pi as usize];
            ay[*a as usize] -= m;
            ay[*b as usize] -= m;
            for &k in cn {
                if state.in_c[k as usize] {
                    ay[k as usize] += m;
                }
            }
        }
        for (qi, q) in cliques.iter().enumerate() {
            let m = ((duals[n_pair_rows + qi] * DUAL_SCALE as f64).floor() as i128)
                .clamp(0, DUAL_M_MAX);
            if m == 0 {
                continue;
            }
            base -= m;
            for &v in q {
                ay[v as usize] -= m;
            }
        }
        // Hole rows: `Σ_{v∈H} -x_v ≥ -2`, so y·b contributes -2m per row.
        for (hi, h) in holes.iter().enumerate() {
            let m = ((duals[n_pair_rows + cliques.len() + hi] * DUAL_SCALE as f64).floor() as i128)
                .clamp(0, DUAL_M_MAX);
            if m == 0 {
                continue;
            }
            base -= 2 * m;
            for &v in h {
                ay[v as usize] -= m;
            }
        }
        let d: Vec<i128> = ay.iter().map(|&a| -DUAL_SCALE - a).collect();
        let sum: i128 = (0..n).filter(|&v| state.in_c[v]).map(|v| d[v].min(0)).sum();
        let prune = base + sum >= -best_floor * DUAL_SCALE;
        return Some((
            RefreshOutcome {
                base,
                d,
                sum,
                prune,
            },
            None,
        ));
    }
    // Build the restricted LP in the solver's raw numeric form directly — no
    // per-term PbTerm/PbLit allocations, no per-row BTreeMap dedup. Row coeff
    // order: endpoints and CN merged sorted (pairs store a < b; CN is sorted).
    // Every None return below is TRACE-visible: an untraced decline path is
    // exactly how the hole-row row-count bug hid (all solves silently
    // discarded, zero decline lines — see viol_odd_hole_rows).
    let trace = std::env::var_os("TWO_CLUB_TRACE").is_some();
    let mut rows_raw: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
    let mut pair_of_row: Vec<u32> = Vec::new();
    for (pi, (a, b, cn)) in tc.pairs.iter().enumerate() {
        if !state.both_in[pi] {
            continue;
        }
        let (a, b) = (*a as usize, *b as usize);
        let mut coeffs: Vec<(usize, f64)> = Vec::with_capacity(cn.len() + 2);
        // Merge {a: -1, b: -1} into the sorted CN stream (CN never contains a
        // or b — a common neighbour is adjacent to both, endpoints are not;
        // a < b by the recognizer's normalization).
        let mut placed_a = false;
        let mut placed_b = false;
        for &k in cn {
            let k = k as usize;
            if state.in_c[k] {
                if !placed_a && a < k {
                    coeffs.push((a, -1.0));
                    placed_a = true;
                }
                if !placed_b && b < k {
                    if !placed_a {
                        coeffs.push((a, -1.0));
                        placed_a = true;
                    }
                    coeffs.push((b, -1.0));
                    placed_b = true;
                }
                coeffs.push((k, 1.0));
            }
        }
        if !placed_a {
            coeffs.push((a, -1.0));
        }
        if !placed_b {
            coeffs.push((b, -1.0));
        }
        rows_raw.push((coeffs, -1.0));
        pair_of_row.push(pi as u32);
        if cfg.max_rows != 0 && rows_raw.len() > cfg.max_rows {
            if trace {
                eprintln!(
                    "  [solve-none-maxrows] rows={} max={}",
                    rows_raw.len(),
                    cfg.max_rows
                );
            }
            return None; // too heavy at this node — decline (no prune).
        }
    }
    let c: Vec<f64> = (0..n)
        .map(|v| if state.in_c[v] { -1.0 } else { 0.0 })
        .collect();
    // FLOAT CLIQUE-CUT ROWS: violating-pair cliques (size ≥ 3) as extra LP
    // rows `Σ_{v∈Q} -x_v ≥ -1`. The 2-cliques are already the empty-CN pair
    // rows, so these are strictly new tightening — the lever aimed at the
    // measured c≈138 kill-frontier wall, where the plain relaxation stalls.
    let n_pair_rows = rows_raw.len();
    let cliques = viol_clique_rows(tc, state, 2000);
    for q in &cliques {
        let coeffs: Vec<(usize, f64)> = q.iter().map(|&v| (v as usize, -1.0)).collect();
        rows_raw.push((coeffs, -1.0));
    }
    let holes = viol_odd_hole_rows(tc, state, 400);
    for h in &holes {
        let coeffs: Vec<(usize, f64)> = h.iter().map(|&v| (v as usize, -1.0)).collect();
        rows_raw.push((coeffs, -2.0));
    }
    let nrows_dbg = rows_raw.len();
    let (duals, xstar) = match crate::optimize::safe_lp_bound::safe_lp_duals_and_primal_from_raw(
        n,
        c,
        rows_raw,
        // Early-exit at the prune threshold (see the Support-mode call above).
        Some(-(best_floor as f64) + 0.5),
        should_stop,
    ) {
        Some(dp) => dp,
        None => {
            if trace {
                eprintln!("  [solve-none-raw] raw returned None (rows={nrows_dbg})");
            }
            return None;
        }
    };
    if duals.len() != n_pair_rows + cliques.len() + holes.len() {
        if trace {
            eprintln!(
                "  [solve-none-len] duals={} pair={} cliques={} holes={}",
                duals.len(),
                n_pair_rows,
                cliques.len(),
                holes.len()
            );
        }
        return None; // row mapping broken — fail-closed.
    }
    // Dual SUPPORT (pairs whose row carried a positive multiplier) — the rows
    // that actually produce the bound; cached for cheap Support solves at
    // nearby nodes. A vertex optimum has at most ~#cols of them. (Clique rows
    // are node-local and never cached.)
    let mut support: Vec<u32> = Vec::new();
    for (row_i, &pi) in pair_of_row.iter().enumerate() {
        if duals[row_i] > 1e-12 {
            support.push(pi);
        }
    }

    // Round duals DOWN onto the integer grid (still a valid y >= 0) and price
    // the columns exactly: base = y·b (b_i = -1 for every row), Ay_v per column.
    let mut base: i128 = 0;
    let mut ay = vec![0i128; n];
    for (row_i, &pi) in pair_of_row.iter().enumerate() {
        let m = ((duals[row_i] * DUAL_SCALE as f64).floor() as i128).clamp(0, DUAL_M_MAX);
        if m == 0 {
            continue;
        }
        base -= m;
        let (a, b, cn) = &tc.pairs[pi as usize];
        ay[*a as usize] -= m;
        ay[*b as usize] -= m;
        for &k in cn {
            if state.in_c[k as usize] {
                ay[k as usize] += m;
            }
        }
    }
    for (qi, q) in cliques.iter().enumerate() {
        let m =
            ((duals[n_pair_rows + qi] * DUAL_SCALE as f64).floor() as i128).clamp(0, DUAL_M_MAX);
        if m == 0 {
            continue;
        }
        base -= m;
        for &v in q {
            ay[v as usize] -= m;
        }
    }
    // Hole rows: `Σ_{v∈H} -x_v ≥ -2`, so y·b contributes -2m per row. (Still
    // inside the overflow audit: ≤ 400 rows, |b| = 2 ⇒ base grows < 2^50.)
    for (hi, h) in holes.iter().enumerate() {
        let m = ((duals[n_pair_rows + cliques.len() + hi] * DUAL_SCALE as f64).floor() as i128)
            .clamp(0, DUAL_M_MAX);
        if m == 0 {
            continue;
        }
        base -= 2 * m;
        for &v in h {
            ay[v as usize] -= m;
        }
    }
    let mut d: Vec<i128> = ay.iter().map(|&a| -DUAL_SCALE - a).collect();
    let mut sum: i128 = (0..n).filter(|&v| state.in_c[v]).map(|v| d[v].min(0)).sum();

    // Prune decisions, all on the exact scaled grid: UB ≤ floor  ⇔
    // base + sum ≥ -floor·SCALE.
    let mut prune = base + sum >= -best_floor * DUAL_SCALE;
    // 2-DOMINATION CUT ROUND (near-misses only): separate the facet family at
    // x*, append violated cuts, resolve ONCE, re-price exactly, and adopt the
    // strengthened pricing when tighter. Diagnostic history: exact-triple
    // separation finds violations 0.05-0.33 at ~2/3 of near-misses, exactly at
    // the binding points (the development design notes*).
    if !prune && base + sum >= -(best_floor + 4) * DUAL_SCALE {
        // BOUNDED SEPARATION: both families — 2-domination triples
        // (hub-charging) and x*-violated cliques — are re-separated at each
        // round's new fractional point; cuts accumulate. Measurements showed
        // no prune conversions beyond the first round, so production keeps the
        // generic engine capped at one round to avoid the observed tailing-off.
        const CUT_SEPARATION_ROUNDS: usize = 1;
        let mut all_cuts: Vec<(Vec<u32>, Vec<(u32, u8)>)> = Vec::new();
        let mut x_cur = xstar.clone();
        for round in 0..CUT_SEPARATION_ROUNDS {
            if prune {
                break;
            }
            let mut fresh = indep_2dom_cuts(tc, state, &x_cur, 40);
            fresh.extend(violated_cliques_at_x(tc, state, &x_cur, 40));
            // Dedup against accumulated cuts by member list.
            fresh.retain(|(m, _)| !all_cuts.iter().any(|(m2, _)| m2 == m));
            if fresh.is_empty() {
                break;
            }
            all_cuts.extend(fresh);
            let Some((mut rows2, pair_of_row2, cliques2)) = build_solve_rows(tc, state, cfg) else {
                break;
            };
            let n_pc = rows2.len();
            for (members, hubs) in &all_cuts {
                let mut coeffs: Vec<(usize, f64)> = members
                    .iter()
                    .map(|&i| (i as usize, -1.0))
                    .chain(hubs.iter().map(|&(v, c)| (v as usize, c as f64)))
                    .collect();
                coeffs.sort_unstable_by_key(|e| e.0);
                rows2.push((coeffs, -1.0));
            }
            let c2: Vec<f64> = (0..n)
                .map(|v| if state.in_c[v] { -1.0 } else { 0.0 })
                .collect();
            let Some((duals2, x2)) =
                crate::optimize::safe_lp_bound::safe_lp_duals_and_primal_from_raw(
                    n,
                    c2,
                    rows2,
                    Some(-(best_floor as f64) + 0.5),
                    should_stop,
                )
            else {
                break;
            };
            if duals2.len() != n_pc + all_cuts.len() {
                break;
            }
            let mut base2: i128 = 0;
            let mut ay2 = vec![0i128; n];
            for (row_i, &pi) in pair_of_row2.iter().enumerate() {
                let m = ((duals2[row_i] * DUAL_SCALE as f64).floor() as i128).clamp(0, DUAL_M_MAX);
                if m == 0 {
                    continue;
                }
                base2 -= m;
                let (a, b, cn) = &tc.pairs[pi as usize];
                ay2[*a as usize] -= m;
                ay2[*b as usize] -= m;
                for &kk in cn {
                    if state.in_c[kk as usize] {
                        ay2[kk as usize] += m;
                    }
                }
            }
            for (qi, q) in cliques2.iter().enumerate() {
                let m = ((duals2[pair_of_row2.len() + qi] * DUAL_SCALE as f64).floor() as i128)
                    .clamp(0, DUAL_M_MAX);
                if m == 0 {
                    continue;
                }
                base2 -= m;
                for &v in q {
                    ay2[v as usize] -= m;
                }
            }
            for (ci, (members, hubs)) in all_cuts.iter().enumerate() {
                let m =
                    ((duals2[n_pc + ci] * DUAL_SCALE as f64).floor() as i128).clamp(0, DUAL_M_MAX);
                if m == 0 {
                    continue;
                }
                base2 -= m;
                for &i in members {
                    ay2[i as usize] -= m;
                }
                for &(v, cc) in hubs {
                    ay2[v as usize] += (cc as i128) * m;
                }
            }
            let d2: Vec<i128> = ay2.iter().map(|&a| -DUAL_SCALE - a).collect();
            let sum2: i128 = (0..n)
                .filter(|&v| state.in_c[v])
                .map(|v| d2[v].min(0))
                .sum();
            let improved = base2 + sum2 > base + sum;
            if std::env::var_os("TWO_CLUB_TRACE").is_some() {
                eprintln!(
                    "  [2cut] c={} round={} ub={:.2}->{:.2} ncuts={} improved={}",
                    state.c_size,
                    round + 1,
                    -((base + sum) as f64) / DUAL_SCALE as f64,
                    -((base2 + sum2) as f64) / DUAL_SCALE as f64,
                    all_cuts.len(),
                    improved,
                );
            }
            if improved {
                base = base2;
                d = d2;
                sum = sum2;
                prune = base + sum >= -best_floor * DUAL_SCALE;
            }
            x_cur = x2;
            if !improved {
                break;
            }
        }
    }
    if !prune && cfg.exact_margin > 0 && base + sum >= -(best_floor + cfg.exact_margin) * DUAL_SCALE
    {
        // Near miss: escalate to the exact rational LP + cutting-plane loop,
        // targeting exactly the floor (early exit once decisive). The
        // PB-constraint form is built lazily — only this rare path needs it.
        if let Some((objective, rows, _)) = build_restricted_lp(tc, state, cfg) {
            if let Some(exact_l) = crate::optimize::lp_bound::lp_lower_bound_with_target(
                &objective,
                &rows,
                n as u32,
                Some(-best_floor),
                should_stop,
            ) {
                prune = -exact_l <= best_floor;
            }
        }
    }
    Some((
        RefreshOutcome {
            base,
            d,
            sum,
            prune,
        },
        Some(support),
    ))
}

/// Exhaustive branch-and-bound. Returns (best_size, best_set) IFF the search ran
/// to completion within budgets; None on any cut-off (fail-closed).
fn solve_exact(
    tc: &TwoClub,
    seed_size: usize,
    lp: &LpNodeBound,
    should_stop: &dyn Fn() -> bool,
    on_club: &mut dyn FnMut(usize, &[bool]),
) -> Option<SearchVerdict> {
    solve_exact_cell(tc, &[], &[], seed_size, lp, should_stop, on_club)
}

/// Exhaustive max-2-club search over the CELL where every vertex in `forced_in`
/// is permanently kept and every vertex in `initial_removed` is removed before
/// the search begins. `forced_in = []`, `initial_removed = []` is the whole
/// space (the default `solve_exact`, byte-for-byte). The parallel prover
/// partitions the space by MINIMUM EXCLUDED VERTEX: cell `m` keeps `0..m` and
/// removes `m`. Every proper subset has a unique minimum excluded vertex, so
/// the cells are a disjoint, complete cover — N workers exhaust N non-
/// overlapping slices and their union is one full optimality proof.
fn solve_exact_cell(
    tc: &TwoClub,
    forced_in: &[bool],
    initial_removed: &[usize],
    seed_size: usize,
    lp: &LpNodeBound,
    should_stop: &dyn Fn() -> bool,
    on_club: &mut dyn FnMut(usize, &[bool]),
) -> Option<SearchVerdict> {
    let n = tc.n;
    let is_forced = |v: usize| forced_in.get(v).copied().unwrap_or(false);
    let mut state = SearchState {
        in_c: vec![true; n],
        c_size: n,
        cn_alive: tc.pairs.iter().map(|(_, _, cn)| cn.len() as u32).collect(),
        both_in: vec![true; tc.pairs.len()],
    };
    // Apply the cell's fixed removals once; they are never undone (the whole
    // search lives and dies inside this cell).
    let mut _init_undo = Vec::new();
    for &v in initial_removed {
        if state.in_c[v] {
            state.remove(v, tc, &mut _init_undo);
        }
    }
    let mut best: Option<(usize, Vec<bool>)> = None;
    let mut best_floor = seed_size; // sound pruning floor: a KNOWN 2-club size
    let mut nodes: u64 = 0;
    let node_cap = max_nodes();
    let progress = std::env::var_os("TWO_CLUB_TRACE").is_some();
    let t_start = std::time::Instant::now();
    let mut next_report: u64 = 50_000_000;
    let mut next_time_report: u64 = 600;
    // Incremental dual-bound state (see `LpNodeBound` / `DualSnapshot`). The
    // starting pricing is `y = 0`: base 0, every reduced cost `-DUAL_SCALE` —
    // whose bound is EXACTLY the cardinality bound, so behavior before the first
    // refresh is identical to the baseline. `dual_stack` holds previous pricings
    // to restore as refresh subtrees unwind. Invariant whenever `lp.enabled`:
    // `dual_sum == Σ_{v∈C} min(0, dual_d[v])`, maintained O(1) at every
    // remove/undo site below.
    let mut dual_base: i128 = 0;
    let mut dual_d: Vec<i128> = vec![-DUAL_SCALE; n];
    let mut dual_sum: i128 = -(state.c_size as i128) * DUAL_SCALE;
    let mut dual_stack: Vec<DualSnapshot> = Vec::new();
    let mut lp_next_refresh: u64 = lp.warmup;
    let mut lp_prunes: u64 = 0;
    // Of `lp_prunes`, how many came from the free O(1) inherited-pricing test
    // (the rest paid a refresh LP). The ratio tells whether inheritance is
    // engaged (healthy) or every kill is buying a fresh LP (thrash).
    let mut lp_prunes_o1: u64 = 0;
    // Of `lp_prunes`, how many were KILL-LIFT prunes (a node killed at
    // AfterLeft before its right child expanded — each erases a sibling
    // subtree and cascades the unwind one level higher).
    let mut lp_prunes_lift: u64 = 0;
    // Success-feedback gate for kill-lift: set on every LP prune, cleared on a
    // failed lift, a 2-club leaf, or a dead branch. Lifting only while kills
    // keep succeeding collapses a killed cone upward in O(depth) refreshes and
    // wastes at most ONE refresh per cascade — measured without this gate,
    // lifting at every in-window AfterLeft was 95% failures (UB is
    // path-dependent: band-top C's are LP-fat even where deep C's are thin).
    let mut cascade = false;
    let mut lp_refreshes: u64 = 0;
    // Matching-bound kills (LP-free; see greedy_viol_matching).
    let mut lp_prunes_m: u64 = 0;
    // Cheap dual re-pricings (no simplex) tried at cascade rungs.
    let mut lp_reprices: u64 = 0;
    // CEILING ATTACK state: `ceil_frontier` tracks the highest c of any
    // LP-family kill (trace/diagnostic); the GATE uses `lift_frontier` — the
    // highest c of CASCADE kills only. Enter-matching kills land during
    // descents at up to ~c=140 and would otherwise starve the cascade-top
    // escalations (which top out lower) if they set the gate.
    let mut ceil_frontier: usize = 0;
    let mut lift_frontier: usize = 0;
    let mut ceil_spent = std::time::Duration::ZERO;
    let mut lp_ceil_try: u64 = 0;
    // Endgame-shape instrumentation: dives (boundary first-touch events) and
    // right-child expansions by height band — the effective branching factor
    // ABOVE the kill frontier decides whether the residual enumeration is
    // days or centuries.
    let mut n_dives: u64 = 0;
    let mut rx_150: u64 = 0; // right expansions at c in [150,160)
    let mut rx_160: u64 = 0; // [160,170)
    let mut rx_170: u64 = 0; // [170,200]
    let mut rx_lo: u64 = 0; //  < 150
    let mut lp_ceil_kill_a: u64 = 0; // float-solve tier
    let lp_ceil_kill_b: u64 = 0; // exact LP+cuts tier
                                 // Dual SUPPORT pairs from the most recent FULL refresh; Support solves
                                 // re-optimize y on just these rows (~100x cheaper) at nearby nodes.
    let mut dual_support: Option<Vec<u32>> = None;

    // Explicit DFS: each frame is (vertex_removed, undo_log, phase).
    enum Frame {
        Enter,
        AfterLeft { second: Option<usize> },
        Exit,
    }
    // Recursive helper via explicit stack of (frame, removed_vertex, undo).
    // `snap`: this node adopted a dual snapshot when it branched; pop it
    // (restoring the previous pricing) when its subtree unwinds — BEFORE undoing
    // the node's own removal, which was accounted under the previous pricing.
    struct StackItem {
        frame: Frame,
        removed: Option<usize>,
        undo: Vec<(u32, u8)>,
        snap: bool,
        /// `c_size` when this frame was pushed — lets the progress trace report
        /// the OPEN stack's c-distribution (how much skeleton hangs above the
        /// kill frontier, the number that decides grind-vs-restructure).
        c_at: usize,
    }
    let mut stack = vec![StackItem {
        frame: Frame::Enter,
        removed: None,
        undo: Vec::new(),
        snap: false,
        c_at: state.c_size,
    }];
    let mut completed = true;

    while let Some(mut item) = stack.pop() {
        match item.frame {
            Frame::Enter => {
                nodes += 1;
                if nodes & STOP_POLL_MASK == 0 && should_stop() {
                    completed = false;
                    break;
                }
                if nodes > node_cap {
                    completed = false;
                    break;
                }
                // Progress line: node-count based, PLUS time-based (every 600s,
                // checked on the cheap stop-poll cadence) so LP-band cells whose
                // node rate is orders below the raw rate still report.
                if progress
                    && (nodes >= next_report
                        || (nodes & STOP_POLL_MASK == 0
                            && t_start.elapsed().as_secs() >= next_time_report))
                {
                    let secs = t_start.elapsed().as_secs_f64();
                    // Open-stack c-distribution: min/median/max of the c at
                    // which the open frames were pushed — the live picture of
                    // how much skeleton hangs above the kill frontier.
                    let mut cs: Vec<usize> = stack.iter().map(|it| it.c_at).collect();
                    cs.sort_unstable();
                    let (cmin, cmed, cmax) = if cs.is_empty() {
                        (0, 0, 0)
                    } else {
                        (cs[0], cs[cs.len() / 2], cs[cs.len() - 1])
                    };
                    eprintln!(
                        "  [cell] nodes={nodes} rate={:.0}/s open={} oc={cmin}/{cmed}/{cmax} floor={best_floor} lp_prunes={lp_prunes} o1={lp_prunes_o1} lift={lp_prunes_lift} m={lp_prunes_m} refreshes={lp_refreshes} subs={lp_reprices} ceil={lp_ceil_try}/{lp_ceil_kill_a}+{lp_ceil_kill_b} front={ceil_frontier} dives={n_dives} rx={rx_lo}/{rx_150}/{rx_160}/{rx_170} t={secs:.0}s",
                        nodes as f64 / secs.max(1e-9),
                        stack.len()
                    );
                    if nodes >= next_report {
                        next_report += 50_000_000;
                    }
                    next_time_report = t_start.elapsed().as_secs() + 600;
                }
                // Prune: cannot beat the best known 2-club (seed or discovered).
                if state.c_size <= best_floor {
                    // Deliberately does NOT arm the kill-lift cascade:
                    // cardinality prunes fire constantly inside cardinality-
                    // tight (LP-fat) cones, where every armed lift is a wasted
                    // full LP — measured: arming here collapsed total prunes
                    // 183 → 6 per 150 s. Only LP prunes (evidence of
                    // LP-thinness on this path) arm cascades.
                    // undo this frame's removal on unwind.
                    if let Some(v) = item.removed {
                        if lp.enabled {
                            dual_sum += dual_d[v].min(0);
                        }
                        state.undo(v, &item.undo);
                    }
                    continue;
                }
                // MATCHING prune — LP-free: every 2-club in C excludes one
                // endpoint of each violating pair, and matched pairs are
                // vertex-disjoint, so |S| ≤ c_size − ν. Measured: ν ≥ c−floor
                // at essentially every site the LP kills, so this replaces most
                // refresh LPs with a ~20µs scan. Arms the cascade (matching IS
                // the LP's deep-cone mechanism, so it is the same thinness
                // signal).
                if lp.enabled && state.c_size > best_floor {
                    let nu = greedy_viol_matching(tc, &state);
                    if state.c_size - nu <= best_floor {
                        lp_prunes += 1;
                        lp_prunes_m += 1;
                        cascade = true;
                        ceil_frontier = ceil_frontier.max(state.c_size);
                        if let Some(v) = item.removed {
                            dual_sum += dual_d[v].min(0);
                            state.undo(v, &item.undo);
                        }
                        continue;
                    }
                }
                // O(1) dual-snapshot prune — as sound as the cardinality prune
                // (`-(base+sum)/SCALE` upper-bounds every 2-club in C):
                // UB ≤ floor  ⇔  base + sum ≥ -floor·SCALE.
                let mut fresh: Option<RefreshOutcome> = None;
                if lp.enabled {
                    let floor_scaled = -(best_floor as i128) * DUAL_SCALE;
                    if dual_base + dual_sum >= floor_scaled {
                        lp_prunes += 1;
                        lp_prunes_o1 += 1;
                        cascade = true;
                        if let Some(v) = item.removed {
                            dual_sum += dual_d[v].min(0);
                            state.undo(v, &item.undo);
                        }
                        continue;
                    }
                    // Refresh policy: (a) FIRST-TOUCH — exactly at the window
                    // BOUNDARY crossing (c == floor+window; or the cell's root
                    // if it starts inside the band) with no adopted pricing:
                    // refresh immediately so band entries are priced (and, in
                    // LP-thin regions, killed) on contact. The trigger MUST be
                    // the crossing, not "no pricing adopted": in
                    // cardinality-tight cones (UB = |C|, measured at c≈71–85)
                    // adoption can never succeed, and an is-empty trigger
                    // re-fires a full LP at EVERY node — measured 3,851
                    // refreshes for 4,096 nodes, a 40 ms/node collapse.
                    // (b) CADENCED — inside the band, re-price every `cadence`
                    // nodes: kills where the path is LP-thin, bounded waste
                    // where it is tight.
                    let boundary = best_floor.saturating_add(lp.window);
                    if state.c_size <= boundary
                        && state.c_size > best_floor.saturating_add(lp.low_margin)
                        && (nodes >= lp_next_refresh
                            || (dual_stack.is_empty() && (state.c_size == boundary || nodes == 1)))
                    {
                        if dual_stack.is_empty() && state.c_size == boundary {
                            n_dives += 1;
                        }
                        lp_next_refresh = nodes.saturating_add(lp.cadence);
                        // Reprice-first here too: sibling band entries price
                        // near-identical C's, so the cached dual usually
                        // already proves the kill for ~1ms; the full solve is
                        // paid only when the cheap bound cannot prune.
                        fresh = None;
                        if let Some(cache) = dual_support.as_deref() {
                            lp_reprices += 1;
                            if let Some((f, _)) = refresh_dual_snapshot(
                                tc,
                                &state,
                                lp,
                                best_floor as i128,
                                RefreshMode::Support(cache),
                                should_stop,
                            ) {
                                if f.prune {
                                    fresh = Some(f);
                                }
                            }
                        }
                        if fresh.is_none() {
                            fresh = refresh_dual_snapshot(
                                tc,
                                &state,
                                lp,
                                best_floor as i128,
                                RefreshMode::Solve,
                                should_stop,
                            )
                            .map(|(f, y)| {
                                if let Some(y) = y {
                                    dual_support = Some(y);
                                }
                                f
                            });
                        }
                        if let Some(f) = &fresh {
                            lp_refreshes += 1;
                            // TRACE: sampled refresh (c, UB) distribution — for
                            // pruning refreshes the c-histogram locates the
                            // crossover c* (how high in the tree the LP still
                            // dips under the floor: the window should reach it);
                            // for non-pruning ones the UB says whether stronger
                            // in-refresh cuts could convert them.
                            if progress
                                && (lp_refreshes.is_multiple_of(128)
                                    || (!f.prune && lp_refreshes.is_multiple_of(32)))
                            {
                                eprintln!(
                                    "  [refresh] c={} ub={:.2} floor={best_floor} pruned={} nu={}",
                                    state.c_size,
                                    -((f.base + f.sum) as f64) / DUAL_SCALE as f64,
                                    f.prune,
                                    greedy_viol_matching(tc, &state),
                                );
                            }
                            if f.prune {
                                lp_prunes += 1;
                                cascade = true;
                                ceil_frontier = ceil_frontier.max(state.c_size);
                                if let Some(v) = item.removed {
                                    dual_sum += dual_d[v].min(0);
                                    state.undo(v, &item.undo);
                                }
                                continue;
                            }
                            // Adopt only a pricing that is strictly tighter at
                            // this node than the inherited one.
                            if f.base + f.sum <= dual_base + dual_sum {
                                fresh = None;
                            }
                        }
                    }
                }
                match state.find_violating() {
                    None => {
                        // C is a 2-club: the subtree was NOT killed — ancestors
                        // contain it and will not LP-prune; disarm the cascade.
                        cascade = false;
                        // Record incumbent = whole C.
                        let set: Vec<bool> = state.in_c.clone();
                        on_club(state.c_size, &set);
                        if state.c_size > best_floor {
                            best_floor = state.c_size;
                            best = Some((state.c_size, set));
                        }
                        if let Some(v) = item.removed {
                            if lp.enabled {
                                dual_sum += dual_d[v].min(0);
                            }
                            state.undo(v, &item.undo);
                        }
                        continue;
                    }
                    Some(pi) => {
                        let a = tc.pairs[pi].0 as usize;
                        let b = tc.pairs[pi].1 as usize;
                        // Only NON-forced endpoints may be removed. A violating
                        // pair whose BOTH endpoints are forced-in cannot be
                        // repaired — this cell holds no 2-club: dead branch.
                        let ra = !is_forced(a);
                        let rb = !is_forced(b);
                        if !ra && !rb {
                            // Dead branch by forcing, not by bound — the parent
                            // C is not evidence of LP-thinness; disarm.
                            cascade = false;
                            if let Some(v) = item.removed {
                                if lp.enabled {
                                    dual_sum += dual_d[v].min(0);
                                }
                                state.undo(v, &item.undo);
                            }
                            continue;
                        }
                        // Adopt the fresh pricing for this subtree: save the
                        // previous state; the flag on this node's own frame pops
                        // it when the subtree unwinds.
                        if let Some(f) = fresh {
                            dual_stack.push(DualSnapshot {
                                base: dual_base,
                                d: std::mem::replace(&mut dual_d, f.d),
                                saved_sum: dual_sum,
                            });
                            dual_base = f.base;
                            dual_sum = f.sum;
                            item.snap = true;
                        }
                        let left = if ra { a } else { b };
                        let second = if ra && rb { Some(b) } else { None };
                        // Re-push self to run the right branch after the left.
                        item.frame = Frame::AfterLeft { second };
                        stack.push(item);
                        let mut undo = Vec::new();
                        if lp.enabled {
                            dual_sum -= dual_d[left].min(0);
                        }
                        state.remove(left, tc, &mut undo);
                        stack.push(StackItem {
                            frame: Frame::Enter,
                            removed: Some(left),
                            undo,
                            snap: false,
                            c_at: state.c_size,
                        });
                    }
                }
            }
            Frame::AfterLeft { second } => match second {
                Some(j) => {
                    // KILL-LIFT: before expanding the right child, re-price THIS
                    // node's C (the left subtree has fully unwound, so the state
                    // is exactly C_X). If UB(C_X) ≤ floor, no 2-club in C_X can
                    // beat the incumbent — the right child (⊆ C_X) is skipped
                    // and the node dies. This is what collapses a killed bottom
                    // cone in O(depth) refreshes instead of 2^depth nodes: the
                    // per-node LP bound is far below the floor throughout the
                    // cone (measured UB ≈ c/2 on 2club200v15p5scn), but without
                    // the lift the DFS only ever kills at the cone's bottom.
                    // NOTE: deliberately NOT window-limited. The window bounds
                    // where refreshes START (band entries); a cascade must be
                    // free to climb ABOVE it — after a boundary kill at c=130
                    // (measured UB 66.5 there), ancestors at 131, 132, … often
                    // still price under the floor, and each successful lift
                    // erases an exponentially larger above-boundary subtree.
                    // Success-feedback (one failed refresh ends the climb) is
                    // the only stop condition a cascade needs.
                    if lp.enabled
                        && cascade
                        && state.c_size > best_floor.saturating_add(lp.low_margin)
                    {
                        // Rung 1 (cheap): re-price the cached dual against the
                        // current rows — no simplex, ~1000× cheaper. Between
                        // ladder rungs C changes by one vertex, so the stale
                        // dual stays sharp and this kills most rungs alone.
                        // Rung 2 (full solve) only when the cheap bound cannot
                        // prune — it also refreshes the cache.
                        let mut lift_kill: Option<i128> = None;
                        // Rung 0 (free): the matching bound.
                        let nu = greedy_viol_matching(tc, &state);
                        if state.c_size - nu <= best_floor {
                            lift_kill = Some(-((state.c_size - nu) as i128) * DUAL_SCALE);
                            lp_prunes_m += 1;
                        }
                        if lift_kill.is_none() {
                            if let Some(cache) = dual_support.as_deref() {
                                lp_reprices += 1;
                                if let Some((f, _)) = refresh_dual_snapshot(
                                    tc,
                                    &state,
                                    lp,
                                    best_floor as i128,
                                    RefreshMode::Support(cache),
                                    should_stop,
                                ) {
                                    if f.prune {
                                        lift_kill = Some(f.base + f.sum);
                                    }
                                }
                            }
                        }
                        // NO unconditional full-solve rung: a failed cascade
                        // must cost ~ms — measured with an ungated full-solve
                        // fallback, cheap matching kills spawned failed
                        // cascades whose full solves exploded 247 → 1,884 per
                        // 120 s and throughput DROPPED.
                        //
                        // CEILING ATTACK — the one place expensive solves buy
                        // the exponent: at the cascade's TOP failed rung, only
                        // within 2 levels of the kill frontier and under a
                        // ≤¼-wall-time budget, escalate: (A) full float solve
                        // (also feeds the support cache); (B) the exact
                        // rational LP + clique/cover cut loop with a hard
                        // deadline. Each success extends the cascade one level
                        // ≈ halves the remaining above-frontier skeleton.
                        if lift_kill.is_none()
                            && lp.ceiling
                            && state.c_size + 2 >= lift_frontier
                            && lift_frontier > 0
                            && ceil_spent.as_secs_f64() * 4.0
                                <= t_start.elapsed().as_secs_f64() + 1.0
                        {
                            lp_ceil_try += 1;
                            let t0 = std::time::Instant::now();
                            // Tier A: full float solve.
                            lp_refreshes += 1;
                            let mut ceil_fail_ub: Option<f64> = None;
                            if let Some((f, y)) = refresh_dual_snapshot(
                                tc,
                                &state,
                                lp,
                                best_floor as i128,
                                RefreshMode::Solve,
                                should_stop,
                            ) {
                                if let Some(y) = y {
                                    dual_support = Some(y);
                                }
                                if f.prune {
                                    lift_kill = Some(f.base + f.sum);
                                    lp_ceil_kill_a += 1;
                                } else {
                                    // The near-miss question: how far above the
                                    // floor does the strengthened LP sit where
                                    // the frontier stalls?
                                    ceil_fail_ub =
                                        Some(-((f.base + f.sum) as f64) / DUAL_SCALE as f64);
                                }
                            }
                            // EXACT-AT-NEAR-MISS tier: tried and REMOVED —
                            // measured 0-for-8 (the exact rational LP cannot
                            // converge on ~9.5k rows inside a 30s deadline, so
                            // the float-slack hypothesis at the 70.1-70.5
                            // near-misses stays untestable at acceptable cost;
                            // net ~-7% throughput). The frontier at 145-147 is
                            // the TRUE strength of the pair+clique float
                            // relaxation.
                            ceil_spent += t0.elapsed();
                            if progress {
                                eprintln!(
                                    "  [ceil] c={} lfront={} kill={} ub={} t={:.1}s spent={:.0}s",
                                    state.c_size,
                                    lift_frontier,
                                    lift_kill.is_some(),
                                    ceil_fail_ub
                                        .map(|u| format!("{u:.1}"))
                                        .unwrap_or_else(|| "-".into()),
                                    t0.elapsed().as_secs_f64(),
                                    ceil_spent.as_secs_f64(),
                                );
                            }
                        }
                        if let Some(lb) = lift_kill {
                            lp_prunes += 1;
                            lp_prunes_lift += 1;
                            ceil_frontier = ceil_frontier.max(state.c_size);
                            lift_frontier = lift_frontier.max(state.c_size);
                            // TRACE every lift kill: the c at which cascades
                            // erase subtrees is the whole value question
                            // (a kill at c=131 outweighs ~2^55 kills at 76).
                            if progress {
                                eprintln!(
                                    "  [lift] c={} ub={:.2} floor={best_floor} nu={}",
                                    state.c_size,
                                    -(lb as f64) / DUAL_SCALE as f64,
                                    greedy_viol_matching(tc, &state),
                                );
                            }
                            // Unwind exactly like the no-second-branch arm.
                            if item.snap {
                                if let Some(prev) = dual_stack.pop() {
                                    dual_base = prev.base;
                                    dual_d = prev.d;
                                    dual_sum = prev.saved_sum;
                                } else {
                                    debug_assert!(false, "snapshot stack underflow");
                                    dual_base = 0;
                                    dual_d = vec![-DUAL_SCALE; n];
                                    dual_sum = -(state.c_size as i128) * DUAL_SCALE;
                                }
                            }
                            if let Some(v) = item.removed {
                                dual_sum += dual_d[v].min(0);
                                state.undo(v, &item.undo);
                            }
                            continue;
                        }
                    }
                    // Right child expands ⇒ this node was not liftable; the
                    // cascade (if any) ends here.
                    match state.c_size {
                        c if c >= 170 => rx_170 += 1,
                        c if c >= 160 => rx_160 += 1,
                        c if c >= 150 => rx_150 += 1,
                        _ => rx_lo += 1,
                    }
                    cascade = false;
                    item.frame = Frame::Exit;
                    stack.push(item);
                    let mut undo = Vec::new();
                    if lp.enabled {
                        dual_sum -= dual_d[j].min(0);
                    }
                    state.remove(j, tc, &mut undo);
                    stack.push(StackItem {
                        frame: Frame::Enter,
                        removed: Some(j),
                        undo,
                        snap: false,
                        c_at: state.c_size,
                    });
                }
                None => {
                    // No second (right) branch — the left endpoint was the only
                    // removable one. Unwind: pop this node's snapshot FIRST
                    // (the subtree's removes/undos all paired up under it, so
                    // the restored `saved_sum` is exact), THEN undo the node's
                    // own removal against the restored (parent-era) pricing.
                    if item.snap {
                        if let Some(prev) = dual_stack.pop() {
                            dual_base = prev.base;
                            dual_d = prev.d;
                            dual_sum = prev.saved_sum;
                        } else {
                            // Unreachable by construction; recover to the sound
                            // zero pricing (== cardinality bound) fail-closed.
                            debug_assert!(false, "snapshot stack underflow");
                            dual_base = 0;
                            dual_d = vec![-DUAL_SCALE; n];
                            dual_sum = -(state.c_size as i128) * DUAL_SCALE;
                        }
                    }
                    if let Some(v) = item.removed {
                        if lp.enabled {
                            dual_sum += dual_d[v].min(0);
                        }
                        state.undo(v, &item.undo);
                    }
                }
            },
            Frame::Exit => {
                // Pop-before-undo: same discipline as AfterLeft(None).
                if item.snap {
                    if let Some(prev) = dual_stack.pop() {
                        dual_base = prev.base;
                        dual_d = prev.d;
                        dual_sum = prev.saved_sum;
                    } else {
                        debug_assert!(false, "snapshot stack underflow");
                        dual_base = 0;
                        dual_d = vec![-DUAL_SCALE; n];
                        dual_sum = -(state.c_size as i128) * DUAL_SCALE;
                    }
                }
                if let Some(v) = item.removed {
                    if lp.enabled {
                        dual_sum += dual_d[v].min(0);
                    }
                    state.undo(v, &item.undo);
                }
            }
        }
    }

    if progress {
        eprintln!(
            "  [cell done] nodes={nodes} lp_prunes={lp_prunes} o1={lp_prunes_o1} lift={lp_prunes_lift} m={lp_prunes_m} refreshes={lp_refreshes} subs={lp_reprices} ceil={lp_ceil_try}/{lp_ceil_kill_a}+{lp_ceil_kill_b} front={ceil_frontier} dives={n_dives} rx={rx_lo}/{rx_150}/{rx_160}/{rx_170} floor={best_floor} completed={completed} t={:.2}s",
            t_start.elapsed().as_secs_f64()
        );
    }

    if completed {
        Some(match best {
            Some((size, set)) => SearchVerdict::Better(size, set),
            None => SearchVerdict::SeedOptimal,
        })
    } else {
        None
    }
}

/// Outcome of an EXHAUSTED search relative to the seeded floor.
enum SearchVerdict {
    /// A 2-club strictly larger than the seed was found (and is the optimum).
    Better(usize, Vec<bool>),
    /// No 2-club beats the seed: the seeded incumbent is optimal.
    SeedOptimal,
}

/// Parallel optimality prover: worker `w` of `nworkers` exhausts exactly the
/// min-excluded cells `m` with `m % nworkers == w` (plus, on worker 0, the
/// full-set cell). Because the cells are disjoint and cover every proper
/// subset, the union of all workers reporting `all_done` with no club beating
/// the seed IS a complete proof that the seed is the maximum 2-club. Returns
/// `(best_found, all_owned_cells_exhausted)`; `None` if not recognized or the
/// seed does not re-verify (the prover REQUIRES a verified floor — fail-closed).
pub(crate) fn two_club_prove_worker(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize(instance, objective)?;
    let n = tc.n;
    let seed_size = match seed {
        Some(s) if s.len() == n && verify_all_constraints(&instance.constraints, s) => {
            s.iter().filter(|&&b| b).count()
        }
        _ => return None,
    };
    let mut stream = |size: usize, set: &[bool]| {
        if verify_all_constraints(&instance.constraints, set) {
            on_improve(-(size as i128), set);
        }
    };
    let mut best = seed_size;
    let mut all_done = true;
    // The full-set cell (S = V, no excluded vertex): worker 0 owns it.
    if worker == 0 {
        let forced = vec![true; n];
        match solve_exact_cell(&tc, &forced, &[], seed_size, lp, should_stop, &mut stream) {
            Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
            Some(SearchVerdict::SeedOptimal) => {}
            None => all_done = false,
        }
    }
    let mut m = worker;
    while m < n && all_done {
        if should_stop() {
            all_done = false;
            break;
        }
        // Cell m: keep 0..m permanently, remove m at the start.
        let mut forced = vec![false; n];
        forced[..m].fill(true);
        match solve_exact_cell(&tc, &forced, &[m], seed_size, lp, should_stop, &mut stream) {
            Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
            Some(SearchVerdict::SeedOptimal) => {}
            None => all_done = false,
        }
        m += nworkers;
    }
    Some((best, all_done))
}

/// DEPTH-2 parallel prover: splits every top-level cell `m` (with
/// `m % base_mod` in `classes`) by its SECOND excluded vertex `m2 > m` into
/// sub-cells `[m, m2]` (keep `0..m` and `m+1..m2` , remove `m` and `m2`), plus
/// the single-point sub-cell `V \ {m}`. The sub-cells of a top cell are a
/// disjoint complete cover of it (second-min-excluded), so this refines the
/// level-1 partition without changing what it covers — it exists purely to
/// spread a billion-node bottleneck cell across many cores. Worker `w` of
/// `nworkers` owns sub-cells by global round-robin index. Returns
/// `(best, all_owned_exhausted)`; `None` if not recognized / seed unverified.
pub(crate) fn two_club_prove_d2_worker(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    base_mod: usize,
    classes: &[usize],
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize(instance, objective)?;
    let n = tc.n;
    let seed_size = match seed {
        Some(s) if s.len() == n && verify_all_constraints(&instance.constraints, s) => {
            s.iter().filter(|&&b| b).count()
        }
        _ => return None,
    };
    let mut stream = |size: usize, set: &[bool]| {
        if verify_all_constraints(&instance.constraints, set) {
            on_improve(-(size as i128), set);
        }
    };
    let mut best = seed_size;
    let mut all_done = true;
    // Global sub-cell counter for round-robin ownership across the SAME (m, m2)
    // enumeration every worker walks — so the assignment is consistent without
    // any shared state.
    let mut gidx = 0usize;
    let owns = |g: usize| g % nworkers == worker;
    let in_class = |m: usize| classes.iter().any(|&c| m % base_mod == c);

    // The full-set cell (S = V, no excluded vertex) belongs to no `[m]` — the
    // level-1 prover checks it explicitly and so must this one, or a graph whose
    // whole vertex set is a 2-club is silently dropped. Owned as sub-cell 0.
    // (Only meaningful when class 0 is present, matching level-1's worker-0
    // convention; it is a single dead-fast check otherwise.)
    if owns(gidx) && in_class(0) {
        let forced = vec![true; n];
        match solve_exact_cell(&tc, &forced, &[], seed_size, lp, should_stop, &mut stream) {
            Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
            Some(SearchVerdict::SeedOptimal) => {}
            None => all_done = false,
        }
    }
    gidx += 1;

    for m in 0..n {
        if !in_class(m) {
            continue;
        }
        // Single-point sub-cell: is V \ {m} itself a 2-club?
        if owns(gidx) {
            let mut forced = vec![true; n];
            forced[m] = false;
            match solve_exact_cell(&tc, &forced, &[m], seed_size, lp, should_stop, &mut stream) {
                Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
                Some(SearchVerdict::SeedOptimal) => {}
                None => all_done = false,
            }
        }
        gidx += 1;
        // Sub-cells [m, m2] for every second excluded vertex m2 > m.
        for m2 in (m + 1)..n {
            if owns(gidx) {
                if should_stop() {
                    all_done = false;
                } else {
                    // keep 0..m and m+1..m2, remove m and m2, free > m2.
                    let mut forced = vec![false; n];
                    for (v, f) in forced.iter_mut().enumerate().take(m2) {
                        *f = v != m; // v < m2, v != m (m2 itself is removed)
                    }
                    match solve_exact_cell(
                        &tc,
                        &forced,
                        &[m, m2],
                        seed_size,
                        lp,
                        should_stop,
                        &mut stream,
                    ) {
                        Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
                        Some(SearchVerdict::SeedOptimal) => {}
                        None => all_done = false,
                    }
                }
            }
            gidx += 1;
        }
    }
    Some((best, all_done))
}

/// PIVOT-SET parallel prover — the load-balanced partition. The min-excluded
/// scheme concentrates work in one corner (exclude the lowest vertices, force
/// NOTHING in) that stays near-full-size at every split depth, because forcing
/// vertices IN is what shrinks a 2-club search and that corner forces none.
/// This instead fixes a pivot set `P` of the `k` HIGHEST-degree vertices and
/// enumerates all `2^k` in/out patterns: cell `A ⊆ P` forces `A` in and removes
/// `P \ A`. Every proper... every subset `S` has a unique `S ∩ P`, so the `2^k`
/// cells are a disjoint, complete cover — and crucially EVERY cell fixes `k`
/// decisions, so no cell is the whole problem. Patterns that force an
/// incompatible pair in die immediately; the all-out cell removes the `k`
/// highest-degree hubs (a big cut), so the heavy tail is bounded. Worker `w`
/// owns patterns `p` with `p % nworkers == w`.
pub(crate) fn two_club_prove_pivot_worker(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    k: usize,
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize(instance, objective)?;
    let n = tc.n;
    let seed_size = match seed {
        Some(s) if s.len() == n && verify_all_constraints(&instance.constraints, s) => {
            s.iter().filter(|&&b| b).count()
        }
        _ => return None,
    };
    let k = k.min(n).min(20); // 2^k patterns — keep it sane
                              // Pivots: the k highest-degree vertices (fewest non-adjacent pairs). Degree
                              // ties broken by index for determinism across workers.
    let mut non_adj_ct = vec![0usize; n];
    for &(a, b, _) in &tc.pairs {
        non_adj_ct[a as usize] += 1;
        non_adj_ct[b as usize] += 1;
    }
    let mut by_deg: Vec<usize> = (0..n).collect();
    by_deg.sort_by_key(|&v| (non_adj_ct[v], v)); // fewest non-adj first = highest degree
    let pivots: Vec<usize> = by_deg.into_iter().take(k).collect();

    let mut stream = |size: usize, set: &[bool]| {
        if verify_all_constraints(&instance.constraints, set) {
            on_improve(-(size as i128), set);
        }
    };
    let mut best = seed_size;
    let mut all_done = true;
    for pat in 0u32..(1u32 << k) {
        if pat as usize % nworkers != worker {
            continue;
        }
        if should_stop() {
            all_done = false;
            break;
        }
        let mut forced_in = vec![false; n];
        let mut removed = Vec::new();
        for (i, &p) in pivots.iter().enumerate() {
            if pat & (1 << i) != 0 {
                forced_in[p] = true; // pivot in the club
            } else {
                removed.push(p); // pivot excluded
            }
        }
        match solve_exact_cell(
            &tc,
            &forced_in,
            &removed,
            seed_size,
            lp,
            should_stop,
            &mut stream,
        ) {
            Some(SearchVerdict::Better(sz, _)) => best = best.max(sz),
            Some(SearchVerdict::SeedOptimal) => {}
            None => all_done = false,
        }
    }
    Some((best, all_done))
}

/// Attempts to solve `instance` exactly as a maximum 2-club. Returns
/// `Some(OptimumFound)` with a re-verified witness when recognized and the
/// exhaustive search completes; `None` otherwise (not recognized, budget or
/// deadline cut — fail-closed, the portfolio continues untouched).
pub(crate) fn try_two_club_exact(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: Option<&[bool]>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<PbSolution> {
    let tc = recognize(instance, objective)?;
    if should_stop() {
        return None;
    }
    // Seed floor: the incumbent must RE-VERIFY as a feasible 2-club of the
    // instance before its size may prune anything (a bad seed could otherwise
    // prune the true optimum away — fail-closed: unverified seeds are ignored).
    let mut seed_size = 0usize;
    let mut seed_set: Option<Vec<bool>> = None;
    if let Some(inc) = incumbent {
        if inc.len() == tc.n && verify_all_constraints(&instance.constraints, inc) {
            seed_size = inc.iter().filter(|&&b| b).count();
            seed_set = Some(inc.to_vec());
        }
    }
    // Star fallback seed: for any vertex v, {v} ∪ N(v) is a 2-club (every pair
    // meets through v). Take the max-degree star; verify like any other seed.
    if seed_set.is_none() {
        let n = tc.n;
        let mut non_adj = vec![vec![false; n]; n];
        for &(a, b, _) in &tc.pairs {
            non_adj[a as usize][b as usize] = true;
            non_adj[b as usize][a as usize] = true;
        }
        let mut best_v = 0usize;
        let mut best_deg = 0usize;
        for v in 0..n {
            let deg = (0..n).filter(|&u| u != v && !non_adj[v][u]).count();
            if deg > best_deg {
                best_deg = deg;
                best_v = v;
            }
        }
        let mut star = vec![false; n];
        star[best_v] = true;
        for u in 0..n {
            if u != best_v && !non_adj[best_v][u] {
                star[u] = true;
            }
        }
        if verify_all_constraints(&instance.constraints, &star) {
            seed_size = best_deg + 1;
            seed_set = Some(star);
        }
    }
    let mut stream = |size: usize, set: &[bool]| {
        // Every discovered 2-club is a feasible witness: stream it (anytime).
        let value = -(size as i128);
        if verify_all_constraints(&instance.constraints, set) {
            on_improve(value, set);
        }
    };
    // Production: the sound LP node bound is on — it can only prune subtrees
    // that cannot beat the incumbent, so the exhaustion proof is unchanged while
    // the tree can be vastly smaller than under cardinality-only pruning.
    let lp = LpNodeBound::standard();
    let verdict = solve_exact(&tc, seed_size, &lp, should_stop, &mut stream)?;
    let (best_size, best_set) = match verdict {
        SearchVerdict::Better(size, set) => (size, set),
        SearchVerdict::SeedOptimal => (seed_size, seed_set?),
    };
    // Belt and suspenders: the optimum witness must re-verify against EVERY
    // original constraint with the exact claimed objective.
    if !verify_all_constraints(&instance.constraints, &best_set) {
        return None;
    }
    let value = eval_objective(objective, &best_set);
    if value != -(best_size as i128) {
        return None;
    }
    Some(PbSolution {
        status: PbStatus::OptimumFound,
        assignment: best_set,
        objective: Some(value),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit, PbTerm};

    fn lit(var: u32, negated: bool) -> PbLit {
        PbLit { var, negated }
    }
    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var, false)],
        }
    }

    /// Build the standard 2-club PB encoding for an explicit edge list.
    fn encode(n: usize, edges: &[(usize, usize)]) -> (PbInstance, PbObjective) {
        let mut adj = vec![vec![false; n]; n];
        for &(a, b) in edges {
            adj[a][b] = true;
            adj[b][a] = true;
        }
        let mut constraints = Vec::new();
        for a in 0..n {
            for b in (a + 1)..n {
                if adj[a][b] {
                    continue;
                }
                let mut terms = vec![term(-1, (a + 1) as u32), term(-1, (b + 1) as u32)];
                for k in 0..n {
                    if adj[a][k] && adj[b][k] {
                        terms.push(term(1, (k + 1) as u32));
                    }
                }
                constraints.push(PbConstraint {
                    terms,
                    rel: PbRel::Ge,
                    rhs: -1,
                });
            }
        }
        let objective = PbObjective {
            terms: (1..=n).map(|v| term(-1, v as u32)).collect(),
        };
        let num_constraints = constraints.len() as u32;
        (
            PbInstance {
                num_vars: n as u32,
                num_constraints,
                constraints,
                objective: Some(objective.clone()),
            },
            objective,
        )
    }

    /// Brute force: max |S| with induced diameter <= 2.
    fn brute_force(n: usize, edges: &[(usize, usize)]) -> usize {
        let mut adj = vec![vec![false; n]; n];
        for &(a, b) in edges {
            adj[a][b] = true;
            adj[b][a] = true;
        }
        let mut best = 0;
        for mask in 0u32..(1 << n) {
            let set: Vec<usize> = (0..n).filter(|&v| mask & (1 << v) != 0).collect();
            let ok = set.iter().all(|&a| {
                set.iter().all(|&b| {
                    a == b
                        || adj[a][b]
                        || set
                            .iter()
                            .any(|&k| k != a && k != b && adj[a][k] && adj[b][k])
                })
            });
            if ok {
                best = best.max(set.len());
            }
        }
        best
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    /// Differential: the exact solver must match brute force on random graphs.
    #[test]
    fn two_club_matches_bruteforce() {
        let mut rng = Rng(0x2c1b_5eed);
        for round in 0..30 {
            let n = 6 + (round % 6); // 6..11 vertices
            let mut edges = Vec::new();
            for a in 0..n {
                for b in (a + 1)..n {
                    if rng.next() % 100 < 30 {
                        edges.push((a, b));
                    }
                }
            }
            let (instance, objective) = encode(n, &edges);
            if instance.constraints.is_empty() {
                continue; // complete graph: no rows -> encoding degenerate, skip
            }
            let expect = brute_force(n, &edges);
            let mut _im = |_v: i128, _a: &[bool]| {};
            let got = try_two_club_exact(&instance, &objective, None, &|| false, &mut _im)
                .unwrap_or_else(|| panic!("round {round}: solver declined valid encoding"));
            assert_eq!(
                got.objective,
                Some(-(expect as i128)),
                "round {round}: n={n} edges={edges:?}"
            );
        }
    }

    /// The PARALLEL PROVER's min-excluded partition must reproduce brute force
    /// EXACTLY — for several worker counts, the max over every worker's slice
    /// equals the true optimum AND every worker exhausts its cells (disjoint +
    /// complete). This is the guard on the parallelization: a cell that dropped
    /// or double-counted a subset would move the aggregate off brute force.
    #[test]
    fn two_club_partition_matches_bruteforce() {
        let mut rng = Rng(0x2c1b_a11e);
        for round in 0..30 {
            let n = 6 + (round % 6); // 6..11 vertices
            let mut edges = Vec::new();
            for a in 0..n {
                for b in (a + 1)..n {
                    if rng.next() % 100 < 30 {
                        edges.push((a, b));
                    }
                }
            }
            let (instance, objective) = encode(n, &edges);
            if instance.constraints.is_empty() {
                continue; // complete graph: degenerate encoding, skip
            }
            let expect = brute_force(n, &edges);
            // A single vertex is always a valid 2-club: the verified seed floor.
            let mut seed = vec![false; n];
            seed[0] = true;
            // Validate BOTH the cardinality-only baseline AND the LP-bounded
            // search: the LP node bound is sound iff every partition scheme still
            // reproduces brute force with it enabled. `standard()` uses a wide
            // window/short cadence here, so the tiny graphs actually exercise the
            // LP prune path.
            for lp in [LpNodeBound::disabled(), LpNodeBound::standard()] {
                for nw in [1usize, 2, 3, n] {
                    let mut agg_best = 0usize;
                    let mut all_done = true;
                    for w in 0..nw {
                        let mut _im = |_v: i128, _a: &[bool]| {};
                        let (b, done) = two_club_prove_worker(
                            &instance,
                            &objective,
                            Some(&seed),
                            w,
                            nw,
                            &lp,
                            &|| false,
                            &mut _im,
                        )
                        .unwrap_or_else(|| panic!("round {round}: prover declined valid encoding"));
                        agg_best = agg_best.max(b);
                        all_done &= done;
                    }
                    assert!(
                        all_done,
                        "round {round} nw={nw}: a worker left cells unexhausted"
                    );
                    assert_eq!(
                        agg_best, expect,
                        "round {round}: n={n} nw={nw} edges={edges:?}"
                    );
                }
                // DEPTH-2 refinement (all top cells, base_mod=1 class 0) must ALSO
                // reproduce brute force — the second-min-excluded split of every
                // cell is disjoint and complete, so refining it cannot change the
                // aggregate optimum.
                for nw in [1usize, 4, n] {
                    let mut agg_best = 0usize;
                    let mut all_done = true;
                    for w in 0..nw {
                        let mut _im = |_v: i128, _a: &[bool]| {};
                        let (b, done) = two_club_prove_d2_worker(
                            &instance,
                            &objective,
                            Some(&seed),
                            1,
                            &[0],
                            w,
                            nw,
                            &lp,
                            &|| false,
                            &mut _im,
                        )
                        .unwrap_or_else(|| {
                            panic!("round {round}: d2 prover declined valid encoding")
                        });
                        agg_best = agg_best.max(b);
                        all_done &= done;
                    }
                    assert!(
                        all_done,
                        "round {round} d2 nw={nw}: a worker left cells unexhausted"
                    );
                    assert_eq!(
                        agg_best, expect,
                        "round {round} d2: n={n} nw={nw} edges={edges:?}"
                    );
                }
                // PIVOT-set partition (the load-balanced one): 2^k in/out patterns
                // over the k highest-degree vertices, disjoint + complete by S∩P.
                for k in [1usize, 3, 5] {
                    for nw in [1usize, 4] {
                        let mut agg_best = 0usize;
                        let mut all_done = true;
                        for w in 0..nw {
                            let mut _im = |_v: i128, _a: &[bool]| {};
                            let (b, done) = two_club_prove_pivot_worker(
                                &instance,
                                &objective,
                                Some(&seed),
                                k,
                                w,
                                nw,
                                &lp,
                                &|| false,
                                &mut _im,
                            )
                            .unwrap_or_else(|| panic!("round {round}: pivot prover declined"));
                            agg_best = agg_best.max(b);
                            all_done &= done;
                        }
                        assert!(
                            all_done,
                            "round {round} pivot k={k} nw={nw}: cells unexhausted"
                        );
                        assert_eq!(agg_best, expect, "round {round} pivot k={k}: n={n} nw={nw}");
                    }
                }
            }
        }
    }

    /// The INCREMENTAL DUAL-SNAPSHOT machinery under maximum stress: refresh at
    /// every eligible branching node (cadence 1, zero warmup, unbounded window,
    /// unlimited rows) so snapshots are pushed and popped throughout the tree,
    /// including under `forced_in` + `initial_removed` cells. Any error in the
    /// push/pop pairing, the O(1) sum maintenance, or the scaled-integer
    /// pricing shows up as a wrong optimum vs brute force.
    #[test]
    fn two_club_lp_snapshot_stress_matches_bruteforce() {
        let aggressive = LpNodeBound {
            enabled: true,
            warmup: 0,
            cadence: 1,
            window: 1_000_000,
            max_rows: 0,
            low_margin: 0,
            ceiling: true,
            exact_margin: 4,
        };
        let mut rng = Rng(0x2c1b_d0a1);
        for round in 0..30 {
            let n = 6 + (round % 6); // 6..11 vertices
            let mut edges = Vec::new();
            for a in 0..n {
                for b in (a + 1)..n {
                    if rng.next() % 100 < 30 {
                        edges.push((a, b));
                    }
                }
            }
            let (instance, objective) = encode(n, &edges);
            if instance.constraints.is_empty() {
                continue; // complete graph: degenerate encoding, skip
            }
            let expect = brute_force(n, &edges);
            let mut seed = vec![false; n];
            seed[0] = true;
            let mut _im = |_v: i128, _a: &[bool]| {};
            // Whole space as one cell (pivot k=0): the deepest snapshot stacks.
            let (b, done) = two_club_prove_pivot_worker(
                &instance,
                &objective,
                Some(&seed),
                0,
                0,
                1,
                &aggressive,
                &|| false,
                &mut _im,
            )
            .unwrap_or_else(|| panic!("round {round}: pivot prover declined"));
            assert!(done, "round {round}: stress cell unexhausted");
            assert_eq!(b, expect, "round {round}: n={n} edges={edges:?}");
            // Depth-2 partition: cells begin with forced_in + initial_removed,
            // so snapshots are exercised against pre-fixed states too.
            let mut agg_best = 0usize;
            let mut all_done = true;
            for w in 0..3 {
                let (b, done) = two_club_prove_d2_worker(
                    &instance,
                    &objective,
                    Some(&seed),
                    1,
                    &[0],
                    w,
                    3,
                    &aggressive,
                    &|| false,
                    &mut _im,
                )
                .unwrap_or_else(|| panic!("round {round}: d2 prover declined"));
                agg_best = agg_best.max(b);
                all_done &= done;
            }
            assert!(all_done, "round {round} d2: stress cells unexhausted");
            assert_eq!(agg_best, expect, "round {round} d2: n={n}");
        }
    }

    /// A tampered row (wrong common-neighbour set) must make the recognizer decline.
    #[test]
    fn recognizer_declines_tampered_row() {
        let (mut instance, objective) = encode(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]);
        // Corrupt: drop a +1 term from the first row that has one.
        for c in instance.constraints.iter_mut() {
            if c.terms.len() > 2 {
                c.terms.pop();
                break;
            }
        }
        let mut _im = |_v: i128, _a: &[bool]| {};
        assert!(try_two_club_exact(&instance, &objective, None, &|| false, &mut _im).is_none());
    }
}

#[cfg(test)]
mod file_probe {
    use super::*;

    /// Manual probe: TWO_CLUB_FILE=<opb> — recognize + solve the real instance.
    #[test]
    #[ignore = "manual; set TWO_CLUB_FILE"]
    fn two_club_file_probe() {
        let path = std::env::var("TWO_CLUB_FILE").expect("set TWO_CLUB_FILE");
        let raw = std::fs::read_to_string(&path).expect("read");
        let inst = crate::parse_opb(&raw).expect("parse");
        let obj = inst.objective.clone().expect("objective");
        let t0 = std::time::Instant::now();
        let deadline = t0
            + std::time::Duration::from_secs(
                std::env::var("TWO_CLUB_SECS")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(300),
            );
        let stop = || std::time::Instant::now() >= deadline;
        let mut best = i128::MAX;
        let mut stream = |v: i128, _a: &[bool]| {
            if v < best {
                best = v;
                eprintln!("  incumbent {v} @ {:?}", t0.elapsed());
            }
        };
        // TWO_CLUB_SEED_FILE: space-separated 0/1 per var — an external
        // incumbent (e.g. the MIPLIB best-known witness) to seed the pruning
        // floor. try_two_club_exact re-verifies it fail-closed.
        let seed: Option<Vec<bool>> = std::env::var("TWO_CLUB_SEED_FILE").ok().map(|sf| {
            std::fs::read_to_string(&sf)
                .expect("read seed")
                .split_whitespace()
                .map(|t| t == "1")
                .collect()
        });
        if let Some(sd) = &seed {
            eprintln!(
                "seed loaded: {} vars, {} selected",
                sd.len(),
                sd.iter().filter(|&&b| b).count()
            );
        }
        // LP node bound (measurement toggle, same convention as TWO_CLUB_TRACE):
        // TWO_CLUB_LP=0 runs the cardinality-only baseline for an A/B; default on.
        // TWO_CLUB_LP_{CADENCE,WINDOW,MAXROWS,EXACT} tune it for the real instance.
        let env_usize = |k: &str, d: usize| {
            std::env::var(k)
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(d)
        };
        let lp = if std::env::var("TWO_CLUB_LP").ok().as_deref() == Some("0") {
            LpNodeBound::disabled()
        } else {
            let base = LpNodeBound::standard();
            LpNodeBound {
                enabled: true,
                warmup: env_usize("TWO_CLUB_LP_WARMUP", base.warmup as usize) as u64,
                cadence: env_usize("TWO_CLUB_LP_CADENCE", base.cadence as usize) as u64,
                window: env_usize("TWO_CLUB_LP_WINDOW", base.window),
                max_rows: env_usize("TWO_CLUB_LP_MAXROWS", base.max_rows),
                low_margin: env_usize("TWO_CLUB_LP_LOWCUT", base.low_margin),
                ceiling: env_usize("TWO_CLUB_LP_CEIL", 1) != 0,
                exact_margin: env_usize("TWO_CLUB_LP_EXACT", base.exact_margin as usize) as i128,
            }
        };
        eprintln!(
            "lp node bound: enabled={} warmup={} cadence={} window={} max_rows={} exact_margin={}",
            lp.enabled, lp.warmup, lp.cadence, lp.window, lp.max_rows, lp.exact_margin
        );
        // Parallel prover: TWO_CLUB_WORKER=w TWO_CLUB_NWORKERS=N exhausts this
        // worker's disjoint min-excluded slice. All N workers reporting
        // all_done + best==seed is a complete optimality proof.
        if let (Ok(w), Ok(nw)) = (
            std::env::var("TWO_CLUB_WORKER"),
            std::env::var("TWO_CLUB_NWORKERS"),
        ) {
            let (w, nw): (usize, usize) = (w.parse().unwrap(), nw.parse().unwrap());
            // Depth-2 mode: TWO_CLUB_D2_BASEMOD + TWO_CLUB_D2_CLASSES ("0,1,2")
            // split the named top-cell classes by their SECOND excluded vertex,
            // spreading a bottleneck cell across all workers.
            let res = if let Ok(kp) = std::env::var("TWO_CLUB_PIVOT_K") {
                // Load-balanced pivot partition: 2^k in/out patterns over the k
                // highest-degree vertices.
                let k: usize = kp.parse().unwrap();
                two_club_prove_pivot_worker(
                    &inst,
                    &obj,
                    seed.as_deref(),
                    k,
                    w,
                    nw,
                    &lp,
                    &stop,
                    &mut stream,
                )
            } else if let (Ok(bm), Ok(cls)) = (
                std::env::var("TWO_CLUB_D2_BASEMOD"),
                std::env::var("TWO_CLUB_D2_CLASSES"),
            ) {
                let bm: usize = bm.parse().unwrap();
                let classes: Vec<usize> = cls.split(',').map(|s| s.parse().unwrap()).collect();
                two_club_prove_d2_worker(
                    &inst,
                    &obj,
                    seed.as_deref(),
                    bm,
                    &classes,
                    w,
                    nw,
                    &lp,
                    &stop,
                    &mut stream,
                )
            } else {
                two_club_prove_worker(&inst, &obj, seed.as_deref(), w, nw, &lp, &stop, &mut stream)
            };
            eprintln!(
                "TWO_CLUB WORKER {w}/{nw}: {res:?} time={:?} (all_done+best==seed across ALL workers = optimality proof)",
                t0.elapsed()
            );
            return;
        }
        let got = try_two_club_exact(&inst, &obj, seed.as_deref(), &stop, &mut stream);
        match got {
            Some(sol) => eprintln!(
                "TWO_CLUB PROVED: obj={:?} time={:?}",
                sol.objective,
                t0.elapsed()
            ),
            None => eprintln!(
                "TWO_CLUB declined/cut after {:?} (best streamed {best})",
                t0.elapsed()
            ),
        }
    }
}
