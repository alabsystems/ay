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
use sha2::{Digest, Sha256};

/// Hard ceiling on vertices (the family is ~200; the recognizer is O(rows·arity)).
const MAX_VERTICES: usize = 512;
/// Node budget: exhaustion within this many nodes or the solver declines.
const MAX_NODES: u64 = 20_000_000;

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
    /// STRENGTHENED NEIGHBORHOOD rows (Carvalho–Almeida lifting; opt-in via
    /// `TwoClubLpConfig::nbhd_rows` / `ay-pb-dev two-club --nbhd-rows`): add
    /// the merged pair+conflict-clique rows
    /// `Σ_{v∈I∪{a,b}} x_v − Σ_{r∈CN(a,b)∩C} x_r ≤ 1` to every float LP solve.
    /// See [`strengthened_nbhd_rows`] for the exact family and its validity
    /// proof. Default OFF (campaign-stable behavior; measured negative on the
    /// target instance — see the note at `TwoClubLpConfig::nbhd_rows`).
    pub nbhd_rows: bool,
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
            nbhd_rows: false,
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
            // Opt-in via `TwoClubLpConfig::nbhd_rows` (developer campaigns
            // only); production always runs with the family off.
            nbhd_rows: false,
        }
    }
}

mod branching;
use branching::{unwind_frame, Frame, RightBranch, StackItem, ViolatingBranchRule};

/// Process controls snapshotted once before recognition. Production preserves
/// the historical environment overrides; mandatory tests and `ay-pb-dev` use
/// [`Self::explicit`] so ambient `TWO_CLUB_*` state cannot change their search.
#[derive(Clone)]
pub(crate) struct TwoClubRuntime {
    max_nodes: u64,
    branch_rule: ViolatingBranchRule,
    trace: bool,
    dump_frontier: bool,
    sdp_worker: Option<SdpWorkerConfig>,
}

impl TwoClubRuntime {
    fn from_env() -> Self {
        #[cfg(test)]
        {
            // Unit tests must be hermetic even when a developer has an active
            // hours-scale campaign configured in the parent shell.
            Self::explicit(MAX_NODES, false, false, false)
        }
        #[cfg(not(test))]
        {
            // B74: carried by the typed switch set (`--pb-two-club-*`).
            let switches = crate::ab_switches::get();
            Self {
                max_nodes: switches.two_club_max_nodes.unwrap_or(MAX_NODES),
                branch_rule: ViolatingBranchRule::from_selector(
                    switches.two_club_branch.map(std::ffi::OsStr::new),
                ),
                trace: switches.two_club_trace,
                dump_frontier: switches.two_club_dump_frontier,
                // The certificate verifier is an explicit developer-tool
                // dependency, not a process-global production solver knob.
                sdp_worker: None,
            }
        }
    }

    pub(crate) const fn explicit(
        max_nodes: u64,
        use_violating_degree: bool,
        trace: bool,
        dump_frontier: bool,
    ) -> Self {
        Self {
            max_nodes,
            branch_rule: if use_violating_degree {
                ViolatingBranchRule::ViolDegree
            } else {
                ViolatingBranchRule::First
            },
            trace,
            dump_frontier,
            sdp_worker: None,
        }
    }

    #[cfg(feature = "dev-tools")]
    pub(crate) const fn explicit_marked(max_nodes: u64, trace: bool, dump_frontier: bool) -> Self {
        Self {
            max_nodes,
            branch_rule: ViolatingBranchRule::Marked,
            trace,
            dump_frontier,
            sdp_worker: None,
        }
    }

    #[cfg(feature = "dev-tools")]
    pub(crate) const fn explicit_marked_min_degree(
        max_nodes: u64,
        trace: bool,
        dump_frontier: bool,
    ) -> Self {
        Self {
            max_nodes,
            branch_rule: ViolatingBranchRule::MarkedMinDegree,
            trace,
            dump_frontier,
            sdp_worker: None,
        }
    }

    #[cfg(feature = "dev-tools")]
    pub(crate) fn with_sdp_worker(
        mut self,
        script: &std::path::Path,
        instance: &std::path::Path,
    ) -> Self {
        self.sdp_worker = Some(SdpWorkerConfig {
            interpreter: std::path::PathBuf::from("python3"),
            script: script.to_path_buf(),
            instance: instance.to_path_buf(),
        });
        self
    }
}

#[derive(Clone)]
struct SdpWorkerConfig {
    interpreter: std::path::PathBuf,
    script: std::path::PathBuf,
    instance: std::path::PathBuf,
}

struct TwoClub {
    n: usize,
    /// Snapshotted once at recognition so a long proof does not perform a
    /// process-global environment read at every node or change traversal order
    /// if another thread mutates the selector mid-search.
    branch_rule: ViolatingBranchRule,
    /// Per-cell node ceiling, explicit for tests and developer campaigns.
    max_nodes: u64,
    /// Emit campaign progress and LP diagnostics.
    trace: bool,
    /// Emit frontier sets on ceiling misses.
    dump_frontier: bool,
    /// Explicit exact-certificate worker used only by developer campaigns.
    sdp_worker: Option<SdpWorkerConfig>,
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
fn recognize_with_runtime(
    instance: &PbInstance,
    objective: &PbObjective,
    runtime: TwoClubRuntime,
) -> Option<TwoClub> {
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
        branch_rule: runtime.branch_rule,
        max_nodes: runtime.max_nodes,
        trace: runtime.trace,
        dump_frontier: runtime.dump_frontier,
        sdp_worker: runtime.sdp_worker,
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

/// Row caps for the strengthened-neighborhood family (full solves / support
/// rungs). Solve models are ~10k rows so 600 extra is marginal; support models
/// are ~1k rows, so the support cap is kept smaller.
const NBHD_ROW_CAP_SOLVE: usize = 600;
const NBHD_ROW_CAP_SUPPORT: usize = 250;

/// STRENGTHENED NEIGHBORHOOD rows (Carvalho–Almeida 2011, restated for the
/// candidate-set dynamics of this engine). For an ACTIVE non-adjacent pair
/// `(a, b)` (both in `C`, `CN(a,b) ∩ C ≠ ∅`) and a nonempty lift set `I ⊆ C`
/// such that, ALL AT THE CURRENT `C`:
///
///   (1) every `i ∈ I` forms a VIOLATING pair with `a` AND with `b`
///       (non-adjacent with `CN ∩ C = ∅` — no 2-club within `C` can contain
///       both endpoints), and
///   (2) `I` is a clique of the violating-pair graph (pairwise violating),
///
/// the inequality
///
/// ```text
///   Σ_{v ∈ I ∪ {a,b}} x_v  −  Σ_{r ∈ CN(a,b) ∩ C} x_r  ≤  1
/// ```
///
/// is valid for EVERY 2-club `S ⊆ C`. Proof by cases on `S`:
///
/// - `S ∩ I ≠ ∅`: by (2) at most one `i ∈ I` lies in `S` (a violating pair
///   has no surviving common neighbour in `C ⊇ S`, and a 2-club's witness must
///   lie inside `S` itself), so `|S ∩ I| = 1`; by (1) that `i` excludes both
///   `a` and `b` from `S`. LHS `= 1 − |S ∩ CN| ≤ 1`. ✓
/// - `{a,b} ⊆ S` (hence `S ∩ I = ∅` by (1)): `a,b` are non-adjacent, so the
///   2-club property of `S` demands a common neighbour `r ∈ S`; `S ⊆ C` puts
///   `r ∈ CN(a,b) ∩ C`. LHS `≤ 2 − 1 = 1`. ✓
/// - otherwise `|S ∩ (I ∪ {a,b})| ≤ 1`: LHS `≤ 1`. ✓
///
/// This MERGES the engine's existing pair row (`I = ∅` case) with its
/// conflict-clique rows (`I ∪ {a}` and `I ∪ {b}` are cliques of the violating
/// graph) into one strictly stronger facet: summing those three existing rows
/// only yields `Σ_I x + x_a + x_b − ½·Σ_CN x ≤ 1.5`, while this row has rhs 1
/// with the full CN term — e.g. `x_a = x_b = x_i = ½, CN mass 0` violates this
/// row (LHS 1.5) but satisfies every pair/clique row.
///
/// VERTEX-REMOVAL DYNAMICS (the trap that killed the odd-hole rows): being a
/// 2-club is an intrinsic property of `S` (diameter ≤ 2 in the subgraph
/// induced by `S` — witnesses inside `S`), so a row valid for all 2-clubs
/// `⊆ C` is automatically valid at every DESCENDANT `C' ⊆ C` (its 2-clubs are
/// a subset). Dual snapshots priced on these rows therefore inherit soundly
/// down the whole subtree of the refresh node. On UNWIND `C` GROWS and a
/// violating pair can un-violate, killing conditions (1)/(2) — so, exactly
/// like `viol_clique_rows`, the family is REGENERATED FRESH at every LP solve
/// and never cached across nodes.
///
/// Returns up to `cap` entries `(pair_index, I)`; the caller materializes
/// coefficients via [`nbhd_row_coeffs`] (freezing `CN ∩ C` at generation) and
/// prices `b = -1` in Ge form `Σ −x_{I∪{a,b}} + Σ x_{CN∩C} ≥ −1`.
fn strengthened_nbhd_rows(tc: &TwoClub, state: &SearchState, cap: usize) -> Vec<(u32, Vec<u32>)> {
    use std::collections::HashMap;
    if cap == 0 {
        return Vec::new();
    }
    // Violating-pair adjacency at the CURRENT C (same scan as viol_clique_rows).
    let mut adj: HashMap<u32, Vec<u32>> = HashMap::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        if state.both_in[pi] && state.cn_alive[pi] == 0 {
            adj.entry(*a).or_default().push(*b);
            adj.entry(*b).or_default().push(*a);
        }
    }
    if adj.is_empty() {
        return Vec::new();
    }
    let mut found: Vec<(u32, Vec<u32>)> = Vec::new();
    for (pi, (a, b, _)) in tc.pairs.iter().enumerate() {
        // Host pair: active with a LIVE common neighbourhood (cn_alive > 0).
        // Pairs with cn_alive == 0 are violating — their lift degenerates to a
        // conflict clique, which viol_clique_rows already covers.
        if !state.both_in[pi] || state.cn_alive[pi] == 0 {
            continue;
        }
        let (Some(va), Some(vb)) = (adj.get(a), adj.get(b)) else {
            continue;
        };
        // Lift candidates: in a violating pair with BOTH a and b (condition 1).
        let mut cands: Vec<u32> = va.iter().copied().filter(|u| vb.contains(u)).collect();
        if cands.is_empty() {
            continue;
        }
        // Grow I as a clique of the violating-pair graph (condition 2),
        // densest candidates first.
        cands.sort_unstable_by_key(|u| std::cmp::Reverse(adj[u].len()));
        let mut iset: Vec<u32> = Vec::new();
        for u in cands {
            let ua = &adj[&u];
            if iset.iter().all(|&q| ua.contains(&q)) {
                iset.push(u);
            }
        }
        found.push((pi as u32, iset));
        // Collect a few times the cap so the |I|-sort below has slack, then stop.
        if found.len() >= cap.saturating_mul(4) {
            break;
        }
    }
    // Biggest lift first (|I| large = strongest strengthening over the pair row).
    found.sort_unstable_by_key(|(_, iset)| std::cmp::Reverse(iset.len()));
    found.truncate(cap);
    found
}

/// Materialize one strengthened-neighborhood row in the raw Ge form
/// `Σ_{v∈I∪{a,b}} −x_v + Σ_{r∈CN(a,b)∩C} x_r ≥ −1` with sorted, strictly
/// increasing column indices (the `RowF64` contract). Columns never collide:
/// each `i ∈ I` is non-adjacent to `a` and `b` so `i ∉ CN(a,b)`, and
/// `a, b ∉ CN(a,b)` (no self-loops).
fn nbhd_row_coeffs(tc: &TwoClub, state: &SearchState, pi: u32, iset: &[u32]) -> Vec<(usize, f64)> {
    let (a, b, cn) = &tc.pairs[pi as usize];
    let mut coeffs: Vec<(usize, f64)> = Vec::with_capacity(iset.len() + 2 + cn.len());
    coeffs.push((*a as usize, -1.0));
    coeffs.push((*b as usize, -1.0));
    for &i in iset {
        coeffs.push((i as usize, -1.0));
    }
    for &r in cn {
        if state.in_c[r as usize] {
            coeffs.push((r as usize, 1.0));
        }
    }
    coeffs.sort_unstable_by_key(|e| e.0);
    coeffs
}

/// Exact-integer pricing of one strengthened-neighborhood row under multiplier
/// `m ≥ 0` (already grid-floored/clamped): `b = −1` contributes `−m` to base;
/// members get `−m`, live CN hubs `+m`. Overflow stays inside the audit at
/// [`refresh_dual_snapshot`]: ≤ [`NBHD_ROW_CAP_SOLVE`] rows of unit
/// coefficients with `m ≤ 2^40`.
fn price_nbhd_row(
    tc: &TwoClub,
    state: &SearchState,
    pi: u32,
    iset: &[u32],
    m: i128,
    base: &mut i128,
    ay: &mut [i128],
) {
    *base -= m;
    let (a, b, cn) = &tc.pairs[pi as usize];
    ay[*a as usize] -= m;
    ay[*b as usize] -= m;
    for &i in iset {
        ay[i as usize] -= m;
    }
    for &r in cn {
        if state.in_c[r as usize] {
            ay[r as usize] += m;
        }
    }
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
/// merge of endpoints into the CN stream), clique-cut rows, then (when
/// `cfg.nbhd_rows`) strengthened-neighborhood rows. Returns
/// `(rows_raw, pair_of_row, cliques, nbs)`; `None` if over `cfg.max_rows`.
#[allow(clippy::type_complexity)]
fn build_solve_rows(
    tc: &TwoClub,
    state: &SearchState,
    cfg: &LpNodeBound,
) -> Option<(
    Vec<(Vec<(usize, f64)>, f64)>,
    Vec<u32>,
    Vec<Vec<u32>>,
    Vec<(u32, Vec<u32>)>,
)> {
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
    let nbs = if cfg.nbhd_rows {
        strengthened_nbhd_rows(tc, state, NBHD_ROW_CAP_SOLVE)
    } else {
        Vec::new()
    };
    for (pi, iset) in &nbs {
        rows_raw.push((nbhd_row_coeffs(tc, state, *pi, iset), -1.0));
    }
    Some((rows_raw, pair_of_row, cliques, nbs))
}

/// Certified-SDP-bound worker bridge (the development design notes).
///
/// The worker returns bounds carried by EXACT certificates (interval LDL^T
/// AND fraction-free Bareiss both verified in the worker; the float SDP
/// solver only proposes — see the development design notes). This side
/// performs the prune comparison in exact i128: kill iff num < (floor+1)·den
/// (F1 integer semantics). The non-default developer tool supplies both the
/// worker and instance paths explicitly; production and mandatory tests never
/// consult ambient SDP environment variables. Any graph-identity mismatch,
/// protocol failure, arithmetic overflow, or timeout costs the caller the
/// bound (fail-closed: no prune) — see `SdpReply` for which of those retire
/// the bridge and which are ordinary in-protocol answers.
struct SdpWorker {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    rx: std::sync::mpsc::Receiver<String>,
}

impl SdpWorker {
    fn spawn(config: &SdpWorkerConfig, expected_graph_sha256: &str) -> Option<SdpWorker> {
        let mut child = std::process::Command::new(&config.interpreter)
            .arg(&config.script)
            .arg(&config.instance)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit())
            .spawn()
            .ok()?;
        let stdin = match child.stdin.take() {
            Some(stdin) => stdin,
            None => {
                terminate_child(&mut child);
                return None;
            }
        };
        let stdout = match child.stdout.take() {
            Some(stdout) => stdout,
            None => {
                terminate_child(&mut child);
                return None;
            }
        };
        let (tx, rx) = std::sync::mpsc::channel::<String>();
        std::thread::spawn(move || {
            use std::io::BufRead;
            let reader = std::io::BufReader::new(stdout);
            for line in reader.lines() {
                let Ok(line) = line else { break };
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        // The worker independently parses the configured instance. Its
        // canonical graph digest must equal the exact graph recognized by
        // Rust, closing the path-replacement/TOCTOU mismatch class.
        let expected = format!("graph_sha256={expected_graph_sha256}");
        match rx.recv_timeout(std::time::Duration::from_mins(1)) {
            Ok(line)
                if line
                    .split_ascii_whitespace()
                    .next()
                    .is_some_and(|token| token == "READY")
                    && line.split_ascii_whitespace().any(|token| token == expected) =>
            {
                Some(SdpWorker { child, stdin, rx })
            }
            _ => {
                terminate_child(&mut child);
                None
            }
        }
    }

    /// Certified bound for the candidate set. Never prune except on `Bound`.
    fn query(&mut self, cset: &[usize], timeout: std::time::Duration) -> SdpReply {
        use std::io::Write;
        let line = cset
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        if writeln!(self.stdin, "{line}").is_err() || self.stdin.flush().is_err() {
            return SdpReply::Broken;
        }
        match self.rx.recv_timeout(timeout) {
            Ok(response) => match parse_sdp_bound_response(&response) {
                Some((num, den)) => SdpReply::Bound(num, den),
                // `FAIL <reason>` is the worker's documented in-protocol answer
                // for "this node has no certificate" (uncertified tier, invalid
                // cset, internal exception it caught). The child is healthy and
                // the stream is still synchronized, so the bridge survives.
                // Anything else on the wire is a protocol violation.
                None if response.split_ascii_whitespace().next() == Some("FAIL") => {
                    SdpReply::NoCertificate
                }
                None => SdpReply::Broken,
            },
            // Timeout or a closed pipe. A timeout leaves the stream
            // DESYNCHRONIZED (the worker may still emit the late answer), so the
            // child cannot be reused — but it can be replaced, which is what the
            // caller does. Round 3b measured the cost of conflating the two:
            // one 120 s solve under CPU contention retired the tier for the
            // remaining 11.9 h of the cell on 7 of 8 workers.
            Err(_) => SdpReply::Broken,
        }
    }
}

/// Outcome of one certified-bound query, split by what it implies for the
/// bridge: `NoCertificate` is an ordinary answer from a healthy worker (keep
/// it), `Broken` means this child can no longer be trusted to be in protocol
/// (replace it). Only `Bound` may ever license a prune.
#[derive(Debug, PartialEq, Eq)]
enum SdpReply {
    Bound(i128, i128),
    NoCertificate,
    Broken,
}

fn parse_sdp_bound_response(response: &str) -> Option<(i128, i128)> {
    let mut fields = response.split_ascii_whitespace();
    if fields.next()? != "BOUND" {
        return None;
    }
    let num: i128 = fields.next()?.parse().ok()?;
    let den: i128 = fields.next()?.parse().ok()?;
    if fields.next().is_some() || num < 0 || den <= 0 {
        return None;
    }
    Some((num, den))
}

fn terminate_child(child: &mut std::process::Child) {
    let _ = child.kill();
    let _ = child.wait();
}

impl Drop for SdpWorker {
    fn drop(&mut self) {
        use std::io::Write;
        let _ = writeln!(self.stdin, "QUIT");
        terminate_child(&mut self.child);
    }
}

fn graph_sha256(n: usize, pairs: &[(u32, u32, Vec<u32>)]) -> String {
    let mut canonical = pairs.to_vec();
    canonical.sort_unstable();
    let mut hasher = Sha256::new();
    hasher.update((n as u64).to_be_bytes());
    hasher.update((canonical.len() as u64).to_be_bytes());
    for (a, b, common) in canonical {
        hasher.update(a.to_be_bytes());
        hasher.update(b.to_be_bytes());
        hasher.update((common.len() as u64).to_be_bytes());
        for vertex in common {
            hasher.update(vertex.to_be_bytes());
        }
    }
    format!("{:x}", hasher.finalize())
}

/// Converts a certified non-negative rational upper bound into the scaled
/// marker used by the existing lift-prune path. Every arithmetic operation is
/// checked; a malformed or unrepresentable response declines the prune.
fn certified_sdp_prune_marker(num: i128, den: i128, best_floor: usize) -> Option<i128> {
    if num < 0 || den <= 0 {
        return None;
    }
    let threshold = (best_floor as i128).checked_add(1)?.checked_mul(den)?;
    if num >= threshold {
        return None;
    }
    num.checked_mul(DUAL_SCALE)?.checked_div(den)?.checked_neg()
}

/// How far above the kill line (`floor + 1`) the LP's own failing UB may sit
/// before the certified-SDP query is skipped as out of reach. Purely an
/// allocation heuristic — skipping can only cost a prune, never license one.
/// Calibrated on the 70 paired round-3b field queries where both the LP failing
/// UB and the certified SDP bound are known: the SDP came in 2.16 below the LP
/// on average (max 2.70), and all 48 certified kills in that sample had an LP UB
/// below `floor + 4`, while 15 queries above it produced 2.
const SDP_REACH_SLACK: f64 = 3.0;

/// Consecutive broken bridges (timeout, protocol violation, or failed spawn)
/// that retire the certified-SDP tier for the rest of the cell. One break is a
/// slow solve or a contended machine and is replaced; a run of them means the
/// toolchain itself is gone, and retrying costs 120 s a throw.
const SDP_MAX_BROKEN_STREAK: u32 = 4;

/// Fixed-point scale for the exact-integer dual arithmetic. Duals are rounded
/// DOWN onto this grid (`m = ⌊y·SCALE⌋ ≥ 0`), which preserves `y ≥ 0` and hence
/// soundness — rounding only weakens the bound, never inflates it.
const DUAL_SCALE: i128 = 1 << 20;

/// Return whether an exact scaled lower bound on the negated objective proves
/// that an integral objective cannot improve on `best_floor`.
///
/// If `upper_bound = -scaled_neg_upper_bound / DUAL_SCALE`, integrality permits
/// pruning exactly when `upper_bound < best_floor + 1`. The comparison is
/// strict: equality still permits an integer solution of size
/// `best_floor + 1`. Arithmetic overflow declines the prune.
fn scaled_dual_bound_prunes(scaled_neg_upper_bound: i128, best_floor: i128) -> bool {
    let Some(next_floor) = best_floor.checked_add(1) else {
        return false;
    };
    let Some(threshold) = next_floor
        .checked_mul(DUAL_SCALE)
        .and_then(i128::checked_neg)
    else {
        return false;
    };
    scaled_neg_upper_bound > threshold
}
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
    /// Strengthened-neighborhood rows fed to this refresh's PRIMARY solve
    /// (0 when the family is off) — the `nb=` added-rows counter.
    nb_rows: u32,
    /// The pricing behind the RETURNED bound carries a positive (grid-floored)
    /// multiplier on ≥ 1 strengthened-neighborhood row — prunes with this set
    /// are the `nb=` attributable-prune counter.
    nb_used: bool,
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
        // Strengthened-neighborhood rows (opt-in): regenerated per solve, like
        // the clique rows — see strengthened_nbhd_rows for why caching would
        // be unsound across unwinds.
        let nbs = if cfg.nbhd_rows {
            strengthened_nbhd_rows(tc, state, NBHD_ROW_CAP_SUPPORT)
        } else {
            Vec::new()
        };
        for (pi, iset) in &nbs {
            rows_raw.push((nbhd_row_coeffs(tc, state, *pi, iset), -1.0));
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
        if duals.len() != n_pair_rows + cliques.len() + holes.len() + nbs.len() {
            if tc.trace {
                eprintln!(
                    "  [support-none-len] duals={} pair={} cliques={} holes={} nb={}",
                    duals.len(),
                    n_pair_rows,
                    cliques.len(),
                    holes.len(),
                    nbs.len()
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
        let mut nb_used = false;
        for (ni, (pi, iset)) in nbs.iter().enumerate() {
            let m = ((duals[n_pair_rows + cliques.len() + holes.len() + ni] * DUAL_SCALE as f64)
                .floor() as i128)
                .clamp(0, DUAL_M_MAX);
            if m == 0 {
                continue;
            }
            nb_used = true;
            price_nbhd_row(tc, state, *pi, iset, m, &mut base, &mut ay);
        }
        let d: Vec<i128> = ay.iter().map(|&a| -DUAL_SCALE - a).collect();
        let sum: i128 = (0..n).filter(|&v| state.in_c[v]).map(|v| d[v].min(0)).sum();
        let prune = scaled_dual_bound_prunes(base + sum, best_floor);
        return Some((
            RefreshOutcome {
                base,
                d,
                sum,
                prune,
                nb_rows: nbs.len() as u32,
                nb_used,
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
    let trace = tc.trace;
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
    // Strengthened-neighborhood rows (opt-in; regenerated per solve — never
    // cached across nodes, see strengthened_nbhd_rows).
    let nbs = if cfg.nbhd_rows {
        strengthened_nbhd_rows(tc, state, NBHD_ROW_CAP_SOLVE)
    } else {
        Vec::new()
    };
    for (pi, iset) in &nbs {
        rows_raw.push((nbhd_row_coeffs(tc, state, *pi, iset), -1.0));
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
    if duals.len() != n_pair_rows + cliques.len() + holes.len() + nbs.len() {
        if trace {
            eprintln!(
                "  [solve-none-len] duals={} pair={} cliques={} holes={} nb={}",
                duals.len(),
                n_pair_rows,
                cliques.len(),
                holes.len(),
                nbs.len()
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
    // Strengthened-neighborhood rows: b = -1 ⇒ base -= m; members -m, live CN
    // hubs +m. (≤ 600 unit-coefficient rows — inside the overflow audit.)
    let mut nb_used = false;
    for (ni, (pi, iset)) in nbs.iter().enumerate() {
        let m =
            ((duals[n_pair_rows + cliques.len() + holes.len() + ni] * DUAL_SCALE as f64).floor()
                as i128)
                .clamp(0, DUAL_M_MAX);
        if m == 0 {
            continue;
        }
        nb_used = true;
        price_nbhd_row(tc, state, *pi, iset, m, &mut base, &mut ay);
    }
    let mut d: Vec<i128> = ay.iter().map(|&a| -DUAL_SCALE - a).collect();
    let mut sum: i128 = (0..n).filter(|&v| state.in_c[v]).map(|v| d[v].min(0)).sum();

    // Prune decisions are exact on the scaled grid. Because 2-club size is
    // integral, UB < floor+1 proves that no solution can improve the floor.
    let mut prune = scaled_dual_bound_prunes(base + sum, best_floor);
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
            let Some((mut rows2, pair_of_row2, cliques2, nbs2)) = build_solve_rows(tc, state, cfg)
            else {
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
            let mut nb2_used = false;
            for (ni, (pi, iset)) in nbs2.iter().enumerate() {
                let m = ((duals2[pair_of_row2.len() + cliques2.len() + ni] * DUAL_SCALE as f64)
                    .floor() as i128)
                    .clamp(0, DUAL_M_MAX);
                if m == 0 {
                    continue;
                }
                nb2_used = true;
                price_nbhd_row(tc, state, *pi, iset, m, &mut base2, &mut ay2);
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
            if tc.trace {
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
                nb_used = nb2_used; // the adopted pricing is the round-2 one
                prune = scaled_dual_bound_prunes(base + sum, best_floor);
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
            nb_rows: nbs.len() as u32,
            nb_used,
        },
        Some(support),
    ))
}

/// MARKED-CONFLICT deletion sweep to a FIXED POINT (`TWO_CLUB_BRANCH=marked`).
///
/// A marked vertex is committed to EVERY solution the current subtree is
/// responsible for (cell-forced vertices carry the same commitment, so they
/// are marked from the cell root). If a pair (m, u) with m marked is violating
/// (both in `C`, non-adjacent, zero surviving common neighbours in `C`), no
/// 2-club within `C` contains both — and every solution of interest contains
/// `m`, so `u` is in NONE of them: delete `u`.
///
/// Violating status is MONOTONE under vertex removal (common neighbourhoods
/// only shrink), so a deletion can cascade NEW violations against OTHER marked
/// vertices — hence the outer loop repeats until a full pass over the marked
/// set deletes nothing. Every deletion goes through `SearchState::remove` with
/// its own undo log appended to `extra` (the caller unwinds in exact reverse
/// order), and the incremental dual sum is updated exactly like the branch
/// removal sites, so the O(1) snapshot bound stays exact (marked vertices are
/// never removed, so the snapshot's row pricing stays valid).
///
/// Returns `false` iff a violating pair has BOTH endpoints marked: two
/// committed vertices can no longer coexist, so the branch holds no solution
/// of interest — DEAD (the caller prunes; nothing here is undone, the caller's
/// frame unwind reverses `extra`).
#[allow(clippy::too_many_arguments)]
fn marked_sweep(
    tc: &TwoClub,
    state: &mut SearchState,
    marked: &[bool],
    marked_list: &[usize],
    lp_enabled: bool,
    dual_d: &[i128],
    dual_sum: &mut i128,
    extra: &mut Vec<(usize, Vec<(u32, u8)>)>,
    mk_dels: &mut u64,
) -> bool {
    loop {
        let mut changed = false;
        for &m in marked_list {
            debug_assert!(state.in_c[m], "marked vertex left C");
            for &pi in &tc.pair_of_vertex[m] {
                let pi = pi as usize;
                if !state.both_in[pi] || state.cn_alive[pi] != 0 {
                    continue;
                }
                let (a, b, _) = &tc.pairs[pi];
                let u = if *a as usize == m {
                    *b as usize
                } else {
                    *a as usize
                };
                if marked[u] {
                    return false; // marked-marked violating pair: DEAD branch
                }
                if lp_enabled {
                    *dual_sum -= dual_d[u].min(0);
                }
                let mut log = Vec::new();
                state.remove(u, tc, &mut log);
                extra.push((u, log));
                *mk_dels += 1;
                changed = true;
            }
        }
        if !changed {
            return true;
        }
    }
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
    // MARKED BRANCHING state (`TWO_CLUB_BRANCH=marked`): `marked[v]` ⇒ v is
    // committed to every solution of the current subtree. Cell-forced vertices
    // carry that commitment for the WHOLE cell, so they are marked up front —
    // the root's sweep then performs the IRR reduction (delete anything
    // conflicting with a committed vertex) before the first branch, and a
    // forced-forced violation kills the cell as dead-by-marked-pair.
    let marked_mode = tc.branch_rule.is_marked();
    let mut marked = vec![false; n];
    let mut marked_list: Vec<usize> = Vec::new();
    if marked_mode {
        for v in 0..n {
            if is_forced(v) && state.in_c[v] {
                marked[v] = true;
                marked_list.push(v);
            }
        }
    }
    // Marked-branching counters: branch marks made / sweep conflict deletions
    // / dead-by-marked-pair prunes (the `mk=` trace triple).
    let mut mk_marks: u64 = 0;
    let mut mk_dels: u64 = 0;
    let mut mk_dead: u64 = 0;
    let mut best: Option<(usize, Vec<bool>)> = None;
    let mut best_floor = seed_size; // sound pruning floor: a KNOWN 2-club size
    let mut nodes: u64 = 0;
    let node_cap = tc.max_nodes;
    let progress = tc.trace;
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
    // STRENGTHENED-NEIGHBORHOOD rows (config `nbhd_rows`, dev-campaign
    // opt-in): rows fed to refresh solves / prunes whose adopted pricing
    // carried a positive multiplier on ≥ 1 such row (the `nb=` trace pair;
    // 0/0 when off).
    let mut nb_rows_total: u64 = 0;
    let mut nb_prunes: u64 = 0;
    // CEILING ATTACK state: `ceil_frontier` tracks the highest c of any
    // LP-family kill (trace/diagnostic); the GATE uses `lift_frontier` — the
    // highest c of CASCADE kills only. Enter-matching kills land during
    // descents at up to ~c=140 and would otherwise starve the cascade-top
    // escalations (which top out lower) if they set the gate.
    let mut ceil_frontier: usize = 0;
    let mut lift_frontier: usize = 0;
    let mut ceil_spent = std::time::Duration::ZERO;
    let mut lp_ceil_try: u64 = 0;
    // Certified-SDP bridge: lazily spawned, and REPLACED (not retired) when a
    // child breaks — a single slow solve must not cost the cell its strongest
    // tier. Retired only on a run of consecutive breaks, i.e. something
    // systemic (interpreter gone, instance unreadable, digest mismatch).
    // Budget: sdp_spent*4 <= elapsed (<= 25% of wall time), and every break
    // (including the 120 s timeout that produced it) is charged to it.
    let mut sdp: Option<SdpWorker> = None;
    let mut sdp_dead = tc.sdp_worker.is_none();
    let graph_sha256 = tc
        .sdp_worker
        .as_ref()
        .map(|_| graph_sha256(tc.n, &tc.pairs));
    let mut sdp_spent = std::time::Duration::ZERO;
    let mut sdp_try: u64 = 0;
    let mut sdp_kill: u64 = 0;
    let mut sdp_spawns: u64 = 0;
    let mut sdp_nocert: u64 = 0;
    let mut sdp_skip: u64 = 0;
    let mut sdp_broken_streak: u32 = 0;
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

    let mut stack = vec![StackItem {
        frame: Frame::Enter,
        removed: None,
        undo: Vec::new(),
        snap: false,
        c_at: state.c_size,
        mark: None,
        extra: Vec::new(),
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
                        "  [cell] nodes={nodes} rate={:.0}/s open={} oc={cmin}/{cmed}/{cmax} floor={best_floor} lp_prunes={lp_prunes} o1={lp_prunes_o1} lift={lp_prunes_lift} m={lp_prunes_m} refreshes={lp_refreshes} subs={lp_reprices} ceil={lp_ceil_try}/{lp_ceil_kill_a}+{lp_ceil_kill_b} sdp={sdp_try}/{sdp_kill} sdpx={sdp_spawns}/{sdp_nocert}/{sdp_skip}/{sdp_dead} nb={nb_rows_total}/{nb_prunes} front={ceil_frontier} mk={mk_marks}/{mk_dels}/{mk_dead} dives={n_dives} rx={rx_lo}/{rx_150}/{rx_160}/{rx_170} t={secs:.0}s",
                        nodes as f64 / secs.max(1e-9),
                        stack.len()
                    );
                    if nodes >= next_report {
                        next_report += 50_000_000;
                    }
                    next_time_report = t_start.elapsed().as_secs() + 600;
                }
                // MARKED-CONFLICT sweep (marked mode, before any bound test so
                // the prunes below see the reduced C): delete every vertex
                // conflicting with the committed set, to a fixed point. A
                // marked-marked violation = DEAD branch (no solution of this
                // subtree's responsibility survives).
                if marked_mode
                    && !marked_list.is_empty()
                    && !marked_sweep(
                        tc,
                        &mut state,
                        &marked,
                        &marked_list,
                        lp.enabled,
                        &dual_d,
                        &mut dual_sum,
                        &mut item.extra,
                        &mut mk_dels,
                    )
                {
                    mk_dead += 1;
                    // Dead by commitment, not by bound — the parent C is not
                    // evidence of LP-thinness; disarm the kill-lift cascade.
                    cascade = false;
                    unwind_frame(
                        &mut item,
                        &mut state,
                        lp.enabled,
                        &dual_d,
                        &mut dual_sum,
                        &mut marked,
                        &mut marked_list,
                    );
                    continue;
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
                    unwind_frame(
                        &mut item,
                        &mut state,
                        lp.enabled,
                        &dual_d,
                        &mut dual_sum,
                        &mut marked,
                        &mut marked_list,
                    );
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
                        unwind_frame(
                            &mut item,
                            &mut state,
                            lp.enabled,
                            &dual_d,
                            &mut dual_sum,
                            &mut marked,
                            &mut marked_list,
                        );
                        continue;
                    }
                }
                // O(1) dual-snapshot prune — as sound as the cardinality prune
                // (`-(base+sum)/SCALE` upper-bounds every 2-club in C).
                // Integrality permits pruning exactly when UB < floor+1.
                let mut fresh: Option<RefreshOutcome> = None;
                if lp.enabled {
                    if scaled_dual_bound_prunes(dual_base + dual_sum, best_floor as i128) {
                        lp_prunes += 1;
                        lp_prunes_o1 += 1;
                        cascade = true;
                        unwind_frame(
                            &mut item,
                            &mut state,
                            lp.enabled,
                            &dual_d,
                            &mut dual_sum,
                            &mut marked,
                            &mut marked_list,
                        );
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
                                nb_rows_total += f.nb_rows as u64;
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
                                nb_rows_total += f.nb_rows as u64;
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
                                if f.nb_used {
                                    nb_prunes += 1;
                                }
                                cascade = true;
                                ceil_frontier = ceil_frontier.max(state.c_size);
                                unwind_frame(
                                    &mut item,
                                    &mut state,
                                    lp.enabled,
                                    &dual_d,
                                    &mut dual_sum,
                                    &mut marked,
                                    &mut marked_list,
                                );
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
                // Marked mode selects a (pair, branch vertex); the other rules
                // select a pair and derive the branch vertex from forcing.
                let selected = if marked_mode {
                    state.find_violating_marked(tc)
                } else {
                    state.find_violating(tc).map(|pi| (pi, usize::MAX))
                };
                match selected {
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
                        unwind_frame(
                            &mut item,
                            &mut state,
                            lp.enabled,
                            &dual_d,
                            &mut dual_sum,
                            &mut marked,
                            &mut marked_list,
                        );
                        continue;
                    }
                    Some((pi, commit)) => {
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
                            unwind_frame(
                                &mut item,
                                &mut state,
                                lp.enabled,
                                &dual_d,
                                &mut dual_sum,
                                &mut marked,
                                &mut marked_list,
                            );
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
                        let (left, right) = if marked_mode {
                            // Sweep invariant: after this node's fixed point no
                            // violating pair touches a marked (⊇ forced)
                            // vertex, so both endpoints are free. Branch
                            // `v OUT` | `v COMMITTED` — the include side's
                            // child sweep deletes every conflict of v (the
                            // pair's other endpoint among them): the O(1.62^n)
                            // device. `commit` is an endpoint of this pair (see
                            // find_violating_marked), so the invariant covers it.
                            debug_assert!(
                                ra && rb && !marked[a] && !marked[b],
                                "marked sweep invariant broken"
                            );
                            debug_assert!(
                                commit == a || commit == b,
                                "marked selection returned a vertex outside its own pair"
                            );
                            (commit, Some(RightBranch::Mark(commit)))
                        } else {
                            let left = if ra { a } else { b };
                            let right = if ra && rb {
                                Some(RightBranch::Remove(b))
                            } else {
                                None
                            };
                            (left, right)
                        };
                        // Re-push self to run the right branch after the left.
                        item.frame = Frame::AfterLeft { right };
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
                            mark: None,
                            extra: Vec::new(),
                        });
                    }
                }
            }
            Frame::AfterLeft { right } => match right {
                Some(rbranch) => {
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
                                    nb_rows_total += f.nb_rows as u64;
                                    if f.prune {
                                        lift_kill = Some(f.base + f.sum);
                                        if f.nb_used {
                                            nb_prunes += 1;
                                        }
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
                                nb_rows_total += f.nb_rows as u64;
                                if f.prune {
                                    lift_kill = Some(f.base + f.sum);
                                    lp_ceil_kill_a += 1;
                                    if f.nb_used {
                                        nb_prunes += 1;
                                    }
                                } else {
                                    // The near-miss question: how far above the
                                    // floor does the strengthened LP sit where
                                    // the frontier stalls?
                                    ceil_fail_ub =
                                        Some(-((f.base + f.sum) as f64) / DUAL_SCALE as f64);
                                }
                            }
                            // CERTIFIED SDP TIER: at frontier-defining
                            // failures only (within 1 of the lift frontier),
                            // query the certified-bound worker. Measured on
                            // the 8 real wall sets: bounds 68.1-70.7, all
                            // below the 71 kill line, ~15-25s per certified
                            // kill (the development design notes).
                            if lift_kill.is_none()
                                && !sdp_dead
                                && !should_stop()
                                && state.c_size + 1 >= lift_frontier
                                && sdp_spent.as_secs_f64() * 4.0
                                    <= t_start.elapsed().as_secs_f64() + 1.0
                            {
                                // REACH GATE (skip-only, never a prune): the SDP
                                // bound sits a measured ~2.1 below the LP's own
                                // failing UB at the same node (mean 2.16, max
                                // 2.70 over the 70 paired round-3b field
                                // queries; every one of the 48 kills in that
                                // sample had LP UB < floor+4). Nodes whose LP UB
                                // is further out than the tier can reach are
                                // hopeless, and marked branching produces them
                                // in bulk at c≈160+ (LP UB 78-90) where they
                                // would otherwise eat the whole 25% budget at
                                // ~11 s each.
                                let ub_in_reach = ceil_fail_ub.is_none_or(|ub| {
                                    ub < (best_floor + 1) as f64 + SDP_REACH_SLACK
                                });
                                if !ub_in_reach {
                                    sdp_skip += 1;
                                }
                                if ub_in_reach {
                                    let t_sdp = std::time::Instant::now();
                                    if sdp.is_none() {
                                        sdp = tc.sdp_worker.as_ref().and_then(|config| {
                                            SdpWorker::spawn(config, graph_sha256.as_deref()?)
                                        });
                                        match sdp {
                                            Some(_) => sdp_spawns += 1,
                                            // A spawn that fails is itself a
                                            // break; a run of them is systemic.
                                            None => sdp_broken_streak += 1,
                                        }
                                    }
                                    if let Some(w) = sdp.as_mut() {
                                        sdp_try += 1;
                                        let cset: Vec<usize> =
                                            (0..n).filter(|&v| state.in_c[v]).collect();
                                        // 5 minutes, not 2: the worker's ladder
                                        // now has a triangle rung (DERIVATION
                                        // 2c) costing ~40-90 s of solve plus a
                                        // ~30 s separation solve on top of the
                                        // plain and DNN rungs, and round 3b
                                        // measured ordinary solves stretching
                                        // 10x under CPU contention. A timeout
                                        // is survivable here (the bridge
                                        // replaces the child rather than
                                        // retiring the tier) and every second
                                        // spent is charged to the 25% budget,
                                        // so the deadline only bounds how long
                                        // one hopeless query may run.
                                        match w.query(&cset, std::time::Duration::from_mins(5)) {
                                            SdpReply::Bound(num, den) => {
                                                sdp_broken_streak = 0;
                                                if let Some(marker) =
                                                    certified_sdp_prune_marker(num, den, best_floor)
                                                {
                                                    lift_kill = Some(marker);
                                                    sdp_kill += 1;
                                                }
                                            }
                                            // Healthy worker, no certificate for
                                            // this node: costs the bound only.
                                            SdpReply::NoCertificate => {
                                                sdp_broken_streak = 0;
                                                sdp_nocert += 1;
                                            }
                                            // Desynchronized/dead child: drop it
                                            // (Drop reaps) and let the next
                                            // eligible node spawn a replacement,
                                            // which re-runs the graph-identity
                                            // handshake. Only a RUN of breaks
                                            // retires the tier for the cell.
                                            SdpReply::Broken => {
                                                sdp = None;
                                                sdp_broken_streak += 1;
                                            }
                                        }
                                    }
                                    if sdp_broken_streak >= SDP_MAX_BROKEN_STREAK {
                                        sdp_dead = true;
                                    }
                                    sdp_spent += t_sdp.elapsed();
                                    if progress {
                                        eprintln!(
                                            "  [sdp] c={} try={} kill={} spent={:.0}s dead={} \
                                             spawns={} nocert={} skip={}",
                                            state.c_size,
                                            sdp_try,
                                            sdp_kill,
                                            sdp_spent.as_secs_f64(),
                                            sdp_dead,
                                            sdp_spawns,
                                            sdp_nocert,
                                            sdp_skip,
                                        );
                                    }
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
                            // CDCL-oracle go/no-go: dump the frontier fixing
                            // set (removed vertices) at ceiling FAILURES so the
                            // offline probe can measure PB-CDCL refutation cost
                            // on the real sets. TRACE-gated.
                            if lift_kill.is_none() && tc.dump_frontier {
                                let out: Vec<String> = (0..tc.n)
                                    .filter(|&v| !state.in_c[v])
                                    .map(|v| v.to_string())
                                    .collect();
                                eprintln!(
                                    "  [frontier-set] c={} out={}",
                                    state.c_size,
                                    out.join(",")
                                );
                            }
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
                            unwind_frame(
                                &mut item,
                                &mut state,
                                lp.enabled,
                                &dual_d,
                                &mut dual_sum,
                                &mut marked,
                                &mut marked_list,
                            );
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
                    match rbranch {
                        RightBranch::Remove(j) => {
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
                                mark: None,
                                extra: Vec::new(),
                            });
                        }
                        RightBranch::Mark(v) => {
                            // Commit v (v ∈ every solution of this subtree).
                            // No state change here — the child's Enter sweep
                            // deletes v's conflicts (its violating partner at
                            // minimum) to a fixed point, through the standard
                            // remove path with per-deletion undo logs.
                            mk_marks += 1;
                            marked[v] = true;
                            marked_list.push(v);
                            stack.push(StackItem {
                                frame: Frame::Enter,
                                removed: None,
                                undo: Vec::new(),
                                snap: false,
                                c_at: state.c_size,
                                mark: Some(v),
                                extra: Vec::new(),
                            });
                        }
                    }
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
                    unwind_frame(
                        &mut item,
                        &mut state,
                        lp.enabled,
                        &dual_d,
                        &mut dual_sum,
                        &mut marked,
                        &mut marked_list,
                    );
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
                unwind_frame(
                    &mut item,
                    &mut state,
                    lp.enabled,
                    &dual_d,
                    &mut dual_sum,
                    &mut marked,
                    &mut marked_list,
                );
            }
        }
    }

    if progress {
        eprintln!(
            "  [cell done] nodes={nodes} lp_prunes={lp_prunes} o1={lp_prunes_o1} lift={lp_prunes_lift} m={lp_prunes_m} refreshes={lp_refreshes} subs={lp_reprices} ceil={lp_ceil_try}/{lp_ceil_kill_a}+{lp_ceil_kill_b} sdp={sdp_try}/{sdp_kill} sdpx={sdp_spawns}/{sdp_nocert}/{sdp_skip}/{sdp_dead} nb={nb_rows_total}/{nb_prunes} front={ceil_frontier} mk={mk_marks}/{mk_dels}/{mk_dead} dives={n_dives} rx={rx_lo}/{rx_150}/{rx_160}/{rx_170} floor={best_floor} completed={completed} t={:.2}s",
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
    two_club_prove_worker_with_runtime(
        instance,
        objective,
        seed,
        worker,
        nworkers,
        lp,
        TwoClubRuntime::from_env(),
        should_stop,
        on_improve,
    )
}

fn two_club_prove_worker_with_runtime(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    runtime: TwoClubRuntime,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize_with_runtime(instance, objective, runtime)?;
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
    two_club_prove_d2_worker_with_runtime(
        instance,
        objective,
        seed,
        base_mod,
        classes,
        worker,
        nworkers,
        lp,
        TwoClubRuntime::from_env(),
        should_stop,
        on_improve,
    )
}

#[allow(clippy::too_many_arguments)]
fn two_club_prove_d2_worker_with_runtime(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    base_mod: usize,
    classes: &[usize],
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    runtime: TwoClubRuntime,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize_with_runtime(instance, objective, runtime)?;
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
    two_club_prove_pivot_worker_with_runtime(
        instance,
        objective,
        seed,
        k,
        worker,
        nworkers,
        lp,
        TwoClubRuntime::from_env(),
        should_stop,
        on_improve,
    )
}

#[allow(clippy::too_many_arguments)]
fn two_club_prove_pivot_worker_with_runtime(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    k: usize,
    worker: usize,
    nworkers: usize,
    lp: &LpNodeBound,
    runtime: TwoClubRuntime,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<(usize, bool)> {
    let tc = recognize_with_runtime(instance, objective, runtime)?;
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
    try_two_club_exact_with_runtime(
        instance,
        objective,
        incumbent,
        TwoClubRuntime::from_env(),
        TwoClubLpSelection::Standard,
        should_stop,
        on_improve,
    )
}

/// Selects the LP-node-bound configuration without conflating the production
/// default with a developer campaign's explicit parameters.
#[derive(Clone, Copy)]
enum TwoClubLpSelection {
    /// Production always uses the audited standard configuration.
    Standard,
    /// Feature-gated developer campaigns use exactly the requested value.
    #[cfg(feature = "dev-tools")]
    Explicit(LpNodeBound),
}

impl TwoClubLpSelection {
    fn resolve(self) -> LpNodeBound {
        match self {
            Self::Standard => LpNodeBound::standard(),
            #[cfg(feature = "dev-tools")]
            Self::Explicit(config) => config,
        }
    }
}

fn try_two_club_exact_with_runtime(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: Option<&[bool]>,
    runtime: TwoClubRuntime,
    lp_selection: TwoClubLpSelection,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<PbSolution> {
    let tc = recognize_with_runtime(instance, objective, runtime)?;
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
    // Production selects the standard sound LP node bound. Feature-gated
    // developer campaigns use their exact explicit selection, including the
    // cardinality-only baseline when requested.
    let lp = lp_selection.resolve();
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

/// Typed partition modes used by the feature-gated `ay-pb-dev` campaign.
#[cfg(feature = "dev-tools")]
pub(crate) enum TwoClubCampaignPartition<'a> {
    Whole,
    Worker {
        worker: usize,
        workers: usize,
    },
    DepthTwo {
        base_mod: usize,
        classes: &'a [usize],
        worker: usize,
        workers: usize,
    },
    Pivot {
        pivot_count: usize,
        worker: usize,
        workers: usize,
    },
}

/// Runs one explicitly configured developer campaign without consulting any
/// `TWO_CLUB_*` environment variable.
#[cfg(feature = "dev-tools")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_configured_campaign(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    partition: TwoClubCampaignPartition<'_>,
    lp: &LpNodeBound,
    runtime: TwoClubRuntime,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<TwoClubCampaignResult> {
    match partition {
        TwoClubCampaignPartition::Whole => {
            let solution = try_two_club_exact_with_runtime(
                instance,
                objective,
                seed,
                runtime,
                TwoClubLpSelection::Explicit(*lp),
                should_stop,
                on_improve,
            );
            Some(TwoClubCampaignResult::Whole(solution))
        }
        TwoClubCampaignPartition::Worker { worker, workers } => {
            let result = two_club_prove_worker_with_runtime(
                instance,
                objective,
                seed,
                worker,
                workers,
                lp,
                runtime,
                should_stop,
                on_improve,
            )?;
            Some(TwoClubCampaignResult::Worker(result))
        }
        TwoClubCampaignPartition::DepthTwo {
            base_mod,
            classes,
            worker,
            workers,
        } => {
            let result = two_club_prove_d2_worker_with_runtime(
                instance,
                objective,
                seed,
                base_mod,
                classes,
                worker,
                workers,
                lp,
                runtime,
                should_stop,
                on_improve,
            )?;
            Some(TwoClubCampaignResult::Worker(result))
        }
        TwoClubCampaignPartition::Pivot {
            pivot_count,
            worker,
            workers,
        } => {
            let result = two_club_prove_pivot_worker_with_runtime(
                instance,
                objective,
                seed,
                pivot_count,
                worker,
                workers,
                lp,
                runtime,
                should_stop,
                on_improve,
            )?;
            Some(TwoClubCampaignResult::Worker(result))
        }
    }
}

#[cfg(feature = "dev-tools")]
pub(crate) enum TwoClubCampaignResult {
    Whole(Option<PbSolution>),
    Worker((usize, bool)),
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
    pub(super) fn encode(n: usize, edges: &[(usize, usize)]) -> (PbInstance, PbObjective) {
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

    /// Hermetic recognizer for tests that need to inspect or override the
    /// selected branch rule directly.
    fn recognize(instance: &PbInstance, objective: &PbObjective) -> Option<TwoClub> {
        recognize_with_runtime(
            instance,
            objective,
            TwoClubRuntime::explicit(MAX_NODES, false, false, false),
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

    #[test]
    fn violating_branch_rule_defaults_to_first_and_requires_exact_opt_in() {
        use std::ffi::OsStr;

        assert_eq!(
            ViolatingBranchRule::from_selector(None),
            ViolatingBranchRule::First
        );
        for value in ["", "first", "VIOL", "viol "] {
            assert_eq!(
                ViolatingBranchRule::from_selector(Some(OsStr::new(value))),
                ViolatingBranchRule::First,
                "only the exact `viol` selector may change proof traversal"
            );
        }
        assert_eq!(
            ViolatingBranchRule::from_selector(Some(OsStr::new("viol"))),
            ViolatingBranchRule::ViolDegree
        );
        assert_eq!(
            ViolatingBranchRule::from_selector(Some(OsStr::new("marked"))),
            ViolatingBranchRule::Marked
        );
        assert_eq!(
            ViolatingBranchRule::from_selector(Some(OsStr::new("marked-min"))),
            ViolatingBranchRule::MarkedMinDegree
        );
        // `marked-min` must be EXACT opt-in too. The archived campaign ledgers
        // were produced under plain `marked`; a near-miss selector silently
        // changing the traversal would break comparability with every recorded
        // cell.
        for value in ["marked-", "markedmin", "marked min", "MARKED-MIN", "min"] {
            assert_ne!(
                ViolatingBranchRule::from_selector(Some(OsStr::new(value))),
                ViolatingBranchRule::MarkedMinDegree,
                "only the exact `marked-min` selector may change proof traversal"
            );
        }
        // Both marked variants run the mark/sweep device; the other rules do not.
        assert!(ViolatingBranchRule::Marked.is_marked());
        assert!(ViolatingBranchRule::MarkedMinDegree.is_marked());
        assert!(!ViolatingBranchRule::First.is_marked());
        assert!(!ViolatingBranchRule::ViolDegree.is_marked());
    }

    #[test]
    fn integral_dual_prune_is_strict_at_next_integer_boundary() {
        let floor = 17_i128;
        let next_integer = -(floor + 1) * DUAL_SCALE;

        assert!(
            !scaled_dual_bound_prunes(next_integer, floor),
            "UB == floor + 1 can still improve the incumbent"
        );
        assert!(
            scaled_dual_bound_prunes(next_integer + 1, floor),
            "one exact grid tick below floor + 1 cannot reach another integer"
        );
        assert!(
            scaled_dual_bound_prunes(-floor * DUAL_SCALE, floor),
            "UB == floor is prunable"
        );
        assert!(
            !scaled_dual_bound_prunes(0, i128::MAX),
            "overflow must decline rather than manufacture a prune"
        );
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

    /// BRANCH SELECTION MUST NOT CHANGE THE ANSWER.
    ///
    /// `MarkedMinDegree` branches on a different vertex than `Marked` — the free
    /// vertex of MINIMUM violating degree rather than `pairs[pi].0`. The claim
    /// that this is safe rests on the include/exclude dichotomy
    /// `{2-clubs subset C} = {those without v} disjoint-union {those with v}`
    /// holding at EVERY `v` in `C`, so selection can only reorder the tree, never
    /// make the enumeration incomplete.
    ///
    /// That is exactly the kind of claim that deserves a differential rather than
    /// a comment: every branch rule must reproduce brute force on the same graphs.
    /// Track 1 shipped this rule with no tests at all; this is the gate.
    #[test]
    fn every_branch_rule_matches_bruteforce() {
        let mut rng = Rng(0x2c1b_b12a);
        let rules = [
            ("marked", ViolatingBranchRule::Marked),
            ("marked-min", ViolatingBranchRule::MarkedMinDegree),
            ("first", ViolatingBranchRule::First),
            ("viol", ViolatingBranchRule::ViolDegree),
        ];
        let mut checked = 0usize;
        for round in 0..30 {
            let n = 6 + (round % 6);
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
                continue;
            }
            let expect = brute_force(n, &edges);
            for (name, rule) in rules {
                let runtime = TwoClubRuntime {
                    max_nodes: u64::MAX,
                    branch_rule: rule,
                    trace: false,
                    dump_frontier: false,
                    sdp_worker: None,
                };
                let mut _im = |_v: i128, _a: &[bool]| {};
                let got = try_two_club_exact_with_runtime(
                    &instance,
                    &objective,
                    None,
                    runtime,
                    TwoClubLpSelection::Standard,
                    &|| false,
                    &mut _im,
                )
                .unwrap_or_else(|| panic!("round {round} rule {name}: declined a valid encoding"));
                assert_eq!(
                    got.objective,
                    Some(-(expect as i128)),
                    "round {round} rule {name}: n={n} edges={edges:?} — a branch \
                     SELECTION rule changed the proven optimum, so the \
                     include/exclude dichotomy is not holding at the vertex it picks"
                );
                checked += 1;
            }
        }
        assert!(
            checked >= 80,
            "only {checked} (graph, rule) pairs ran — the differential is too thin"
        );
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

    #[cfg(feature = "dev-tools")]
    #[test]
    fn developer_whole_lp_selection_preserves_the_explicit_value() {
        let configured = LpNodeBound {
            enabled: false,
            warmup: 7,
            cadence: 11,
            window: 13,
            max_rows: 17,
            low_margin: 19,
            ceiling: false,
            exact_margin: 23,
            nbhd_rows: true,
        };
        let resolved = TwoClubLpSelection::Explicit(configured).resolve();

        assert!(!resolved.enabled);
        assert_eq!(resolved.warmup, 7);
        assert_eq!(resolved.cadence, 11);
        assert_eq!(resolved.window, 13);
        assert_eq!(resolved.max_rows, 17);
        assert_eq!(resolved.low_margin, 19);
        assert!(!resolved.ceiling);
        assert_eq!(resolved.exact_margin, 23);
        assert!(resolved.nbhd_rows);
    }

    #[test]
    fn certified_sdp_prune_marker_is_strict_and_fail_closed() {
        assert_eq!(
            certified_sdp_prune_marker(70, 1, 70),
            Some(-70 * DUAL_SCALE)
        );
        assert_eq!(
            certified_sdp_prune_marker(141, 2, 70),
            Some(-(141 * DUAL_SCALE / 2))
        );
        assert_eq!(certified_sdp_prune_marker(71, 1, 70), None);
        assert_eq!(certified_sdp_prune_marker(-1, 1, 70), None);
        assert_eq!(certified_sdp_prune_marker(1, 0, 70), None);
        assert_eq!(certified_sdp_prune_marker(1, -1, 70), None);
        assert_eq!(certified_sdp_prune_marker(0, i128::MAX, 1), None);
    }

    #[test]
    fn certified_sdp_protocol_requires_one_exact_bound_record() {
        assert_eq!(parse_sdp_bound_response("BOUND 141 2"), Some((141, 2)));
        assert_eq!(parse_sdp_bound_response(" BOUND 141 2 "), Some((141, 2)));
        assert_eq!(parse_sdp_bound_response("BOUND 141 2 trailing"), None);
        assert_eq!(parse_sdp_bound_response("BOUND 141"), None);
        assert_eq!(parse_sdp_bound_response("BOUND -1 2"), None);
        assert_eq!(parse_sdp_bound_response("BOUND 1 0"), None);
        assert_eq!(parse_sdp_bound_response("BOUND 1 -2"), None);
        assert_eq!(
            parse_sdp_bound_response("BOUND 170141183460469231731687303715884105728 1"),
            None
        );
        assert_eq!(parse_sdp_bound_response("FAIL uncertified"), None);
    }

    #[test]
    fn certified_sdp_graph_digest_is_row_order_independent() {
        let first = vec![(0, 2, vec![1]), (1, 3, vec![0, 2])];
        let reordered = vec![(1, 3, vec![0, 2]), (0, 2, vec![1])];
        let changed = vec![(1, 3, vec![0, 2]), (0, 2, vec![3])];

        let digest = graph_sha256(4, &first);
        assert_eq!(
            digest,
            "d2c81ed7c4b1851e5e25d401ec72e5e4eb580ae85d692ef4ef0c4fcfa5e11ce4"
        );
        assert_eq!(digest, graph_sha256(4, &reordered));
        assert_ne!(graph_sha256(4, &first), graph_sha256(4, &changed));
    }

    /// Scripted stand-in for the development design notes, driven through
    /// the real protocol over real pipes (`/bin/sh`, so the fixture cannot
    /// accidentally depend on the certified toolchain being installed).
    #[cfg(unix)]
    struct FakeWorker {
        config: SdpWorkerConfig,
        directory: std::path::PathBuf,
    }

    #[cfg(unix)]
    impl FakeWorker {
        fn new(label: &str, body: &str) -> Self {
            use std::sync::atomic::{AtomicU64, Ordering};
            static NEXT_ID: AtomicU64 = AtomicU64::new(0);
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ay-sdp-worker-{}-{label}-{id}", std::process::id()));
            std::fs::create_dir(&directory).expect("create fake-worker directory");
            let script = directory.join("worker.sh");
            let instance = directory.join("instance.opb");
            std::fs::write(&script, body).expect("write fake worker");
            std::fs::write(&instance, b"* fake fixture\n").expect("write fake instance");
            Self {
                config: SdpWorkerConfig {
                    interpreter: std::path::PathBuf::from("/bin/sh"),
                    script,
                    instance,
                },
                directory,
            }
        }
    }

    #[cfg(unix)]
    impl Drop for FakeWorker {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.config.script);
            let _ = std::fs::remove_file(&self.config.instance);
            let _ = std::fs::remove_dir(&self.directory);
        }
    }

    #[cfg(unix)]
    #[test]
    fn certified_sdp_worker_checks_identity_and_reaps_on_timeout() {
        let digest = graph_sha256(4, &[(0, 2, vec![1]), (1, 3, vec![0, 2])]);
        let successful = FakeWorker::new(
            "success",
            &format!(
                "printf '%s\\n' 'READY graph_sha256={digest} n=4 pairs=2'\n\
                 IFS= read -r request || exit 3\n\
                 printf '%s\\n' 'BOUND 141 2'\n\
                 IFS= read -r quit || true\n"
            ),
        );
        let mut worker =
            SdpWorker::spawn(&successful.config, &digest).expect("matching worker handshake");
        assert_eq!(
            worker.query(&[0, 1], std::time::Duration::from_secs(1)),
            SdpReply::Bound(141, 2)
        );
        drop(worker);

        let mismatch = FakeWorker::new(
            "mismatch",
            "printf '%s\\n' 'READY graph_sha256=deadbeef n=4 pairs=2'\nwhile :; do :; done\n",
        );
        assert!(
            SdpWorker::spawn(&mismatch.config, &digest).is_none(),
            "a graph-identity mismatch must decline"
        );

        let timeout = FakeWorker::new(
            "timeout",
            &format!(
                "printf '%s\\n' 'READY graph_sha256={digest} n=4 pairs=2'\n\
                 IFS= read -r request || exit 3\n\
                 while :; do :; done\n"
            ),
        );
        let mut worker =
            SdpWorker::spawn(&timeout.config, &digest).expect("matching worker handshake");
        assert_eq!(
            worker.query(&[0, 1], std::time::Duration::from_millis(20)),
            SdpReply::Broken,
            "a timed-out query leaves the stream desynchronized: the child must \
             be classified as unusable, not merely uncertified"
        );
        drop(worker);
    }

    /// The failure taxonomy the bridge policy rests on. Round 3b retired the
    /// certified tier on 7 of 8 workers within the first 25 minutes of a 12-hour
    /// cell because BOTH of the answers below were funnelled into one "any
    /// failure is permanent" path: a `FAIL` line (a healthy worker reporting no
    /// certificate for one node) and a 120 s solve under CPU contention.
    /// `NoCertificate` must cost only the bound; `Broken` must cost only the
    /// child.
    #[cfg(unix)]
    #[test]
    fn certified_sdp_in_protocol_fail_keeps_the_bridge_usable() {
        let digest = graph_sha256(4, &[(0, 2, vec![1]), (1, 3, vec![0, 2])]);

        // A worker that cannot certify the first node and can the second — the
        // stream stays synchronized across the refusal, so the SAME child
        // answers the follow-up query.
        let refusing = FakeWorker::new(
            "refusing",
            &format!(
                "printf '%s\\n' 'READY graph_sha256={digest} n=4 pairs=2'\n\
                 IFS= read -r first || exit 3\n\
                 printf '%s\\n' 'FAIL uncertified iv=True ex=False'\n\
                 IFS= read -r second || exit 3\n\
                 printf '%s\\n' 'BOUND 141 2'\n\
                 IFS= read -r quit || true\n"
            ),
        );
        let mut worker =
            SdpWorker::spawn(&refusing.config, &digest).expect("matching worker handshake");
        assert_eq!(
            worker.query(&[0, 1], std::time::Duration::from_secs(5)),
            SdpReply::NoCertificate
        );
        assert_eq!(
            worker.query(&[0, 2], std::time::Duration::from_secs(5)),
            SdpReply::Bound(141, 2),
            "an in-protocol refusal must not cost the bridge its next bound"
        );
        drop(worker);

        // Off-protocol chatter is NOT a refusal: the caller cannot know where in
        // the stream it is, so the child is unusable (fail-closed).
        let garbage = FakeWorker::new(
            "garbage",
            &format!(
                "printf '%s\\n' 'READY graph_sha256={digest} n=4 pairs=2'\n\
                 IFS= read -r first || exit 3\n\
                 printf '%s\\n' 'BOUND 141 2 trailing'\n\
                 IFS= read -r quit || true\n"
            ),
        );
        let mut worker =
            SdpWorker::spawn(&garbage.config, &digest).expect("matching worker handshake");
        assert_eq!(
            worker.query(&[0, 1], std::time::Duration::from_secs(5)),
            SdpReply::Broken
        );
        drop(worker);

        // A child that exits mid-protocol reports EOF, not a refusal, and a
        // REPLACEMENT spawn on the same config recovers the tier — the recovery
        // the call site performs instead of retiring on the first break.
        let quitting = FakeWorker::new(
            "quitting",
            &format!(
                "printf '%s\\n' 'READY graph_sha256={digest} n=4 pairs=2'\n\
                 IFS= read -r first || exit 3\n\
                 exit 0\n"
            ),
        );
        let mut worker =
            SdpWorker::spawn(&quitting.config, &digest).expect("matching worker handshake");
        assert_eq!(
            worker.query(&[0, 1], std::time::Duration::from_secs(5)),
            SdpReply::Broken
        );
        drop(worker);
        let mut replacement = SdpWorker::spawn(&quitting.config, &digest)
            .expect("a broken child must be replaceable — identity is re-checked");
        assert_eq!(
            replacement.query(&[0, 1], std::time::Duration::from_secs(5)),
            SdpReply::Broken
        );
        drop(replacement);

        // The retirement rule itself: only a RUN of breaks is systemic.
        const _: () = assert!(SDP_MAX_BROKEN_STREAK >= 2, "one break must be survivable");
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
            // Stress the strengthened-neighborhood rows end-to-end too: with
            // cadence 1 every branching node prices them; any validity or
            // pricing error shows up as a wrong optimum vs brute force.
            nbhd_rows: true,
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

    /// The `marked` selector must be an EXACT opt-in, like `viol`.
    #[test]
    fn marked_branch_rule_requires_exact_opt_in() {
        use std::ffi::OsStr;
        assert_eq!(
            ViolatingBranchRule::from_selector(Some(OsStr::new("marked"))),
            ViolatingBranchRule::Marked
        );
        for value in ["MARKED", "marked ", "mark"] {
            assert_eq!(
                ViolatingBranchRule::from_selector(Some(OsStr::new(value))),
                ViolatingBranchRule::First,
                "only the exact `marked` selector may change proof traversal"
            );
        }
    }

    /// MARKED BRANCHING differential: `remove v | mark v` with the
    /// mark-conflict fixed-point sweep must reproduce brute force — whole
    /// space AND the min-excluded partition, whose forced cells exercise
    /// initial marks (IRR at the cell root) and dead-by-marked-pair cells —
    /// under no LP and under the refresh-every-node LP stress config
    /// (snapshot push/pop interleaved with sweep deletions).
    #[test]
    fn two_club_marked_branching_matches_bruteforce() {
        let aggressive = LpNodeBound {
            enabled: true,
            warmup: 0,
            cadence: 1,
            window: 1_000_000,
            max_rows: 0,
            low_margin: 0,
            ceiling: true,
            exact_margin: 4,
            // Stress the strengthened-neighborhood rows end-to-end too: with
            // cadence 1 every branching node prices them; any validity or
            // pricing error shows up as a wrong optimum vs brute force.
            nbhd_rows: true,
        };
        let mut rng = Rng(0x2c1b_3a6b);
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
            let mut tc = recognize(&instance, &objective).expect("recognize");
            // BOTH marked variants. `MarkedMinDegree` changes only WHICH free
            // vertex is committed, and the include/exclude dichotomy is valid at
            // every vertex of C — so it must reproduce brute force exactly like
            // `Marked` does, on the whole space and on every partition cell. A
            // selection rule that made the enumeration incomplete would show up
            // here as a missed optimum.
            for rule in [
                ViolatingBranchRule::Marked,
                ViolatingBranchRule::MarkedMinDegree,
            ] {
                tc.branch_rule = rule;
                for lp in [LpNodeBound::disabled(), aggressive] {
                    let mut _cb = |_s: usize, _a: &[bool]| {};
                    // Whole space in one cell (seed floor 1: a single vertex).
                    let verdict = solve_exact(&tc, 1, &lp, &|| false, &mut _cb)
                        .unwrap_or_else(|| panic!("round {round}: marked search unfinished"));
                    let got = match verdict {
                        SearchVerdict::Better(sz, _) => sz,
                        SearchVerdict::SeedOptimal => 1,
                    };
                    assert_eq!(got, expect, "round {round}: n={n} edges={edges:?}");
                    // Min-excluded partition: full-set cell + every cell m. Forced
                    // vertices become initial marks in marked mode.
                    let mut agg = 1usize;
                    let mut all_done = true;
                    let forced = vec![true; n];
                    match solve_exact_cell(&tc, &forced, &[], 1, &lp, &|| false, &mut _cb) {
                        Some(SearchVerdict::Better(sz, _)) => agg = agg.max(sz),
                        Some(SearchVerdict::SeedOptimal) => {}
                        None => all_done = false,
                    }
                    for m in 0..n {
                        let mut forced = vec![false; n];
                        forced[..m].fill(true);
                        match solve_exact_cell(&tc, &forced, &[m], 1, &lp, &|| false, &mut _cb) {
                            Some(SearchVerdict::Better(sz, _)) => agg = agg.max(sz),
                            Some(SearchVerdict::SeedOptimal) => {}
                            None => all_done = false,
                        }
                    }
                    assert!(
                        all_done,
                        "round {round}: marked partition left cells unexhausted"
                    );
                    assert_eq!(
                        agg, expect,
                        "round {round} partition: n={n} edges={edges:?} rule={rule:?}"
                    );
                }
            }
        }
    }

    /// ADVERSARIAL completeness gates for marked branching: two deterministic
    /// graphs engineered so that specific naive mark-deletion bugs LOSE the
    /// optimum (random differentials need not hit these shapes).
    ///
    /// Graph 1 (mark-leak / backtrack order), n=8, edges
    /// (0,2),(2,3),(2,4),(2,5),(1,6),(1,7),(6,7), optimum {0,2,3,4,5} = 5:
    /// the root's first violating pair is (0,1); the LEFT subtree (0 removed)
    /// branches on (1,2) and MARKS 1 (sweep-deleting 3,4,5); the optimum lives
    /// only in the root's RIGHT subtree, where 0 is marked and 1 must be
    /// sweep-DELETED. If 1's mark leaked out of the left subtree (missing or
    /// out-of-order unmark), the right branch dies as a marked-marked pair
    /// (0,1) and the search reports 4 — the optimum is lost.
    #[test]
    fn two_club_marked_leak_adversarial_graph() {
        let n = 8;
        let edges = [(0, 2), (2, 3), (2, 4), (2, 5), (1, 6), (1, 7), (6, 7)];
        assert_eq!(brute_force(n, &edges), 5, "test-graph self-check");
        let (instance, objective) = encode(n, &edges);
        let mut tc = recognize(&instance, &objective).expect("recognize");
        tc.branch_rule = ViolatingBranchRule::Marked;
        let aggressive = LpNodeBound {
            enabled: true,
            warmup: 0,
            cadence: 1,
            window: 1_000_000,
            max_rows: 0,
            low_margin: 0,
            ceiling: true,
            exact_margin: 4,
            // Stress the strengthened-neighborhood rows end-to-end too: with
            // cadence 1 every branching node prices them; any validity or
            // pricing error shows up as a wrong optimum vs brute force.
            nbhd_rows: true,
        };
        for lp in [LpNodeBound::disabled(), aggressive] {
            let mut _cb = |_s: usize, _a: &[bool]| {};
            let verdict = solve_exact(&tc, 1, &lp, &|| false, &mut _cb).expect("search unfinished");
            let got = match verdict {
                SearchVerdict::Better(sz, set) => {
                    // The reported set must itself be the real optimum's size
                    // AND a valid 2-club (guards corrupted-state incumbents).
                    let members: Vec<usize> = (0..n).filter(|&v| set[v]).collect();
                    assert_eq!(members.len(), sz);
                    sz
                }
                SearchVerdict::SeedOptimal => 1,
            };
            assert_eq!(got, 5, "mark leak or unwind-order bug lost the optimum");
        }
    }

    /// Graph 2 (forced-cell fixed-point cascade), n=6, edges
    /// (0,2),(1,2),(2,5),(0,3),(3,4),(4,5),(1,5); cell forces {0,1}
    /// (non-adjacent, sole common neighbour 2). The sweep processes the
    /// marked list in order [0, 1]:
    ///   pass 1: m=0 deletes nothing; m=1 hits (1,3) violating (CN=∅) →
    ///   delete 3 — which was the SOLE common neighbour of (0,4);
    ///   pass 2: m=0 (the EARLIER mark) now hits (0,4) violating → delete 4.
    /// The deletion is triggered by the LAST marked vertex and cascades
    /// against an EARLIER one, so only the outer fixed-point loop catches it.
    /// A single-pass sweep leaves the marked-touching pair (0,4) alive for
    /// find_violating, breaking the sweep invariant — in release the branch
    /// code would then REMOVE forced vertex 0. The correct cell answer (max
    /// 2-club containing both 0 and 1) is {0,1,2,5} = 4.
    /// Also: forcing {1,3} (a violating pair over the whole graph) must kill
    /// the cell at the root sweep as dead-by-marked-pair, reported as a
    /// COMPLETED SeedOptimal — not a lost/aborted cell.
    #[test]
    fn two_club_marked_forced_cell_cascade_adversarial() {
        let n = 6;
        let edges = [(0, 2), (1, 2), (2, 5), (0, 3), (3, 4), (4, 5), (1, 5)];
        let (instance, objective) = encode(n, &edges);
        let mut tc = recognize(&instance, &objective).expect("recognize");
        tc.branch_rule = ViolatingBranchRule::Marked;
        let aggressive = LpNodeBound {
            enabled: true,
            warmup: 0,
            cadence: 1,
            window: 1_000_000,
            max_rows: 0,
            low_margin: 0,
            ceiling: true,
            exact_margin: 4,
            // Stress the strengthened-neighborhood rows end-to-end too: with
            // cadence 1 every branching node prices them; any validity or
            // pricing error shows up as a wrong optimum vs brute force.
            nbhd_rows: true,
        };
        // Cell-restricted brute force: max 2-club containing BOTH 0 and 1.
        let cell_expect = {
            let mut adj = vec![vec![false; n]; n];
            for &(a, b) in &edges {
                adj[a][b] = true;
                adj[b][a] = true;
            }
            let mut best = 0usize;
            for mask in 0u32..(1 << n) {
                if mask & 0b11 != 0b11 {
                    continue; // must contain 0 and 1
                }
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
        };
        assert_eq!(cell_expect, 4, "test-graph self-check");
        for lp in [LpNodeBound::disabled(), aggressive] {
            let mut _cb = |_s: usize, _a: &[bool]| {};
            // Whole space must match brute force.
            let whole = solve_exact(&tc, 1, &lp, &|| false, &mut _cb).expect("unfinished");
            let got = match whole {
                SearchVerdict::Better(sz, _) => sz,
                SearchVerdict::SeedOptimal => 1,
            };
            assert_eq!(got, brute_force(n, &edges));
            // Forced {0,1}: initial marks + two-round cascade at the root.
            let mut forced = vec![false; n];
            forced[0] = true;
            forced[1] = true;
            let cell = solve_exact_cell(&tc, &forced, &[], 1, &lp, &|| false, &mut _cb)
                .expect("cascade cell unfinished");
            let got = match cell {
                SearchVerdict::Better(sz, set) => {
                    assert!(set[0] && set[1], "cell solution dropped a forced vertex");
                    sz
                }
                SearchVerdict::SeedOptimal => 1,
            };
            assert_eq!(
                got, cell_expect,
                "fixed-point cascade lost the cell optimum"
            );
            // Forced {1,3}: (1,3) is violating over the whole graph — the cell
            // is dead; must complete as SeedOptimal (fail-closed None would be
            // a lost cell, Better would be unsound).
            let mut forced = vec![false; n];
            forced[1] = true;
            forced[3] = true;
            match solve_exact_cell(&tc, &forced, &[], 1, &lp, &|| false, &mut _cb) {
                Some(SearchVerdict::SeedOptimal) => {}
                Some(SearchVerdict::Better(sz, _)) => {
                    panic!("dead forced-forced cell reported a club of size {sz}")
                }
                None => panic!("dead cell must COMPLETE, not abort"),
            }
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

    /// Bounded synthetic A/B gate for default versus marked branching. The
    /// larger campaign is benchmark evidence, not a disabled test; this gate
    /// keeps the same two-arm exactness check on deterministic small graphs.
    #[test]
    fn two_club_marked_ab_probe_is_bounded_and_exact() {
        let run = |n: usize, edges: &[(usize, usize)], tag: &str| {
            let (instance, objective) = encode(n, edges);
            if instance.constraints.is_empty() {
                return;
            }
            // Max-degree star seed: {v} ∪ N(v) is always a 2-club.
            let mut deg = vec![0usize; n];
            for &(a, b) in edges {
                deg[a] += 1;
                deg[b] += 1;
            }
            let star = 1 + deg.iter().copied().max().unwrap_or(0);
            let mut opts: Vec<Option<usize>> = Vec::new();
            for rule in [ViolatingBranchRule::First, ViolatingBranchRule::Marked] {
                let mut tc = recognize(&instance, &objective).expect("recognize");
                tc.branch_rule = rule;
                eprintln!(">>> AB {tag} n={n} rule={rule:?} seed={star}");
                let t0 = std::time::Instant::now();
                let mut _cb = |_s: usize, _a: &[bool]| {};
                let verdict = solve_exact(&tc, star, &LpNodeBound::disabled(), &|| false, &mut _cb);
                let got = verdict.map(|v| match v {
                    SearchVerdict::Better(sz, _) => sz,
                    SearchVerdict::SeedOptimal => star,
                });
                eprintln!(
                    "<<< AB {tag} n={n} rule={rule:?} opt={got:?} t={:.2}s",
                    t0.elapsed().as_secs_f64()
                );
                opts.push(got);
            }
            // A `None` arm hit the node cap (raise TWO_CLUB_MAX_NODES to
            // compare) — only two FINISHED arms must agree.
            if let (Some(a), Some(b)) = (opts[0], opts[1]) {
                assert_eq!(a, b, "{tag} n={n}: optima differ between arms");
            }
        };
        // A small deterministic slice of the exact gate graph family.
        let mut rng = Rng(0x2c1b_5eed);
        for round in 0..4 {
            let n = 6 + (round % 6);
            let mut edges = Vec::new();
            for a in 0..n {
                for b in (a + 1)..n {
                    if rng.next() % 100 < 30 {
                        edges.push((a, b));
                    }
                }
            }
            run(n, &edges, &format!("gate{round}"));
        }
    }

    /// Test helper: index of the non-adjacent pair {u, w} if it is ACTIVE at
    /// the current state (both endpoints still in C); None if u, w adjacent.
    fn find_active_pair(tc: &TwoClub, state: &SearchState, u: u32, w: u32) -> Option<usize> {
        tc.pair_of_vertex[u as usize]
            .iter()
            .map(|&pi| pi as usize)
            .find(|&pi| {
                let (a, b, _) = &tc.pairs[pi];
                state.both_in[pi] && ((*a == u && *b == w) || (*a == w && *b == u))
            })
    }

    /// VALIDITY GATE for the strengthened-neighborhood rows — the gate that
    /// would have caught the odd-hole trap. On random small graphs it
    /// EXHAUSTIVELY enumerates every subset of the current candidate set `C`,
    /// tests the 2-club property exactly (witnesses inside the subset), and
    /// asserts EVERY generated row — including rows frozen at ANCESTOR states
    /// and re-checked at every descendant state, because the engine prices a
    /// refresh's rows down its whole subtree — is satisfied by every 2-club's
    /// incidence vector. Exhaustive per graph/state, never sampled. Each row's
    /// structural side conditions are also independently re-derived.
    #[test]
    fn strengthened_nbhd_rows_exhaustive_validity_gate() {
        // (n, density%, graph reps): 2^n subset enumeration stays exact & fast.
        let configs = [
            (12usize, 30u64, 3usize),
            (12, 50, 3),
            (15, 15, 3),
            (15, 30, 3),
            (18, 15, 2),
            (18, 25, 2),
        ];
        let mut rng = Rng(0x5eed_2c1b);
        let mut rows_checked = 0u64;
        let mut rows_at_descendants = 0u64;
        let mut lifted_ge2 = 0u64;
        for &(n, den, reps) in &configs {
            for _rep in 0..reps {
                let mut edges = Vec::new();
                for a in 0..n {
                    for b in (a + 1)..n {
                        if rng.next() % 100 < den {
                            edges.push((a, b));
                        }
                    }
                }
                let (instance, objective) = encode(n, &edges);
                if instance.constraints.is_empty() {
                    continue;
                }
                let tc = recognize(&instance, &objective).expect("valid encoding");
                let mut nbr = vec![0u32; n];
                for &(a, b) in &edges {
                    nbr[a] |= 1 << b;
                    nbr[b] |= 1 << a;
                }
                let is_two_club = |mask: u32| -> bool {
                    let mut vs = mask;
                    while vs != 0 {
                        let a = vs.trailing_zeros() as usize;
                        vs &= vs - 1;
                        let mut ws = vs;
                        while ws != 0 {
                            let b = ws.trailing_zeros() as usize;
                            ws &= ws - 1;
                            if nbr[a] & (1 << b) == 0 && nbr[a] & nbr[b] & mask == 0 {
                                return false;
                            }
                        }
                    }
                    true
                };
                // Search state exactly as solve_exact_cell builds it.
                let mut state = SearchState {
                    in_c: vec![true; n],
                    c_size: n,
                    cn_alive: tc.pairs.iter().map(|(_, _, cn)| cn.len() as u32).collect(),
                    both_in: vec![true; tc.pairs.len()],
                };
                let mut undo_sink = Vec::new();
                // Rows FROZEN at generation time (members + live CN), kept and
                // re-checked across all later phases (descendant states).
                let mut frozen: Vec<(usize, Vec<u32>, Vec<u32>)> = Vec::new();
                for phase in 0..5 {
                    for (pi, iset) in strengthened_nbhd_rows(&tc, &state, 100_000) {
                        let (a, b, cn) = &tc.pairs[pi as usize];
                        // Independently re-derive the family's side conditions.
                        assert!(
                            state.both_in[pi as usize] && state.cn_alive[pi as usize] > 0,
                            "host pair must be active with live CN"
                        );
                        assert!(!iset.is_empty(), "empty lift is just the pair row");
                        for (k, &i) in iset.iter().enumerate() {
                            for &other in [*a, *b].iter().chain(iset[..k].iter()) {
                                let pj = find_active_pair(&tc, &state, i, other).expect(
                                    "every lift member must be non-adjacent to a, b, and the rest of I, with both endpoints in C",
                                );
                                assert_eq!(
                                    state.cn_alive[pj], 0,
                                    "lift pairs must be VIOLATING at the current C"
                                );
                            }
                        }
                        if iset.len() >= 2 {
                            lifted_ge2 += 1;
                        }
                        let mut members = vec![*a, *b];
                        members.extend_from_slice(&iset);
                        let cn_live: Vec<u32> = cn
                            .iter()
                            .copied()
                            .filter(|&r| state.in_c[r as usize])
                            .collect();
                        assert!(!cn_live.is_empty(), "cn_alive > 0 must mean live CN");
                        frozen.push((phase, members, cn_live));
                    }
                    // EXHAUSTIVE: every subset of the current C, exact 2-club
                    // test, every frozen row (ancestor rows included).
                    let cmask: u32 = (0..n).filter(|&v| state.in_c[v]).map(|v| 1u32 << v).sum();
                    for mask in 0u32..(1u32 << n) {
                        if mask & !cmask != 0 || !is_two_club(mask) {
                            continue;
                        }
                        for (born, members, cn_live) in &frozen {
                            let m_in =
                                members.iter().filter(|&&v| mask & (1 << v) != 0).count() as i64;
                            let r_in =
                                cn_live.iter().filter(|&&v| mask & (1 << v) != 0).count() as i64;
                            assert!(
                                m_in - r_in <= 1,
                                "row born phase {born} VIOLATED at phase {phase}: members={members:?} cn={cn_live:?} club={mask:#b} n={n} edges={edges:?}"
                            );
                            rows_checked += 1;
                            if *born < phase {
                                rows_at_descendants += 1;
                            }
                        }
                    }
                    // Descend through the engine's exact removal path so the
                    // cn_alive/both_in dynamics are the real ones.
                    for _ in 0..(n / 5).max(2) {
                        if state.c_size <= 4 {
                            break;
                        }
                        let alive: Vec<usize> = (0..n).filter(|&v| state.in_c[v]).collect();
                        let v = alive[(rng.next() % alive.len() as u64) as usize];
                        state.remove(v, &tc, &mut undo_sink);
                    }
                }
            }
        }
        assert!(
            rows_checked > 0,
            "gate vacuous: no (row, 2-club) checks ran"
        );
        assert!(
            rows_at_descendants > 0,
            "gate never re-checked an ancestor row at a descendant state"
        );
        assert!(lifted_ge2 > 0, "gate never saw a lift of size >= 2");
    }

    /// ADVERSARIAL deterministic gate (reviewer-added): hand-placed structure
    /// aimed at the family's weakest hypotheses, instead of random graphs.
    ///
    /// Graph (n = 9): host pair (0,1), hubs CN(0,1) = {2,3}; lift candidates
    /// 4, 5; 6 = the SOLE witness of (0,4); 7 = the SOLE witness of (4,5) and
    /// itself a lift candidate ADJACENT to 5; 8 shares hubs {2,3} with 0 and 1.
    /// The schedule removes 6, 7, then BOTH hubs while 0,1,4,5 stay in C:
    ///
    ///   - born-late condition (1): (0,4) un-violates only when 6 leaves C —
    ///     4 must not be liftable before that;
    ///   - condition (2) trap: 4 and 5 are both candidates while their witness
    ///     7 is alive — a row lifting BOTH is killed by the 2-club {4,5,7};
    ///   - witness-in-S: after both hubs leave C, frozen ancestor rows reduce
    ///     to `x0+x1+x4+x5 <= 1` — valid only because a 2-club's witness must
    ///     lie inside S itself (with hubs still in G but outside C);
    ///   - unwind trap: the phase-2 row (I = {4,5}) is PROVABLY INVALID at the
    ///     root C, so cross-unwind caching of this family would be unsound —
    ///     the regenerate-per-solve discipline is load-bearing.
    #[test]
    fn strengthened_nbhd_rows_adversarial_gate() {
        let n = 9usize;
        let edges: Vec<(usize, usize)> = vec![
            (0, 2),
            (1, 2),
            (0, 3),
            (1, 3), // hubs: CN(0,1) = {2,3}
            (4, 6),
            (0, 6), // 6 = sole witness of (0,4)
            (4, 7),
            (5, 7), // 7 = sole witness of (4,5)
            (2, 8),
            (3, 8), // 8: CN(0,8) = CN(1,8) = {2,3}
        ];
        let (instance, objective) = encode(n, &edges);
        let tc = recognize(&instance, &objective).expect("valid encoding");
        let mut nbr = vec![0u32; n];
        for &(a, b) in &edges {
            nbr[a] |= 1 << b;
            nbr[b] |= 1 << a;
        }
        let is_two_club = |mask: u32| -> bool {
            let mut vs = mask;
            while vs != 0 {
                let a = vs.trailing_zeros() as usize;
                vs &= vs - 1;
                let mut ws = vs;
                while ws != 0 {
                    let b = ws.trailing_zeros() as usize;
                    ws &= ws - 1;
                    if nbr[a] & (1 << b) == 0 && nbr[a] & nbr[b] & mask == 0 {
                        return false;
                    }
                }
            }
            true
        };
        let mut state = SearchState {
            in_c: vec![true; n],
            c_size: n,
            cn_alive: tc.pairs.iter().map(|(_, _, cn)| cn.len() as u32).collect(),
            both_in: vec![true; tc.pairs.len()],
        };
        let mut undo = Vec::new();
        // (born phase, members, live CN frozen at generation)
        let mut frozen: Vec<(usize, Vec<u32>, Vec<u32>)> = Vec::new();
        let host_isets = |tc: &TwoClub, state: &SearchState| -> Vec<Vec<u32>> {
            strengthened_nbhd_rows(tc, state, 100_000)
                .into_iter()
                .filter(|(pi, _)| {
                    let (a, b, _) = &tc.pairs[*pi as usize];
                    (*a, *b) == (0, 1)
                })
                .map(|(_, iset)| iset)
                .collect()
        };
        let schedule: [Option<usize>; 5] = [None, Some(6), Some(7), Some(2), Some(3)];
        let mut lift2_row: Option<(Vec<u32>, Vec<u32>)> = None;
        for (phase, rm) in schedule.iter().enumerate() {
            if let Some(v) = rm {
                state.remove(*v, &tc, &mut undo);
            }
            for (pi, iset) in strengthened_nbhd_rows(&tc, &state, 100_000) {
                let (a, b, cn) = &tc.pairs[pi as usize];
                let mut members = vec![*a, *b];
                members.extend_from_slice(&iset);
                let cn_live: Vec<u32> = cn
                    .iter()
                    .copied()
                    .filter(|&r| state.in_c[r as usize])
                    .collect();
                frozen.push((phase, members, cn_live));
            }
            let host = host_isets(&tc, &state);
            match phase {
                0 => {
                    assert!(
                        host.iter().any(|i| i.contains(&5)),
                        "root host row must lift 5"
                    );
                    assert!(
                        host.iter().all(|i| !i.contains(&4)),
                        "4 lifted while (0,4) still has witness 6 in C"
                    );
                }
                1 => {
                    assert!(
                        !host.is_empty(),
                        "host (0,1) must still generate a row at phase 1"
                    );
                    assert!(
                        host.iter().all(|i| !(i.contains(&4) && i.contains(&5))),
                        "4 and 5 lifted together while their witness 7 is in C"
                    );
                }
                2 => {
                    let full = host
                        .iter()
                        .find(|i| i.contains(&4) && i.contains(&5))
                        .expect("after removing 7, I must contain both 4 and 5");
                    let mut members = vec![0u32, 1];
                    members.extend_from_slice(full);
                    lift2_row = Some((members, vec![2, 3]));
                }
                _ => {}
            }
            // EXHAUSTIVE: every 2-club within the CURRENT C against every
            // frozen row, ancestors included (phases 3/4 = hub removal with
            // every row member still in C).
            let cmask: u32 = (0..n).filter(|&v| state.in_c[v]).map(|v| 1u32 << v).sum();
            for mask in 0u32..(1u32 << n) {
                if mask & !cmask != 0 || !is_two_club(mask) {
                    continue;
                }
                for (born, members, cn_live) in &frozen {
                    let m_in = members.iter().filter(|&&v| mask & (1 << v) != 0).count() as i64;
                    let r_in = cn_live.iter().filter(|&&v| mask & (1 << v) != 0).count() as i64;
                    assert!(
                        m_in - r_in <= 1,
                        "row born phase {born} VIOLATED at phase {phase}: \
                         members={members:?} cn={cn_live:?} club={mask:#b}"
                    );
                }
            }
        }
        // UNWIND TRAP: the phase-2 row is invalid for 2-clubs of the ROOT C —
        // {4,5,7} is a 2-club (witness 7 inside S) with two members and no
        // live hub. Caching this family across unwinds would be unsound.
        let (members, cn_live) = lift2_row.expect("phase-2 lift row exists");
        let bad: u32 = (1 << 4) | (1 << 5) | (1 << 7);
        assert!(
            is_two_club(bad),
            "{{4,5,7}} must be a 2-club of the root graph"
        );
        let m_in = members.iter().filter(|&&v| bad & (1 << v) != 0).count() as i64;
        let r_in = cn_live.iter().filter(|&&v| bad & (1 << v) != 0).count() as i64;
        assert!(
            m_in - r_in > 1,
            "descendant row must be invalid at the root, else the unwind trap is untested"
        );
    }
}

#[cfg(test)]
mod file_probe {
    use super::*;

    #[test]
    fn two_club_path_fixture_is_recognized_and_solved_exactly() {
        // The largest induced diameter-two subset of a six-vertex path has
        // exactly three vertices. This exercises recognition, exact search,
        // witness streaming, and final re-verification without external files.
        let edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)];
        let (inst, obj) = tests::encode(6, &edges);
        let seed = vec![true, false, false, false, false, false];
        assert!(verify_all_constraints(&inst.constraints, &seed));
        let mut streamed = Vec::new();
        let mut on_improve = |value: i128, assignment: &[bool]| {
            assert!(verify_all_constraints(&inst.constraints, assignment));
            assert_eq!(eval_objective(&obj, assignment), value);
            streamed.push(value);
        };
        let runtime = TwoClubRuntime::explicit(MAX_NODES, false, false, false);
        let solution = try_two_club_exact_with_runtime(
            &inst,
            &obj,
            Some(&seed),
            runtime,
            TwoClubLpSelection::Standard,
            &|| false,
            &mut on_improve,
        )
        .expect("2-club");

        assert_eq!(solution.status, PbStatus::OptimumFound);
        assert_eq!(solution.objective, Some(-3));
        assert_eq!(
            solution
                .assignment
                .iter()
                .filter(|&&selected| selected)
                .count(),
            3
        );
        assert!(verify_all_constraints(
            &inst.constraints,
            &solution.assignment
        ));
        assert!(!streamed.is_empty(), "the anytime path must emit a witness");
        assert!(streamed.iter().all(|&value| value >= -3));
    }
}
