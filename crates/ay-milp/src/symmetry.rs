// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formulation-symmetry detection (normalized matrix view) and node-local
//! orbital fixing.
//!
//! # What is detected
//!
//! Involutions `g` of the model's columns (each an exact permutation of order
//! two: disjoint column swaps `u <-> g(u)`) together with an induced row
//! permutation, such that applying both maps the model's NORMALIZED VIEW
//! (below) exactly to itself: swapped columns have bit-identical
//! objective/bounds/kind, paired rows have exactly-equal effective bounds, and
//! every row's (non-excluded) coefficient list maps onto its partner's.
//! Detection is a deterministic, work-budgeted pipeline that FAILS CLOSED at
//! every stage (a model with no verified generator solves bit-identically to a
//! build without this module):
//!
//! 1. COLOR REFINEMENT (1-WL on the column/row bipartite graph, coefficient
//!    bits as edge labels): columns start colored by (kind, bound bits,
//!    objective bits), rows by (effective-bound hashes); each round rehashes a
//!    vertex with the sorted multiset of its (neighbor color, coefficient)
//!    pairs. Orbits of the true automorphism group always refine the stable
//!    color classes, so a column whose class is a singleton provably has no
//!    symmetric partner. Hash collisions can only MERGE classes, i.e. propose
//!    false candidates, which stage 3 rejects.
//! 2. INVOLUTION CONSTRUCTION: for a seed pair `(a, b)` in one class, force
//!    `a <-> b` and propagate: paired columns force their rows to pair (same
//!    coefficient bits, same row color), paired rows force their columns to
//!    pair. Ambiguous choices take the canonical smallest candidate (with a
//!    self-map preference); a wrong greedy pick just fails verification.
//! 3. EXACT VERIFICATION: the candidate is checked coefficient-by-coefficient
//!    against the view (bit equality on coefficients, exact rational equality
//!    on effective bounds). Only verified automorphisms survive.
//!
//! # The normalized view, and why it is licensed
//!
//! Bit-identical matrix equality misses symmetries that are broken only by
//! REPRESENTATION artifacts (measured on noswot: the S4 over its four
//! interchangeable units — SCIP's 24x4 orbitope — is invisible raw, because
//! one block writes its capacity rows as equalities with slack columns and
//! another shares a dominated column across its rows). Two sound
//! normalizations are applied before anything is compared (all arithmetic
//! exact rational; both deterministic):
//!
//! * PINNED-ZERO COLUMNS (box exactly `[0, 0]`) are dropped from every row's
//!   coefficient list. Their term contributes exactly `a * 0 = 0` to every
//!   activity at every point of every node box (boxes only shrink, so a pin
//!   never re-opens), so two rows differing only in pinned-zero entries
//!   constrain the same points identically. The pinned columns themselves are
//!   fixed by every generator (they never enter a class).
//!   `dual_pin_dominated` (below) manufactures these pins soundly where a
//!   dominated column masks a symmetry — noswot's x128.
//!
//! * SLACK COLUMNS — continuous, zero objective, at most one row entry — are
//!   dropped from their host row, and the row's bounds are ABSORBED: with
//!   entry `a` and slack box `[l, u]`, the effective bounds become
//!   `lb' = lb - max(a*l, a*u)`, `ub' = ub - min(a*l, a*u)` (`+-inf` where the
//!   box is open). This is exact Fourier–Motzkin elimination of the slack: a
//!   point of the remaining columns satisfies `[lb', ub']` iff SOME value of
//!   the slack inside its box completes it to satisfy `[lb, ub]` — exact for
//!   one slack by direct inversion, and for several in one row because a sum
//!   of intervals is an interval (all slacks are continuous). noswot's
//!   x126/x127 equality-row slacks normalize `-8.928*y + w + s = 0`,
//!   `s in [0, U]` into the same `-8.928*y + w <= 0` shape as its sibling
//!   units' plain `<=` rows.
//!
//! * VACUITY FILTER: an effective bound that PROVABLY excludes no point of
//!   the box (exact activity-range comparison, applied uniformly to every
//!   row) is replaced by its infinity. A bound that constrains nothing is not
//!   part of the structure, and absorbed rows routinely carry such a side
//!   (the slack's own derived box came from the very row being absorbed).
//!
//! A verified view-automorphism `g` lifts to an OBJECTIVE- AND
//! FEASIBILITY-PRESERVING self-map `phi` of the real model's points: permute
//! the non-excluded coordinates by `g`; keep every excluded coordinate of an
//! UNMOVED row (and every no-entry column) unchanged; recompute each MOVED
//! row's slack coordinates from the row. The recomputation is possible
//! exactly because the permuted point satisfies the view row — that IS the
//! solvability condition the absorption encodes — and the recomputed values
//! land inside the slacks' tightened boxes because the completed point is
//! model-feasible and tightened bounds are implied (they cut no feasible
//! point). `phi` preserves the objective bit-for-bit: moved columns have
//! bit-equal objective coefficients and every excluded column has objective
//! zero or a point box (a constant either way). Node-locally the lift needs
//! one guard the plain involution did not: a MOVED row's slack must still
//! have its ROOT box at the node (`SymGen::guards`) — a node that tightened
//! it may have cut the recomputed value. Pinned-zero columns need no guard
//! (a `[0, 0]` box cannot shrink).
//!
//! # What is exploited: node-local orbital fixing (down-branch)
//!
//! At a branch `x_j <= f | x_j >= f+1`, for every verified generator `g`
//! whose support has PAIRWISE EQUAL boxes at this node (each swapped pair
//! `(u, g(u))` has `lo_u == lo_{g(u)}` and `up_u == up_{g(u)}` in the node's
//! current box) and whose slack guards hold, the orbit of `j` under the group
//! generated by the applicable generators may be fixed `<= f` alongside `j`
//! in the DOWN child. See `Symmetry::down_orbit` and the soundness journal at
//! the branch site in `bab.rs` for the full license (it quantifies over the
//! lifted map `phi` constructed above).

use crate::model::{exact_small, ColKind, Model};
use ay_lra::rational::Rational;

/// An exact bound; `None` is the infinity of whichever side it sits on.
type Bnd = Option<Rational>;

/// A verified involution: the moved columns, as disjoint swaps `u <-> v`
/// (`u < v`, no column appears twice), plus a flat lookup table.
pub(crate) struct SymGen {
    /// Disjoint swapped pairs, sorted by first element; every moved column
    /// appears in exactly one pair.
    pub(crate) pairs: Vec<(u32, u32)>,
    /// `(col, image)` for BOTH directions, sorted by `col` — the O(log)
    /// image lookup the per-branch orbit walk uses.
    moves: Vec<(u32, u32)>,
    /// Slack columns hosted in rows this generator MOVES, with their root box
    /// bits `(col, lo_bits, up_bits)`. Applicability requires each to still
    /// have exactly that box: the lifted map recomputes these coordinates,
    /// and the recomputed value is only licensed into the ROOT box (module
    /// journal). Empty for generators whose moved rows have no slacks — the
    /// common case, where this check is free.
    guards: Vec<(u32, u64, u64)>,
}

impl SymGen {
    fn new(mut pairs: Vec<(u32, u32)>, guards: Vec<(u32, u64, u64)>) -> Self {
        pairs.sort_unstable();
        let mut moves = Vec::with_capacity(pairs.len() * 2);
        for &(u, v) in &pairs {
            moves.push((u, v));
            moves.push((v, u));
        }
        moves.sort_unstable();
        Self {
            pairs,
            moves,
            guards,
        }
    }

    /// The image of `col` under this involution (identity off the support).
    fn image(&self, col: u32) -> u32 {
        match self.moves.binary_search_by_key(&col, |&(c, _)| c) {
            Ok(i) => self.moves[i].1,
            Err(_) => col,
        }
    }

    /// Is this generator usable at a node with the given box? True exactly
    /// when every swapped pair has a bit-equal box (which licenses mapping
    /// the node's box onto itself) AND every slack guard still has its root
    /// box (which licenses recomputing the slack coordinates).
    fn applicable(&self, lower: &[f64], upper: &[f64]) -> bool {
        self.pairs.iter().all(|&(u, v)| {
            let (u, v) = (u as usize, v as usize);
            lower[u] == lower[v] && upper[u] == upper[v]
        }) && self.guards.iter().all(|&(c, lo, up)| {
            let c = c as usize;
            lower[c].to_bits() == lo && upper[c].to_bits() == up
        })
    }
}

/// A FULL ORBITOPE component: `k >= 2` interchangeable blocks of `m >= 2`
/// columns each, position-aligned, under the FULL symmetric group `S_k`
/// (verified: a star of transpositions through block 1, which generates it).
///
/// # The static constraint `C`, and its license
///
/// At the root, this component imposes `vec(B_1) >=_lex vec(B_2) >=_lex ...
/// >=_lex vec(B_k)` (lex over the fixed position order). SOUND: for any
/// feasible point, the `S_k` action (by the lifted maps of the star's
/// closure — position-consistent block permutations, see the module journal)
/// permutes the block vectors arbitrarily, so SORTING them lex-nonincreasing
/// yields a feasible point of the SAME objective value satisfying `C`. Every
/// orbit therefore keeps a representative: the optimum value, feasibility,
/// and every rigorous dual bound are preserved. The lift is a ROOT-level
/// argument (slack guards are trivially satisfied on the root box), so `C`
/// needs NO node-local guard — this is what makes it survive arbitrary
/// branching where box-equality orbital fixing dies (measured on noswot:
/// 9 orbital fixes in 508k nodes; the group was retired by depth ~10 in
/// every subtree).
///
/// What is NOT preserved is literal box exhaustiveness (points violating `C`
/// are cut), so the first derived reduction poisons the whole-tree capture,
/// exactly like the orbital lane.
///
/// COMPOSITION with the other lanes: model propagation removes only
/// infeasible points; incumbent-licensed fixing (reduced-cost, and its
/// orbital pin transfer) removes only points no better than the incumbent —
/// both preserve "some optimal point satisfying `C` survives (or the
/// incumbent already witnesses the value)". Down-branch orbital fixing does
/// NOT compose (its surviving image may violate `C`), so generators touching
/// a component are excluded from the per-branch orbit walk (`col_gens` is
/// built from the leftovers only).
pub(crate) struct Orbitope {
    /// `blocks[i][p]` = the model column of block `i` at position `p`.
    /// Blocks are ordered by their smallest column; positions put integral
    /// columns first (branching fixes them, which is what arms the lex
    /// propagation), then continuous, each by column index of block 1.
    pub(crate) blocks: Vec<Vec<u32>>,
}

/// Verified symmetry generators plus the per-branch scratch state.
pub(crate) struct Symmetry {
    pub(crate) gens: Vec<SymGen>,
    /// Assembled full-orbitope components (disjoint supports).
    pub(crate) orbitopes: Vec<Orbitope>,
    /// Per column: indices into `gens` of the generators that move it AND
    /// are licensed for the per-branch orbit walk (component-touching
    /// generators are excluded — see `Orbitope`).
    col_gens: Vec<Vec<u32>>,
    /// Scratch (stamped, so no per-branch clearing): generator applicability
    /// memo and orbit membership, both valid for the current `stamp` only.
    stamp: u32,
    gen_stamp: Vec<u32>,
    gen_ok: Vec<bool>,
    orbit_stamp: Vec<u32>,
    /// Per column: lex rank inside its orbitope (position-major, block
    /// minor), `u64::MAX` off the orbitopes — the branch-alignment key (see
    /// `orbitope_rank`).
    ranks: Vec<u64>,
    /// Per column: `(orbitope id, position index)` of the cell, or
    /// `(u32::MAX, u32::MAX)` off the orbitopes — the dynamic lane's lookup
    /// that turns a branching on an orbitope cell into a position-sequence
    /// extension (`cell`, bab.rs `SymSeq`).
    cells: Vec<(u32, u32)>,
    /// DYNAMIC ORBITOPAL LANE toggle (set by the solver from
    /// `AY_MILP_ORBITOPE_DYN`): when true, nodes propagate the lex order
    /// relative to the BRANCHING ORDER TAKEN (`propagate_orbitopes_dyn`)
    /// instead of the static root order. The two orders are NOT composable
    /// (journal at `propagate_orbitopes_dyn`), so a solve uses exactly one.
    pub(crate) dyn_lane: bool,
    /// Stats (trace only).
    pub(crate) fixes_made: usize,
    pub(crate) branches_hit: usize,
    pub(crate) orbitope_reductions: usize,
    pub(crate) orbitope_cutoffs: usize,
    /// Dynamic-lane stats (trace only): nodes propagated with a nonempty
    /// sequence, total/max sequence length over those nodes, and adjacent
    /// pairs found ENTAILED at their first sequence position (lex strict
    /// there — the constraint is spent for that pair at that node).
    pub(crate) dyn_nodes: usize,
    pub(crate) dyn_seq_sum: usize,
    pub(crate) dyn_seq_max: usize,
    pub(crate) dyn_pairs_spent: usize,
    pub(crate) dyn_pairs: usize,
}

/// Per-branch budget: at most this many fresh `applicable` evaluations
/// (memoized hits are free). Keeps a branch on a wide symmetric model from
/// paying more for orbit work than for its LP.
const MAX_GEN_CHECKS: usize = 96;
/// At most this many orbit members fixed per branch.
const MAX_ORBIT: usize = 256;

impl Symmetry {
    /// Debug probe (`AY_MILP_SYM_DEBUG`): why is each generator that moves
    /// `j` inapplicable at this box? Prints the first failing pair/guard.
    pub(crate) fn debug_applicability(&self, j: usize, lower: &[f64], upper: &[f64]) {
        for &gid in &self.col_gens[j] {
            let g = &self.gens[gid as usize];
            let bad_pair = g.pairs.iter().find(|&&(u, v)| {
                let (u, v) = (u as usize, v as usize);
                lower[u] != lower[v] || upper[u] != upper[v]
            });
            let bad_guard = g.guards.iter().find(|&&(c, lo, up)| {
                let c = c as usize;
                lower[c].to_bits() != lo || upper[c].to_bits() != up
            });
            match (bad_pair, bad_guard) {
                (None, None) => eprintln!("SYM_DEBUG j={j} gen {gid}: applicable"),
                (Some(&(u, v)), _) => eprintln!(
                    "SYM_DEBUG j={j} gen {gid}: pair ({u},{v}) boxes [{},{}] vs [{},{}]",
                    lower[u as usize], upper[u as usize], lower[v as usize], upper[v as usize]
                ),
                (None, Some(&(c, lo, up))) => eprintln!(
                    "SYM_DEBUG j={j} gen {gid}: guard col {c} box [{},{}] vs root [{},{}]",
                    lower[c as usize],
                    upper[c as usize],
                    f64::from_bits(lo),
                    f64::from_bits(up)
                ),
            }
        }
    }

    /// The orbit of branching column `j` under the generators applicable at a
    /// node with box (`lower`, `upper`), excluding `j` itself, appended to
    /// `out`. Every returned column has a box bit-equal to `j`'s (each
    /// generator on the BFS path swaps box-equal pairs, and equality chains).
    pub(crate) fn down_orbit(
        &mut self,
        j: usize,
        lower: &[f64],
        upper: &[f64],
        out: &mut Vec<usize>,
    ) {
        out.clear();
        if self.col_gens.get(j).is_none_or(Vec::is_empty) {
            return;
        }
        // Stamp wrap: reset the memo vectors on overflow (u32 branches later).
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            self.gen_stamp.iter_mut().for_each(|s| *s = u32::MAX);
            self.orbit_stamp.iter_mut().for_each(|s| *s = u32::MAX);
            self.stamp = 1;
        }
        let stamp = self.stamp;
        self.orbit_stamp[j] = stamp;
        let mut frontier: Vec<u32> = vec![j as u32];
        let mut checks = 0usize;
        while let Some(u) = frontier.pop() {
            for gi in 0..self.col_gens[u as usize].len() {
                let gid = self.col_gens[u as usize][gi] as usize;
                let ok = if self.gen_stamp[gid] == stamp {
                    self.gen_ok[gid]
                } else {
                    if checks >= MAX_GEN_CHECKS {
                        // Budget spent: keep the orbit found so far. Fixing a
                        // SUBSET of the orbit is individually licensed per
                        // member, so stopping early is always sound.
                        return;
                    }
                    checks += 1;
                    let ok = self.gens[gid].applicable(lower, upper);
                    self.gen_stamp[gid] = stamp;
                    self.gen_ok[gid] = ok;
                    ok
                };
                if !ok {
                    continue;
                }
                let v = self.gens[gid].image(u);
                if self.orbit_stamp[v as usize] != stamp {
                    self.orbit_stamp[v as usize] = stamp;
                    out.push(v as usize);
                    if out.len() >= MAX_ORBIT {
                        return;
                    }
                    frontier.push(v);
                }
            }
        }
    }
}

impl Symmetry {
    /// ORBITOPE-ALIGNED BRANCHING KEY: the lex rank of `j` inside its
    /// orbitope (position-major, block-minor), `u64::MAX` off the orbitopes.
    /// The static lex constraint `C` only propagates through positions the
    /// box has pinned, in position order — so a search that fixes positions
    /// in that order arms `C` maximally, while one that wanders fixes
    /// positions `C` cannot yet reason about (measured on noswot: 180k
    /// reductions but only 238 cutoffs in 1.2M nodes with pseudocost-order
    /// branching). Branching order is license-free: preferring the smallest
    /// rank changes WHICH sound tree is searched, never what a node claims.
    pub(crate) fn orbitope_rank(&self, j: usize) -> u64 {
        self.ranks.get(j).copied().unwrap_or(u64::MAX)
    }

    /// The `(orbitope id, position index)` of column `j`, when `j` is an
    /// orbitope cell — the dynamic lane's branch hook.
    pub(crate) fn cell(&self, j: usize) -> Option<(u32, u32)> {
        match self.cells.get(j) {
            Some(&(o, p)) if o != u32::MAX => Some((o, p)),
            _ => None,
        }
    }

    /// NODE-LOCAL ORBITOPAL PROPAGATION: tighten (`lo`, `up`) by everything
    /// the static constraint `C` (see `Orbitope`) implies on this box, or
    /// report that NO point of the box satisfies `C` (`Err`) — the node is
    /// then prunable (its whole region is covered, up to symmetry, by the
    /// lex-greater part of the tree).
    ///
    /// Per adjacent block pair `(i, i+1)` (adjacent sortedness IS the whole
    /// of `C`), this is the complete bounds-consistent propagator for
    /// `X >=_lex Y` over boxes (Frisch et al.'s lex propagator, in its
    /// interval form):
    ///
    /// * walk positions from the front while FORCED EQUAL (both boxes the
    ///   same single point) — for such prefixes lex defers to the frontier;
    /// * at the frontier `p`, `C` implies `x_p >= y_p`: tighten
    ///   `lo(x_p) >= lo(y_p)` and `up(y_p) <= up(x_p)`; impossible
    ///   (`up(x_p) < lo(y_p)`) means NO box point satisfies `C` — cutoff;
    /// * if now `lo(x_p) > up(y_p)`, every box point is STRICT at `p` and
    ///   the pair constraint is entailed regardless of the tail — stop;
    /// * STRICT-TAIL RULE: otherwise, if equality at `p` cannot be extended
    ///   (`tail_can_geq` says no box point has `X[p+1..] >=_lex Y[p+1..]`),
    ///   then `x_p > y_p` in every `C`-point; on integral columns that is
    ///   `lo(x_p) >= lo(y_p) + 1` and `up(y_p) <= up(x_p) - 1` (bounds of
    ///   integral columns are integers here — branching and propagation
    ///   keep them so).
    ///
    /// Iterated to fixpoint across the pairs (a tightening at one pair can
    /// re-arm its neighbours). Every derived bound is a logical consequence
    /// of `C` and the incoming box alone: no group action, no guards.
    ///
    /// Returns the number of bound entries tightened.
    pub(crate) fn propagate_orbitopes(
        &mut self,
        lo: &mut [f64],
        up: &mut [f64],
        integral: &[bool],
    ) -> Result<usize, ()> {
        let mut changed = 0usize;
        for ot in &self.orbitopes {
            match lex_chain(&ot.blocks, None, lo, up, integral) {
                Ok(n) => changed += n,
                Err(()) => {
                    self.orbitope_cutoffs += 1;
                    return Err(());
                }
            }
        }
        self.orbitope_reductions += changed;
        Ok(changed)
    }

    /// DYNAMIC ORBITOPAL FIXING (Bendotti–Fouilhoux–Pesneau's dynamic full
    /// orbitope, in the interval form; consistency conditions after
    /// van Doornmalen–Hojny): propagate, per orbitope, the lex order between
    /// adjacent blocks RESTRICTED TO the position sequence `seqs[oid]` — the
    /// positions branched on along the path to this node, EARLIEST BRANCH
    /// MOST SIGNIFICANT — instead of the static root order. `Err` when no
    /// box point is sorted under that node-local order (the node is covered,
    /// up to symmetry, elsewhere in the tree).
    ///
    /// # The dynamic constraint, and its license
    ///
    /// Node `N` carries a sequence `σ_N` of positions (bab.rs `SymSeq`):
    /// `σ_root = []`, and when a node branches on an orbitope cell at a
    /// position not yet in its sequence, BOTH children get `σ ++ [p]`
    /// (identical in both — the append is decided by the branch, not the
    /// side). `C_N` = "block vectors restricted to `σ_N`, read in that
    /// sequence, are lex-nonincreasing in the fixed block order". Extending
    /// the sequence STRENGTHENS the constraint (a lex comparison on a prefix
    /// is implied by one on its extension), so fixings derived at a node
    /// remain valid in its whole subtree — the van Doornmalen–Hojny
    /// consistency condition.
    ///
    /// SOUNDNESS (value preservation, by induction down the tree). Invariant
    /// at node `N`: EITHER the incumbent already witnesses the optimum
    /// value, OR some champion `c` — model-feasible, of optimal value, an
    /// image of an optimal point under the verified `S_k` action — lies in
    /// `region(N)` and satisfies `C_N`. Root: sort any optimal point's
    /// blocks (the star's closure acts position-consistently; the lifted map
    /// keeps it feasible at the same value — the `Orbitope` root-level
    /// argument), `σ = []` makes `C_root` trivial. Maintenance:
    ///
    /// * In-node reductions cannot lose the champion: infeasibility-licensed
    ///   propagation never cuts a feasible point; incumbent-licensed fixing
    ///   cutting it means the incumbent already equals the optimum (switch
    ///   to the first disjunct); THIS propagator only cuts points violating
    ///   `C_N`, which the champion satisfies — and while the champion is
    ///   present the `Err` cutoff cannot fire.
    /// * Branch on a non-orbitope column, or on a cell whose position is
    ///   already in `σ_N`: `σ` is unchanged, the champion is integral there
    ///   (it is feasible) and follows its value into one child.
    /// * Branch on a cell at a NEW position `p`: resort the champion STABLY
    ///   by the cell values at `p` within groups of blocks whose
    ///   `σ_N`-restrictions are EQUAL — `c'` is `σ ++ [p]`-sorted (the old
    ///   sequence is the more significant prefix, and `c` was already
    ///   `σ_N`-sorted). `c'` is a block permutation of `c`, hence a verified
    ///   group image: model-feasible, same value. `c'` still satisfies every
    ///   BRANCH bound on the path: branch bounds on orbitope cells live only
    ///   at `σ_N`-positions (a position enters `σ` when FIRST branched), and
    ///   the permuted blocks have EQUAL values at every `σ_N`-position, so
    ///   those cells are unchanged; non-orbitope coordinates are untouched
    ///   by the lifted map (slacks of moved rows are recomputed, but no
    ///   branch bound sits on a continuous column). Derived bounds then
    ///   follow by induction over their own derivation order:
    ///   infeasibility-licensed ones hold for every model-feasible point
    ///   inside the branch bounds; `C`-derived ones are consequences of an
    ///   ancestor's `C_A` (implied by `c'`'s `σ'`-sortedness) and the box so
    ///   far; incumbent-licensed ones either hold for `c'` or the incumbent
    ///   already equals the optimum. So `c'` is in `region(N)` and lands in
    ///   the child matching its value at the branching cell.
    ///
    /// Every leaf keeps the invariant, so the optimum value survives the
    /// handled tree — which is exactly what `Outcome::Optimal` claims. What
    /// is NOT preserved is literal box exhaustiveness (the caller poisons
    /// the whole-tree capture on every firing, as with the static lane).
    ///
    /// NOT COMPOSABLE with the static order: a point sorted under one order
    /// need not be sortable under both at once (two positions, two blocks,
    /// values (0,1)/(1,0) — either order alone is satisfiable, both never).
    /// A solve uses exactly one lane (`dyn_lane`).
    pub(crate) fn propagate_orbitopes_dyn(
        &mut self,
        seqs: &[Vec<u32>],
        lo: &mut [f64],
        up: &mut [f64],
        integral: &[bool],
    ) -> Result<usize, ()> {
        let mut changed = 0usize;
        for (ot, seq) in self.orbitopes.iter().zip(seqs) {
            if seq.is_empty() {
                continue; // trivial constraint: nothing branched yet
            }
            self.dyn_nodes += 1;
            self.dyn_seq_sum += seq.len();
            self.dyn_seq_max = self.dyn_seq_max.max(seq.len());
            for i in 0..ot.blocks.len() - 1 {
                self.dyn_pairs += 1;
                let p = seq[0] as usize;
                let (u, v) = (ot.blocks[i][p] as usize, ot.blocks[i + 1][p] as usize);
                if lo[u] > up[v] {
                    self.dyn_pairs_spent += 1;
                }
            }
            match lex_chain(&ot.blocks, Some(seq), lo, up, integral) {
                Ok(n) => changed += n,
                Err(()) => {
                    self.orbitope_cutoffs += 1;
                    return Err(());
                }
            }
        }
        self.orbitope_reductions += changed;
        Ok(changed)
    }

    /// STATIC LEX-LEADER FIRST-DIFFERENCE ROWS (the `rows` exploitation mode):
    /// for each verified generator `g`, one row `x_c - x_{g(c)} >= 0`, where
    /// `c` is the smallest-index column `g` moves.
    ///
    /// SOUNDNESS: order solution vectors lexicographically by column index
    /// over the NON-EXCLUDED columns (excluded coordinates do not participate
    /// — under the lifted maps they are pinned, kept, or recomputed, and
    /// carry zero objective). Every orbit (under the FULL group the verified
    /// generators generate, acting by the lifted maps) contains a lex-max
    /// element `x*`; for any group element `phi`, `x* >=_lex phi(x*)` on that
    /// subvector, and comparing at `c = min support(phi)` — the first
    /// coordinate where they can differ — gives `x*_c >= x*_{phi(c)}`.
    /// In particular every generator's row holds at `x*`. So the augmented
    /// model retains at least one member of every orbit: feasibility and the
    /// optimum VALUE are preserved (the witness produced is genuinely feasible
    /// for the original model — the rows only restrict). This is the classic
    /// fundamental-domain relaxation (Liberti's narrowing; the first row of a
    /// lex-leader/orbitope encoding), robust at every depth — unlike per-node
    /// orbital fixing, whose wide-support applicability check dies as soon as
    /// any moved column is fixed asymmetrically. The two mechanisms are NOT
    /// composable (an orbital image may violate these rows), so a solve uses
    /// exactly one of them.
    pub(crate) fn breaking_rows(&self) -> Vec<(u32, u32)> {
        // (c, g(c)) per generator; pairs are sorted so pairs[0].0 is min supp.
        self.gens.iter().map(|g| g.pairs[0]).collect()
    }

    /// ORBITAL PIN PROPAGATION: transfer a round of incumbent-licensed pins
    /// (reduced-cost fixing) across orbits.
    ///
    /// Contract: (`lo`, `up`) differs from (`pre_lo`, `pre_up`) ONLY by pins
    /// whose license is "every feasible point of this box strictly better
    /// than the incumbent takes exactly this value" — reduced-cost fixing's
    /// license. For any generator `g` applicable on the PRE-ROUND box, a pin
    /// on `u` transfers to `g(u)`: a better-than-incumbent point `s` with
    /// `s_{g(u)}` outside the pin maps to `phi(s)` — feasible, same
    /// objective, inside the pre-round box (pairwise-equal boxes; guarded
    /// slacks recompute into their root boxes), violating `u`'s pin.
    /// So no such point exists and pinning `g(u)` removes only
    /// not-better-than-incumbent points: the SAME license as the fixing
    /// itself. Chained transfers (via several applicable generators) compose,
    /// because every generator is applicable on the SAME pre-round box. If a
    /// pair's transferred pins cross (`lo > up`), both pins were licensed, so
    /// NO better-than-incumbent point exists there at all — the empty box is
    /// the truthful outcome and the tree's stale-box discard handles it.
    ///
    /// Beyond strengthening the fixing, this is what KEEPS the boxes of a
    /// symmetric pair equal, so branch-time orbital fixing stays armed
    /// (measured on noswot: without it, the root fixing's asymmetric pins
    /// retire the generator after ONE branch).
    ///
    /// Returns the number of bound entries tightened.
    pub(crate) fn propagate_pins(
        &self,
        pre_lo: &[f64],
        pre_up: &[f64],
        lo: &mut [f64],
        up: &mut [f64],
    ) -> usize {
        let app: Vec<usize> = (0..self.gens.len())
            .filter(|&g| self.gens[g].applicable(pre_lo, pre_up))
            .collect();
        if app.is_empty() {
            return 0;
        }
        let mut changed = 0usize;
        for _round in 0..8 {
            let mut any = false;
            for &g in &app {
                for &(u, v) in &self.gens[g].pairs {
                    let (u, v) = (u as usize, v as usize);
                    if lo[u] > lo[v] {
                        lo[v] = lo[u];
                        any = true;
                        changed += 1;
                    } else if lo[v] > lo[u] {
                        lo[u] = lo[v];
                        any = true;
                        changed += 1;
                    }
                    if up[u] < up[v] {
                        up[v] = up[u];
                        any = true;
                        changed += 1;
                    } else if up[v] < up[u] {
                        up[u] = up[v];
                        any = true;
                        changed += 1;
                    }
                }
            }
            if !any {
                break;
            }
        }
        changed
    }
}

/// The adjacent-pair interval lex propagator over a POSITION SEQUENCE:
/// `seq = None` is the static full order `0..m` (the historical
/// `propagate_orbitopes` body, verbatim iteration); `Some(s)` reads
/// positions through `s` — the dynamic lane's branching order. Frisch et
/// al.'s bounds-consistent lex propagator per adjacent block pair, iterated
/// to fixpoint across the pairs (a tightening at one pair can re-arm its
/// neighbours; bounds move monotonically onto one another so this
/// terminates, the round cap is belt-and-braces). Every derived bound is a
/// logical consequence of the (static or dynamic) lex constraint and the
/// incoming box alone: no group action, no guards. `Err` when NO box point
/// satisfies the constraint.
fn lex_chain(
    blocks: &[Vec<u32>],
    seq: Option<&[u32]>,
    lo: &mut [f64],
    up: &mut [f64],
    integral: &[bool],
) -> Result<usize, ()> {
    let k = blocks.len();
    let len = seq.map_or(blocks[0].len(), <[u32]>::len);
    let mut changed = 0usize;
    for _round in 0..16 {
        let mut any = false;
        for i in 0..k - 1 {
            let (a, b) = (&blocks[i], &blocks[i + 1]);
            for t in 0..len {
                let p = seq.map_or(t, |s| s[t] as usize);
                let (u, v) = (a[p] as usize, b[p] as usize);
                // C (with the prefix forced equal) implies x_u >= x_v.
                if up[u] < lo[v] {
                    return Err(());
                }
                if lo[v] > lo[u] {
                    lo[u] = lo[v];
                    changed += 1;
                    any = true;
                }
                if up[u] < up[v] {
                    up[v] = up[u];
                    changed += 1;
                    any = true;
                }
                if lo[u] > up[v] {
                    break; // strict at p for every box point: entailed
                }
                if lo[u] == up[u] && lo[v] == up[v] && lo[u] == lo[v] {
                    continue; // forced equal: the frontier moves on
                }
                // Frontier with possible equality: the strict-tail rule.
                if integral[u] && !tail_can_geq(a, b, seq, t + 1, lo, up) {
                    // Equality at p cannot be completed: x_u > x_v.
                    if up[u] < lo[v] + 1.0 {
                        return Err(());
                    }
                    if lo[v] + 1.0 > lo[u] {
                        lo[u] = lo[v] + 1.0;
                        changed += 1;
                        any = true;
                    }
                    if up[u] - 1.0 < up[v] {
                        up[v] = up[u] - 1.0;
                        changed += 1;
                        any = true;
                    }
                }
                break;
            }
        }
        if !any {
            break;
        }
    }
    Ok(changed)
}

/// Can some box point have `X[from..] >=_lex Y[from..]` over the sequence
/// tail (X from blocks `a`, Y from blocks `b`; `from` indexes the SEQUENCE,
/// identity when `seq` is `None`)? Exact interval reasoning: walk positions
/// choosing equality while forced; at each position strictly-greater is
/// possible iff `up(x) > lo(y)` (choose it — every earlier position was
/// chosen equal); `up(x) < lo(y)` is forced-less with no escape left — no;
/// `up(x) == lo(y)` admits exactly the touching value as equality (it lies
/// in both boxes) — walk on. Equal to the end is a yes.
fn tail_can_geq(
    a: &[u32],
    b: &[u32],
    seq: Option<&[u32]>,
    from: usize,
    lo: &[f64],
    up: &[f64],
) -> bool {
    let len = seq.map_or(a.len(), <[u32]>::len);
    for t in from..len {
        let p = seq.map_or(t, |s| s[t] as usize);
        let (u, v) = (a[p] as usize, b[p] as usize);
        if up[u] > lo[v] {
            return true;
        }
        if up[u] < lo[v] {
            return false;
        }
    }
    true
}

/// SplitMix64-style deterministic mixer — fixed constants, no per-process
/// randomness, so detection is identical across runs and machines.
fn mix(h: u64, v: u64) -> u64 {
    let mut x = h ^ v.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^= x >> 31;
    x
}

/// A hash of an effective bound. Approximate (f64 image of the exact
/// rational): collisions only merge WL classes / index buckets, and stage 3
/// compares the exact rationals, so this cannot admit a wrong generator.
fn bnd_hash(tag: u64, b: &Bnd) -> u64 {
    use num_traits::ToPrimitive;
    match b {
        None => mix(tag, 0x1CF5_11B0_11D5),
        Some(q) => mix(tag, q.to_big().to_f64().map_or(1, f64::to_bits)),
    }
}

/// Size caps: above these the detector declines outright (self-gating; the
/// solve is bit-identical to no-detection).
const MAX_COLS: usize = 200_000;
const MAX_ROWS: usize = 200_000;
const MAX_NNZ: usize = 4_000_000;
/// Refinement rounds (or until the class counts stabilize).
const REFINE_ITERS: usize = 12;
/// Seed pairs attempted across all classes.
const MAX_SEED_ATTEMPTS: usize = 512;
/// Seed pairs attempted within ONE class: ALL pairs up to this many, so the
/// full transposition set of a block symmetry is harvested — a star of
/// transpositions through one element (the old first-member seeding) dies
/// wholesale once that element is branched asymmetrically, while the full
/// set keeps the residual subgroup alive under the stabilizer bookkeeping
/// (noswot: branching a unit-1 column must leave the S3 on units 2..4).
const MAX_CLASS_PAIRS: usize = 64;
/// Verified generators kept.
const MAX_GENS: usize = 1024;

const NONE_U32: u32 = u32::MAX;

/// DUAL PIN for dominated columns: a CONTINUOUS column with objective exactly
/// zero whose every row entry is unconstraining in one direction is pinned to
/// the bound on that side (when finite).
///
/// LICENSE (pin to the LOWER bound; the mirror is symmetric): every entry
/// `(r, a)` has `a > 0` with row `lb = -inf`, or `a < 0` with row
/// `ub = +inf`, so DECREASING the column never violates any row. Take any
/// feasible point `s`: lowering the coordinate to `l` keeps every row
/// satisfied and every bound (it moves within the box), and the objective is
/// unchanged (coefficient zero). So the pinned model keeps a point of every
/// objective value the full model attains: the optimum VALUE is preserved
/// exactly, feasibility is preserved (and infeasibility trivially — pinning
/// only restricts), every witness of the pinned model is a witness for the
/// caller's, and a rigorous dual bound for the pinned model is rigorous for
/// the caller's (a better caller point would lower to a better pinned point).
/// What is NOT preserved is literal box exhaustiveness — the pin removes
/// feasible (dominated) points — so the caller POISONS the whole-tree
/// infeasibility capture when any pin fires, exactly like the orbital lane.
///
/// Continuous only: an integer column's lowest FEASIBLE value is `ceil(l)`,
/// and this pass does not want to own that rounding. Zero entries are
/// ignored. Columns already pinned are skipped.
///
/// This is textbook presolve (dominated column / dual fixing), run here — in
/// the symmetry lane, not in `presolve.rs` — because its payoff and its
/// capture-poisoning cost are both symmetry-shaped: noswot's x128 (entries
/// +2/+3/+4 in three `<=` rows, objective 0) is what hides the S4 unit
/// symmetry from bit-exact comparison. Returns the number of pins applied.
pub(crate) fn dual_pin_dominated(model: &mut Model) -> usize {
    let n = model.num_cols();
    let m = model.num_rows();
    if n == 0 || n > MAX_COLS || m > MAX_ROWS {
        return 0;
    }
    // FAIL-CLOSED for inexact models: domination pins columns by reading the row
    // `f64`s. Sign reasoning survives rounding, but a pinned column narrows the
    // model the search authoritatively uses, and this is a pure optimization —
    // decline it rather than reason on rounded proxies.
    if model.has_inexact_coeffs() {
        return 0;
    }
    let mut down_ok = vec![true; n];
    let mut up_ok = vec![true; n];
    for r in 0..m {
        let (coeffs, lb, ub) = model.row(model.row_at(r).expect("in range"));
        let lb_open = lb == f64::NEG_INFINITY;
        let ub_open = ub == f64::INFINITY;
        for &(c, a) in coeffs {
            let j = c as usize;
            if a > 0.0 {
                // Decreasing x_j decreases the activity: needs lb open.
                down_ok[j] &= lb_open;
                up_ok[j] &= ub_open;
            } else if a < 0.0 {
                down_ok[j] &= ub_open;
                up_ok[j] &= lb_open;
            }
        }
    }
    let mut pinned = 0usize;
    for j in 0..n {
        let col = model.col_at(j).expect("in range");
        if model.col_kind(col) != ColKind::Continuous || model.obj_coeff(col) != 0.0 {
            continue;
        }
        let (lo, up) = model.col_bounds(col);
        if lo == up {
            continue;
        }
        if down_ok[j] && lo.is_finite() {
            model.set_col_bounds(col, lo, lo);
            pinned += 1;
        } else if up_ok[j] && up.is_finite() {
            model.set_col_bounds(col, up, up);
            pinned += 1;
        }
    }
    pinned
}

/// The normalized matrix view detection and verification run on. See the
/// module journal for the license of each normalization.
struct View {
    /// Per column: `(row, coeff bits)` over non-excluded entries.
    col_rows: Vec<Vec<(u32, u64)>>,
    /// Per row: `(col, coeff)` with excluded columns dropped, model order.
    row_cols: Vec<Vec<(u32, f64)>>,
    /// Effective row bounds: slack-absorbed, then vacuity-filtered.
    bounds: Vec<(Bnd, Bnd)>,
    /// Columns outside the view: pinned-to-zero, or continuous zero-objective
    /// with at most one row entry (slacks and free columns).
    excluded: Vec<bool>,
    /// Per row: the excluded columns with a NON-POINT box hosted there — the
    /// generator guard set (point boxes cannot shrink and need no guard).
    row_slacks: Vec<Vec<u32>>,
}

/// Build the view. `None` only when the model is out of cap.
fn build_view(model: &Model) -> Option<View> {
    let n = model.num_cols();
    let m = model.num_rows();
    if !(2..=MAX_COLS).contains(&n) || m > MAX_ROWS {
        return None;
    }
    let mut entries = vec![0usize; n];
    let mut nnz = 0usize;
    for r in 0..m {
        let (coeffs, _, _) = model.row(model.row_at(r).expect("in range"));
        nnz += coeffs.len();
        for &(c, a) in coeffs {
            if a != 0.0 {
                entries[c as usize] += 1;
            }
        }
    }
    if nnz > MAX_NNZ {
        return None;
    }
    let mut excluded = vec![false; n];
    for j in 0..n {
        let col = model.col_at(j).expect("in range");
        let (lo, up) = model.col_bounds(col);
        let pinned_zero = lo == 0.0 && up == 0.0;
        let slackish = model.col_kind(col) == ColKind::Continuous
            && model.obj_coeff(col) == 0.0
            && entries[j] <= 1;
        excluded[j] = pinned_zero || slackish;
    }
    let mut col_rows: Vec<Vec<(u32, u64)>> = vec![Vec::new(); n];
    let mut row_cols: Vec<Vec<(u32, f64)>> = Vec::with_capacity(m);
    let mut bounds: Vec<(Bnd, Bnd)> = Vec::with_capacity(m);
    let mut row_slacks: Vec<Vec<u32>> = Vec::with_capacity(m);
    for r in 0..m {
        let (coeffs, rlb, rub) = model.row(model.row_at(r).expect("in range"));
        let mut lb: Bnd = exact_small(rlb);
        let mut ub: Bnd = exact_small(rub);
        let mut kept: Vec<(u32, f64)> = Vec::new();
        let mut slacks: Vec<u32> = Vec::new();
        // Exact activity range of the KEPT part, for the vacuity filter.
        let (mut min_act, mut max_act): (Bnd, Bnd) =
            (Some(Rational::new(0, 1)), Some(Rational::new(0, 1)));
        for &(c, a) in coeffs {
            if a == 0.0 {
                continue;
            }
            let j = c as usize;
            let (clo, cup) = model.col_bounds(model.col_at(j).expect("in range"));
            let a_r = exact_small(a).expect("finite coefficient");
            // The entry's exact contribution interval over the column box.
            let (cmin, cmax) = if a > 0.0 {
                (
                    exact_small(clo).map(|b| a_r.clone() * &b),
                    exact_small(cup).map(|b| a_r.clone() * &b),
                )
            } else {
                (
                    exact_small(cup).map(|b| a_r.clone() * &b),
                    exact_small(clo).map(|b| a_r.clone() * &b),
                )
            };
            if excluded[j] {
                // ABSORB: subtract the contribution interval from the bounds.
                lb = match (lb, &cmax) {
                    (Some(b), Some(c)) => Some(&b - c),
                    _ => None,
                };
                ub = match (ub, &cmin) {
                    (Some(b), Some(c)) => Some(&b - c),
                    _ => None,
                };
                if clo != cup {
                    slacks.push(c);
                }
            } else {
                kept.push((c, a));
                col_rows[j].push((r as u32, a.to_bits()));
                min_act = match (min_act, cmin) {
                    (Some(b), Some(c)) => Some(&b + &c),
                    _ => None,
                };
                max_act = match (max_act, cmax) {
                    (Some(b), Some(c)) => Some(&b + &c),
                    _ => None,
                };
            }
        }
        // VACUITY: a side no box point can violate is no side at all.
        if let (Some(l), Some(ma)) = (&lb, &min_act) {
            if l <= ma {
                lb = None;
            }
        }
        if let (Some(u), Some(ma)) = (&ub, &max_act) {
            if u >= ma {
                ub = None;
            }
        }
        row_cols.push(kept);
        bounds.push((lb, ub));
        row_slacks.push(slacks);
    }
    Some(View {
        col_rows,
        row_cols,
        bounds,
        excluded,
        row_slacks,
    })
}

/// Detect verified involutions of `model` (via its normalized view). `None`
/// when nothing is found (or the model is out of cap), in which case the
/// caller behaves bit-identically to a build without detection.
pub(crate) fn detect(model: &Model) -> Option<Symmetry> {
    let view = build_view(model)?;
    let n = model.num_cols();
    let m = model.num_rows();
    let nnz: usize = view.row_cols.iter().map(Vec::len).sum();
    let col_sig = |j: usize| -> (u8, u64, u64, u64) {
        let col = model.col_at(j).expect("in range");
        let (lb, ub) = model.col_bounds(col);
        let kind = match model.col_kind(col) {
            ColKind::Continuous => 0u8,
            ColKind::Binary => 1,
            ColKind::Integer => 2,
        };
        (
            kind,
            lb.to_bits(),
            ub.to_bits(),
            model.obj_coeff(col).to_bits(),
        )
    };

    // ---- Stage 1: color refinement. ----
    let mut ccol: Vec<u64> = (0..n)
        .map(|j| {
            if view.excluded[j] {
                return 0;
            }
            let (k, lb, ub, ob) = col_sig(j);
            mix(mix(mix(mix(0x5157, u64::from(k)), lb), ub), ob)
        })
        .collect();
    let mut crow: Vec<u64> = view
        .bounds
        .iter()
        .map(|(lb, ub)| bnd_hash(bnd_hash(0x21b7, lb), ub))
        .collect();
    let distinct = |v: &[u64]| -> usize {
        let mut s: Vec<u64> = v.to_vec();
        s.sort_unstable();
        s.dedup();
        s.len()
    };
    let mut counts = (distinct(&ccol), distinct(&crow));
    let mut scratch: Vec<(u64, u64)> = Vec::new();
    for _ in 0..REFINE_ITERS {
        let ncc: Vec<u64> = (0..n)
            .map(|j| {
                scratch.clear();
                scratch.extend(
                    view.col_rows[j]
                        .iter()
                        .map(|&(r, ab)| (crow[r as usize], ab)),
                );
                scratch.sort_unstable();
                let mut h = mix(ccol[j], 0x9d5f);
                for &(rc, ab) in scratch.iter() {
                    h = mix(mix(h, rc), ab);
                }
                h
            })
            .collect();
        let ncr: Vec<u64> = (0..m)
            .map(|r| {
                scratch.clear();
                scratch.extend(
                    view.row_cols[r]
                        .iter()
                        .map(|&(c, a)| (ccol[c as usize], a.to_bits())),
                );
                scratch.sort_unstable();
                let mut h = mix(crow[r], 0x7ae3);
                for &(cc, ab) in scratch.iter() {
                    h = mix(mix(h, cc), ab);
                }
                h
            })
            .collect();
        ccol = ncc;
        crow = ncr;
        let nc = (distinct(&ccol), distinct(&crow));
        if nc == counts {
            break;
        }
        counts = nc;
    }

    // ---- Classes (deterministic order: by smallest member). ----
    let mut by_color: std::collections::HashMap<u64, Vec<u32>> = std::collections::HashMap::new();
    for j in 0..n {
        if !view.excluded[j] {
            by_color.entry(ccol[j]).or_default().push(j as u32);
        }
    }
    let mut classes: Vec<Vec<u32>> = by_color.into_values().filter(|v| v.len() >= 2).collect();
    classes.sort_unstable_by_key(|v| v[0]);
    if classes.is_empty() {
        return None;
    }

    // ---- Stages 2+3: build and verify involutions. ----
    // Global work budget, charged per candidate scanned; deterministic. Sized
    // so a rich group (hundreds of generators whose closures each touch a
    // large support) is fully harvested: each build/verify is O(support nnz),
    // and the budget admits ~512 of them on a mid-size model. Detection cost
    // observed at this budget: single-digit milliseconds on the MIPLIB corpus.
    let mut budget: i64 = (512 * nnz + (1 << 20)) as i64;
    let mut gens: Vec<SymGen> = Vec::new();
    let mut covered: std::collections::HashSet<(u32, u32)> = std::collections::HashSet::new();
    let mut attempts = 0usize;
    'outer: for cls in &classes {
        let mut class_pairs = 0usize;
        'class: for i in 0..cls.len() {
            let a = cls[i];
            for &b in &cls[i + 1..] {
                if attempts >= MAX_SEED_ATTEMPTS || gens.len() >= MAX_GENS || budget <= 0 {
                    break 'outer;
                }
                if class_pairs >= MAX_CLASS_PAIRS {
                    break 'class;
                }
                class_pairs += 1;
                if covered.contains(&(a, b)) {
                    continue;
                }
                attempts += 1;
                let Some(pairs) = build_involution(
                    a as usize,
                    b as usize,
                    &view.col_rows,
                    &view.row_cols,
                    &ccol,
                    &crow,
                    &mut budget,
                ) else {
                    continue;
                };
                if verify(&pairs, model, &view, &mut budget) {
                    for &(u, v) in &pairs {
                        covered.insert((u, v));
                        covered.insert((v, u));
                    }
                    let guards = gen_guards(&pairs, model, &view);
                    gens.push(SymGen::new(pairs, guards));
                }
            }
        }
    }
    if gens.is_empty() {
        return None;
    }
    // `AY_MILP_NO_ORBITOPE` keeps every generator on the per-branch orbit
    // walk instead of assembling components — the A/B lane for the static
    // orbitope machinery.
    let (orbitopes, in_component) = if std::env::var_os("AY_MILP_NO_ORBITOPE").is_some() {
        (Vec::new(), vec![false; gens.len()])
    } else {
        assemble_orbitopes(model, &view, &classes, &gens, n)
    };
    // The per-branch orbit walk is licensed only for generators DISJOINT
    // from every component (see `Orbitope` on composition).
    let mut col_gens: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (gi, g) in gens.iter().enumerate() {
        if in_component[gi] {
            continue;
        }
        for &(u, v) in &g.pairs {
            col_gens[u as usize].push(gi as u32);
            col_gens[v as usize].push(gi as u32);
        }
    }
    let mut ranks = vec![u64::MAX; n];
    let mut cells = vec![(u32::MAX, u32::MAX); n];
    for (oi, ot) in orbitopes.iter().enumerate() {
        let k = ot.blocks.len() as u64;
        for (bi, block) in ot.blocks.iter().enumerate() {
            for (p, &c) in block.iter().enumerate() {
                ranks[c as usize] = (p as u64) * k + bi as u64;
                cells[c as usize] = (oi as u32, p as u32);
            }
        }
    }
    let n_gens = gens.len();
    Some(Symmetry {
        gens,
        orbitopes,
        col_gens,
        ranks,
        cells,
        dyn_lane: false,
        stamp: 0,
        gen_stamp: vec![u32::MAX; n_gens],
        gen_ok: vec![false; n_gens],
        orbit_stamp: vec![u32::MAX; n],
        fixes_made: 0,
        branches_hit: 0,
        orbitope_reductions: 0,
        orbitope_cutoffs: 0,
        dyn_nodes: 0,
        dyn_seq_sum: 0,
        dyn_seq_max: 0,
        dyn_pairs_spent: 0,
        dyn_pairs: 0,
    })
}

/// At most this many orbitope components per model, and caps on their shape.
const MAX_ORBITOPES: usize = 8;
const MAX_ORBITOPE_BLOCKS: usize = 64;

/// Assemble FULL ORBITOPE components from the verified transpositions.
///
/// For an anchor class `{c_1 < ... < c_k}` (one column per block of a
/// candidate k-block structure), the component exists when a verified STAR of
/// transpositions `g_i: c_1 <-> c_i` is present whose supports intersect
/// pairwise in exactly one common block: `B_1 = support(g_2) ∩ ... ∩
/// support(g_k)` with `|B_1| = |support|/2`, `B_i = g_i(B_1)`, and all
/// `B_1..B_k` pairwise disjoint. The star generates the full `S_k` acting
/// position-consistently on the blocks (conjugation: `g_i g_j g_i` swaps
/// `B_i` and `B_j` pointwise in `B_1`'s position order), which is exactly
/// the license the static lex constraint needs (`Orbitope`).
///
/// Blocks of size 1 (`m == 1`, identical columns) are NOT assembled: the
/// per-branch orbit walk already handles them and was measured good
/// (misc07/p0201); the component lane exists for the matrix case it alone
/// can keep alive. `k == 2` components (a single verified block swap) are
/// assembled from that one generator: any 2-coloring of its pairs is a valid
/// block split, and `S_2` needs no star.
///
/// Returns the components plus, per generator, whether its support touches
/// any component (such generators are excluded from the orbit walk).
fn assemble_orbitopes(
    model: &Model,
    view: &View,
    classes: &[Vec<u32>],
    gens: &[SymGen],
    n: usize,
) -> (Vec<Orbitope>, Vec<bool>) {
    // Position order (any FIXED order is licensed — the sort license does not
    // care which coordinate order defines lex). The propagation frontier only
    // advances through positions that branching + propagation actually pin,
    // so put the columns the search touches early FIRST: integral before
    // continuous, higher view-degree (row count) before lower — on noswot
    // that is w-integers/y-binaries before the barely-branched link binaries,
    // which is the difference between the frontier moving and not
    // (`AY_MILP_ORBITOPE_ORDER`: `deg` default, `index`, `revindex` A/B).
    let order = std::env::var("AY_MILP_ORBITOPE_ORDER").unwrap_or_default();
    // General-integer DENSITY floor for the static-lex lane (percent of the
    // block; see the lane choice below). Default 12: assemble only when
    // general integers are >= ~1/8 of the block. `0` restores the pre-2026-07-18
    // behaviour (assemble every non-all-binary component); `100` is ~NO_ORBITOPE.
    let min_int_pct: usize = std::env::var("AY_MILP_ORBITOPE_MIN_INT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(12);
    let pos_key = |c: u32| -> (u8, i64, i64) {
        let col = model.col_at(c as usize).expect("in range");
        let cont = u8::from(model.col_kind(col) == ColKind::Continuous);
        match order.as_str() {
            "index" => (cont, 0, i64::from(c)),
            "revindex" => (cont, 0, -i64::from(c)),
            _ => (
                cont,
                -(view.col_rows[c as usize].len() as i64),
                i64::from(c),
            ),
        }
    };
    let mut consumed = vec![false; n];
    let mut orbitopes: Vec<Orbitope> = Vec::new();
    // (u, v) -> gen index, for star lookup.
    let mut by_pair: std::collections::HashMap<(u32, u32), usize> =
        std::collections::HashMap::new();
    for (gi, g) in gens.iter().enumerate() {
        for &(u, v) in &g.pairs {
            by_pair.entry((u, v)).or_insert(gi);
        }
    }
    for cls in classes {
        if orbitopes.len() >= MAX_ORBITOPES {
            break;
        }
        let k = cls.len();
        if k < 2 || k > MAX_ORBITOPE_BLOCKS {
            continue;
        }
        if cls.iter().any(|&c| consumed[c as usize]) {
            continue;
        }
        let c1 = cls[0];
        let star: Option<Vec<usize>> = cls[1..]
            .iter()
            .map(|&ci| by_pair.get(&(c1.min(ci), c1.max(ci))).copied())
            .collect();
        let Some(star) = star else {
            continue; // an incomplete star cannot certify the full S_k
        };
        // B_1: the common block = intersection of the star supports (k >= 3),
        // or the `u`-side of the single generator (k == 2).
        let support: Vec<std::collections::HashSet<u32>> = star
            .iter()
            .map(|&gi| gens[gi].pairs.iter().flat_map(|&(u, v)| [u, v]).collect())
            .collect();
        let mut b1: Vec<u32> = if k == 2 {
            gens[star[0]].pairs.iter().map(|&(u, _)| u).collect()
        } else {
            support[0]
                .iter()
                .copied()
                .filter(|c| support[1..].iter().all(|s| s.contains(c)))
                .collect()
        };
        b1.sort_unstable();
        let msz = b1.len();
        if msz < 2 || star.iter().any(|&gi| gens[gi].pairs.len() != msz) {
            continue; // m == 1 stays with the orbit walk; ragged star: decline
        }
        // LANE CHOICE, measured (same-load 60s A/B, 2026-07-17): an
        // ALL-BINARY component stays on the per-branch orbit walk — branching
        // plus pin transfer re-pin whole binary orbits, the pairwise-equal-box
        // condition keeps holding, and the walk's many-columns-per-branch
        // fixes dominate (misc07, 3x81 binary: down-orbit proves in 6.2s,
        // the static lex lane needs 25s). A component with general-integer or
        // continuous columns goes to the static orbitope lane — wide boxes
        // never re-equalize once branched, the walk retires by depth ~10
        // (noswot, 4x25 mixed: 9 orbit fixes in 508k nodes, ever), and only
        // the root lex order keeps cutting (43k reductions, nodes -62%).
        if b1.iter().all(|&c| {
            model.col_kind(model.col_at(c as usize).expect("in range")) == ColKind::Binary
        }) {
            continue;
        }
        // FINER LANE CHOICE (2026-07-18, rout tree-size arm). The all-binary
        // rule above is too coarse: a component whose block is only SPARSELY
        // general-integer keeps the per-branch orbit walk ALIVE — its many
        // binary columns re-equalize under branching, so orbital fixing keeps
        // firing whole-orbit fixes — while the static lex, whose reductions need
        // pinned general-integers to bite, does little. Measured (unseeded 60s,
        // same-box A/B): rout (3 int / 111-col block) 1052->1075 dual and
        // orbital fixing 0->3,256; qiu (0/210) dual gap halved (-583->-394);
        // gen (1/145) identical; only noswot (5/25 = 20%) NEEDS the static lex
        // (its walk dies by depth ~10, 52 fixes in 892k nodes). So assemble ONLY
        // when general integers reach a real density of the block; otherwise the
        // generators fall through to the orbit walk (`col_gens`, below).
        let n_gen_int = b1
            .iter()
            .filter(|&&c| {
                model.col_kind(model.col_at(c as usize).expect("in range")) == ColKind::Integer
            })
            .count();
        if n_gen_int * 100 < b1.len() * min_int_pct {
            continue;
        }
        // Position order: see `pos_key` above.
        b1.sort_by_key(|&c| pos_key(c));
        // B_i = g_i(B_1), in B_1's position order; all blocks disjoint.
        let mut blocks: Vec<Vec<u32>> = vec![b1.clone()];
        let mut seen: std::collections::HashSet<u32> = b1.iter().copied().collect();
        let mut ok = true;
        for &gi in &star {
            let bi: Vec<u32> = b1.iter().map(|&c| gens[gi].image(c)).collect();
            for &c in &bi {
                if !seen.insert(c) {
                    ok = false; // overlaps B_1 or an earlier block
                    break;
                }
            }
            if !ok {
                break;
            }
            blocks.push(bi);
        }
        if !ok {
            continue;
        }
        for b in &blocks {
            for &c in b {
                consumed[c as usize] = true;
            }
        }
        orbitopes.push(Orbitope { blocks });
    }
    let in_component: Vec<bool> = gens
        .iter()
        .map(|g| {
            g.pairs
                .iter()
                .any(|&(u, v)| consumed[u as usize] || consumed[v as usize])
        })
        .collect();
    (orbitopes, in_component)
}

/// The slack guards for a verified generator: every non-point-box excluded
/// column hosted in a row the generator moves, with that column's ROOT box
/// bits (see `SymGen::guards`).
fn gen_guards(pairs: &[(u32, u32)], model: &Model, view: &View) -> Vec<(u32, u64, u64)> {
    let mut cols: Vec<u32> = Vec::new();
    for &(u, v) in pairs {
        for &c in [u, v].iter() {
            for &(r, _) in &view.col_rows[c as usize] {
                cols.extend_from_slice(&view.row_slacks[r as usize]);
            }
        }
    }
    cols.sort_unstable();
    cols.dedup();
    cols.into_iter()
        .map(|c| {
            let (lo, up) = model.col_bounds(model.col_at(c as usize).expect("in range"));
            (c, lo.to_bits(), up.to_bits())
        })
        .collect()
}

/// Propagate the forced closure of `a <-> b` into a full candidate
/// involution. Returns the swapped pairs `(u < v)`, or `None` on any dead end
/// or budget exhaustion. Greedy choices are canonical (self-map preferred,
/// then smallest index); a wrong pick fails verification, never soundness.
fn build_involution(
    a: usize,
    b: usize,
    col_rows: &[Vec<(u32, u64)>],
    row_cols: &[Vec<(u32, f64)>],
    ccol: &[u64],
    crow: &[u64],
    budget: &mut i64,
) -> Option<Vec<(u32, u32)>> {
    let n = col_rows.len();
    let m = row_cols.len();
    let mut colmap: Vec<u32> = vec![NONE_U32; n];
    let mut rowmap: Vec<u32> = vec![NONE_U32; m];
    *budget -= ((n + m) / 8) as i64; // charge the allocation/clear
    colmap[a] = b as u32;
    colmap[b] = a as u32;
    let mut queue: Vec<(bool, u32, u32)> = vec![(true, a as u32, b as u32)];
    let mut head = 0usize;
    while head < queue.len() {
        if *budget <= 0 {
            return None;
        }
        let (is_col, x, y) = queue[head];
        head += 1;
        if is_col {
            let (u, w) = (x as usize, y as usize);
            if col_rows[u].len() != col_rows[w].len() {
                return None;
            }
            *budget -= (col_rows[u].len() + col_rows[w].len()) as i64;
            for &(r, ab) in &col_rows[u] {
                let r = r as usize;
                if rowmap[r] != NONE_U32 {
                    continue; // consistency settled by final verification
                }
                // Candidates among w's rows: same coeff bits, same color, unmapped.
                let mut self_ok = false;
                let mut best: u32 = NONE_U32;
                for &(r2, ab2) in &col_rows[w] {
                    if ab2 != ab || crow[r2 as usize] != crow[r] {
                        continue;
                    }
                    if r2 as usize == r {
                        self_ok = true;
                        break;
                    }
                    if rowmap[r2 as usize] == NONE_U32 && r2 < best {
                        best = r2;
                    }
                }
                if self_ok {
                    rowmap[r] = r as u32;
                    continue;
                }
                if best == NONE_U32 {
                    return None;
                }
                rowmap[r] = best;
                rowmap[best as usize] = r as u32;
                queue.push((false, r as u32, best));
            }
        } else {
            let (r, r2) = (x as usize, y as usize);
            if row_cols[r].len() != row_cols[r2].len() {
                return None;
            }
            *budget -= (row_cols[r].len() + row_cols[r2].len()) as i64;
            for &(jc, av) in &row_cols[r] {
                let jc = jc as usize;
                if colmap[jc] != NONE_U32 {
                    continue;
                }
                let ab = av.to_bits();
                let mut self_ok = false;
                let mut best: u32 = NONE_U32;
                for &(j2, av2) in &row_cols[r2] {
                    if av2.to_bits() != ab || ccol[j2 as usize] != ccol[jc] {
                        continue;
                    }
                    if j2 as usize == jc {
                        self_ok = true;
                        break;
                    }
                    if colmap[j2 as usize] == NONE_U32 && j2 < best {
                        best = j2;
                    }
                }
                if self_ok {
                    colmap[jc] = jc as u32; // pinned to itself
                    continue;
                }
                if best == NONE_U32 {
                    return None;
                }
                colmap[jc] = best;
                colmap[best as usize] = jc as u32;
                queue.push((true, jc as u32, best));
            }
        }
    }
    let mut pairs: Vec<(u32, u32)> = Vec::new();
    for (u, &v) in colmap.iter().enumerate() {
        if v != NONE_U32 && (u as u32) < v {
            pairs.push((u as u32, v));
        }
    }
    if pairs.is_empty() {
        return None;
    }
    Some(pairs)
}

/// Exact verification: the candidate involution (columns) with its induced
/// row map must map the VIEW exactly onto itself — bit equality on column
/// data and coefficients, exact rational equality on effective row bounds.
/// Any mismatch rejects the candidate — this is the fail-closed gate that
/// makes the greedy construction above safe.
fn verify(pairs: &[(u32, u32)], model: &Model, view: &View, budget: &mut i64) -> bool {
    // Column data must match bit-for-bit.
    let mut colmap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    for &(u, v) in pairs {
        if colmap.insert(u, v).is_some() || colmap.insert(v, u).is_some() {
            return false; // not disjoint — construction bug, fail closed
        }
        if view.excluded[u as usize] || view.excluded[v as usize] {
            return false; // excluded columns are FIXED by every generator
        }
        let (cu, cv) = (
            model.col_at(u as usize).expect("in range"),
            model.col_at(v as usize).expect("in range"),
        );
        let (ul, uu) = model.col_bounds(cu);
        let (vl, vu) = model.col_bounds(cv);
        if ul.to_bits() != vl.to_bits()
            || uu.to_bits() != vu.to_bits()
            || model.col_kind(cu) != model.col_kind(cv)
            || model.obj_coeff(cu).to_bits() != model.obj_coeff(cv).to_bits()
        {
            return false;
        }
    }
    // The induced row map: re-derive it as the unique bound-and-coefficient
    // preserving pairing, row by row, over every row that touches a moved
    // column. A row maps to the row whose coefficient list IS the π-image of
    // its own; if that row does not exist, or is claimed twice, reject.
    // Affected rows, deduplicated.
    let mut affected: Vec<u32> = Vec::new();
    for &(u, v) in pairs {
        affected.extend(view.col_rows[u as usize].iter().map(|&(r, _)| r));
        affected.extend(view.col_rows[v as usize].iter().map(|&(r, _)| r));
    }
    affected.sort_unstable();
    affected.dedup();
    // Index rows by a hash of their (effective bounds, sorted coefficient
    // list) for image lookup; collisions are settled by exact comparison.
    let mut index: std::collections::HashMap<u64, Vec<u32>> = std::collections::HashMap::new();
    for &r in &affected {
        let (lb, ub) = &view.bounds[r as usize];
        let mut h = bnd_hash(bnd_hash(0x77aa, lb), ub);
        for &(c, a) in &view.row_cols[r as usize] {
            h = mix(mix(h, u64::from(c)), a.to_bits());
        }
        index.entry(h).or_default().push(r);
    }
    let mut image: Vec<(u32, u64)> = Vec::new();
    let mut claimed: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for &r in &affected {
        *budget -= view.row_cols[r as usize].len() as i64;
        if *budget <= 0 {
            return false;
        }
        image.clear();
        image.extend(
            view.row_cols[r as usize]
                .iter()
                .map(|&(c, a)| (*colmap.get(&c).unwrap_or(&c), a.to_bits())),
        );
        image.sort_unstable_by_key(|&(c, _)| c);
        let (lb, ub) = &view.bounds[r as usize];
        let mut h = bnd_hash(bnd_hash(0x77aa, lb), ub);
        for &(c, ab) in &image {
            h = mix(mix(h, u64::from(c)), ab);
        }
        // The image row must exist among the affected rows with identical
        // effective bounds and identical (column, coeff-bits) list.
        let Some(cands) = index.get(&h) else {
            return false;
        };
        let mut found = false;
        for &r2 in cands {
            if view.bounds[r2 as usize] != view.bounds[r as usize] {
                continue;
            }
            let rc = &view.row_cols[r2 as usize];
            if rc.len() == image.len()
                && rc
                    .iter()
                    .zip(image.iter())
                    .all(|(&(c2, a2), &(ci, abi))| c2 == ci && a2.to_bits() == abi)
            {
                // Each image row may be claimed by exactly one source row —
                // the row map must be injective to be a permutation.
                if r2 != r && !claimed.insert(r2) {
                    return false;
                }
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Model, Sense};

    /// Two interchangeable blocks (y0,z0) | (y1,z1) with a coupling row —
    /// detection must find the swap; perturbing one coefficient must kill it.
    #[test]
    fn detects_block_interchange_and_rejects_perturbation() {
        let build = |perturb: bool| {
            let mut m = Model::new();
            let y0 = m.add_binary_col();
            let z0 = m.add_int_col(0.0, 9.0);
            let y1 = m.add_binary_col();
            let z1 = m.add_int_col(0.0, 9.0);
            // VUB per block: z_i - 9.6 y_i <= 0 (perturbed: 9.5 on block 1)
            m.add_row(f64::NEG_INFINITY, 0.0, &[(z0, 1.0), (y0, -9.6)]);
            m.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(z1, 1.0), (y1, if perturb { -9.5 } else { -9.6 })],
            );
            // Coupling: z0 + z1 <= 12 (symmetric in the blocks).
            m.add_row(f64::NEG_INFINITY, 12.0, &[(z0, 1.0), (z1, 1.0)]);
            m.set_objective(&[(z0, -1.0), (z1, -1.0)], Sense::Minimize);
            m
        };
        let sym = detect(&build(false)).expect("symmetric model must be detected");
        assert_eq!(sym.gens.len(), 1);
        assert_eq!(sym.gens[0].pairs, vec![(0, 2), (1, 3)]);
        assert!(
            detect(&build(true)).is_none(),
            "perturbed model has no symmetry"
        );
    }

    /// Identical columns (block size 1, class size 3): all pairs from the
    /// class seed must verify, and the orbit walk must reach all three.
    #[test]
    fn identical_columns_form_a_full_orbit() {
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_binary_col();
        let c = m.add_binary_col();
        let d = m.add_binary_col(); // distinguished by the row below
        m.add_row(1.0, 2.0, &[(a, 1.0), (b, 1.0), (c, 1.0), (d, 2.0)]);
        m.set_objective(&[(a, 1.0), (b, 1.0), (c, 1.0), (d, 5.0)], Sense::Minimize);
        let mut sym = detect(&m).expect("identical columns must be detected");
        assert!(sym.gens.len() >= 2, "need at least a<->b and a<->c");
        let lower = vec![0.0; 4];
        let upper = vec![1.0; 4];
        let mut orbit = Vec::new();
        sym.down_orbit(0, &lower, &upper, &mut orbit);
        orbit.sort_unstable();
        assert_eq!(orbit, vec![1, 2], "orbit of col 0 is {{1, 2}}, d excluded");
        // Asymmetric box on b retires every generator that moves b, but the
        // a<->c swap must survive.
        let upper2 = vec![1.0, 0.0, 1.0, 1.0];
        sym.down_orbit(0, &lower, &upper2, &mut orbit);
        assert_eq!(orbit, vec![2], "b's box differs; only c remains reachable");
    }

    /// An asymmetric model must yield nothing (the self-gate the corpus
    /// bit-identity rests on).
    #[test]
    fn asymmetric_model_detects_nothing() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        let z = m.add_int_col(0.0, 5.0);
        m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 1.0), (y, 2.0), (z, 1.0)]);
        m.add_row(0.0, f64::INFINITY, &[(x, 1.0), (z, -0.5)]);
        m.set_objective(&[(x, -1.0), (y, -2.0), (z, -1.0)], Sense::Minimize);
        assert!(detect(&m).is_none());
    }

    /// The noswot block-D shape in miniature: three "units", symmetric ONLY
    /// through both normalizations. Unit 1's capacity row is an EQUALITY with
    /// a continuous slack column; units 2 and 3 have plain `<=` rows carrying
    /// a shared dominated column with DIFFERENT coefficients (2 and 3). On
    /// the raw model bit-exact comparison finds nothing across units; after
    /// `dual_pin_dominated` pins the dominated column and the view absorbs
    /// the slack, the full S3 (all three transpositions) must verify.
    #[test]
    fn slack_and_pin_normalization_unlocks_block_symmetry() {
        let build = || {
            let mut m = Model::new();
            let y1 = m.add_binary_col(); // 0
            let w1 = m.add_int_col(0.0, 3.0); // 1
            let y2 = m.add_binary_col(); // 2
            let w2 = m.add_int_col(0.0, 3.0); // 3
            let y3 = m.add_binary_col(); // 4
            let w3 = m.add_int_col(0.0, 3.0); // 5
            let s = m.add_col(0.0, 3.0); // 6: unit 1's equality slack
            let t = m.add_col(0.0, 10.0); // 7: the dominated column
                                          // Unit 1: -3 y1 + w1 + s = 0  (== -3 y1 + w1 <= 0 after absorb;
                                          // the >= side is vacuous because s's box covers the range).
            m.add_row(0.0, 0.0, &[(y1, -3.0), (w1, 1.0), (s, 1.0)]);
            // Units 2, 3: -3 y_i + w_i + k*t <= 0 with k = 2, 3.
            m.add_row(f64::NEG_INFINITY, 0.0, &[(y2, -3.0), (w2, 1.0), (t, 2.0)]);
            m.add_row(f64::NEG_INFINITY, 0.0, &[(y3, -3.0), (w3, 1.0), (t, 3.0)]);
            // Symmetric coupling.
            m.add_row(f64::NEG_INFINITY, 5.0, &[(w1, 1.0), (w2, 1.0), (w3, 1.0)]);
            m.set_objective(&[(w1, -1.0), (w2, -1.0), (w3, -1.0)], Sense::Minimize);
            m
        };
        // Raw (unpinned): t's live box keeps the unit rows distinct, so no
        // cross-unit generator may verify — and nothing else here is
        // symmetric, so detection must find nothing at all.
        assert!(
            detect(&build()).is_none(),
            "unpinned units are NOT symmetric"
        );
        let mut m = build();
        let pins = dual_pin_dominated(&mut m);
        assert_eq!(pins, 1, "exactly the dominated column t is pinned");
        assert_eq!(m.col_bounds(m.col_at(7).expect("t")), (0.0, 0.0));
        let mut sym = detect(&m).expect("normalized units must be symmetric");
        assert_eq!(
            sym.gens.len(),
            3,
            "all three unit transpositions must verify"
        );
        // The (1,2) and (1,3) generators move unit 1's equality row, whose
        // slack `s` must be guarded; the (2,3) generator must NOT carry that
        // guard (t is pinned — a point box needs no guard).
        let with_guard = sym.gens.iter().filter(|g| !g.guards.is_empty()).count();
        assert_eq!(with_guard, 2, "exactly the two unit-1 swaps guard s");
        // MIXED-KIND component (w is integer): the static orbitope lane owns
        // it — one 3-block component of 2 positions, degree order w before y.
        assert_eq!(sym.orbitopes.len(), 1);
        assert_eq!(
            sym.orbitopes[0].blocks,
            vec![vec![1, 0], vec![3, 2], vec![5, 4]]
        );
        // Guard mechanics (the pin-transfer lane still reads `applicable`):
        // shrinking the slack's box retires the guarded unit-1 swaps but not
        // the (2,3) swap.
        let lower = vec![0.0; 8];
        let upper = vec![1.0, 3.0, 1.0, 3.0, 1.0, 3.0, 3.0, 0.0];
        let upper_cut = vec![1.0, 3.0, 1.0, 3.0, 1.0, 3.0, 2.0, 0.0];
        assert!(sym.gens.iter().all(|g| g.applicable(&lower, &upper)));
        assert_eq!(
            sym.gens
                .iter()
                .filter(|g| g.applicable(&lower, &upper_cut))
                .count(),
            1,
            "only the guardless (2,3) swap survives the slack tightening"
        );
        // Orbitope propagation: pinning w1 = 0 cascades `up <= up` down the
        // lex order — w2 and w3 collapse to 0 through the adjacent pairs.
        let integral = vec![true, true, true, true, true, true, false, false];
        let mut lo = lower.clone();
        let mut up = vec![1.0, 0.0, 1.0, 3.0, 1.0, 3.0, 3.0, 0.0];
        let n = sym
            .propagate_orbitopes(&mut lo, &mut up, &integral)
            .expect("box has C-points");
        assert!(n >= 2, "cascade must fire");
        assert_eq!((up[3], up[5]), (0.0, 0.0), "w2, w3 forced to 0");
        // And a box that inverts the order at the frontier has no C-point.
        let mut lo = vec![0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
        let mut up = vec![1.0, 0.0, 1.0, 3.0, 1.0, 3.0, 3.0, 0.0];
        assert!(
            sym.propagate_orbitopes(&mut lo, &mut up, &integral)
                .is_err(),
            "w1 <= 0 < 1 <= w2 violates the lex order everywhere"
        );
    }

    /// DYNAMIC LEX-CHAIN PROPAGATION, exhaustively verified: for random
    /// boxes over a 3x3 all-integer orbitope and random position SEQUENCES
    /// (the dynamic lane's branching orders, including the empty and the
    /// full one), enumerate every integer point of the box and compare
    /// against `lex_chain`:
    ///
    /// * `Err` only when NO box point is lex-sorted under the sequence
    ///   (the cutoff license — pruning such a node loses nothing);
    /// * on `Ok`, the tightened box still contains EVERY sorted box point
    ///   (derived bounds are consequences of the constraint: no sorted
    ///   point — in particular no champion — is ever cut) and is a subset
    ///   of the incoming box;
    /// * the static path (`seq = None`) satisfies the same contract for the
    ///   full identity order.
    #[test]
    fn dynamic_lex_chain_never_cuts_a_sorted_point() {
        let blocks: Vec<Vec<u32>> = (0..3u32).map(|i| (3 * i..3 * i + 3).collect()).collect();
        let integral = vec![true; 9];
        let mut seed = 0xD1_5EEDu64;
        let mut rnd = move |m: u64| -> u64 {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) % m
        };
        // Is `x` lex-nonincreasing across adjacent blocks over `seq`?
        let sorted = |x: &[i64; 9], seq: &[u32]| -> bool {
            (0..2).all(|i| {
                for &p in seq {
                    let (u, v) = (x[3 * i + p as usize], x[3 * (i + 1) + p as usize]);
                    if u > v {
                        return true;
                    }
                    if u < v {
                        return false;
                    }
                }
                true
            })
        };
        for case in 0..400 {
            let mut lo = [0.0f64; 9];
            let mut up = [0.0f64; 9];
            for j in 0..9 {
                lo[j] = rnd(3) as f64;
                up[j] = lo[j] + rnd(3 - lo[j] as u64) as f64;
            }
            // A random sequence: a shuffled subset of the positions (empty,
            // partial, and full all occur), plus the static lane every 4th.
            let mut seq: Vec<u32> = (0..3).collect();
            for i in (1..3usize).rev() {
                seq.swap(i, rnd(i as u64 + 1) as usize);
            }
            seq.truncate(rnd(4) as usize);
            let use_static = case % 4 == 3;
            let eff: Vec<u32> = if use_static {
                (0..3).collect() // static == identity sequence
            } else {
                seq.clone()
            };
            // Enumerate the box's integer points; collect the sorted ones.
            let mut sorted_pts: Vec<[i64; 9]> = Vec::new();
            let mut x = [0i64; 9];
            'pts: loop {
                let mut carry = 0usize;
                if sorted(&x, &eff) && (0..9).all(|j| (lo[j] as i64..=up[j] as i64).contains(&x[j]))
                {
                    sorted_pts.push(x);
                }
                loop {
                    x[carry] += 1;
                    if x[carry] <= 2 {
                        break;
                    }
                    x[carry] = 0;
                    carry += 1;
                    if carry == 9 {
                        break 'pts;
                    }
                }
            }
            let (mut tl, mut tu) = (lo, up);
            let arg = if use_static { None } else { Some(&seq[..]) };
            match lex_chain(&blocks, arg, &mut tl, &mut tu, &integral) {
                Err(()) => assert!(
                    sorted_pts.is_empty(),
                    "case {case}: cutoff with sorted points alive (seq {eff:?}, lo {lo:?}, up {up:?})"
                ),
                Ok(_) => {
                    for j in 0..9 {
                        assert!(
                            tl[j] >= lo[j] && tu[j] <= up[j],
                            "case {case}: propagation must only shrink"
                        );
                    }
                    for pt in &sorted_pts {
                        assert!(
                            (0..9).all(|j| (tl[j] as i64..=tu[j] as i64).contains(&pt[j])),
                            "case {case}: a sorted point was cut (seq {eff:?}, pt {pt:?}, lo {tl:?}, up {tu:?})"
                        );
                    }
                }
            }
        }
    }

    /// DIAGNOSTIC (ignored; run with `--ignored --nocapture`): how far is the
    /// pairwise-fixpoint lex chain from COMPLETE orbitopal fixing (per-cell
    /// min/max over the enumerated sorted points)? Prints a deficit count.
    #[test]
    #[ignore]
    fn lex_chain_completeness_deficit_stats() {
        let blocks: Vec<Vec<u32>> = (0..4u32).map(|i| (3 * i..3 * i + 3).collect()).collect();
        let n = 12usize;
        let integral = vec![true; n];
        let mut seed = 0xC0FFEEu64;
        let mut rnd = move |m: u64| -> u64 {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) % m
        };
        let sorted = |x: &[i64], seq: &[u32]| -> bool {
            (0..3).all(|i| {
                for &p in seq {
                    let (u, v) = (x[3 * i + p as usize], x[3 * (i + 1) + p as usize]);
                    if u > v {
                        return true;
                    }
                    if u < v {
                        return false;
                    }
                }
                true
            })
        };
        let (mut deficit_cells, mut deficit_cases, mut cases, mut missed_cutoffs) = (0, 0, 0, 0);
        for case in 0..2000 {
            let mut lo = vec![0.0f64; n];
            let mut up = vec![0.0f64; n];
            for j in 0..n {
                lo[j] = rnd(3) as f64;
                up[j] = lo[j] + rnd(3 - lo[j] as u64) as f64;
            }
            let mut seq: Vec<u32> = (0..3).collect();
            for i in (1..3usize).rev() {
                seq.swap(i, rnd(i as u64 + 1) as usize);
            }
            if case % 2 == 0 {
                seq.truncate(1 + rnd(3) as usize);
            }
            let mut mins = vec![i64::MAX; n];
            let mut maxs = vec![i64::MIN; n];
            let mut any = false;
            let mut x = vec![0i64; n];
            'pts: loop {
                if (0..n).all(|j| (lo[j] as i64..=up[j] as i64).contains(&x[j])) && sorted(&x, &seq)
                {
                    any = true;
                    for j in 0..n {
                        mins[j] = mins[j].min(x[j]);
                        maxs[j] = maxs[j].max(x[j]);
                    }
                }
                let mut carry = 0usize;
                loop {
                    x[carry] += 1;
                    if x[carry] <= 2 {
                        break;
                    }
                    x[carry] = 0;
                    carry += 1;
                    if carry == n {
                        break 'pts;
                    }
                }
            }
            let (mut tl, mut tu) = (lo.clone(), up.clone());
            match lex_chain(&blocks, Some(&seq), &mut tl, &mut tu, &integral) {
                Err(()) => assert!(!any),
                Ok(_) => {
                    if !any {
                        missed_cutoffs += 1;
                        continue;
                    }
                    cases += 1;
                    let mut d = 0;
                    for j in 0..n {
                        if (mins[j] as f64) > tl[j] || (maxs[j] as f64) < tu[j] {
                            d += 1;
                        }
                    }
                    if d > 0 {
                        deficit_cases += 1;
                        deficit_cells += d;
                    }
                }
            }
        }
        eprintln!(
            "lex_chain completeness: {cases} feasible cases, {deficit_cases} with deficit \
             ({deficit_cells} cells), {missed_cutoffs} missed cutoffs"
        );
    }

    /// `dual_pin_dominated` pins exactly the dominated columns: zero
    /// objective, continuous, every entry unconstraining in one direction.
    #[test]
    fn dual_pin_pins_only_dominated_columns() {
        let mut m = Model::new();
        let x = m.add_binary_col(); // integer kinds: never pinned by this pass
        let t = m.add_col(0.0, 10.0); // dominated down (only <=-rows, positive)
        let s = m.add_col(0.0, 5.0); // equality slack: NOT dominated
        let c = m.add_col(0.0, 4.0); // objective != 0: NOT eligible
        let g = m.add_col(0.0, 7.0); // dominated up (>=-row, positive coeff)
        m.add_row(f64::NEG_INFINITY, 4.0, &[(x, 1.0), (t, 2.0)]);
        m.add_row(f64::NEG_INFINITY, 6.0, &[(x, 2.0), (t, 3.0)]);
        m.add_row(1.0, 1.0, &[(x, 1.0), (s, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 1.0), (c, 1.0)]);
        m.add_row(2.0, f64::INFINITY, &[(x, 1.0), (g, 1.0)]);
        m.set_objective(&[(x, -1.0), (c, 1.0)], Sense::Minimize);
        let pins = dual_pin_dominated(&mut m);
        assert_eq!(pins, 2, "t pinned down, g pinned up");
        assert_eq!(m.col_bounds(m.col_at(1).expect("t")), (0.0, 0.0));
        assert_eq!(m.col_bounds(m.col_at(2).expect("s")), (0.0, 5.0));
        assert_eq!(m.col_bounds(m.col_at(3).expect("c")), (0.0, 4.0));
        assert_eq!(m.col_bounds(m.col_at(4).expect("g")), (7.0, 7.0));
        assert_eq!(m.col_bounds(m.col_at(0).expect("x")), (0.0, 1.0));
    }
}
