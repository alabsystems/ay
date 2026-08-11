// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared occurrence list for SAT inprocessing (subsumption, BCE, BVE).
//!
//! Tracks which clauses contain each literal. Used during preprocessing
//! and inprocessing passes to efficiently find clauses that share literals.
//!
//! Position maps (`pos_map`) give O(1) clause-index-to-position lookup,
//! replacing the O(n) `iter().position()` scan in `remove_clause`.
//! This matters on high-occurrence literals (hundreds of entries) during
//! BVE, BCE, and subsumption passes. See #3036 Finding 3.

use crate::literal::Literal;

/// Position map type: maps clause_idx -> position in the occurrence vec.
///
/// Uses `hashbrown::HashMap` with `foldhash` for fast integer hashing,
/// matching the rest of ay-sat's hash map usage (see `kani_compat.rs`).
type PosMap = hashbrown::HashMap<usize, usize, foldhash::fast::FixedState>;

/// Sentinel partner literal stored in `partner` for occurrence entries whose
/// clause is NOT binary (size != 2). Keeps `partner[lit]` positionally aligned
/// with `occ[lit]` so the factor binary fast path can skip large clauses by a
/// cheap inline compare (no arena dereference). `u32::MAX` is never a real
/// literal (variable index would be `u32::MAX >> 1`, far above any live var).
pub(crate) const PARTNER_SENTINEL: Literal = Literal(u32::MAX);

/// Occurrence list mapping literals to clause indices.
///
/// For each literal (indexed by `2*var + polarity`), stores the set of
/// clause indices that contain that literal.
#[derive(Debug, Clone)]
pub(crate) struct OccList {
    /// For each literal index, the list of clause indices containing that literal.
    pub(crate) occ: Vec<Vec<usize>>,
    /// For each literal index, maps clause_idx -> position in `occ[lit_index]`.
    /// Maintained in sync with `occ` for O(1) position lookup in `remove_clause`.
    pos_map: Vec<PosMap>,
    /// Optional parallel array to `occ` (factor pass only): `partner[l][i]` is
    /// the OTHER literal of `occ[l][i]`'s clause when that clause is binary,
    /// else [`PARTNER_SENTINEL`]. Lets `find_next_factor` read a binary
    /// partner literal inline instead of dereferencing the clause arena for
    /// every occurrence element (kissat's inline binary watches). Empty and
    /// unmaintained unless `track_partners` is set; kept positionally in
    /// lockstep with `occ` via the same `push`/`swap_remove` positions.
    partner: Vec<Vec<Literal>>,
    /// Whether `partner` is being maintained. Default `false`; only the factor
    /// occurrence build enables it, so BVE/BCE/subsumption pay only a
    /// predictable never-taken branch in `add_clause`/`remove_clause`.
    track_partners: bool,
    /// Whether the `pos_map` position index is maintained. Default `true`
    /// (every position-based consumer — BVE/BCE/subsumption/CCE/factor/HTR —
    /// needs O(1) `remove_clause`/`contains`). Set `false` by
    /// [`OccList::new_occ_only`] for build-once/read-only-`get()` consumers
    /// (level-0 GC's `gc_occ`) that never call `remove_clause`/`contains`/
    /// `swap_to_front`/`sort_each_by_key`. Skipping the per-occurrence
    /// `HashMap` insert eliminates the `reserve_rehash` storm that dominated
    /// incremental MaxSAT core extraction on million-clause hard formulas
    /// (the `pos_map` was written on every rebuild but never read there).
    track_pos_map: bool,
}

impl OccList {
    /// Create a new occurrence list for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        let n = num_vars * 2;
        Self {
            occ: vec![Vec::new(); n],
            pos_map: (0..n).map(|_| PosMap::default()).collect(),
            partner: Vec::new(),
            track_partners: false,
            track_pos_map: true,
        }
    }

    /// Create an occurrence list that maintains ONLY the `occ` vectors, never
    /// the `pos_map` position index. For build-once, `get()`-only consumers
    /// (level-0 garbage collection's `gc_occ`) that never call
    /// `remove_clause`/`contains`/`swap_to_front`/`sort_each_by_key`. Behaves
    /// identically for `add_clause`/`get`/`count`/`clear` while skipping the
    /// per-occurrence `pos_map` `HashMap` inserts (and their `reserve_rehash`
    /// growth) that would otherwise be pure dead work in that path.
    pub(crate) fn new_occ_only(num_vars: usize) -> Self {
        let n = num_vars * 2;
        Self {
            occ: vec![Vec::new(); n],
            // Left empty and never grown: no position lookups are performed.
            pos_map: Vec::new(),
            partner: Vec::new(),
            track_partners: false,
            track_pos_map: false,
        }
    }

    /// Enable binary-partner tracking (factor pass only). Must be called on a
    /// freshly-created occ list BEFORE any `add_clause`, so `partner` is
    /// populated in lockstep. Allocates one partner list per literal slot.
    pub(crate) fn enable_partner_tracking(&mut self) {
        self.track_partners = true;
        self.partner = vec![Vec::new(); self.occ.len()];
    }

    /// Whether binary-partner tracking is active.
    #[inline]
    pub(crate) fn tracks_partners(&self) -> bool {
        self.track_partners
    }

    /// Partner literals parallel to `get(lit)` when tracking is enabled.
    /// Entry `i` is the other literal of `get(lit)[i]`'s clause if that clause
    /// is binary, else [`PARTNER_SENTINEL`]. Empty slice when not tracking.
    #[inline]
    pub(crate) fn partners(&self, lit: Literal) -> &[Literal] {
        let idx = lit.index();
        if idx < self.partner.len() {
            &self.partner[idx]
        } else {
            &[]
        }
    }

    /// Ensure the occurrence list can index literals for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let target = num_vars.saturating_mul(2);
        if self.occ.len() < target {
            self.occ.resize_with(target, Vec::new);
        }
        if self.track_pos_map {
            while self.pos_map.len() < target {
                self.pos_map.push(PosMap::default());
            }
        }
        if self.track_partners {
            // Keep `partner` length equal to `occ` length (both index literal
            // slots) so tracked lists stay positionally aligned.
            self.partner.resize_with(self.occ.len(), Vec::new);
        }
    }

    /// Add a clause to occurrence lists for all its literals.
    /// Grow every parallel array so literal index `idx` is addressable.
    ///
    /// Kept out of line: it fires once per literal-space extension, never on the
    /// steady-state `add_clause` path.
    #[cold]
    #[inline(never)]
    fn grow_to_literal(&mut self, idx: usize) {
        let target = idx + 1;
        self.occ.resize_with(target, Vec::new);
        if self.track_pos_map {
            while self.pos_map.len() < target {
                self.pos_map.push(PosMap::default());
            }
        }
        if self.track_partners {
            self.partner.resize_with(self.occ.len(), Vec::new);
        }
    }

    pub(crate) fn add_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        let track = self.track_partners;
        let is_binary = literals.len() == 2;
        for (i, &lit) in literals.iter().enumerate() {
            let idx = lit.index();
            // Grow to cover this literal. Previously an out-of-range literal was
            // SILENTLY DROPPED, which made the occurrence list quietly wrong
            // whenever it had not been pre-sized — a latent hazard, and the
            // thing that forced every engine to allocate `2 * num_vars` slots at
            // solver construction (128 resident bytes per variable each, paid on
            // every instance whether or not the engine ever runs). Self-sizing
            // here lets those allocations be lazy without any caller having to
            // remember `ensure_num_vars`.
            if idx >= self.occ.len() {
                self.grow_to_literal(idx);
            }
            {
                let pos = self.occ[idx].len();
                self.occ[idx].push(clause_idx);
                if self.track_pos_map {
                    self.pos_map[idx].insert(clause_idx, pos);
                }
                if track {
                    // Store the other literal for binaries (partner scan reads
                    // it inline); sentinel for larger clauses keeps positions
                    // aligned with `occ[idx]` for O(1) `swap_remove`.
                    let p = if is_binary {
                        literals[1 - i]
                    } else {
                        PARTNER_SENTINEL
                    };
                    debug_assert_eq!(self.partner[idx].len(), pos);
                    self.partner[idx].push(p);
                }
            }
        }
    }

    /// Remove a clause from occurrence lists for all its literals.
    ///
    /// O(L) where L = clause length. Each per-literal removal is O(1) via
    /// position map lookup + `swap_remove` + map update for the moved element.
    /// Previously O(L * max_occ) due to `iter().position()` linear scan (#3036).
    pub(crate) fn remove_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        debug_assert!(
            self.track_pos_map,
            "remove_clause requires the pos_map index (not built for occ-only lists)"
        );
        let track = self.track_partners;
        for &lit in literals {
            let idx = lit.index();
            if idx < self.occ.len() {
                if let Some(pos) = self.pos_map[idx].remove(&clause_idx) {
                    let last = self.occ[idx].len() - 1;
                    if pos < last {
                        // swap_remove moves the last element into `pos`.
                        // Update the moved element's position in the map first.
                        let moved_clause = self.occ[idx][last];
                        self.pos_map[idx].insert(moved_clause, pos);
                    }
                    self.occ[idx].swap_remove(pos);
                    if track {
                        // Mirror the swap_remove at the same position to keep
                        // `partner[idx]` aligned with `occ[idx]`.
                        self.partner[idx].swap_remove(pos);
                    }
                }
            }
        }
    }

    /// Get clause indices containing a literal.
    pub(crate) fn get(&self, lit: Literal) -> &[usize] {
        let idx = lit.index();
        if idx < self.occ.len() {
            &self.occ[idx]
        } else {
            &[]
        }
    }

    /// Return whether the occurrence list for `lit` contains `clause_idx`.
    pub(crate) fn contains(&self, lit: Literal, clause_idx: usize) -> bool {
        debug_assert!(
            self.track_pos_map,
            "contains requires the pos_map index (not built for occ-only lists)"
        );
        let idx = lit.index();
        idx < self.pos_map.len() && self.pos_map[idx].contains_key(&clause_idx)
    }

    /// Get number of clauses containing a literal.
    pub(crate) fn count(&self, lit: Literal) -> usize {
        self.get(lit).len()
    }

    /// Swap the element at `pos` to the front of the occurrence list for `lit`.
    ///
    /// Used by CCE's CLA move-to-front heuristic: when a clause kills the
    /// intersection early, move it to front so future iterations abort faster.
    /// CaDiCaL cover.cpp:286-292.
    pub(crate) fn swap_to_front(&mut self, lit: Literal, pos: usize) {
        debug_assert!(
            !self.track_partners,
            "swap_to_front would desync the parallel partner array"
        );
        debug_assert!(
            self.track_pos_map,
            "swap_to_front requires the pos_map index (not built for occ-only lists)"
        );
        let idx = lit.index();
        if idx < self.occ.len() && pos > 0 && pos < self.occ[idx].len() {
            let clause_at_0 = self.occ[idx][0];
            let clause_at_pos = self.occ[idx][pos];
            self.occ[idx].swap(0, pos);
            self.pos_map[idx].insert(clause_at_0, pos);
            self.pos_map[idx].insert(clause_at_pos, 0);
        }
    }

    /// Sort each non-empty occurrence list using a caller-provided key function.
    ///
    /// Used by CCE to sort occurrence lists by clause size ascending
    /// so that CLA intersects smaller clauses first (CaDiCaL cover.cpp:608).
    pub(crate) fn sort_each_by_key<F>(&mut self, key_fn: F)
    where
        F: Fn(usize) -> usize,
    {
        debug_assert!(
            !self.track_partners,
            "sort_each_by_key would desync the parallel partner array"
        );
        debug_assert!(
            self.track_pos_map,
            "sort_each_by_key requires the pos_map index (not built for occ-only lists)"
        );
        for (lit_idx, list) in self.occ.iter_mut().enumerate() {
            if list.len() > 1 {
                list.sort_unstable_by_key(|&clause_idx| key_fn(clause_idx));
                // Rebuild position map for this literal after sorting.
                let map = &mut self.pos_map[lit_idx];
                map.clear();
                for (pos, &clause_idx) in list.iter().enumerate() {
                    map.insert(clause_idx, pos);
                }
            }
        }
    }

    /// Number of literal slots (occ.len()). Used for capacity checks.
    pub(crate) fn capacity(&self) -> usize {
        self.occ.len()
    }

    /// Deep-copy another OccList's data into this one, rebuilding position maps.
    ///
    /// Used by BCE's `adopt_occ_list` to clone BVE's occ lists without exposing
    /// internal position map fields.
    pub(crate) fn clone_from_other(&mut self, other: &Self) {
        debug_assert!(
            !self.track_partners && !other.track_partners,
            "clone_from_other does not carry the parallel partner array"
        );
        debug_assert!(
            self.track_pos_map,
            "clone_from_other rebuilds the pos_map index (not valid for occ-only lists)"
        );
        self.occ.clear();
        self.occ.resize_with(other.occ.len(), Vec::new);
        self.pos_map.clear();
        self.pos_map.resize_with(other.occ.len(), PosMap::default);
        for (lit_idx, (dst, src)) in self.occ.iter_mut().zip(other.occ.iter()).enumerate() {
            dst.clear();
            dst.extend_from_slice(src);
            // Rebuild position map from the copied vec.
            let map = &mut self.pos_map[lit_idx];
            map.clear();
            for (pos, &clause_idx) in dst.iter().enumerate() {
                map.insert(clause_idx, pos);
            }
        }
    }

    /// Clear all occurrence lists.
    pub(crate) fn clear(&mut self) {
        for list in &mut self.occ {
            list.clear();
        }
        for map in &mut self.pos_map {
            map.clear();
        }
        if self.track_partners {
            for list in &mut self.partner {
                list.clear();
            }
        }
    }
}

#[cfg(test)]
#[path = "occ_list_tests.rs"]
mod tests;
