// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array theory ROW2 propagation implementation.
//!
//! Propagates `select(store(a, i, v), j) = select(a, j)` when `i ≠ j`.
//! Extracted from `theory_impl.rs` to keep each file under 500 lines.
//!
//! # Dirty-entry incremental scanning
//!
//! The scan over `eq_select_entries_sorted` is a pure function of
//! (a) the structural caches (`select_cache` / `store_cache` /
//! `eq_pair_index` / the entry list itself), (b) the equality graph edges
//! consulted at each entry's `lhs` / `rhs` / view-array terms, and (c) the
//! assignment values of the entry atom and every index/array equality atom
//! probed along the (short-circuiting) evaluation path. A full rescan on
//! every BCP quiescence recomputed all of that per call — measured at 4.6M
//! entry visits / 33M view iterations to produce 908 propagations on a
//! single QF_AX swap file (>99.9% redundant).
//!
//! Instead, each entry derivation records the exact terms/atoms it read —
//! together with a wake mask describing which state transitions could change
//! its outcome — into a reverse watch index. Assignments and eq-graph edge
//! changes wake only the entries whose masks match; everything else is
//! skipped. Correctness of the short-circuit dependency set: the evaluation
//! outcome is determined by the values read along the evaluated prefix — a
//! change to a value that was never read (or a transition outside the mask)
//! cannot alter which probe fails/succeeds first, so the outcome (and any
//! emitted reason) is unchanged. Structural changes (new terms/atoms, cache
//! rebuilds, external injections, pops) conservatively mark ALL entries
//! dirty. A `cfg(debug_assertions)` oracle re-derives the full scan after
//! every incremental scan and asserts nothing was missed.
//!
//! Missing a wake would be a COMPLETENESS hazard (fewer theory propagations,
//! more search), never a soundness one: emitted propagations always carry
//! freshly derived reasons, and `check`/`final_check` remain the deciders.

use super::*;

const SENT_PROPAGATIONS_SOFT_CAP: usize = 16_384;

/// Growth cap for the ROW2 watch index. Registrations only grow when an
/// entry's dependency sequence actually changes between derivations; past
/// this bound the next scan goes full and rebuilds the index from scratch.
const ROW2_WATCH_REGISTRATION_CAP: usize = 1 << 18;

/// Wake when the watched atom is newly assigned `true`.
const WAKE_ON_TRUE: u8 = 1;
/// Wake when the watched atom is newly assigned `false`.
const WAKE_ON_FALSE: u8 = 2;
/// Wake when an eq-graph edge incident to the watched term is
/// added/removed/relabeled (select/store view sources).
const WAKE_ON_EDGE: u8 = 4;

/// Result of deriving ROW2 propagations for a set of entries (read-only).
struct Row2ScanOutcome {
    /// Propagations derived, in ascending scan order (pre-dedup).
    propagations: Vec<TheoryPropagation>,
    /// Flat per-entry dependency records: `(term, wake mask)` runs delimited
    /// by `entry_ranges`.
    watch_buf: Vec<(TermId, u8)>,
    /// `(entry index, start, end)` slices of `watch_buf` per processed entry.
    entry_ranges: Vec<(u32, u32, u32)>,
    /// Entries visited (diagnostics).
    entry_visits: u64,
    /// Inner view-triple iterations (diagnostics).
    view_iters: u64,
    /// `Some(pos)` if the external interrupt flag stopped the scan before
    /// processing position `pos` of the scan order.
    interrupted_at: Option<usize>,
}

impl ArraySolver<'_> {
    /// Mark every ROW2 entry dirty (structural or bulk state change).
    pub(crate) fn row2_mark_all_dirty(&mut self) {
        self.row2_all_dirty = true;
    }

    /// Structural invalidation: the entry list itself was rebuilt, so entry
    /// indices (and therefore the watch index) are meaningless.
    pub(crate) fn row2_invalidate_entries(&mut self) {
        self.row2_all_dirty = true;
        self.row2_watch.clear();
        self.row2_watch_registrations = 0;
        self.row2_dirty_entries.clear();
        self.row2_entry_is_dirty.clear();
        self.row2_entry_watches.clear();
    }

    /// Wake ROW2 entries for a fresh `term := value` assignment.
    pub(crate) fn row2_wake_assign(&mut self, term: TermId, value: bool) {
        let bit = if value { WAKE_ON_TRUE } else { WAKE_ON_FALSE };
        self.row2_wake(term, bit);
    }

    /// Wake ROW2 entries for an eq-graph edge change incident to `term`.
    pub(crate) fn row2_wake_edge_term(&mut self, term: TermId) {
        self.row2_wake(term, WAKE_ON_EDGE);
    }

    fn row2_wake(&mut self, term: TermId, bit: u8) {
        if self.row2_all_dirty {
            return;
        }
        let Some(watchers) = self.row2_watch.get(&term) else {
            return;
        };
        for &(idx, mask) in watchers {
            if mask & bit == 0 {
                continue;
            }
            if let Some(flag) = self.row2_entry_is_dirty.get_mut(idx as usize) {
                if !*flag {
                    *flag = true;
                    self.row2_dirty_entries.push(idx);
                }
            }
        }
    }

    /// ROW2 propagation: `i ≠ j → select(store(a, i, v), j) = select(a, j)`.
    ///
    /// Scans equality terms for unassigned `(= select_a select_b)` atoms where
    /// one side reads through a store with a provably different index.
    pub(crate) fn propagate_impl(&mut self) -> Vec<TheoryPropagation> {
        // #8615: Early exit if the external interrupt flag is set.
        if self.is_interrupted() {
            return Vec::new();
        }

        self.populate_caches();

        // No-change fast path: every input this scan reads is covered by
        // `propagate_state_version` (assignments, eq-graph edges, external
        // (dis)equalities + reasons, cache rebuilds — populate_caches above
        // bumps on any rebuild, which also covers new interned terms for the
        // `find_eq` lookups in singleton-support). With unchanged inputs the
        // recomputation below is deterministic and every propagation it
        // produces is already in `sent_propagations` from the last completed
        // scan — the dedup at the end would return the empty set. Skipping
        // the O(eq_atoms × views) rescan per quiescent BCP round was
        // measured as a top cost block on the QF_AX swap family.
        if self.last_full_scan_version == Some(self.propagate_state_version) {
            return Vec::new();
        }

        // #8605: Cap sent_propagations to prevent unbounded heap growth within
        // a single scope. Each entry is (TheoryLit, Vec<TheoryLit>) with a
        // heap-allocated reason vector. Clearing is safe: re-emitting a
        // propagation the DPLL(T) layer already knows is a no-op.
        if self.sent_propagations.len() > SENT_PROPAGATIONS_SOFT_CAP {
            self.sent_propagations.clear();
            self.sent_propagations.shrink_to_fit();
            // Parity with the historical full-rescan behavior: after the dedup
            // memory is dropped, the next scan re-derives (and re-emits)
            // everything instead of silently skipping clean entries.
            self.row2_all_dirty = true;
        }

        let entries_len = self.eq_select_entries_sorted.len();
        // Defensive: a stale flag vector means the entry list changed shape
        // without passing through row2_invalidate_entries().
        if self.row2_entry_is_dirty.len() != entries_len
            || self.row2_entry_watches.len() != entries_len
        {
            self.row2_all_dirty = true;
        }
        if self.row2_watch_registrations > ROW2_WATCH_REGISTRATION_CAP {
            self.row2_all_dirty = true;
        }

        let full_scan = self.row2_all_dirty;
        let mut dirty_list: Vec<u32> = Vec::new();
        if full_scan {
            // The watch index is rebuilt from scratch by a full scan; drop
            // stale registrations now.
            self.row2_watch.clear();
            self.row2_watch_registrations = 0;
            self.row2_dirty_entries.clear();
            self.row2_entry_is_dirty.clear();
            self.row2_entry_is_dirty.resize(entries_len, false);
            self.row2_entry_watches.clear();
            self.row2_entry_watches.resize(entries_len, Vec::new());
        } else {
            dirty_list = std::mem::take(&mut self.row2_dirty_entries);
            dirty_list.sort_unstable();
            dirty_list.dedup();
            dirty_list.retain(|&idx| (idx as usize) < entries_len);
            // Clear flags up front; no wakes can occur mid-scan (the scan
            // itself never mutates assignments or the eq graph).
            for &idx in &dirty_list {
                self.row2_entry_is_dirty[idx as usize] = false;
            }
        }

        let outcome = self.derive_row2_entries(if full_scan { None } else { Some(&dirty_list) });

        // Mandatory dirty-entry completeness oracle (debug builds): the
        // incremental scan must never miss a propagation the full scan would
        // have produced. Anything the full derivation finds must either have
        // been sent already (clean entry, unchanged dependency prefix) or be
        // part of this scan's output.
        #[cfg(debug_assertions)]
        if !full_scan && outcome.interrupted_at.is_none() && !self.is_interrupted() {
            let full = self.derive_row2_entries(None);
            if full.interrupted_at.is_none() {
                for p in &full.propagations {
                    let sig = (p.literal, p.reason.clone());
                    debug_assert!(
                        self.sent_propagations.contains(&sig)
                            || outcome
                                .propagations
                                .iter()
                                .any(|q| q.literal == p.literal && q.reason == p.reason),
                        "arrays ROW2 dirty-entry scan missed a propagation: {:?} <- {:?}",
                        p.literal,
                        p.reason
                    );
                }
            }
        }

        // Interrupt handling: unprocessed entries must stay dirty so a
        // same-version rescan still produces their propagations.
        match outcome.interrupted_at {
            Some(pos) => {
                if !full_scan {
                    for &idx in &dirty_list[pos..] {
                        if !self.row2_entry_is_dirty[idx as usize] {
                            self.row2_entry_is_dirty[idx as usize] = true;
                            self.row2_dirty_entries.push(idx);
                        }
                    }
                }
                // A full scan interrupted mid-way keeps row2_all_dirty set.
            }
            None => {
                if full_scan {
                    self.row2_all_dirty = false;
                }
            }
        }

        // Register watch sets for every processed entry whose dependency
        // sequence changed since its last derivation. Old registrations stay
        // behind as stale (they can only cause spurious wakes) and are culled
        // by the next full-scan rebuild.
        for &(idx, start, end) in &outcome.entry_ranges {
            let slice = &outcome.watch_buf[start as usize..end as usize];
            // `row2_entry_watches[idx]` is the UNION of everything this entry
            // has ever registered (sorted by term). Only genuinely new
            // (term, bit) sensitivities are registered, so watch lists are
            // bounded by distinct (entry, term, bit) triples — re-derivations
            // of an unchanged dependency prefix register nothing. Watching a
            // superset of the current dependency set is safe: extra wakes are
            // spurious re-derivations, never missed ones.
            let stored = &mut self.row2_entry_watches[idx as usize];
            for &(t, m) in slice {
                if m == 0 {
                    continue;
                }
                match stored.binary_search_by_key(&t.0, |e| e.0 .0) {
                    Ok(i) => {
                        let new_bits = m & !stored[i].1;
                        if new_bits != 0 {
                            stored[i].1 |= new_bits;
                            self.row2_watch_registrations += 1;
                            self.row2_watch.entry(t).or_default().push((idx, new_bits));
                        }
                    }
                    Err(i) => {
                        stored.insert(i, (t, m));
                        self.row2_watch_registrations += 1;
                        self.row2_watch.entry(t).or_default().push((idx, m));
                    }
                }
            }
        }

        // Emission order parity: singleton-support propagations first, then
        // entry propagations in ascending scan order — the exact order the
        // historical single-pass scan produced (#3060 determinism).
        let mut propagations = self.singleton_support_propagations();
        propagations.extend(outcome.propagations);

        self.scan_count += 1;
        self.scan_entry_visits += outcome.entry_visits;
        self.scan_view_iters += outcome.view_iters;

        let mut deduped = Vec::with_capacity(propagations.len());
        for propagation in propagations {
            let TheoryPropagation {
                literal,
                reason,
                reason_data,
            } = propagation;
            let sig = (literal, reason);
            if self.sent_propagations.contains(&sig) {
                continue;
            }
            deduped.push(TheoryPropagation {
                literal,
                reason: sig.1.clone(),
                reason_data,
            });
            self.sent_propagations.insert(sig);
        }

        // Arm the no-change fast path only after an UNINTERRUPTED scan — an
        // interrupted scan may have skipped propagations that a same-version
        // rescan must still produce.
        if !self.is_interrupted() {
            self.last_full_scan_version = Some(self.propagate_state_version);
        }

        self.propagation_count += deduped.len() as u64;
        deduped
    }

    /// Derive ROW2 propagations for the given entry indices (`None` = every
    /// entry), recording each processed entry's dependency set. Read-only:
    /// the scan is a pure function of the solver state, which is what makes
    /// the dirty-entry memoization and the debug oracle sound.
    fn derive_row2_entries(&self, scan_indices: Option<&[u32]>) -> Row2ScanOutcome {
        #[derive(Clone)]
        struct SelectView {
            array: TermId,
            index: TermId,
            reason: Vec<TheoryLit>,
        }

        #[derive(Clone)]
        struct StoreView {
            base_array: TermId,
            store_index: TermId,
            reason: Vec<TheoryLit>,
        }

        let mut outcome = Row2ScanOutcome {
            propagations: Vec::new(),
            watch_buf: Vec::new(),
            entry_ranges: Vec::new(),
            entry_visits: 0,
            view_iters: 0,
            interrupted_at: None,
        };

        // Use pre-built indices (eq_pair_index and eq_adj) instead of
        // rebuilding per call.
        //
        // Probe-first discipline: these predicates return the required reason
        // literal (if any) WITHOUT touching a reason vector, so the hot triple
        // loop below only allocates when a triple actually succeeds. Every
        // equality atom a probe consults is pushed into `deps` with the wake
        // mask for exactly the transitions that could flip the probe's branch
        // (see module docs). Probes on pairs with NO interned atom depend on
        // atom creation, which structurally invalidates all entries.
        //
        // Outcome encoding: `None` = probe failed; `Some(None)` = holds
        // tautologically (no reason lit); `Some(Some(lit))` = holds under lit.
        let require_equal =
            |deps: &mut Vec<(TermId, u8)>, t1: TermId, t2: TermId| -> Option<Option<TheoryLit>> {
                if t1 == t2 {
                    return Some(None);
                }
                let key = Self::ordered_pair(t1, t2);
                if let Some(&eq_term) = self.eq_pair_index.get(&key) {
                    if self.assigns.get(&eq_term) == Some(&true) {
                        // Success under `eq_term = true`: only losing that
                        // assignment changes the branch.
                        deps.push((eq_term, WAKE_ON_FALSE));
                        return Some(Some(TheoryLit::new(eq_term, true)));
                    }
                    // Failure (unassigned or false): only `-> true` flips it.
                    deps.push((eq_term, WAKE_ON_TRUE));
                }
                None
            };

        let require_distinct =
            |deps: &mut Vec<(TermId, u8)>, t1: TermId, t2: TermId| -> Option<Option<TheoryLit>> {
                if t1 == t2 {
                    return None;
                }
                let key = Self::ordered_pair(t1, t2);
                if let Some(&eq_term) = self.eq_pair_index.get(&key) {
                    if self.assigns.get(&eq_term) == Some(&false) {
                        // Success under `eq_term = false`: only leaving false
                        // changes branch/reason.
                        deps.push((eq_term, WAKE_ON_TRUE));
                        return Some(Some(TheoryLit::new(eq_term, false)));
                    }
                    // Not-false (unassigned or true): a `-> false` transition
                    // switches to the reason-carrying branch.
                    deps.push((eq_term, WAKE_ON_FALSE));
                }
                // Tautological: distinct constants or affine offsets (#5086).
                let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
                let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
                if t1_is_const && t2_is_const && t1 != t2 {
                    return Some(None);
                }
                // O(1) tautological affine offset (i vs i+1)
                if self.distinct_by_affine_offset(t1, t2) {
                    return Some(None);
                }
                // Do NOT fall through to diseq_set: external disequalities have
                // no reason terms and would produce incomplete justifications
                // (#5086).
                None
            };

        let select_views_for = |term: TermId| -> Vec<SelectView> {
            let mut views = Vec::new();

            if let Some(&(array, index)) = self.select_cache.get(&term) {
                views.push(SelectView {
                    array,
                    index,
                    reason: Vec::new(),
                });
            }

            if let Some(neighbors) = self.eq_adj.get(&term) {
                for &(other, eq_term) in neighbors {
                    if let Some(&(array, index)) = self.select_cache.get(&other) {
                        let reason = if eq_term.is_sentinel() {
                            Vec::new()
                        } else {
                            vec![TheoryLit::new(eq_term, true)]
                        };
                        views.push(SelectView {
                            array,
                            index,
                            reason,
                        });
                    }
                }
            }

            views
        };

        let store_views_for = |array_term: TermId| -> Vec<StoreView> {
            let mut views = Vec::new();

            if let Some(&(base_array, store_index, _store_value)) =
                self.store_cache.get(&array_term)
            {
                views.push(StoreView {
                    base_array,
                    store_index,
                    reason: Vec::new(),
                });
            }

            if let Some(neighbors) = self.eq_adj.get(&array_term) {
                for &(other, eq_term) in neighbors {
                    if let Some(&(base_array, store_index, _store_value)) =
                        self.store_cache.get(&other)
                    {
                        let reason = if eq_term.is_sentinel() {
                            Vec::new()
                        } else {
                            vec![TheoryLit::new(eq_term, true)]
                        };
                        views.push(StoreView {
                            base_array,
                            store_index,
                            reason,
                        });
                    }
                }
            }

            views
        };

        let mut select_views_cache: HashMap<TermId, Vec<SelectView>> = HashMap::default();
        let mut store_views_cache: HashMap<TermId, Vec<StoreView>> = HashMap::default();

        // Per-entry dependency scratch: every term/atom whose state the
        // entry's evaluation prefix read, with its wake mask. Flushed into
        // `watch_buf`/`entry_ranges` after each entry.
        let mut deps: Vec<(TermId, u8)> = Vec::new();

        // ROW2 propagation (read-over-write different index):
        // i ≠ j → select(store(a, i, v), j) = select(a, j)
        // Deterministic propagation order (#3060): eq_select_entries_sorted
        // is maintained sorted by eq term id in populate_caches() — the same
        // order the per-call collect+sort previously produced here, minus
        // atoms that provably yield zero select views (see field docs).
        let total = scan_indices.map_or(self.eq_select_entries_sorted.len(), <[u32]>::len);
        for pos in 0..total {
            // #8615: Check interrupt in ROW2 propagation loop — this iterates
            // equality_cache × select_views × store_views which can be very
            // expensive on seq push_back chains with many array terms.
            if self.is_interrupted() {
                outcome.interrupted_at = Some(pos);
                break;
            }

            let entry_idx = scan_indices.map_or(pos, |s| s[pos] as usize);
            let (eq_term, lhs, rhs) = self.eq_select_entries_sorted[entry_idx];
            outcome.entry_visits += 1;
            deps.clear();

            if self.assigns.get(&eq_term) == Some(&true) {
                // Skipped while true: only leaving `true` needs a re-derive.
                deps.push((eq_term, WAKE_ON_FALSE));
                let start = outcome.watch_buf.len() as u32;
                outcome.watch_buf.extend_from_slice(&deps);
                outcome.entry_ranges.push((
                    entry_idx as u32,
                    start,
                    outcome.watch_buf.len() as u32,
                ));
                continue;
            }

            // Not currently true: the skip condition cannot start holding
            // without a `-> true` assignment, which never changes this
            // entry's derived output (it only makes it moot), so the entry
            // atom itself needs no wake bits here. Probes that read this
            // atom's value register their own dependencies below.
            //
            // View construction reads the eq-graph adjacency at lhs/rhs (and
            // below at each view's array term).
            deps.push((lhs, WAKE_ON_EDGE));
            deps.push((rhs, WAKE_ON_EDGE));

            if !select_views_cache.contains_key(&lhs) {
                select_views_cache.insert(lhs, select_views_for(lhs));
            }
            if !select_views_cache.contains_key(&rhs) {
                select_views_cache.insert(rhs, select_views_for(rhs));
            }
            let lhs_views = select_views_cache
                .get(&lhs)
                .expect("invariant: lhs select views inserted above");
            let rhs_views = select_views_cache
                .get(&rhs)
                .expect("invariant: rhs select views inserted above");

            // On success, build the reason set: view reasons + probe lits.
            // The final `sort + dedup` canonicalizes order, so probe
            // reordering below cannot change the emitted reason set.
            let emit = |propagations: &mut Vec<TheoryPropagation>,
                        view_reasons: [&[TheoryLit]; 3],
                        probe_lits: [Option<TheoryLit>; 3]| {
                let mut reasons: Vec<TheoryLit> =
                    Vec::with_capacity(view_reasons.iter().map(|r| r.len()).sum::<usize>() + 3);
                for chunk in view_reasons {
                    reasons.extend_from_slice(chunk);
                }
                reasons.extend(probe_lits.into_iter().flatten());
                reasons.retain(|lit| lit.term != eq_term);
                // Skip propagations with no antecedents.
                if reasons.is_empty() {
                    return;
                }
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                propagations.push(TheoryPropagation {
                    literal: TheoryLit::new(eq_term, true),
                    reason: reasons,
                    reason_data: None,
                });
            };

            let mut did_propagate = false;

            for lv in lhs_views {
                deps.push((lv.array, WAKE_ON_EDGE));
                if !store_views_cache.contains_key(&lv.array) {
                    store_views_cache.insert(lv.array, store_views_for(lv.array));
                }
                let store_views = store_views_cache
                    .get(&lv.array)
                    .expect("invariant: lhs store views inserted above");
                for store_view in store_views {
                    // Hoisted rv-independent probe: same conjunction as the
                    // per-triple check, evaluated once per (lv, store_view).
                    let Some(distinct_lit) =
                        require_distinct(&mut deps, lv.index, store_view.store_index)
                    else {
                        continue;
                    };
                    for rv in rhs_views {
                        outcome.view_iters += 1;
                        let Some(index_eq_lit) = require_equal(&mut deps, lv.index, rv.index)
                        else {
                            continue;
                        };
                        let Some(array_eq_lit) =
                            require_equal(&mut deps, rv.array, store_view.base_array)
                        else {
                            continue;
                        };

                        emit(
                            &mut outcome.propagations,
                            [&lv.reason, &rv.reason, &store_view.reason],
                            [index_eq_lit, array_eq_lit, distinct_lit],
                        );
                        did_propagate = true;
                        break;
                    }
                    if did_propagate {
                        break;
                    }
                }
                if did_propagate {
                    break;
                }
            }

            if !did_propagate {
                for rv in rhs_views {
                    deps.push((rv.array, WAKE_ON_EDGE));
                    if !store_views_cache.contains_key(&rv.array) {
                        store_views_cache.insert(rv.array, store_views_for(rv.array));
                    }
                    let store_views = store_views_cache
                        .get(&rv.array)
                        .expect("invariant: rhs store views inserted above");
                    for store_view in store_views {
                        let Some(distinct_lit) =
                            require_distinct(&mut deps, rv.index, store_view.store_index)
                        else {
                            continue;
                        };
                        for lv in lhs_views {
                            outcome.view_iters += 1;
                            let Some(index_eq_lit) = require_equal(&mut deps, lv.index, rv.index)
                            else {
                                continue;
                            };
                            let Some(array_eq_lit) =
                                require_equal(&mut deps, lv.array, store_view.base_array)
                            else {
                                continue;
                            };

                            emit(
                                &mut outcome.propagations,
                                [&lv.reason, &rv.reason, &store_view.reason],
                                [index_eq_lit, array_eq_lit, distinct_lit],
                            );
                            did_propagate = true;
                            break;
                        }
                        if did_propagate {
                            break;
                        }
                    }
                    if did_propagate {
                        break;
                    }
                }
            }

            let start = outcome.watch_buf.len() as u32;
            outcome.watch_buf.extend_from_slice(&deps);
            outcome
                .entry_ranges
                .push((entry_idx as u32, start, outcome.watch_buf.len() as u32));
        }

        outcome
    }
}
