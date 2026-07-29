// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF theory propagation helpers for `TheorySolver::propagate()`.
//!
//! Positive equality propagation and disequality propagation, extracted
//! from `theory_impl.rs` to keep each file under 500 lines.

use ay_core::safe_eprintln;
use ay_core::term::TermId;
use ay_core::TheoryLit;
use ay_core::TheoryPropagation;

use crate::solver::EufSolver;
use crate::types::UndoRecord;

/// #cong-neg-backoff: minimum `func_apps` before the adaptive backoff can
/// engage. Small/medium problems stay on the legacy always-on path (their
/// `cong_neg_barren` never approaches the cap), so their propagations — and
/// therefore decision trajectories — are byte-identical to before this change.
/// Matches the pop-undo campaigns' size gate.
pub(crate) const CONG_NEG_SIZE_GATE: usize = 16_384;
/// #cong-neg-backoff: consecutive NON-firing full lookahead runs (memo misses
/// that returned `None`) that suspend the cascade lookahead. On the giant
/// diseq-dense Certora QF_UFLIA files the cascade fires on ~1 in 15,000 runs
/// (measured: 8237 fires in 128M runs on _27) while costing ~half the CDCL
/// search loop; suspending after a long barren streak ~doubles decision
/// throughput. The counter RESETS on every fire, so a workload that uses the
/// lookahead productively (QG-classification / NEQ QF_UF, where it fires
/// frequently) never accumulates a barren streak this long and is unaffected.
pub(crate) const CONG_NEG_BARREN_CAP: u32 = 200_000;
/// #cong-neg-cold: barren cap for a solve in which the lookahead has NEVER
/// fired. Far tighter than `CONG_NEG_BARREN_CAP` because a never-fired solve has
/// shown no evidence the lookahead pays, and the counter is reset (and this cap
/// abandoned for the generous one) the instant it does fire. Sized to absorb a
/// short warm-up without letting a barren workload pay the full 2x.
pub(crate) const CONG_NEG_COLD_CAP: u32 = 1_000;
/// #cong-neg-backoff: while suspended, run 1 full lookahead in this many as a
/// re-probe. If a probe fires, the lookahead un-suspends (a firing PHASE that
/// begins after a barren warmup recovers). The overhead while suspended is
/// negligible (one full run per 200k skips).
pub(crate) const CONG_NEG_REPROBE: u32 = 200_000;

// ============================================================================
// Lazy propagation justification tokens (#8467 protocol, #euf-lazy-explain)
// ============================================================================
// `reason_data` layout for EUF lazy propagations. Bit 63 is deliberately SET:
// the LRA/LIA lazy decoder claims bit63=1 as its own "interval" encoding and
// immediately returns `None` for it (see `LraSolver::explain_propagation_inner`),
// so when a `TheoryCombiner` broadcasts `explain_propagation` to every
// sub-solver (LIA first, EUF last), an EUF token can never be mis-claimed and
// turned into a bogus arithmetic reason. The magic in the high 32 bits
// distinguishes EUF tokens from any other bit63=1 producer; EUF returns `None`
// for anything without its magic.
//
// The token carries no per-propagation table index: everything needed to
// re-derive the reason is recoverable at materialization time from the
// propagated atom itself (`decode_eq`) plus, for negative propagations, the
// `lazy_neg_witness` side map — so no unbounded per-solve token log exists and
// tokens never dangle across pops (they self-validate against the live
// e-graph instead).

/// High-32-bit magic identifying an EUF lazy justification token.
/// `pub` (re-exported from the crate root) so the eager SAT extension can
/// recognize EUF tokens when applying EUF-specific delivery policy (the
/// ITE-guarded materialize-at-delivery carve-out) without perturbing other
/// theories' lazy propagations.
pub const EUF_LAZY_MAGIC: u64 = 0xEF1A_C0DE_0000_0000;
/// Mask isolating the magic bits of an EUF lazy justification token.
pub const EUF_LAZY_MAGIC_MASK: u64 = 0xFFFF_FFFF_0000_0000;
/// Kind tag: positive equality propagation (`(= a b) := true` because
/// `find(a) == find(b)`); reason = `explain(a, b)` re-derived on demand.
pub(crate) const EUF_LAZY_KIND_POS: u64 = 1;
/// Kind tag: disequality propagation (`(= c d) := false` because an asserted
/// disequality `(= a b) := false` connects their classes); reason = the diseq
/// literal + `explain(c, a·) + explain(d, b·)` re-derived on demand from the
/// witness captured in `lazy_neg_witness`.
pub(crate) const EUF_LAZY_KIND_NEG: u64 = 2;
/// Mask isolating the kind bits.
pub(crate) const EUF_LAZY_KIND_MASK: u64 = 0xF;

/// A simulated-merge edge for emit-time reason reconstruction
/// (#cong-neg-prop): connects the live classes of terms `a` and `b`. The
/// hypothesis edge is the candidate atom's own equality (contributes no
/// reason literal — it is the negated propagated atom); congruence edges are
/// justified by their argument chains, recursively. Edges are only laid
/// between previously-unconnected classes, so the edge set is a forest and
/// paths through it are unique.
#[derive(Clone, Copy)]
struct SimEdge {
    a: u32,
    b: u32,
    hypothesis: bool,
}

impl EufSolver<'_> {
    /// Per-emission gate for LAZY (#8467) justification of the propagation
    /// about to be pushed (#euf-lazy-explain).
    ///
    /// Returns `false` (emit EAGER, materialized reason) when:
    /// - the consumer never opted in via `set_lazy_propagation_supported`
    ///   (legacy `DpllT` loop, verification instances) or the
    ///   `AY_EUF_LAZY_EXPLAIN=0` kill switch is set;
    /// - `AY_EUF_GAP_STATS` profiling is on (`record_emission` needs the
    ///   materialized reason set);
    /// - `AY_DEBUG_EUF` tracing is on (debug lines print reason counts);
    /// - the emission falls in the warmup-then-sample EAGER carve-out: the
    ///   first `WARMUP` emissions per solver and every 64th thereafter stay
    ///   eager so the extension's structural + sampled semantic verification
    ///   gates keep exactly the coverage cadence they apply to eager EUF
    ///   propagations (warmup 512 + 1-in-64, see extension/propagate.rs).
    ///   A lazy emission is never semantically verified at BCP time — its
    ///   soundness backstops are the materialization-time validation gates
    ///   (falsified-on-trail + currently-asserted-reason checks) plus the
    ///   conflict-clause semantic verifier — so keeping the sampling stream
    ///   eager preserves the bug-detector coverage at ~1.6% of the explain()
    ///   cost.
    fn lazy_emit_gate(&mut self) -> bool {
        if !self.lazy_explain_enabled || self.gap_stats_enabled || self.debug_euf {
            return false;
        }
        const WARMUP: u64 = 512;
        self.lazy_emit_counter += 1;
        let n = self.lazy_emit_counter;
        if n <= WARMUP || n.is_multiple_of(64) {
            return false;
        }
        true
    }

    /// Propagate implied equalities: `(= a b) = true` when `find(a) = find(b)`.
    ///
    /// Scans pre-indexed equality terms (`eq_terms`) for unassigned equalities
    /// whose sides are in the same equivalence class, then uses `explain()` to
    /// build minimal propagation reasons.
    pub(crate) fn propagate_positive_equalities(
        &mut self,
        propagations: &mut Vec<TheoryPropagation>,
    ) {
        let debug = self.debug_euf;

        let n_eqs = self.eq_terms.len();
        self.scratch_potential_props.clear();

        if !self.inc_pos_enabled || self.pos_full_scan_needed {
            // FULL scan: (re)build the `class_eqs` index keyed by current
            // representatives and check every equality. Taken on the first call,
            // after a `pop` changed class membership, or when incremental mode is
            // disabled (kill switch). sort(lhs)==sort(rhs) holds by construction
            // (eq_terms is filtered to same-sorted equalities in init_eq_terms).
            self.class_eqs.clear();
            for i in 0..n_eqs {
                let (term_id, lhs, rhs) = self.eq_terms[i];
                let lhs_rep = self.enode_find_const(lhs.0);
                let rhs_rep = self.enode_find_const(rhs.0);
                self.class_eqs.entry(lhs_rep).or_default().push(i);
                if rhs_rep != lhs_rep {
                    self.class_eqs.entry(rhs_rep).or_default().push(i);
                }
                if self.assigns.contains_key(&term_id) {
                    continue;
                }
                if lhs_rep == rhs_rep {
                    self.scratch_potential_props.push((term_id, lhs, rhs));
                }
            }
            self.pos_full_scan_needed = false;
            self.pos_dirty_reps.clear();
        } else {
            // INCREMENTAL scan: an unassigned equality can only newly become
            // congruence-true when one of its endpoints' classes merged. So visit
            // only equalities indexed under a class dirtied since the last scan —
            // `incremental_merge` keeps `class_eqs` and `pos_dirty_reps` current.
            let dirty = std::mem::take(&mut self.pos_dirty_reps);
            let mut seen = std::mem::take(&mut self.scratch_seen_eq_idxs);
            seen.clear();
            let mut idxs = std::mem::take(&mut self.scratch_class_eq_idxs);
            for rep in dirty {
                idxs.clear();
                match self.class_eqs.get(&rep) {
                    Some(v) => idxs.extend_from_slice(v),
                    None => continue,
                }
                for &i in &idxs {
                    if !seen.insert(i) {
                        continue;
                    }
                    let (term_id, lhs, rhs) = self.eq_terms[i];
                    if self.assigns.contains_key(&term_id) {
                        continue;
                    }
                    let lhs_rep = self.enode_find_const(lhs.0);
                    let rhs_rep = self.enode_find_const(rhs.0);
                    if lhs_rep == rhs_rep {
                        self.scratch_potential_props.push((term_id, lhs, rhs));
                    }
                }
            }
            self.scratch_class_eq_idxs = idxs;
            self.scratch_seen_eq_idxs = seen;
        }

        // #euf-emit-batch-memo: one `(a,b)→reasons` cache threaded across every
        // `explain` in this drain. The proof forest is IMMUTABLE for the whole
        // loop (propagation only READS the forest — the closure was rebuilt
        // before `propagate` reached here and nothing below merges), so a cached
        // reason set stays valid across calls and the shared congruence
        // sub-proofs the per-call memo used to re-walk are reused. Taken from
        // `self` to keep capacity; restored after the loop. Sound: see
        // `ExplainMemo` (a nested BFS-fallback `explain` takes the now-empty
        // `self.explain_memo`, never this one).
        let mut pos_memo = std::mem::take(&mut self.explain_memo);
        pos_memo.clear();
        for idx in 0..self.scratch_potential_props.len() {
            let (term_id, lhs, rhs) = self.scratch_potential_props[idx];
            // #euf-lazy-explain (#8467): defer the explain() to conflict
            // analysis. The token carries only the kind tag — at
            // materialization time `explain_lazy_propagation` re-derives
            // (lhs, rhs) via decode_eq, re-checks find(lhs)==find(rhs)
            // against the LIVE e-graph, and re-runs explain(). The proof
            // forest is only unwound by pop(), and the SAT layer always
            // materializes surviving lazy reasons BEFORE the extension pops
            // theory scopes, so the merge that justified this propagation is
            // still present at every materialization; any residual state
            // shift is caught by the validation gates and rejected (sound —
            // the SAT layer demotes the variable to a decision).
            if self.lazy_emit_gate() {
                debug_assert!(
                    !self.assigns.contains_key(&term_id),
                    "BUG: EUF lazy propagate: term {} already assigned (should have been filtered)",
                    term_id.0
                );
                self.lazy_emitted_count += 1;
                propagations.push(TheoryPropagation::lazy(
                    TheoryLit::new(term_id, true),
                    EUF_LAZY_MAGIC | EUF_LAZY_KIND_POS,
                ));
                continue;
            }
            let reasons = self.explain_using_memo(lhs, rhs, &mut pos_memo);
            if debug {
                safe_eprintln!(
                    "[EUF PROPAGATE] Propagating eq {} = true (terms {} == {}) with {} reasons",
                    term_id.0,
                    lhs.0,
                    rhs.0,
                    reasons.len()
                );
            }
            // Skip propagation if explain() returned empty (broken proof forest).
            // An incomplete propagation reason would produce an unsound learned
            // clause — stronger than justified by the actual equality chain. (#6849)
            if reasons.is_empty() {
                continue;
            }
            debug_assert!(
                !self.assigns.contains_key(&term_id),
                "BUG: EUF propagate: term {} already assigned (should have been filtered)",
                term_id.0
            );
            debug_assert!(
                reasons.iter().all(|l| self.assigns.contains_key(&l.term)),
                "BUG: EUF propagate: reason for term {} references unassigned term",
                term_id.0
            );
            if self.gap_stats_enabled {
                self.gap_stats.record_emission(term_id, &reasons, true);
            }
            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(term_id, true),
                reason: reasons,
                reason_data: None,
            });
        }
        // Restore the cache shell (keeps its allocated capacity for next drain).
        self.explain_memo = pos_memo;
    }

    /// Propagate disequalities: `(= c d) = false` when `find(c) != find(d)` and
    /// there exists an asserted `(= a b) = false` with `find(a) = find(c)` and
    /// `find(b) = find(d)` (or symmetric).
    ///
    /// Without this, the SAT solver must guess values that the theory already
    /// knows are false, causing exponential branching on QG-classification
    /// and similar dense UF benchmarks (#5575).
    ///
    /// #inc-neg: two scan modes, mirroring `propagate_positive_equalities`.
    /// The FULL scan (first call, after pop, or kill switch `AY_EUF_INC_NEG=0`)
    /// rebuilds the persistent `diseq_pair_index` from every assignment and
    /// checks every equality. The INCREMENTAL scan processes only (a) negated
    /// equalities asserted since the last scan (`pending_neg_eqs`) and (b)
    /// equalities indexed under a class rep dirtied by a merge
    /// (`neg_dirty_reps` × `class_eqs`, both maintained by `incremental_merge`).
    /// An unassigned equality can only newly match a disequality pair when one
    /// of the two was (re)keyed by exactly those events, so the incremental
    /// scan proposes the same propagations the full scan would. Missing a
    /// propagation is at worst lost SEARCH GUIDANCE — `check()` remains the
    /// conflict/soundness authority — but the full-scan-per-BCP-call this
    /// replaces was the #1 profile leaf on QF_UFLIA model search (hash_sat:
    /// ~220 decisions/s with EufSolver::propagate dominating).
    /// #cong-neg-scan-gate: is the cascade lookahead worth calling AT ALL for this
    /// scan?
    ///
    /// `cong_diseq_lookahead_memo` already returns `None` immediately while the
    /// backoff has it suspended — but not before two `enode_find_const` calls, a
    /// memo hash lookup and (on a miss) a `None` insert. On QF_UF/NEQ that
    /// per-pair bookkeeping is paid millions of times for a lookahead that fires
    /// ZERO times (`euf_cong_neg_propagations = 0`), and once the conflict-verifier
    /// fix removed its competitor it became the largest frame in the profile at
    /// 37% self time.
    ///
    /// Skipping at the CALL SITE removes that cost entirely. The re-probe counter
    /// advances ONCE PER SCAN rather than once per pair — the crucial difference
    /// from an earlier attempt that hoisted this test inside the memo, which
    /// advanced per pair, re-probed far more often, and cost 2 division answers.
    /// Per-scan advancement keeps periodic re-probing (a workload that starts
    /// firing later still recovers) while making the barren case free.
    fn cong_neg_scan_suspended(&mut self) -> bool {
        let adaptive = self.cong_neg_adaptive
            && (self.func_apps.len() >= CONG_NEG_SIZE_GATE || !self.cong_neg_ever_fired);
        if !adaptive || !self.cong_neg_suspended {
            return false;
        }
        self.cong_neg_probe_skip = self.cong_neg_probe_skip.saturating_add(1);
        if self.cong_neg_probe_skip < CONG_NEG_REPROBE {
            return true;
        }
        self.cong_neg_probe_skip = 0; // let this scan re-probe
        false
    }

    pub(crate) fn propagate_disequalities(&mut self, propagations: &mut Vec<TheoryPropagation>) {
        if !self.inc_neg_enabled || self.neg_full_scan_needed {
            self.propagate_disequalities_full_scan();
            self.neg_full_scan_needed = false;
            self.neg_dirty_reps.clear();
            self.pending_neg_eqs.clear();
        } else {
            self.propagate_disequalities_incremental();
        }
        self.emit_diseq_propagations(propagations);
        self.emit_cong_diseq_propagations(propagations);
    }

    /// Scan-local memoized wrapper for `cong_diseq_lookahead` (#cong-neg-prop):
    /// the result depends only on the endpoint CLASS pair, and one scan visits
    /// many atoms over the same pair (totality clauses), so cache per pair.
    /// `scratch_cong_neg_memo` is cleared at every scan start.
    fn cong_diseq_lookahead_memo(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<crate::types::CongNegCascade> {
        if (lhs.0 as usize) >= self.enodes.len() || (rhs.0 as usize) >= self.enodes.len() {
            return None;
        }
        let x = self.enode_find_const(lhs.0);
        let y = self.enode_find_const(rhs.0);
        if x == y {
            return None;
        }
        let key = (x.min(y), x.max(y));
        if let Some(cached) = self.scratch_cong_neg_memo.get(&key) {
            return cached.clone();
        }

        // #cong-neg-backoff: on large problems where the cascade lookahead has
        // stopped paying off (a long barren streak of non-firing runs), skip
        // the expensive simulation and treat it as a miss, re-probing only
        // once per `CONG_NEG_REPROBE` skips so a later firing phase recovers.
        // Guidance-only: `check()` remains the conflict/soundness authority, so
        // skipping can never change the sat/unsat answer — only search guidance.
        // #cong-neg-cold: adaptive backoff applies to big problems (the original
        // size gate) OR to any solve where the lookahead has not yet fired.
        let adaptive = self.cong_neg_adaptive
            && (self.func_apps.len() >= CONG_NEG_SIZE_GATE || !self.cong_neg_ever_fired);
        if adaptive && self.cong_neg_suspended {
            self.cong_neg_probe_skip += 1;
            if self.cong_neg_probe_skip < CONG_NEG_REPROBE {
                self.scratch_cong_neg_memo.insert(key, None);
                return None;
            }
            self.cong_neg_probe_skip = 0; // fall through: run one re-probe
        }

        let res = self.cong_diseq_lookahead(lhs, rhs);
        // Recorded unconditionally: firing history must be accurate even on the
        // runs where the backoff itself is inactive.
        if res.is_some() {
            self.cong_neg_ever_fired = true;
        }
        if adaptive {
            if res.is_some() {
                self.cong_neg_barren = 0;
                self.cong_neg_suspended = false;
            } else {
                self.cong_neg_barren = self.cong_neg_barren.saturating_add(1);
                let cap = if self.cong_neg_ever_fired {
                    CONG_NEG_BARREN_CAP
                } else {
                    CONG_NEG_COLD_CAP
                };
                if self.cong_neg_barren >= cap {
                    self.cong_neg_suspended = true;
                    self.cong_neg_barren = 0;
                    self.cong_neg_probe_skip = 0;
                }
            }
        }
        self.scratch_cong_neg_memo.insert(key, res.clone());
        res
    }

    /// Bounded-fixpoint negative-congruence lookahead (#cong-neg-prop).
    ///
    /// Would asserting `lhs = rhs` (merging their classes X and Y) make two
    /// EXISTING applications congruent whose classes carry an asserted
    /// disequality — either directly (depth 1, the legacy one-step case) or
    /// through a short CASCADE of further congruence merges (depth >= 2:
    /// `a=b` makes `f(a)~f(b)`, whose merge makes `g(f(a))~g(f(b))`, ...)?
    /// If so the equality atom is theory-entailed FALSE and can be propagated
    /// before the SAT solver walks into the conflict.
    ///
    /// Simulation only — the E-graph is not mutated. The simulated world is a
    /// tiny union of live classes (`groups`/`rep_gid`/`canon` overlay). Each
    /// applied simulated merge re-hashes the parents of the side whose
    /// canonical rep changed and probes the live congruence table plus a
    /// local map of re-hashed signatures; every hit is VERIFIED
    /// argument-by-argument (signature hashes can collide, #6153). Verified
    /// congruent pairs are checked against `diseq_pair_index` (under every
    /// live-rep key of their simulated classes) and, below the depth bound,
    /// queued as further simulated merges — congruence is monotone under
    /// merges, so a pair detected in an earlier world stays congruent in
    /// every later one. Missing a candidate here (budget/depth cutoffs) is at
    /// worst lost search guidance — `check()` remains the conflict authority.
    ///
    /// Returns STRUCTURE only (which apps became congruent, in application
    /// order); the reason is rebuilt from the live proof forest at emit time.
    ///
    /// Take/restore wrapper: the simulation state lives in a reusable
    /// `CongNegScratch` on the solver so the hot MISS path (the
    /// overwhelmingly common outcome — this runs per candidate atom during
    /// negative scans) allocates nothing.
    fn cong_diseq_lookahead(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<crate::types::CongNegCascade> {
        let mut scratch = std::mem::take(&mut self.scratch_cong_neg_la);
        let res = self.cong_diseq_lookahead_inner(lhs, rhs, &mut scratch);
        self.scratch_cong_neg_la = scratch;
        res
    }

    /// Worker for `cong_diseq_lookahead`. See the doc comment above.
    #[allow(clippy::too_many_lines)]
    fn cong_diseq_lookahead_inner(
        &self,
        lhs: TermId,
        rhs: TermId,
        s: &mut crate::types::CongNegScratch,
    ) -> Option<crate::types::CongNegCascade> {
        /// Parents-scan budget per live class: classes with huge parent lists
        /// are skipped (guidance-only; keeps the lookahead O(small)).
        const PARENT_SCAN_CAP: usize = 128;
        /// Total re-hash budget across the whole cascade.
        const REHASH_BUDGET: usize = 256;
        /// Total simulated merges applied (hypothesis included).
        const MERGE_APPLY_CAP: usize = 8;

        if (lhs.0 as usize) >= self.enodes.len() || (rhs.0 as usize) >= self.enodes.len() {
            return None;
        }
        let x = self.enode_find_const(lhs.0);
        let y = self.enode_find_const(rhs.0);
        if x == y {
            return None;
        }
        let depth = self.cong_neg_depth;

        // --- simulated union of live classes -------------------------------
        // overlay: (live rep -> simulated group id) as a tiny linear-assoc
        // list (absent = singleton); canon[gid] = the rep every member hashes
        // as. Choosing the TO side's existing canonical means an app whose
        // args all map to themselves keeps its live signature, so un-rehashed
        // apps stay probe-able through the live cong_table.
        s.overlay.clear();
        s.canon.clear();
        s.queue.clear();
        s.local_sigs.clear();
        s.rehashed.clear();
        // Reset the generation-stamped membership mirrors (O(1) clear): bumping
        // the generation invalidates every stale stamp. Size the stamp arrays
        // to cover every live term id so parent ids index in bounds; new slots
        // are 0, which never matches a generation that starts at 1.
        if s.rehashed_stamp.len() < self.enodes.len() {
            s.rehashed_stamp.resize(self.enodes.len(), 0);
            s.round_stamp.resize(self.enodes.len(), 0);
        }
        s.rehashed_gen += 1;
        fn ov_gid(overlay: &[(u32, u32)], r: u32) -> Option<u32> {
            overlay.iter().find(|&&(k, _)| k == r).map(|&(_, g)| g)
        }
        fn ov_mapped(overlay: &[(u32, u32)], canon: &[u32], r: u32) -> u32 {
            ov_gid(overlay, r).map_or(r, |g| canon[g as usize])
        }
        // Simulated-class member keys for the diseq probe: a disequality
        // between two simulated classes can be registered in
        // `diseq_pair_index` under any pair of live-rep members. `keys_a` /
        // `keys_b` must already hold the two member lists.
        let diseq_between = |a_keys: &[u32], b_keys: &[u32]| -> Option<(TermId, TermId, TermId)> {
            for &ka in a_keys {
                for &kb in b_keys {
                    if ka == kb {
                        continue;
                    }
                    let key = (ka.min(kb), ka.max(kb));
                    if let Some(&entry) = self.diseq_pair_index.get(&key) {
                        // Defensive staleness gate: the underlying atom must
                        // still be asserted false.
                        if self.assigns.get(&entry.2) == Some(&false) {
                            return Some(entry);
                        }
                    }
                }
            }
            None
        };
        fn collect_keys(overlay: &[(u32, u32)], r: u32, out: &mut Vec<u32>) {
            out.clear();
            match ov_gid(overlay, r) {
                None => out.push(r),
                Some(g) => {
                    // Newest members first: the hypothesis application pushes
                    // TO then FROM, and the legacy one-step probe checked
                    // [from, to] — keep that probe order so depth 1 selects
                    // the same disequality witness the legacy code did.
                    out.extend(
                        overlay
                            .iter()
                            .rev()
                            .filter(|&&(_, gg)| gg == g)
                            .map(|&(m, _)| m),
                    );
                }
            }
        }

        // Pending simulated merges: (term_a, term_b, level). Level 1 is the
        // hypothesis; a pair detected after applying a level-L merge becomes
        // a level-(L+1) merge, applied only while L+1 <= depth. BFS order, so
        // every recorded merge is congruent in the world of the entries
        // applied before it.
        s.queue.push_back((lhs.0, rhs.0, 1));
        let mut applied: Vec<(u32, u32)> = Vec::new();
        let mut applied_count = 0usize;

        while let Some((ta, tb, level)) = s.queue.pop_front() {
            if applied_count >= MERGE_APPLY_CAP || s.rehashed.len() >= REHASH_BUDGET {
                break;
            }
            if (ta as usize) >= self.enodes.len() || (tb as usize) >= self.enodes.len() {
                continue;
            }
            let ra = self.enode_find_const(ta);
            let rb = self.enode_find_const(tb);
            if ov_mapped(&s.overlay, &s.canon, ra) == ov_mapped(&s.overlay, &s.canon, rb) {
                continue; // already one simulated class
            }
            // Merge the side with fewer total parents into the other, so
            // fewer apps need re-hashing (the TO side keeps its canonical).
            let group_parents = |overlay: &[(u32, u32)], r: u32| -> usize {
                match ov_gid(overlay, r) {
                    None => self.enodes[r as usize].parents.len(),
                    Some(g) => overlay
                        .iter()
                        .filter(|&&(_, gg)| gg == g)
                        .map(|&(m, _)| self.enodes[m as usize].parents.len())
                        .sum(),
                }
            };
            let (from_rep, to_rep) =
                if group_parents(&s.overlay, ra) <= group_parents(&s.overlay, rb) {
                    (ra, rb)
                } else {
                    (rb, ra)
                };
            // Member keys of both sides (needed for the diseq probe and the
            // FROM-side application below).
            collect_keys(&s.overlay, from_rep, &mut s.keys_a);
            collect_keys(&s.overlay, to_rep, &mut s.keys_b);
            if level == 1 {
                // Legacy one-step guard: nothing to pair, or class too big.
                let n = group_parents(&s.overlay, from_rep);
                if n == 0 || n > PARENT_SCAN_CAP {
                    return None;
                }
            } else {
                // Cascade merge application: the merge ITSELF may collide two
                // simulated classes that carry an asserted disequality (the
                // groups may have grown since this pair was detected).
                if let Some(entry) = diseq_between(&s.keys_a, &s.keys_b) {
                    return Some(crate::types::CongNegCascade {
                        merges: applied,
                        hit: (ta, tb),
                        diseq: entry,
                    });
                }
            }

            // Apply the merge to the overlay: FROM members join TO's group.
            let to_gid = match ov_gid(&s.overlay, to_rep) {
                Some(g) => g,
                None => {
                    s.canon.push(to_rep);
                    let g = (s.canon.len() - 1) as u32;
                    s.overlay.push((to_rep, g));
                    g
                }
            };
            for i in 0..s.keys_a.len() {
                let m = s.keys_a[i];
                if let Some(e) = s.overlay.iter_mut().find(|e| e.0 == m) {
                    e.1 = to_gid;
                } else {
                    s.overlay.push((m, to_gid));
                }
            }
            if level >= 2 {
                applied.push((ta, tb));
            }
            applied_count += 1;

            // Re-hash the parents of every FROM-side member: exactly their
            // signatures changed in this step.
            s.round.clear();
            s.round_gen += 1;
            for i in 0..s.keys_a.len() {
                let m = s.keys_a[i];
                let parents = &self.enodes[m as usize].parents;
                if parents.len() > PARENT_SCAN_CAP {
                    continue; // guidance-only skip of a huge class
                }
                for &p in parents {
                    // O(1) dedup via the stamp mirror (was linear `round.contains`).
                    if s.round_stamp[p as usize] != s.round_gen
                        && self.func_app_index.contains_key(&p)
                    {
                        s.round_stamp[p as usize] = s.round_gen;
                        s.round.push(p);
                    }
                }
            }
            if s.rehashed.len() + s.round.len() > REHASH_BUDGET {
                break; // budget exhausted — stop following (guidance-only)
            }

            // NOTE: `local_sigs` is NOT rebuilt between rounds. Entries whose
            // app gets re-hashed again later leave a STALE key behind, but
            // every probe hit is verified argument-by-argument below before
            // use, so a stale entry can only waste one comparison — and every
            // re-hashed app's CURRENT signature is (re)inserted when probed.
            for ri in 0..s.round.len() {
                let p = s.round[ri];
                // O(1) dedup via the stamp mirror (was linear `rehashed.contains`);
                // `rehashed` order is irrelevant, only membership + len matter.
                if s.rehashed_stamp[p as usize] != s.rehashed_gen {
                    s.rehashed_stamp[p as usize] = s.rehashed_gen;
                    s.rehashed.push(p);
                }
                let Some(&p_idx) = self.func_app_index.get(&p) else {
                    continue;
                };
                // Terminal-level disequality prune (#cong-neg-prop). At the LAST
                // cascade level (`level == depth`) a re-hashed parent can only
                // contribute an IMMEDIATE congruence-diseq hit — there is no
                // further level to queue it into. Such a hit is returned only
                // when a disequality is registered between this parent's class
                // and its congruent partner's class, and `diseq_pair_index`
                // mirrors every key into `diseq_keys_by_rep` under BOTH endpoint
                // reps. So a parent whose simulated class carries NO disequality
                // can never be the hit's `p` side, can never be a partner `q`
                // for another parent's hit (the same key must exist under this
                // rep), and its `local_sigs` entry could only pair it into
                // another same-no-diseq pair — none of which can hit. Skipping
                // its signature re-hash + congruence probe is therefore EXACT:
                // identical returned cascade, identical order. On dense but
                // diseq-light UF (QG-classification / NEQ) this is >95% of the
                // re-hash round (the profile-dominant `cong_diseq_lookahead`).
                // Budget/`rehashed` accounting above is left untouched so the
                // deep-cascade cutoff behaviour is bit-identical too.
                if level == depth {
                    let rp0 = self.enode_find_const(p);
                    let touches_diseq = match ov_gid(&s.overlay, rp0) {
                        None => self.diseq_keys_by_rep.contains_key(&rp0),
                        Some(g) => s
                            .overlay
                            .iter()
                            .filter(|&&(_, gg)| gg == g)
                            .any(|&(m, _)| self.diseq_keys_by_rep.contains_key(&m)),
                    };
                    if !touches_diseq {
                        continue;
                    }
                }
                let p_meta = &self.func_apps[p_idx];
                let sig = crate::types::CongruenceTable::make_signature_mapped(
                    p_meta.func_hash,
                    &p_meta.args,
                    &self.enodes,
                    |r| ov_mapped(&s.overlay, &s.canon, r),
                );
                // Candidate partner: an app registered with this signature in
                // the live cong_table (its sig did not change), or an already
                // re-hashed app whose simulated sig collides.
                let q = match self.cong_table.get(&sig) {
                    Some(q) if q != p => q,
                    _ => match s.local_sigs.get(&sig) {
                        Some(&q) if q != p => q,
                        _ => {
                            s.local_sigs.insert(sig, p);
                            continue;
                        }
                    },
                };
                if (q as usize) >= self.enodes.len() {
                    continue;
                }
                // VERIFY the hash match: same function, same arity, arguments
                // pairwise equal under the simulated overlay (#6153).
                let Some(&q_idx) = self.func_app_index.get(&q) else {
                    continue;
                };
                let q_meta = &self.func_apps[q_idx];
                if q_meta.func_hash != p_meta.func_hash || q_meta.args.len() != p_meta.args.len() {
                    continue;
                }
                let args_match = p_meta
                    .args
                    .iter()
                    .zip(q_meta.args.iter())
                    .all(|(&pa, &qa)| {
                        (pa as usize) < self.enodes.len()
                            && (qa as usize) < self.enodes.len()
                            && ov_mapped(&s.overlay, &s.canon, self.enode_find_const(pa))
                                == ov_mapped(&s.overlay, &s.canon, self.enode_find_const(qa))
                    });
                if !args_match {
                    continue;
                }
                let rp = self.enode_find_const(p);
                let rq = self.enode_find_const(q);
                if ov_mapped(&s.overlay, &s.canon, rp) == ov_mapped(&s.overlay, &s.canon, rq) {
                    // p and q end up in ONE simulated class: no disequality
                    // between them is possible, and merging them adds nothing.
                    continue;
                }
                collect_keys(&s.overlay, rp, &mut s.keys_a);
                collect_keys(&s.overlay, rq, &mut s.keys_b);
                if let Some(entry) = diseq_between(&s.keys_a, &s.keys_b) {
                    return Some(crate::types::CongNegCascade {
                        merges: applied,
                        hit: (p, q),
                        diseq: entry,
                    });
                }
                // Follow the cascade only if merging p and q could pair
                // anything further: some parent must exist on either side,
                // and — when the next level is the LAST one — some parent
                // must sit in a class that carries a disequality key at all
                // (a final-level hit pairs a parent of this merge with an app
                // whose diseq is keyed under that parent's class; see
                // `diseq_keys_by_rep`). This prune is what keeps the deep
                // lookahead affordable on dense instances: without it every
                // verified pair drags a full re-hash round behind it.
                if level < depth
                    && self.enodes[rp as usize].parents.len()
                        + self.enodes[rq as usize].parents.len()
                        > 0
                    && (level + 1 < depth || self.cascade_parents_touch_diseq(rp, rq))
                {
                    s.queue.push_back((p, q, level + 1));
                }
            }
        }
        None
    }

    /// Necessary condition for a LAST-level cascade hit after merging classes
    /// `rp` and `rq` (#cong-neg-prop): the hit pairs some PARENT of the
    /// merged class with a partner app such that a disequality is registered
    /// between their classes — and `diseq_pair_index` keys are mirrored into
    /// `diseq_keys_by_rep` under BOTH side reps, so the parent's own class
    /// rep must appear there (up to rare group-membership corner cases —
    /// missing one is guidance-only). O(parents) rep lookups, much cheaper
    /// than the re-hash round it gates.
    fn cascade_parents_touch_diseq(&self, rp: u32, rq: u32) -> bool {
        const PARENT_SCAN_CAP: usize = 128;
        for r in [rp, rq] {
            if (r as usize) >= self.enodes.len() {
                continue;
            }
            let parents = &self.enodes[r as usize].parents;
            for &p in parents.iter().take(PARENT_SCAN_CAP) {
                if (p as usize) >= self.enodes.len() {
                    continue;
                }
                let pr = self.enode_find_const(p);
                if self.diseq_keys_by_rep.contains_key(&pr) {
                    return true;
                }
            }
        }
        false
    }

    /// Find the (unique — the edge set is a forest by construction) path of
    /// simulated-merge edges connecting live class `rs` to live class `rt`
    /// (#cong-neg-prop). Returns edge indices with a direction flag (`true` =
    /// crossed a-side -> b-side). Everything is tiny (<= MERGE_APPLY_CAP
    /// edges), so linear scans beat any indexed structure.
    fn sim_path(&self, rs: u32, rt: u32, edges: &[SimEdge]) -> Option<Vec<(usize, bool)>> {
        // BFS frontier: (live rep, index of predecessor entry, edge, forward).
        let mut visit: Vec<(u32, usize, usize, bool)> = vec![(rs, usize::MAX, usize::MAX, false)];
        let mut head = 0;
        while head < visit.len() {
            let (node, _, _, _) = visit[head];
            if node == rt {
                let mut path = Vec::new();
                let mut i = head;
                while visit[i].1 != usize::MAX {
                    path.push((visit[i].2, visit[i].3));
                    i = visit[i].1;
                }
                path.reverse();
                return Some(path);
            }
            for (ei, e) in edges.iter().enumerate() {
                let ea = self.enode_find_const(e.a);
                let eb = self.enode_find_const(e.b);
                if ea == eb {
                    continue; // endpoints merged live since the edge was laid
                }
                let (next, fwd) = if ea == node {
                    (eb, true)
                } else if eb == node {
                    (ea, false)
                } else {
                    continue;
                };
                if visit.iter().all(|&(n, ..)| n != next) {
                    visit.push((next, head, ei, fwd));
                }
            }
            head += 1;
        }
        None
    }

    /// Are live classes `ra` and `rb` equal in the simulated world?
    fn sim_connected(&self, ra: u32, rb: u32, edges: &[SimEdge]) -> bool {
        ra == rb || self.sim_path(ra, rb, edges).is_some()
    }

    /// Verify that applications `p` and `q` are congruent in the simulated
    /// world spanned by `edges`: same function, same arity, arguments
    /// pairwise sim-connected. Structure check only — no reasons built.
    fn sim_apps_congruent(&self, p: u32, q: u32, edges: &[SimEdge]) -> bool {
        if (p as usize) >= self.enodes.len() || (q as usize) >= self.enodes.len() {
            return false;
        }
        let (Some(&p_idx), Some(&q_idx)) =
            (self.func_app_index.get(&p), self.func_app_index.get(&q))
        else {
            return false;
        };
        let p_meta = &self.func_apps[p_idx];
        let q_meta = &self.func_apps[q_idx];
        if p_meta.func_hash != q_meta.func_hash || p_meta.args.len() != q_meta.args.len() {
            return false;
        }
        p_meta
            .args
            .iter()
            .zip(q_meta.args.iter())
            .all(|(&pa, &qa)| {
                (pa as usize) < self.enodes.len()
                    && (qa as usize) < self.enodes.len()
                    && self.sim_connected(
                        self.enode_find_const(pa),
                        self.enode_find_const(qa),
                        edges,
                    )
            })
    }

    /// Explain `s = t` in the SIMULATED world of the lookahead
    /// (#cong-neg-prop), appending live-proof-forest reasons: walk the unique
    /// edge path between their live classes; within a class use plain
    /// `explain`; crossing the hypothesis edge contributes NO literal (it is
    /// the negated propagated atom); crossing a congruence edge recursively
    /// explains its argument pairs. Well-founded: edge k's argument pairs
    /// were verified connected using only edges < k when the edge was laid,
    /// and paths in a forest are unique, so recursion strictly descends the
    /// edge indices (`depth` cap is a defensive backstop, not load-bearing).
    /// Returns false if the state shifted and no valid chain exists (the
    /// caller then skips the propagation; sound, just lost guidance).
    ///
    /// #euf-emit-batch-memo: the live-class chains are resolved through the
    /// SHARED batch `explain` cache (`memo`) threaded from
    /// `emit_cong_diseq_propagations`, not the per-call `explain()` that clears
    /// its cache on entry. The simulated `edges` overlay is a per-candidate
    /// LOCAL structure and never touches the proof forest, and the drain merges
    /// nothing, so the forest is IMMUTABLE for the whole batch and a cached
    /// `(a,b)→reasons` stays valid across every call here — exactly the
    /// `ExplainMemo` contract (byte-identical: `explain_using_memo` returns the
    /// same reason SET as `explain`, cross-checked by the memo oracle).
    fn explain_sim_into(
        &mut self,
        s: TermId,
        t: TermId,
        edges: &[SimEdge],
        reasons: &mut Vec<TheoryLit>,
        depth: u32,
        memo: &mut crate::explain::ExplainMemo,
    ) -> bool {
        const RECURSION_CAP: u32 = 12;
        if depth > RECURSION_CAP {
            return false;
        }
        if (s.0 as usize) >= self.enodes.len() || (t.0 as usize) >= self.enodes.len() {
            return false;
        }
        let rs = self.enode_find_const(s.0);
        let rt = self.enode_find_const(t.0);
        if rs == rt {
            if s != t {
                let sub = self.explain_using_memo(s, t, memo);
                if sub.is_empty() {
                    // Broken proof forest — refuse the propagation (#6849).
                    return false;
                }
                reasons.extend(sub);
            }
            return true;
        }
        let Some(path) = self.sim_path(rs, rt, edges) else {
            return false;
        };
        let mut cur = s;
        for (ei, fwd) in path {
            let e = edges[ei];
            let (e_in, e_out) = if fwd { (e.a, e.b) } else { (e.b, e.a) };
            // Live chain to the edge's entry endpoint (same live class).
            if cur != TermId(e_in) {
                let sub = self.explain_using_memo(cur, TermId(e_in), memo);
                if sub.is_empty() {
                    return false;
                }
                reasons.extend(sub);
            }
            if !e.hypothesis {
                // Congruence edge: justified by its argument chains, each of
                // which lives in the world of strictly earlier edges.
                let (Some(&a_idx), Some(&b_idx)) =
                    (self.func_app_index.get(&e.a), self.func_app_index.get(&e.b))
                else {
                    return false;
                };
                if self.func_apps[a_idx].func_hash != self.func_apps[b_idx].func_hash
                    || self.func_apps[a_idx].args.len() != self.func_apps[b_idx].args.len()
                {
                    return false;
                }
                let n_args = self.func_apps[a_idx].args.len();
                for i in 0..n_args {
                    let pa = self.func_apps[a_idx].args[i];
                    let qa = self.func_apps[b_idx].args[i];
                    if !self.explain_sim_into(
                        TermId(pa),
                        TermId(qa),
                        edges,
                        reasons,
                        depth + 1,
                        memo,
                    ) {
                        return false;
                    }
                }
            }
            cur = TermId(e_out);
        }
        if cur != t {
            let sub = self.explain_using_memo(cur, t, memo);
            if sub.is_empty() {
                return false;
            }
            reasons.extend(sub);
        }
        true
    }

    /// Emit the negative-congruence lookahead propagations collected in
    /// `scratch_cong_neg_props` (#cong-neg-prop). Reasons are built HERE, from
    /// the live proof forest — never cached — so a reason can never be stale:
    /// the simulated world is REBUILT from the cascade's structure with every
    /// step re-verified against the live E-graph (any mismatch skips the
    /// propagation; sound, just lost guidance), then the reason is
    /// diseq literal + `hit.0 ~ diseq-side` chain + `hit.1 ~ other-side`
    /// chain + argument chains, each routed through the hypothesis/cascade
    /// edges where the chain crosses a simulated merge.
    fn emit_cong_diseq_propagations(&mut self, propagations: &mut Vec<TheoryPropagation>) {
        if self.scratch_cong_neg_props.is_empty() {
            return;
        }
        let debug = self.debug_euf;
        // Deterministic order + drop duplicate proposals for the same atom.
        self.scratch_cong_neg_props
            .sort_by_key(|(term_id, ..)| term_id.0);
        self.scratch_cong_neg_props
            .dedup_by_key(|(term_id, ..)| *term_id);

        let candidates = std::mem::take(&mut self.scratch_cong_neg_props);

        // #euf-emit-batch-memo: one reason cache across the whole cong-neg
        // drain, threaded through every `explain_sim_into` (and its live-class
        // `explain_using_memo` chains). The proof forest is IMMUTABLE here —
        // the drain only READS the forest and builds per-candidate LOCAL
        // simulated overlays; nothing below merges — so a cached
        // `(a,b)→reasons` stays valid across candidates and the shared
        // congruence sub-proofs the per-call cache used to re-walk are reused.
        // Taken from `self` to keep capacity; restored after the loop. Sound:
        // see `ExplainMemo` (a nested BFS-fallback `explain` takes the now-empty
        // `self.explain_memo`, never this one).
        let mut cong_memo = std::mem::take(&mut self.explain_memo);
        cong_memo.clear();
        'cand: for (term_id, lhs, rhs, cascade) in &candidates {
            let (term_id, lhs, rhs) = (*term_id, *lhs, *rhs);
            let (p, q) = cascade.hit;
            let (diseq_a, diseq_b, diseq_term) = cascade.diseq;
            // The atom may have been proposed by the DIRECT diseq scan too;
            // that propagation (same literal, simpler reason) wins.
            if propagations.iter().any(|prop| prop.literal.term == term_id) {
                continue;
            }
            if self.assigns.contains_key(&term_id) {
                continue;
            }
            if self.assigns.get(&diseq_term) != Some(&false) {
                continue;
            }
            if (lhs.0 as usize) >= self.enodes.len()
                || (rhs.0 as usize) >= self.enodes.len()
                || (p as usize) >= self.enodes.len()
                || (q as usize) >= self.enodes.len()
                || (diseq_a.0 as usize) >= self.enodes.len()
                || (diseq_b.0 as usize) >= self.enodes.len()
            {
                continue;
            }
            let x = self.enode_find_const(lhs.0);
            let y = self.enode_find_const(rhs.0);
            if x == y {
                continue; // classes merged since the scan — positive case now
            }

            // Rebuild the simulated world from the recorded structure,
            // re-verifying every cascade merge against the LIVE E-graph.
            // Edges are laid in application order and each merge's argument
            // pairs are verified against the edges laid SO FAR — this is what
            // keeps `explain_sim_into`'s recursion well-founded.
            let mut edges: Vec<SimEdge> = Vec::with_capacity(1 + cascade.merges.len());
            edges.push(SimEdge {
                a: lhs.0,
                b: rhs.0,
                hypothesis: true,
            });
            for &(mp, mq) in &cascade.merges {
                if (mp as usize) >= self.enodes.len() || (mq as usize) >= self.enodes.len() {
                    continue 'cand;
                }
                let rmp = self.enode_find_const(mp);
                let rmq = self.enode_find_const(mq);
                if self.sim_connected(rmp, rmq, &edges) {
                    continue; // redundant edge (merged live since the scan)
                }
                if !self.sim_apps_congruent(mp, mq, &edges) {
                    continue 'cand; // state shifted since the scan — skip (sound)
                }
                edges.push(SimEdge {
                    a: mp,
                    b: mq,
                    hypothesis: false,
                });
            }
            // Verify the final hit pair in the full simulated world.
            if !self.sim_apps_congruent(p, q, &edges) {
                continue;
            }
            // Orient the disequality endpoints to the application pair: the
            // p-side chain target must be sim-equal to p (its class carries
            // the diseq key on p's side), likewise q.
            let rp = self.enode_find_const(p);
            let rq = self.enode_find_const(q);
            let rda = self.enode_find_const(diseq_a.0);
            let rdb = self.enode_find_const(diseq_b.0);
            let (p_target, q_target) = if self.sim_connected(rda, rp, &edges)
                && self.sim_connected(rdb, rq, &edges)
            {
                (diseq_a, diseq_b)
            } else if self.sim_connected(rdb, rp, &edges) && self.sim_connected(rda, rq, &edges) {
                (diseq_b, diseq_a)
            } else {
                continue; // reps shifted since the scan — skip (sound)
            };

            let mut reasons = vec![TheoryLit::new(diseq_term, false)];
            if !self.explain_sim_into(TermId(p), p_target, &edges, &mut reasons, 0, &mut cong_memo)
                || !self.explain_sim_into(
                    TermId(q),
                    q_target,
                    &edges,
                    &mut reasons,
                    0,
                    &mut cong_memo,
                )
            {
                continue;
            }
            {
                // Argument chains: p and q are congruent in the simulated
                // world (function/arity already checked by sim_apps_congruent).
                let Some((_, p_args)) = self.get_func_app_info(p) else {
                    continue;
                };
                let Some((_, q_args)) = self.get_func_app_info(q) else {
                    continue;
                };
                for (&pa, &qa) in p_args.iter().zip(q_args.iter()) {
                    if !self.explain_sim_into(
                        TermId(pa),
                        TermId(qa),
                        &edges,
                        &mut reasons,
                        0,
                        &mut cong_memo,
                    ) {
                        continue 'cand;
                    }
                }
            }

            reasons.sort_unstable_by_key(|l| (l.term.0, l.value));
            reasons.dedup_by_key(|l| (l.term.0, l.value));

            // Adversarial soundness gates (#cong-neg-prop): every reason must
            // be a currently-asserted atom, and the propagated atom must not
            // appear among its own reasons.
            debug_assert!(
                reasons
                    .iter()
                    .all(|l| self.assigns.get(&l.term) == Some(&l.value)),
                "BUG: cong-neg propagation reason references unasserted atom (eq term {})",
                term_id.0
            );
            debug_assert!(
                reasons.iter().all(|l| l.term != term_id),
                "BUG: cong-neg propagation is self-justifying (eq term {})",
                term_id.0
            );
            if reasons
                .iter()
                .any(|l| self.assigns.get(&l.term) != Some(&l.value))
            {
                continue; // release-mode gate: refuse an unsound reason
            }

            // Once-per-solve clause dedup (#cong-neg-prop): the SAT layer keeps
            // every theory-propagation clause permanently with watches, so BCP
            // re-fires an already-emitted implication after backtracking on its
            // own. Re-emitting it would only duplicate the clause in the SAT DB
            // and re-pay explain(). FNV-1a over the sorted reason set keys the
            // exact clause; a DIFFERENT reason for the same atom still emits.
            let mut reason_hash: u64 = 0xcbf2_9ce4_8422_2325;
            for l in &reasons {
                let mut mix = |b: u64| {
                    reason_hash ^= b;
                    reason_hash = reason_hash.wrapping_mul(0x0000_0100_0000_01B3);
                };
                mix(u64::from(l.term.0));
                mix(u64::from(l.value));
            }
            if !self.cong_neg_emitted.insert((term_id, reason_hash)) {
                continue;
            }

            if debug {
                safe_eprintln!(
                    "[EUF PROPAGATE] cong-neg: eq {} = false (terms {} != {}) via apps {}~{}, {} cascade merges, diseq {} ({} reasons)",
                    term_id.0,
                    lhs.0,
                    rhs.0,
                    p,
                    q,
                    cascade.merges.len(),
                    diseq_term.0,
                    reasons.len()
                );
            }
            self.cong_neg_propagation_count += 1;
            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(term_id, false),
                reason: reasons,
                reason_data: None,
            });
        }
        // Restore the cache shell (keeps its allocated capacity for next drain).
        self.explain_memo = cong_memo;
        // Restore the (now empty) scratch buffer to keep its capacity.
        self.scratch_cong_neg_props = candidates;
        self.scratch_cong_neg_props.clear();
    }

    /// FULL negative scan: rebuild `diseq_pair_index`/`diseq_keys_by_rep` from
    /// all current assignments and check every equality term against it.
    fn propagate_disequalities_full_scan(&mut self) {
        let _cong_neg_skip_scan = self.cong_neg_scan_suspended();
        let n_eqs = self.eq_terms.len();

        if self.neg_index_prebuilt {
            // #euf-inc-diseq-undo: an incremental pop restored `diseq_pair_index`
            // / `diseq_keys_by_rep` via the undo trail; their CONTENTS are
            // already exact (the pop's debug cross-check verified the key set),
            // so skip the O(|assigns|) clear+rebuild — the dominant per-pop
            // cost on the giant Certora files — and run only the candidate scan
            // below over the restored index. `diseq_index_base_depth` is left
            // untouched: the restored index still traces back to the last
            // from-scratch build, and the candidate scan produces byte-identical
            // propagations to a rebuild (identical index contents).
            self.neg_index_prebuilt = false;
            // Ensure the inverse index is materialized before the candidate scan
            // (and any cong-neg lookahead) reads it.
            self.ensure_diseq_keys_fresh();
            // #euf-inc-diseq-undo COMPLETENESS: the from-scratch rebuild (else
            // branch) reads EVERY current disequality out of `assigns`, but this
            // skip branch trusts the trail-restored index — which does NOT yet
            // include disequalities asserted AFTER the pop (they sit in
            // `pending_neg_eqs`). The caller clears that queue right after this
            // returns, so drain it into the restored index here first, exactly
            // as the incremental scan / check would.
            self.sync_diseq_index();
        } else {
            // Build diseq index: (min_rep, max_rep) -> (a, b, eq_term)
            self.diseq_pair_index.clear();
            self.diseq_keys_by_rep.clear();
            // #euf-inc-diseq-undo: this from-scratch build bakes in every
            // current disequality without an undo record, so the incremental
            // pop-restore is valid only down to the depth it runs at.
            self.diseq_index_base_depth = self.scopes.len();
            for (&lit_term, &value) in &self.assigns {
                if value {
                    continue; // only interested in false equalities (disequalities)
                }
                if let Some((a, b)) = self.decode_eq(lit_term) {
                    if self.terms.sort(a) != self.terms.sort(b) {
                        continue;
                    }
                    if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                        continue;
                    }
                    let (a_rep, b_rep) = (self.enode_find_const(a.0), self.enode_find_const(b.0));
                    if a_rep == b_rep {
                        // Conflict, not propagation — check() reports it. In
                        // incremental mode ALSO record the candidate: this rebuild
                        // clears `neg_full_scan_needed`, so a subsequent
                        // incremental check would otherwise never see this
                        // already-violated pair (it is not in the index).
                        if self.inc_neg_enabled {
                            self.pending_diseq_conflicts.push((a, b, lit_term));
                        }
                        continue;
                    }
                    let key = (a_rep.min(b_rep), a_rep.max(b_rep));
                    if self
                        .diseq_pair_index
                        .insert(key, (a, b, lit_term))
                        .is_none()
                    {
                        self.diseq_keys_by_rep.entry(key.0).or_default().push(key);
                        self.diseq_keys_by_rep.entry(key.1).or_default().push(key);
                    }
                }
            }
        }

        self.scratch_neg_props.clear();
        self.scratch_cong_neg_props.clear();
        self.scratch_cong_neg_memo.clear();
        // #cong-neg-prop pop-path cost fix: run the O(n_eqs) lookahead sweep
        // only when this full scan was forced by something other than a plain
        // pop (see `neg_full_scan_la_needed`). After a pop, every lookahead
        // implication proposed earlier survives as a permanent SAT clause
        // that BCP re-fires by itself; recomputing the sweep here was the #1
        // profile cost on QG-classification/NEQ QF_UF. Atoms affected by
        // POST-pop events (new merges dirtied `neg_dirty_reps` in
        // `incremental_merge`; new disequalities queued in `pending_neg_eqs`
        // — e.g. the backjump-asserted learned literal) can carry genuinely
        // NEW implications, so they still get the lookahead: expand the new
        // diseqs' trigger classes into `neg_dirty_reps` exactly the way
        // `sync_diseq_index` would, then gate per-atom on that dirty set.
        let la_sweep = self.cong_neg_enabled && self.neg_full_scan_la_needed;
        self.neg_full_scan_la_needed = false;
        if !la_sweep && self.cong_neg_enabled {
            let pending = std::mem::take(&mut self.pending_neg_eqs);
            for &(lit_term, a, b) in &pending {
                if self.assigns.get(&lit_term) != Some(&false) {
                    continue;
                }
                if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                    continue;
                }
                let a_rep = self.enode_find_const(a.0);
                let b_rep = self.enode_find_const(b.0);
                self.dirty_app_member_args(a_rep);
                self.dirty_app_member_args(b_rep);
            }
            self.pending_neg_eqs = pending;
        }
        // Snapshot of the event-dirty reps for the la gate below (taken, not
        // borrowed — the lookahead needs `&mut self`). Restored afterwards to
        // keep the allocation; the caller clears it right after this scan.
        let la_dirty = if la_sweep {
            ay_core::kani_compat::DetHashSet::default()
        } else {
            std::mem::take(&mut self.neg_dirty_reps)
        };
        if self.diseq_pair_index.is_empty() {
            if !la_sweep {
                self.neg_dirty_reps = la_dirty;
            }
            return;
        }

        // Find unassigned equality terms whose sides map to a known disequality pair
        for i in 0..n_eqs {
            let (term_id, lhs, rhs) = self.eq_terms[i];
            if self.assigns.contains_key(&term_id) {
                continue;
            }
            // sort(lhs) == sort(rhs) holds by construction here: `eq_terms` is
            // filtered to same-sorted equalities in `init_eq_terms`, so the old
            // per-iteration `Sort::eq` (a string compare that dominated EUF
            // runtime on QF_UF) is gone.
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            if lhs_rep == rhs_rep {
                continue; // same class — handled by positive propagation
            }
            let key = (lhs_rep.min(rhs_rep), lhs_rep.max(rhs_rep));
            if let Some(&(diseq_a, diseq_b, diseq_term)) = self.diseq_pair_index.get(&key) {
                self.scratch_neg_props
                    .push((term_id, lhs, rhs, diseq_a, diseq_b, diseq_term));
            } else if !_cong_neg_skip_scan
                && (la_sweep
                    || (self.cong_neg_enabled
                        && (la_dirty.contains(&lhs_rep) || la_dirty.contains(&rhs_rep))))
            {
                // #cong-neg-prop: cascade congruence lookahead on direct miss.
                if let Some(cascade) = self.cong_diseq_lookahead_memo(lhs, rhs) {
                    self.scratch_cong_neg_props
                        .push((term_id, lhs, rhs, cascade));
                }
            }
        }
        if !la_sweep {
            self.neg_dirty_reps = la_dirty;
        }
    }

    /// Drain `pending_neg_eqs` into `diseq_pair_index`, recording newly
    /// inserted keys for the incremental propagation matcher and pushing a
    /// conflict candidate when a disequality is asserted over an
    /// already-merged pair. Shared by the incremental negative propagation
    /// scan and the incremental `check_disequality_conflicts` so whichever
    /// runs first keeps the index current for both (#inc-neg).
    pub(crate) fn sync_diseq_index(&mut self) {
        // #euf-inc-diseq-undo: whether this solve trails diseq_pair_index
        // mutations for the incremental pop-restore (constant per solve).
        let diseq_undo = self.diseq_undo_active();
        // #euf-inc-diseq-undo: refresh the inverse index (stale after an
        // incremental pop) before extending it below.
        self.ensure_diseq_keys_fresh();
        let pending = std::mem::take(&mut self.pending_neg_eqs);
        let mut requeue: Vec<(TermId, TermId, TermId)> = Vec::new();
        for (lit_term, a, b) in pending {
            if self.assigns.get(&lit_term) != Some(&false) {
                continue; // retracted or flipped since queueing
            }
            if self.terms.sort(a) != self.terms.sort(b) {
                continue;
            }
            if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                // E-graph does not cover these terms yet; dropping the entry
                // would silently lose the disequality for future conflict
                // detection. Re-queue it for a later sync.
                requeue.push((lit_term, a, b));
                continue;
            }
            let (a_rep, b_rep) = (self.enode_find_const(a.0), self.enode_find_const(b.0));
            if a_rep == b_rep {
                // Asserted disequality over an already-merged pair: conflict.
                self.pending_diseq_conflicts.push((a, b, lit_term));
                continue;
            }
            let key = (a_rep.min(b_rep), a_rep.max(b_rep));
            match self.diseq_pair_index.insert(key, (a, b, lit_term)) {
                Some(old) => {
                    // #euf-inc-diseq-undo: `insert` overwrote the witness of an
                    // already-indexed pair; record the previous witness so pop()
                    // restores the exact scope-entry mapping (its witness must
                    // reference a surviving disequality).
                    if diseq_undo {
                        self.undo_trail
                            .push(UndoRecord::DiseqSet { key, entry: old });
                    }
                    continue; // redundant witness for an already-indexed pair
                }
                None => {
                    // #euf-inc-diseq-undo: a brand-new key was inserted, moving
                    // this diseq from the pending queue into the index. Record a
                    // `DiseqUnsync` so pop() removes it AND (if the assignment
                    // outlives the pop — a deferred sync) re-queues it.
                    if diseq_undo {
                        self.undo_trail.push(UndoRecord::DiseqUnsync {
                            key,
                            entry: (a, b, lit_term),
                        });
                    }
                }
            }
            self.diseq_keys_by_rep.entry(key.0).or_default().push(key);
            self.diseq_keys_by_rep.entry(key.1).or_default().push(key);
            self.pending_diseq_match_keys.push((key, (a, b, lit_term)));
            // #cong-neg-prop trigger: a NEW disequality between these classes
            // can give equality atoms over the ARGUMENT classes of their
            // application members a lookahead hit. Dirty those arg classes so
            // the incremental negative scan revisits their atoms.
            if self.cong_neg_enabled {
                self.dirty_app_member_args(key.0);
                self.dirty_app_member_args(key.1);
            }
        }
        self.pending_neg_eqs.extend(requeue);
    }

    /// Dirty the argument-class representatives of every function-application
    /// member of `class_rep`'s equivalence class (#cong-neg-prop trigger),
    /// recursing `cong_neg_depth` argument levels so equality atoms that can
    /// only hit through a depth>=2 CASCADE are revisited too (the cascade
    /// walks the same parent chain upward that this walks downward).
    /// Bounded: very large classes are skipped and a total class-visit budget
    /// caps the recursion (guidance only — the full scan after any pop
    /// re-derives everything).
    fn dirty_app_member_args(&mut self, class_rep: u32) {
        let levels = self.cong_neg_depth.max(1);
        let mut budget = 32u32;
        self.dirty_app_member_args_rec(class_rep, levels, &mut budget);
    }

    /// Recursive worker for `dirty_app_member_args`; also called from
    /// `incremental_merge`'s reinserted-parent trigger for its deeper levels.
    pub(crate) fn dirty_app_member_args_rec(
        &mut self,
        class_rep: u32,
        levels: u32,
        budget: &mut u32,
    ) {
        const CLASS_WALK_CAP: u32 = 256;
        if levels == 0 || *budget == 0 {
            return;
        }
        *budget -= 1;
        if (class_rep as usize) >= self.enodes.len() {
            return;
        }
        if self.enodes[class_rep as usize].class_size > CLASS_WALK_CAP {
            return;
        }
        let mut member = class_rep;
        loop {
            if let Some(&idx) = self.func_app_index.get(&member) {
                let n_args = self.func_apps[idx].args.len();
                for ai in 0..n_args {
                    let arg = self.func_apps[idx].args[ai];
                    let rep = self.enode_find_const(arg);
                    self.neg_dirty_reps.insert(rep);
                    if levels > 1 {
                        self.dirty_app_member_args_rec(rep, levels - 1, budget);
                    }
                }
            }
            member = self.enodes[member as usize].next;
            if member == class_rep {
                break;
            }
        }
    }

    /// INCREMENTAL negative scan: process only new disequalities and equalities
    /// touching merge-dirtied class reps. See `propagate_disequalities`.
    fn propagate_disequalities_incremental(&mut self) {
        let _cong_neg_skip_scan2 = self.cong_neg_scan_suspended();
        self.scratch_neg_props.clear();
        self.scratch_cong_neg_props.clear();
        self.scratch_cong_neg_memo.clear();

        // (a) Newly asserted negated equalities: index them under their current
        // reps and propose matching unassigned equalities from `class_eqs`.
        self.sync_diseq_index();
        let match_keys = std::mem::take(&mut self.pending_diseq_match_keys);
        for (key, (a, b, lit_term)) in match_keys {
            // The key may have been rekeyed (or collapsed) by merges since it
            // was recorded; matching is by CURRENT index membership.
            if self.diseq_pair_index.get(&key) != Some(&(a, b, lit_term)) {
                continue;
            }
            if self.assigns.get(&lit_term) != Some(&false) {
                continue;
            }
            // Unassigned equalities matching this new pair have an endpoint in
            // class `key.0` (class_eqs indexes each equality under BOTH
            // endpoint reps, so scanning one side finds every candidate).
            let mut idxs = std::mem::take(&mut self.scratch_class_eq_idxs);
            idxs.clear();
            if let Some(v) = self.class_eqs.get(&key.0) {
                idxs.extend_from_slice(v);
            }
            for &i in &idxs {
                let (term_id, lhs, rhs) = self.eq_terms[i];
                if self.assigns.contains_key(&term_id) {
                    continue;
                }
                let (lhs_rep, rhs_rep) =
                    (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
                let eq_key = (lhs_rep.min(rhs_rep), lhs_rep.max(rhs_rep));
                if eq_key == key {
                    self.scratch_neg_props
                        .push((term_id, lhs, rhs, a, b, lit_term));
                }
            }
            self.scratch_class_eq_idxs = idxs;
        }

        // (b) Merge-dirtied reps: re-check their equalities against the index
        // (same iteration shape as the incremental positive scan).
        let dirty = std::mem::take(&mut self.neg_dirty_reps);
        let mut seen = std::mem::take(&mut self.scratch_seen_eq_idxs);
        seen.clear();
        let mut idxs = std::mem::take(&mut self.scratch_class_eq_idxs);
        for rep in dirty {
            idxs.clear();
            match self.class_eqs.get(&rep) {
                Some(v) => idxs.extend_from_slice(v),
                None => continue,
            }
            for &i in &idxs {
                if !seen.insert(i) {
                    continue;
                }
                let (term_id, lhs, rhs) = self.eq_terms[i];
                if self.assigns.contains_key(&term_id) {
                    continue;
                }
                let (lhs_rep, rhs_rep) =
                    (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
                if lhs_rep == rhs_rep {
                    continue; // positive propagation's case
                }
                let key = (lhs_rep.min(rhs_rep), lhs_rep.max(rhs_rep));
                if let Some(&(diseq_a, diseq_b, diseq_term)) = self.diseq_pair_index.get(&key) {
                    self.scratch_neg_props
                        .push((term_id, lhs, rhs, diseq_a, diseq_b, diseq_term));
                } else if self.cong_neg_enabled && !_cong_neg_skip_scan2 {
                    // #cong-neg-prop: cascade congruence lookahead on direct
                    // miss. Trigger coverage: `incremental_merge` dirties the
                    // arg classes of every reinserted parent, and
                    // `sync_diseq_index` dirties the arg classes of newly
                    // disequal classes' application members (recursing
                    // `cong_neg_depth` argument levels for the cascade), so
                    // an atom whose lookahead status may have changed lands
                    // in `dirty` here.
                    if let Some(cascade) = self.cong_diseq_lookahead_memo(lhs, rhs) {
                        self.scratch_cong_neg_props
                            .push((term_id, lhs, rhs, cascade));
                    }
                }
            }
        }
        self.scratch_class_eq_idxs = idxs;
        self.scratch_seen_eq_idxs = seen;
    }

    /// Emit the propagations collected in `scratch_neg_props` (shared tail of
    /// both negative scan modes): build oriented reasons via `explain` and
    /// push `TheoryPropagation`s.
    fn emit_diseq_propagations(&mut self, propagations: &mut Vec<TheoryPropagation>) {
        let debug = self.debug_euf;

        // The incremental scan can propose one equality via BOTH the
        // new-disequality and dirty-rep paths; keep the first proposal only.
        self.scratch_neg_props
            .sort_by_key(|&(term_id, ..)| term_id.0);
        self.scratch_neg_props
            .dedup_by_key(|&mut (term_id, ..)| term_id);

        // #euf-emit-batch-memo: one reason cache across the whole diseq drain.
        // The forest is immutable here (nothing below merges), so shared
        // congruence sub-proofs are reused across the many `explain` chains this
        // loop builds. Taken from `self` to keep capacity; restored after.
        let mut diseq_memo = std::mem::take(&mut self.explain_memo);
        diseq_memo.clear();
        for idx in 0..self.scratch_neg_props.len() {
            let (term_id, lhs, rhs, diseq_a, diseq_b, diseq_term) = self.scratch_neg_props[idx];
            // Production soundness gate: the persistent pair index is a cache,
            // never an assertion authority.  A stale witness must not justify a
            // propagation after its disequality was popped (and in the degenerate
            // self-witness case would otherwise emit `p` with reason `[p]`).
            // Check this before both eager emission and lazy-token creation;
            // lazy materialization independently repeats the same polarity gate.
            if self.assigns.get(&diseq_term) != Some(&false) || diseq_term == term_id {
                safe_eprintln!(
                    "BUG: EUF diseq propagation witness {} is not a live, distinct \
                     asserted disequality for term {} — skipping propagation",
                    diseq_term.0,
                    term_id.0
                );
                continue;
            }
            // Find which orientation matches
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            let (da_rep, db_rep) = (
                self.enode_find_const(diseq_a.0),
                self.enode_find_const(diseq_b.0),
            );

            let (match_a, match_b) = if lhs_rep == da_rep && rhs_rep == db_rep {
                (diseq_a, diseq_b)
            } else if lhs_rep == db_rep && rhs_rep == da_rep {
                (diseq_b, diseq_a)
            } else {
                // Production soundness gate: E-graph representatives changed
                // between index construction and propagation. Skip this
                // propagation (sound but incomplete) and log for diagnostics.
                safe_eprintln!(
                    "BUG: EUF diseq propagation orientation mismatch: \
                     lhs_rep={}, rhs_rep={}, da_rep={}, db_rep={} — skipping propagation",
                    lhs_rep,
                    rhs_rep,
                    da_rep,
                    db_rep
                );
                continue;
            };

            // #euf-lazy-explain (#8467): the orientation above verified the
            // disequality still justifies `term_id := false`; defer the two
            // explain() chains to conflict analysis. The witness triple is
            // recorded so `explain_lazy_propagation` can re-run the SAME
            // orientation check + chain explains against the LIVE e-graph at
            // materialization time (all validation gates re-applied there —
            // a stale witness only ever causes a sound rejection).
            if self.lazy_emit_gate() {
                self.lazy_neg_witness
                    .insert(term_id, (diseq_a, diseq_b, diseq_term));
                self.lazy_emitted_count += 1;
                propagations.push(TheoryPropagation::lazy(
                    TheoryLit::new(term_id, false),
                    EUF_LAZY_MAGIC | EUF_LAZY_KIND_NEG,
                ));
                continue;
            }

            // Build reason: disequality + equality chains.
            // #euf-emit-batch-memo: append each chain DIRECTLY into `reasons`
            // via the proof-forest fast path (no intermediate Vec, no per-chain
            // sort), threaded through the batch cache; fall back to the full
            // BFS-capable `explain` only when the forest path can't resolve the
            // pair (roots differ / broken edge). The single sort+dedup below
            // normalizes, so the reason SET is byte-identical to the former
            // `explain().extend()`.
            let mut reasons = vec![TheoryLit::new(diseq_term, false)];

            // Explain lhs = match_a (if not the same term)
            if lhs != match_a && !self.explain_into(lhs, match_a, &mut reasons, &mut diseq_memo) {
                reasons.extend(self.explain(lhs, match_a));
            }
            // Explain rhs = match_b (if not the same term)
            if rhs != match_b && !self.explain_into(rhs, match_b, &mut reasons, &mut diseq_memo) {
                reasons.extend(self.explain(rhs, match_b));
            }

            // Deduplicate reasons
            reasons.sort_unstable_by_key(|l| (l.term.0, l.value));
            reasons.dedup_by_key(|l| (l.term.0, l.value));

            if debug {
                safe_eprintln!(
                    "[EUF PROPAGATE] Propagating eq {} = false (terms {} != {}) with {} reasons (diseq {} via {})",
                    term_id.0,
                    lhs.0,
                    rhs.0,
                    reasons.len(),
                    diseq_term.0,
                    if match_a == diseq_a {
                        "direct"
                    } else {
                        "swapped"
                    }
                );
            }
            debug_assert!(
                !self.assigns.contains_key(&term_id),
                "BUG: EUF diseq propagate: term {} already assigned",
                term_id.0
            );

            if self.gap_stats_enabled {
                self.gap_stats.record_emission(term_id, &reasons, false);
            }
            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(term_id, false),
                reason: reasons,
                reason_data: None,
            });
        }
        // Restore the cache shell (keeps its allocated capacity for next drain).
        self.explain_memo = diseq_memo;
    }

    /// Materialize the reason for a LAZY propagation on demand
    /// (#8467 protocol, #euf-lazy-explain). Called from
    /// `TheorySolver::explain_propagation` when SAT conflict analysis (or a
    /// backtrack/restart sweep, or the opposite-assignment path in the eager
    /// extension) actually needs the reason — for the ~95%+ of propagations
    /// that never reach this point, the emit-time `explain()` cost is saved
    /// entirely.
    ///
    /// SOUNDNESS. The returned reason must be a valid explanation of the
    /// propagated literal AT THE MOMENT SAT USES IT. Everything is re-derived
    /// from and validated against the LIVE e-graph and assignment state:
    ///
    /// - Tokens are self-describing (magic + kind), never indices into a
    ///   popped log — there is no stale-handle failure mode, only re-derivation
    ///   that either succeeds against current state or returns `None`.
    /// - The SAT layer materializes surviving lazy reasons BEFORE the
    ///   extension pops theory scopes on every backtrack/restart path
    ///   (`materialize_lazy_reasons_through_level_for_backtrack` /
    ///   `materialize_all_lazy_reasons_before_extension_restart`), so at every
    ///   call the e-graph still contains the merges that justified the
    ///   propagation; proof-forest paths are fixed at merge time (later
    ///   merges only attach other trees), so `explain()` re-derives the SAME
    ///   reason chain the eager path would have produced at emit time.
    /// - Every derivation step re-checks its premise against live state
    ///   (class membership via `enode_find_const`, witness orientation,
    ///   assertion polarity); any mismatch returns `None`, which the SAT
    ///   layer handles by demoting the variable to a decision — always sound,
    ///   only weakens the learned clause.
    /// - Final release-mode gate: every reason literal must be a
    ///   currently-asserted theory atom with matching polarity and must not
    ///   be the propagated atom itself. The SAT side additionally re-checks
    ///   that every reason literal is FALSIFIED on the trail at a level no
    ///   higher than the propagated literal's
    ///   (`materialize_lazy_reason_with_ext`, #8511) and rejects tautologies,
    ///   so an invalid reason can never enter conflict analysis.
    pub(crate) fn explain_lazy_propagation(
        &mut self,
        lit: TermId,
        reason_data: u64,
    ) -> Option<Vec<TheoryLit>> {
        if reason_data & EUF_LAZY_MAGIC_MASK != EUF_LAZY_MAGIC {
            // Not an EUF token (combiner broadcast of another theory's
            // handle) — decline without touching statistics.
            return None;
        }
        let reject = |this: &mut Self| {
            this.lazy_explain_rejected_count += 1;
            None
        };
        let Some((lhs, rhs)) = self.decode_eq(lit) else {
            return reject(self);
        };
        if !self.enodes_init
            || (lhs.0 as usize) >= self.enodes.len()
            || (rhs.0 as usize) >= self.enodes.len()
        {
            return reject(self);
        }

        let mut reasons: Vec<TheoryLit> = match reason_data & EUF_LAZY_KIND_MASK {
            EUF_LAZY_KIND_POS => {
                // `lit := true` because find(lhs) == find(rhs). Re-check the
                // class merge against the live e-graph, then re-derive the
                // chain exactly as the eager emitter would have.
                if self.enode_find_const(lhs.0) != self.enode_find_const(rhs.0) {
                    return reject(self);
                }
                let reasons = self.explain(lhs, rhs);
                // Empty reason = broken proof forest (#6849): an incomplete
                // reason would make the learned clause stronger than what the
                // theory proved. Reject (sound demotion).
                if reasons.is_empty() {
                    return reject(self);
                }
                reasons
            }
            EUF_LAZY_KIND_NEG => {
                // `lit := false` because the witness disequality connects the
                // endpoint classes. Re-run the emit-time orientation check
                // against live representatives before any explain() — without
                // it a shifted class could route explain() into its
                // over-approximating fallbacks.
                let Some(&(diseq_a, diseq_b, diseq_term)) = self.lazy_neg_witness.get(&lit) else {
                    return reject(self);
                };
                if self.assigns.get(&diseq_term) != Some(&false) {
                    return reject(self);
                }
                if (diseq_a.0 as usize) >= self.enodes.len()
                    || (diseq_b.0 as usize) >= self.enodes.len()
                {
                    return reject(self);
                }
                let (lhs_rep, rhs_rep) =
                    (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
                let (da_rep, db_rep) = (
                    self.enode_find_const(diseq_a.0),
                    self.enode_find_const(diseq_b.0),
                );
                let (match_a, match_b) = if lhs_rep == da_rep && rhs_rep == db_rep {
                    (diseq_a, diseq_b)
                } else if lhs_rep == db_rep && rhs_rep == da_rep {
                    (diseq_b, diseq_a)
                } else {
                    return reject(self);
                };
                let mut reasons = vec![TheoryLit::new(diseq_term, false)];
                if lhs != match_a {
                    let sub = self.explain(lhs, match_a);
                    if sub.is_empty() {
                        return reject(self); // broken proof forest (#6849)
                    }
                    reasons.extend(sub);
                }
                if rhs != match_b {
                    let sub = self.explain(rhs, match_b);
                    if sub.is_empty() {
                        return reject(self); // broken proof forest (#6849)
                    }
                    reasons.extend(sub);
                }
                reasons
            }
            _ => return reject(self),
        };

        reasons.sort_unstable_by_key(|l| (l.term.0, l.value));
        reasons.dedup_by_key(|l| (l.term.0, l.value));

        // Release-mode validation gates (mirrors the cong-neg emit gates):
        // every reason literal must be a currently-asserted theory atom with
        // matching polarity, and the propagation must not justify itself.
        debug_assert!(
            reasons
                .iter()
                .all(|l| self.assigns.get(&l.term) == Some(&l.value)),
            "BUG: EUF lazy explain produced a reason referencing an unasserted atom (eq term {})",
            lit.0
        );
        debug_assert!(
            reasons.iter().all(|l| l.term != lit),
            "BUG: EUF lazy explain is self-justifying (eq term {})",
            lit.0
        );
        if reasons
            .iter()
            .any(|l| l.term == lit || self.assigns.get(&l.term) != Some(&l.value))
        {
            return reject(self);
        }

        self.lazy_explained_count += 1;
        Some(reasons)
    }

    // NOTE: Disequality collection is implemented in `solver_query.rs` via
    // `collect_disequalities_for_propagation()` (unified path, #8469) and
    // `collect_implied_disequalities()` (backward-compat wrapper).
}
