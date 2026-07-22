// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF conflict detection helpers for `TheorySolver::check()`.
//!
//! Each method checks one category of conflict: disequalities, distinct
//! constraints, constant clashes, and Boolean congruence.

use ay_core::term::{Constant, TermData, TermId};
use ay_core::{Sort, TheoryLit, TheoryResult};

use crate::solver::EufSolver;

impl EufSolver<'_> {
    /// Extend the watermark-cached term-store indexes (#euf-check-scans).
    ///
    /// The term store is append-only, so terms below the watermark never
    /// change classification; each call folds in only the new suffix. This
    /// turns check()'s per-call costs from O(term store) / O(assigns) into
    /// O(matching candidates).
    pub(crate) fn refresh_term_caches(&mut self) {
        let n = self.terms.len();
        if self.term_cache_watermark >= n {
            return;
        }
        for i in self.term_cache_watermark..n {
            let t = TermId(i as u32);
            match self.terms.get(t) {
                TermData::Const(c) => {
                    if !matches!(c, Constant::Bool(_)) {
                        self.const_terms_cache.push(t);
                    }
                }
                TermData::App(sym, _) => {
                    if sym.name() == "distinct" {
                        self.distinct_terms_cache.push(t);
                    }
                    if self.terms.sort(t) == &Sort::Bool && !Self::is_builtin_symbol(sym) {
                        self.bool_cong_candidates_cache.push(t);
                    }
                }
                TermData::Var(_, _) if self.terms.sort(t) == &Sort::Bool => {
                    self.bool_cong_candidates_cache.push(t);
                }
                _ => {}
            }
        }
        self.term_cache_watermark = n;
    }

    /// Check for conflicts from explicit disequalities `(= a b) = false`
    /// where `find(a) = find(b)`.
    ///
    /// #inc-neg: in incremental mode this avoids the full O(assigns) scan +
    /// sort per check() (formerly the #1 hot leaf on QF_UFLIA BCP-time
    /// checks). The `diseq_pair_index` is kept current by `sync_diseq_index`
    /// (new assertions) and `incremental_merge` (rep rekeying), and every
    /// state transition that can create a diseq violation — asserting over an
    /// already-merged pair, or merging an indexed pair's two classes — pushes
    /// a candidate onto `pending_diseq_conflicts`. Verifying candidates
    /// against the live state keeps stale entries harmless. After a pop the
    /// index is stale (`neg_full_scan_needed`), so the legacy full scan runs.
    pub(crate) fn check_disequality_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        if self.inc_neg_enabled && !self.neg_full_scan_needed && self.enodes_init {
            self.sync_diseq_index();
            // Scan candidates without consuming live ones: a still-valid
            // conflict must be re-reported by every check() until the search
            // backtracks past it (pop clears the vec) — the full scan has that
            // behavior for free by re-scanning. Only verified-stale entries
            // (retracted assignment / merge undone) are dropped.
            while let Some(&(lhs, rhs, lit_term)) = self.pending_diseq_conflicts.first() {
                let retracted = self.assigns.get(&lit_term) != Some(&false)
                    || (lhs.0 as usize) >= self.enodes.len()
                    || (rhs.0 as usize) >= self.enodes.len();
                let split =
                    !retracted && self.enode_find_const(lhs.0) != self.enode_find_const(rhs.0);
                if retracted || split {
                    // #euf-inc-diseq-undo: a candidate whose pair SPLIT is no
                    // longer a conflict but a LIVE disequality. When the
                    // incremental pop-restore is active it skips the post-pop
                    // from-scratch index rebuild that would otherwise re-index it,
                    // so re-queue it (the next `sync_diseq_index` re-indexes it,
                    // and any intervening pop sees a non-empty pending queue and
                    // falls back to the sound rebuild). A truly retracted
                    // candidate is simply dropped. Inactive (small files): this
                    // never runs (the post-pop full rebuild re-indexes for free).
                    if split && self.diseq_undo_active() {
                        self.pending_neg_eqs.push((lit_term, lhs, rhs));
                    }
                    let _ = self.pending_diseq_conflicts.swap_remove(0);
                    continue;
                }
                if debug {
                    safe_eprintln!(
                        "[EUF CHECK] Diseq conflict (incremental): term {} != term {}",
                        lhs.0,
                        rhs.0
                    );
                }
                let reasons = self.explain(lhs, rhs);
                self.conflict_count += 1;
                return Some(self.conflict_with_reasons(reasons, TheoryLit::new(lit_term, false)));
            }
            return None;
        }

        self.scratch_diseqs.clear();
        for (&lit_term, &v) in &self.assigns {
            if !v {
                if let Some((lhs, rhs)) = self.decode_eq(lit_term) {
                    if self.terms.sort(lhs) == self.terms.sort(rhs) {
                        self.scratch_diseqs.push((lit_term, lhs, rhs));
                    }
                }
            }
        }
        self.scratch_diseqs
            .sort_by_key(|(lit_term, _, _)| lit_term.0);

        for idx in 0..self.scratch_diseqs.len() {
            let (lit_term, lhs, rhs) = self.scratch_diseqs[idx];
            let (lhs_rep, rhs_rep) = (self.enode_find_const(lhs.0), self.enode_find_const(rhs.0));
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Diseq: term {} != term {} (reps: {} vs {})",
                    lhs.0,
                    rhs.0,
                    lhs_rep,
                    rhs_rep
                );
            }
            if lhs_rep == rhs_rep {
                if debug {
                    safe_eprintln!("[EUF CHECK] CONFLICT DETECTED!");
                }
                let reasons = self.explain(lhs, rhs);
                if debug {
                    safe_eprintln!(
                        "[EUF CHECK] Conflict explained with {} reasons (vs {} all equalities)",
                        reasons.len(),
                        self.all_true_equalities().len()
                    );
                }
                // Empty reasons is legitimate when the equality was asserted
                // via unconditional shared equality (no preconditions).
                // #6812: Do NOT filter out cross-theory reasons from the conflict.
                // In Nelson-Oppen, explain() returns shared equality reasons that
                // reference terms from another theory (LRA, LIA, arrays). These
                // cross-theory reasons are REQUIRED in the conflict clause.
                self.conflict_count += 1;
                return Some(self.conflict_with_reasons(reasons, TheoryLit::new(lit_term, false)));
            }
        }

        None
    }

    /// Check for conflicts from shared disequalities asserted by other theories (#8469).
    ///
    /// When arithmetic (LIA/LRA) asserts `a != b` and EUF has merged `a` and `b`
    /// into the same equivalence class, that's a conflict. This enables
    /// bidirectional disequality propagation in the Nelson-Oppen loop.
    pub(crate) fn check_shared_disequality_conflicts(&mut self) -> Option<TheoryResult> {
        if self.shared_disequalities.is_empty() || !self.enodes_init {
            return None;
        }

        let debug = self.debug_euf;

        // Iterate over all shared disequalities and check if any pair is now equal.
        // Use a sorted iteration for determinism.
        let mut sorted_diseqs: Vec<((u32, u32), Vec<TheoryLit>)> = self
            .shared_disequalities
            .iter()
            .map(|(&k, v)| (k, v.clone()))
            .collect();
        sorted_diseqs.sort_by_key(|((a, b), _)| (*a, *b));

        for ((a, b), reason) in sorted_diseqs {
            let a_term = TermId(a);
            let b_term = TermId(b);
            if (a as usize) >= self.enodes.len() || (b as usize) >= self.enodes.len() {
                continue;
            }
            let a_root = self.enode_find_const(a);
            let b_root = self.enode_find_const(b);
            if a_root == b_root {
                // Conflict: arithmetic says a != b but EUF has a = b.
                if debug {
                    safe_eprintln!(
                        "[EUF CHECK] Shared disequality conflict: {} != {} but same class (rep={})",
                        a,
                        b,
                        a_root
                    );
                }
                let mut conflict = reason;
                let eq_reason = self.explain(a_term, b_term);
                conflict.extend(eq_reason);
                conflict.sort_unstable_by_key(|l| (l.term.0, l.value));
                conflict.dedup_by_key(|l| (l.term.0, l.value));

                if conflict.is_empty() {
                    return Some(TheoryResult::Unknown);
                }

                self.conflict_count += 1;
                return Some(TheoryResult::Unsat(conflict));
            }
        }

        None
    }

    /// Check for conflicts from `(distinct a b c ...) = true`
    /// where two arguments are in the same equivalence class.
    pub(crate) fn check_distinct_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        // #euf-check-scans: iterate only `distinct` terms (watermark-cached,
        // ascending TermId order) instead of scanning every assignment.
        self.refresh_term_caches();
        self.scratch_distincts.clear();
        for idx in 0..self.distinct_terms_cache.len() {
            let lit_term = self.distinct_terms_cache[idx];
            if self.assigns.get(&lit_term) != Some(&true) {
                continue;
            }
            if let Some(args) = self.decode_distinct(lit_term) {
                self.scratch_distincts.push((lit_term, args.to_vec()));
            }
        }

        if debug {
            safe_eprintln!(
                "[EUF CHECK] Found {} distinct constraints",
                self.scratch_distincts.len()
            );
        }

        for idx in 0..self.scratch_distincts.len() {
            let lit_term = self.scratch_distincts[idx].0;
            let n_args = self.scratch_distincts[idx].1.len();
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Checking distinct term {} with {} args",
                    lit_term.0,
                    n_args
                );
            }
            for i in 0..n_args {
                for j in (i + 1)..n_args {
                    // Index directly into scratch buffer to avoid long-lived borrows (#5575).
                    let arg_i = self.scratch_distincts[idx].1[i];
                    let arg_j = self.scratch_distincts[idx].1[j];
                    let (rep_i, rep_j) = (
                        self.enode_find_const(arg_i.0),
                        self.enode_find_const(arg_j.0),
                    );
                    if debug {
                        safe_eprintln!(
                            "[EUF CHECK] args[{}]={} (rep={}) vs args[{}]={} (rep={})",
                            i,
                            arg_i.0,
                            rep_i,
                            j,
                            arg_j.0,
                            rep_j
                        );
                    }
                    if rep_i == rep_j {
                        let reasons = self.explain(arg_i, arg_j);
                        debug_assert!(
                            !reasons.is_empty(),
                            "BUG(#4840): EUF explain returned empty conflict reasons for distinct ({}, {})",
                            arg_i.0, arg_j.0
                        );
                        if reasons.is_empty() {
                            return Some(TheoryResult::Unknown);
                        }
                        self.conflict_count += 1;
                        return Some(
                            self.conflict_with_reasons(reasons, TheoryLit::new(lit_term, true)),
                        );
                    }
                }
            }
        }

        None
    }

    /// Check for conflicts from distinct constants in the same equivalence class.
    ///
    /// Different constants (e.g., 5 and 6) must never be equal. This axiom is
    /// implicit in most theories: distinct numerals denote distinct values.
    pub(crate) fn check_constant_conflicts(&mut self) -> Option<TheoryResult> {
        let debug = self.debug_euf;

        // #euf-check-scans: iterate only constant terms (watermark-cached)
        // instead of walking the whole term store per check.
        self.refresh_term_caches();
        self.scratch_rep_to_const.clear();
        for i in 0..self.const_terms_cache.len() {
            let term_id = self.const_terms_cache[i];
            if let TermData::Const(c) = self.terms.get(term_id) {
                // Skip Boolean constants - they're handled separately
                if matches!(c, Constant::Bool(_)) {
                    continue;
                }
                let rep = if self.enodes_init {
                    self.enode_find_const(term_id.0)
                } else {
                    self.uf.find(term_id.0)
                };
                if let Some(&(other_term, ref other_const)) = self.scratch_rep_to_const.get(&rep) {
                    if c != other_const {
                        if debug {
                            safe_eprintln!(
                                "[EUF CHECK] Constant conflict: {:?} and {:?} in same class (rep={})",
                                c, other_const, rep
                            );
                        }
                        let mut reasons = self.explain(term_id, other_term);
                        if reasons.is_empty() {
                            // #6812: explain() returned empty reasons for a constant
                            // conflict. Fallback: collect ALL shared equality reasons
                            // + all true equalities as a conservative (sound)
                            // over-approximation.
                            for (_, lits) in &self.shared_equality_reasons {
                                reasons.extend(lits.iter().copied());
                            }
                            reasons.extend(self.all_true_equalities());
                            reasons.sort_unstable_by_key(|l| (l.term, l.value));
                            reasons.dedup_by_key(|l| (l.term, l.value));
                            if reasons.is_empty() {
                                return Some(TheoryResult::Unknown);
                            }
                        }
                        self.conflict_count += 1;
                        return Some(TheoryResult::Unsat(reasons));
                    }
                } else {
                    self.scratch_rep_to_const.insert(rep, (term_id, c.clone()));
                }
            }
        }

        None
    }

    /// Check for conflicts from Boolean congruence: merged Boolean-valued terms
    /// must share their truth value assignment.
    pub(crate) fn check_bool_congruence_conflicts(&mut self) -> Option<TheoryResult> {
        // #euf-idle-rebuild fast path. In production incremental mode every
        // assigned qualifying Bool term (same Var / non-builtin-App filter as
        // `bool_cong_candidates_cache`) has already been merged into its
        // polarity's truth class by `incremental_merge_bool_valued_atoms` —
        // `check()` runs `rebuild_closure()` (which drains those merges) before
        // this check. A truth-value clash inside any class therefore implies
        // the two polarity classes themselves collided, so testing the two
        // anchors is EQUIVALENT to the full candidate scan below (which cost
        // O(|candidates|) per check — the top flat cost on hwbench
        // firewire_tree.3 after the requeue fix). The scan stays for the
        // test-only `bool_arg_congruence` mode (derived-value Bool UF args are
        // not polarity-merged) and the legacy `!enodes_init` path.
        if !self.bool_arg_congruence && self.enodes_init {
            let (Some(true_anchor), Some(false_anchor)) =
                (self.bool_true_anchor, self.bool_false_anchor)
            else {
                return None;
            };
            if self.enode_find_const(true_anchor) != self.enode_find_const(false_anchor) {
                return None;
            }
            let term = TermId(true_anchor);
            let other_term = TermId(false_anchor);
            let mut reasons = self.explain(term, other_term);
            debug_assert!(
                !reasons.is_empty(),
                "BUG(#4840): EUF explain returned empty conflict reasons for bool-congruence anchors ({}, {})",
                term.0,
                other_term.0
            );
            if reasons.is_empty() {
                return Some(TheoryResult::Unknown);
            }
            self.conflict_count += 1;
            let term_lit = self.bool_value_reason_lit(term, true);
            let other_lit = self.bool_value_reason_lit(other_term, false);
            return Some(match (term_lit, other_lit) {
                (Some(pivot), other) => {
                    if let Some(o) = other {
                        reasons.push(o);
                    }
                    self.conflict_with_reasons(reasons, pivot)
                }
                (None, Some(pivot)) => self.conflict_with_reasons(reasons, pivot),
                (None, None) => {
                    if reasons.is_empty() {
                        TheoryResult::Unknown
                    } else {
                        TheoryResult::Unsat(reasons)
                    }
                }
            });
        }
        // Sort by TermId for deterministic conflict detection — different HashMap
        // iteration orders can cause different (but valid) conflicts to be found
        // first, leading to non-deterministic solver behavior (#3041).
        // #euf-check-scans: iterate only Bool-congruence candidate terms
        // (watermark-cached Bool-sorted Var / non-builtin App) plus the
        // Bool-UF-arg set, instead of filtering every assignment per check.
        // The union may hold a term twice; the sort+dedup below collapses it.
        self.refresh_term_caches();
        self.scratch_bool_terms.clear();
        for idx in 0..self.bool_cong_candidates_cache.len() {
            let term = self.bool_cong_candidates_cache[idx];
            if let Some(&val) = self.assigns.get(&term) {
                self.scratch_bool_terms.push((term, val));
            }
        }
        if self.bool_arg_congruence {
            // #bool-arg-congruence: also enforce truth-value consistency for any
            // Bool-sorted term used as a UF argument (builtin/connective apps
            // included), mirroring the extended Bool-value merge so that a
            // non-congruent assignment is REJECTED as a conflict rather than
            // accepted as SAT.
            self.scratch_bool_uf_args.clear();
            self.scratch_bool_uf_args
                .extend(self.bool_uf_arg_terms.iter().copied());
            self.scratch_bool_uf_args.sort_unstable();
            for idx in 0..self.scratch_bool_uf_args.len() {
                let term = TermId(self.scratch_bool_uf_args[idx]);
                if self.terms.sort(term) != &Sort::Bool {
                    continue;
                }
                if let Some(&val) = self.assigns.get(&term) {
                    self.scratch_bool_terms.push((term, val));
                }
            }
        }
        // #bool-arg-congruence: include derived-value Bool UF args (e.g.
        // `Not(inner)` whose value is tracked via the inner atom) so the
        // truth-value-consistency net also covers them. The conflict ALSO
        // surfaces through check_disequality_conflicts, but this keeps the
        // bool-congruence net symmetric with the extended Bool-value merge.
        if self.bool_arg_congruence {
            self.scratch_bool_uf_args.clear();
            self.scratch_bool_uf_args.extend(
                self.bool_uf_arg_terms
                    .iter()
                    .copied()
                    .filter(|&t| !self.assigns.contains_key(&TermId(t))),
            );
            self.scratch_bool_uf_args.sort_unstable();
            for idx in 0..self.scratch_bool_uf_args.len() {
                let t = TermId(self.scratch_bool_uf_args[idx]);
                if let Some(v) = self.derive_bool_term_value(t) {
                    self.scratch_bool_terms.push((t, v));
                }
            }
        }
        self.scratch_bool_terms.sort_by_key(|(term, _)| *term);
        // A term can enter via both the candidate cache and the Bool-UF-arg
        // set; its value comes from the same `assigns` lookup either way.
        self.scratch_bool_terms.dedup_by_key(|(term, _)| *term);

        self.scratch_rep_value.clear();
        for idx in 0..self.scratch_bool_terms.len() {
            let (term, val) = self.scratch_bool_terms[idx];
            let rep = if self.enodes_init {
                self.enode_find_const(term.0)
            } else {
                self.uf.find(term.0)
            };
            if let Some(&(other_term, other_val)) = self.scratch_rep_value.get(&rep) {
                if other_val != val {
                    // Use explain() for minimal conflict clause
                    let mut reasons = self.explain(term, other_term);
                    debug_assert!(
                        !reasons.is_empty(),
                        "BUG(#4840): EUF explain returned empty conflict reasons for bool-congruence ({}, {})",
                        term.0, other_term.0
                    );
                    if reasons.is_empty() {
                        return Some(TheoryResult::Unknown);
                    }
                    // #bool-arg-congruence: unwrap `Not`/drop constant endpoints
                    // so the conflict literals reference SAT-owned atoms.
                    // Choose a non-constant endpoint as the conflict pivot; the
                    // other endpoint (if non-constant) becomes a reason literal.
                    // If BOTH endpoints are constants their truth values clash
                    // unconditionally — the merge reasons alone are the (sound,
                    // possibly empty-after-filter) conflict.
                    self.conflict_count += 1;
                    let term_lit = self.bool_value_reason_lit(term, val);
                    let other_lit = self.bool_value_reason_lit(other_term, other_val);
                    match (term_lit, other_lit) {
                        (Some(pivot), other) => {
                            if let Some(o) = other {
                                reasons.push(o);
                            }
                            return Some(self.conflict_with_reasons(reasons, pivot));
                        }
                        (None, Some(pivot)) => {
                            return Some(self.conflict_with_reasons(reasons, pivot));
                        }
                        (None, None) => {
                            if reasons.is_empty() {
                                return Some(TheoryResult::Unknown);
                            }
                            return Some(TheoryResult::Unsat(reasons));
                        }
                    }
                }
            } else {
                self.scratch_rep_value.insert(rep, (term, val));
            }
        }

        None
    }
}
