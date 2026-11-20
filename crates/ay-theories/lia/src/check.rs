// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core LIA check logic.
//!
//! Implements the main `check_inner()` method which coordinates:
//! - Constant Bool atom contradiction detection
//! - GCD feasibility tests
//! - Diophantine equation solving (2-variable and general)
//! - Iterative Diophantine tightening
//! - Gomory cut generation
//! - HNF cut generation
//! - Direct enumeration for small variable domains
//! - Integer bounds gap detection
//! - Modular constraint checking
//! - Branch-and-bound splitting

use super::*;
use crate::intsat_bridge;

impl LiaSolver<'_> {
    // ---------- Phase-timed wrappers (#8823) ----------
    //
    // Each wrapper measures `Instant::now().elapsed()` around the inner call
    // and accumulates into `self.timings.<phase>`. Dispatchers read these
    // via `LiaSolver::timings()`. Before #8823 that accessor returned a
    // static zero, so all dispatch decisions that consulted LIA timings
    // were driven by fake telemetry.

    /// Time-tracked LRA simplex check (`simplex` bucket).
    pub(crate) fn timed_lra_check(&mut self) -> TheoryResult {
        let start = ay_core::time::Instant::now();
        let result = self.lra.check();
        self.timings.simplex += start.elapsed();
        result
    }

    /// Time-tracked BCP-path LRA simplex check (`simplex` bucket).
    pub(crate) fn timed_lra_check_during_propagate(&mut self) -> TheoryResult {
        let start = ay_core::time::Instant::now();
        let result = self.lra.check_during_propagate();
        self.timings.simplex += start.elapsed();
        result
    }

    /// Time-tracked dual-simplex feasibility probe (`simplex` bucket).
    pub(crate) fn timed_lra_dual_simplex(&mut self) -> TheoryResult {
        let start = ay_core::time::Instant::now();
        let result = self.lra.dual_simplex();
        self.timings.simplex += start.elapsed();
        result
    }

    /// Time-tracked Gomory cut generation (`gomory` bucket).
    pub(crate) fn timed_generate_gomory_cuts(&mut self) -> Vec<ay_lra::GomoryCut> {
        let start = ay_core::time::Instant::now();
        let cuts = self.lra.generate_gomory_cuts(&self.integer_vars);
        self.timings.gomory += start.elapsed();
        instrument::bump(&instrument::GOMORY_GEN_CALLS);
        instrument::bump_by(&instrument::GOMORY_GENERATED, cuts.len() as u64);
        cuts
    }

    /// Time-tracked Gomory cut insertion (`gomory` bucket).
    pub(crate) fn timed_add_gomory_cut(&mut self, cut: &ay_lra::GomoryCut, source: TermId) {
        let start = ay_core::time::Instant::now();
        instrument::bump(&instrument::GOMORY_ACCEPTED);
        self.lra.add_gomory_cut(cut, source);
        // A single-var cut tightens that var's direct bound; rather than
        // parse the cut shape, conservatively rescan everything (#C4).
        // Cuts only happen in the full-check cascade, never at BCP time.
        self.mark_int_bounds_all_dirty();
        self.timings.gomory += start.elapsed();
    }

    /// Time-tracked HNF cut round (`hnf` bucket).
    pub(crate) fn timed_try_hnf_cuts(&mut self, var: TermId) -> bool {
        let start = ay_core::time::Instant::now();
        instrument::bump(&instrument::HNF_ATTEMPTS);
        let result = self.try_hnf_cuts(var);
        self.timings.hnf += start.elapsed();
        if result {
            instrument::bump(&instrument::HNF_ROUNDS_FIRED);
        }
        result
    }

    /// Time-tracked general Diophantine solve (`dioph` bucket).
    pub(crate) fn timed_try_diophantine_solve(&mut self) -> Option<Vec<TheoryLit>> {
        let start = ay_core::time::Instant::now();
        let result = self.try_diophantine_solve();
        self.timings.dioph += start.elapsed();
        result
    }

    /// Time-tracked 2-variable Diophantine solve (`dioph` bucket).
    pub(crate) fn timed_try_two_variable_solve(&mut self) -> Option<Vec<TheoryLit>> {
        let start = ay_core::time::Instant::now();
        let result = self.try_two_variable_solve();
        self.timings.dioph += start.elapsed();
        result
    }

    /// Time-tracked Dioph substitution bound propagation (`dioph` bucket).
    pub(crate) fn timed_propagate_bounds_through_substitutions(&mut self) -> bool {
        let start = ay_core::time::Instant::now();
        let result = self.propagate_bounds_through_substitutions();
        self.timings.dioph += start.elapsed();
        result
    }

    /// Time-tracked Dioph tableau-row tightening (`dioph` bucket).
    pub(crate) fn timed_tighten_tableau_rows_via_dioph(&mut self) -> bool {
        let start = ay_core::time::Instant::now();
        let result = self.tighten_tableau_rows_via_dioph();
        self.timings.dioph += start.elapsed();
        result
    }

    /// Augment a Farkas conflict with relevant shared equality and Dioph
    /// reasons (#8147, #8012).
    ///
    /// When shared equalities are active, LRA Farkas conflicts may be
    /// incomplete: N-O shared equality constraints create slack variables
    /// bounded at [0,0]. After simplex pivots, these slacks may not appear
    /// in the conflicting row, so their reasons are invisible to the Farkas
    /// conflict builder.
    ///
    /// The previous blanket fix added ALL shared equality reasons to ALL
    /// conflicts, which was sound but caused 100% QF_UFLIA completeness
    /// regression (all benchmarks returned unknown). This targeted version
    /// only adds reasons from shared equalities whose constraint variables
    /// (lhs or rhs term IDs) appear in the conflict existing literals.
    /// This preserves soundness (relevant reasons are included) while
    /// keeping learned clauses strong (irrelevant reasons are excluded).
    /// #8784: a reason literal is LIVE when it is still on the DPLL trail (or is
    /// a sentinel). Augmenting a conflict with a stale literal weakens the
    /// blocking clause; leaving one out of a core we depend on invalidates it.
    /// Single source of truth for both `probe_needed_shared_equalities` (which
    /// may only build a core out of equalities whose reasons survive this) and
    /// the emit loop below (which applies it).
    fn reason_is_live(&self, reason: &TheoryLit) -> bool {
        reason.term.is_sentinel()
            || self
                .lra
                .conflict_literals_all_asserted(std::slice::from_ref(reason))
            || self
                .asserted
                .iter()
                .any(|&(t, v)| t == reason.term && v == reason.value)
    }

    /// #shared-eq-core: SHRINK the closure's shared-equality set to a subset
    /// that is *provably* sufficient to make `literals` infeasible.
    ///
    /// `candidates` are the equality indices the closure would have used. This
    /// routine only ever returns a SUBSET of them, and only after a probe solver
    /// actually reproduces the infeasibility from `literals` plus exactly that
    /// subset — so the emitted clause is valid by construction, not assumption.
    /// `None` means "could not prove it", and the caller keeps the full closure.
    /// It never returns a set it has not proved: under-including a reason makes
    /// the clause too strong, i.e. a FALSE UNSAT.
    ///
    /// Two contracts constrain the result, and both are load-bearing:
    ///
    /// 1. The subset is drawn ONLY from `candidates`. An equality the closure
    ///    deems unreachable from the conflict must never be dragged in (see
    ///    `test_augmentation_without_appends_keeps_certificate`).
    /// 2. The subset is NEVER EMPTY when candidates exist — even if `literals`
    ///    is already infeasible on its own. The appended reasons are load-bearing
    ///    for PROGRESS, not just validity: the conflict's own atoms can be
    ///    equalities EUF derived by congruence, which the SAT solver cannot flip,
    ///    so a clause built from them alone does not exclude the current
    ///    assignment. The same conflict then recurs, the split loop makes no
    ///    progress, and the eager pipeline's no-progress guard escalates to
    ///    `unknown` (observed on QF_UFLIA/seq_dense_ghost_vec). A reason literal
    ///    IS SAT-visible, so keeping at least one keeps the clause prunable.
    ///    This is the same invariant as `#lemma-must-prune`: a clause emitted in
    ///    response to a model must be falsified by that model.
    ///
    /// Appending an extra reason only ever WEAKENS the clause (adds a disjunct),
    /// so requiring a non-empty subset can never turn a valid clause invalid.
    fn probe_needed_shared_equalities(
        &self,
        literals: &[TheoryLit],
        candidates: &[usize],
    ) -> Option<Vec<usize>> {
        // A probe never probes again (it has no shared equalities of its own).
        if self.conflict_probe || candidates.is_empty() {
            return None;
        }
        // Lever-P ceiling experiment (eager-theory-prop design §5.5):
        // --no-lia-probe-scan skips the minimization scan entirely, taking the
        // sound full-closure augmentation fallback. Diagnostic-only knob to
        // measure how much of the spin-cell budget the probe storm costs vs
        // how load-bearing minimized clauses are. Default (unset) unchanged.
        if ay_core::theory_disable_flags().no_lia_probe_scan {
            return None;
        }

        // Only equalities whose reasons will ACTUALLY REACH the clause may be
        // used in the proof: the clause carries an equality's REASONS, not the
        // equality itself, so if the #8784 liveness filter drops one (or the
        // reason set is empty) the clause would assert an infeasibility it no
        // longer justifies.
        let usable: Vec<usize> = candidates
            .iter()
            .copied()
            .filter(|&i| {
                let (_, _, reasons) = &self.shared_equalities[i];
                !reasons.is_empty() && reasons.iter().all(|r| self.reason_is_live(r))
            })
            .collect();
        if usable.is_empty() {
            return None;
        }

        // Equalities touching a conflict variable first, so the proven subset
        // stays small and the common case settles in one extra check.
        let mut conflict_vars: HashSet<TermId> = HashSet::default();
        for lit in literals {
            collect_atom_vars_impl(self.terms(), lit.term, &mut conflict_vars);
        }
        let touches = |i: usize| -> bool {
            let (lhs, rhs, _) = &self.shared_equalities[i];
            conflict_vars.contains(lhs) || conflict_vars.contains(rhs)
        };
        let mut order: Vec<usize> = usable.iter().copied().filter(|&i| touches(i)).collect();
        order.extend(usable.iter().copied().filter(|&i| !touches(i)));

        let mut probe_checks = 0u64;

        // #probe-subset-cache: consecutive lazy-round conflicts are produced
        // by NEARBY SAT models over the same formula, so the shared-equality
        // subset that reproduced the last infeasibility usually reproduces
        // the next one. Try the last proven subset FIRST in a single batch
        // check before the one-at-a-time forward scan (~5.8 checks/conflict
        // measured; each check pays a BigRational Gaussian elimination — the
        // dominant per-round cost of the UFLIA hybrid's lazy detour). SOUND
        // by the same argument as the forward scan: the guess is only ever
        // ACCEPTED when the probe actually re-derives UNSAT from `literals`
        // plus exactly the asserted subset, and the subset is drawn only
        // from `usable` (contract 1) and never empty (contract 2). A wrong
        // or stale guess costs one extra check and falls through to the
        // forward scan over the remaining candidates (the probe is
        // add-only, so the final `used` is the cached prefix plus the scan
        // prefix — a proven-sufficient, if not minimal, subset).
        // Keyed by (lhs, rhs) TermId pairs (indices shift across rounds:
        // each lazy round builds a fresh combiner). Thread-local: probes are
        // per-solver-thread and the hint is heuristic-only.
        let mut used: Vec<usize> = Vec::new();
        let hinted: Vec<usize> = if !self.probe_subset_cache_active() {
            Vec::new()
        } else {
            PROBE_SUBSET_HINT.with(|hint| {
                let hint = hint.borrow();
                if hint.is_empty() {
                    return Vec::new();
                }
                let pairs: HashSet<(TermId, TermId)> = hint.iter().copied().collect();
                order
                    .iter()
                    .copied()
                    .filter(|&i| {
                        let (lhs, rhs, _) = &self.shared_equalities[i];
                        pairs.contains(&(*lhs, *rhs)) || pairs.contains(&(*rhs, *lhs))
                    })
                    .collect()
            })
        };
        let record_hint = |used: &[usize]| {
            if !self.probe_subset_cache_active() {
                return;
            }
            PROBE_SUBSET_HINT.with(|hint| {
                let mut hint = hint.borrow_mut();
                hint.clear();
                hint.extend(used.iter().map(|&i| {
                    let (lhs, rhs, _) = &self.shared_equalities[i];
                    (*lhs, *rhs)
                }));
            });
        };
        let mut probe = self.build_conflict_probe(literals);

        // #shared-eq-zero-core: ask the STRONGEST question FIRST — are the
        // conflict literals infeasible with NO shared equality asserted at all?
        // The scan below deliberately never asks it ("the check comes AFTER the
        // first add, never before"), so a conflict that needs no shared-equality
        // reason could only be discovered by asserting every candidate and
        // failing — which lands the caller on the full-closure
        // over-approximation, the very clause this probe exists to avoid.
        //
        // That is not a corner case, and the reason it is not is that the probe
        // is NOT monotone in the asserted set: LIA gates its finite-domain CSP
        // search on `shared_equalities` being EMPTY (`FINITE_DOMAIN_SKIPS`), so
        // a probe holding one shared equality can answer `Sat`/`NeedSplit`
        // where the SAME literals with none answer `Unsat`. Measured on the
        // `inc_some_list` dual-vocabulary obligation
        // (#dt-uf-bridge-congruence): the empty probe refutes 135/135
        // augmentations, while the scan then asserts a 224-equality closure one
        // at a time — ~232 full LIA checks apiece, 82 s of a 233 s solve, never
        // reproducing the infeasibility — and hands back the whole closure. The
        // emitted clause grows from the simplex's ~6 literals to 120-624, i.e.
        // essentially the entire interface assignment, and CDCL degenerates
        // into model enumeration (#7956). With the zero-core check the same
        // solve emits at most 19 literals per conflict and the augmentation
        // costs 26 ms in total.
        //
        // SOUNDNESS is the scan's own acceptance rule, unchanged and applied to
        // the strongest subset: the empty set is RETURNED only after an actual
        // probe check re-derives UNSAT from `literals` alone, never by
        // inference. A directly PROVEN empty core
        // carries the same authority as any proven singleton and yields the
        // strongest sound clause available — exactly the negation of the
        // conflict the theory already published.
        //
        // The CERTIFICATE rule below is untouched and its retention on this
        // path is BETTER justified than on the pre-existing one, not worse.
        // The simplex builder may miss pivoted-away shared-equality slack
        // reasons, so appended reasons may be load-bearing. This exit is
        // reached only after a FRESH solver re-derives the infeasibility from
        // the unaugmented literals with no shared equality asserted at all — a
        // direct proof that the literal set is a complete explanation.
        if !self.should_timeout() {
            probe_checks += 1;
            if probe_verdict_is_unsat(&probe.check()) {
                probe_stats_record(probe_checks, true, 0);
                record_hint(&[]);
                PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
                return Some(Vec::new());
            }
        }

        // Size guards: a hint as large as the whole candidate order proves
        // nothing the scan would not, and a large hint both weakens the
        // emitted clause (every member's reasons are appended) and makes the
        // batch detection expensive — measured proven subsets are ~5-6
        // equalities, so 24 is generous headroom against slow ratchet
        // (batch-fail extensions can only grow the hint via `used`).
        if !hinted.is_empty() && hinted.len() < order.len() && hinted.len() <= 24 {
            for &i in &hinted {
                let (lhs, rhs, _) = &self.shared_equalities[i];
                probe.assert_shared_equality(*lhs, *rhs, &[]);
                used.push(i);
            }
            probe_checks += 1;
            if probe_verdict_is_unsat(&probe.check()) {
                probe_stats_record(probe_checks, true, used.len());
                record_hint(&used);
                PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
                return Some(used);
            }
        }

        // Add equalities until the infeasibility reproduces. The check comes
        // AFTER the first add, never before — that is contract 2 (when the
        // cached-subset batch ran above, its members are already asserted
        // and stay in `used`; the scan below skips them).
        let order_len = order.len();
        for i in order {
            if used.contains(&i) {
                continue;
            }
            // #lia-deadline-forward: the forward scan is O(candidates) full
            // probe checks — poll the parent's deadline between adds so a
            // dense probe loop cannot outlive the theory budget. `None`
            // falls back to the sound full-closure augmentation.
            if self.should_timeout() {
                probe_stats_record(probe_checks, false, 0);
                return None;
            }
            let (lhs, rhs, _) = &self.shared_equalities[i];
            let (lhs, rhs) = (*lhs, *rhs);
            // Assert the equality's ARITHMETIC content only (no reasons): we ask
            // which equalities the infeasibility needs, not why they hold.
            probe.assert_shared_equality(lhs, rhs, &[]);
            used.push(i);
            probe_checks += 1;
            if probe_verdict_is_unsat(&probe.check()) {
                probe_stats_record(probe_checks, true, used.len());
                record_hint(&used);
                PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
                return Some(used);
            }
        }
        probe_stats_record(probe_checks, false, 0);
        // A failed scan invalidates the hint: the conflict landscape has
        // moved (or the closure shrank); a stale hint would keep paying the
        // extra batch check on every future conflict.
        if self.probe_subset_cache_active() {
            PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
        }
        // Exhausted scan: every candidate was asserted and the infeasibility
        // still did not reproduce. Counted only when the scan was expensive
        // (saturating).
        if order_len >= PROBE_SCAN_SWITCH_MIN_ORDER {
            PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(streak.get().saturating_add(1)));
            PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.set(total.get().saturating_add(1)));
            probe_scan_big_fail_record(order_len);
        }
        None
    }

    /// Build a conflict-probe solver over `literals`; the scan then asserts
    /// shared equalities into it one at a time, reasons stripped.
    ///
    /// #lia-deadline-forward: the probe runs FULL LIA checks with BigRational
    /// Gaussian elimination inside — a probe with no deadline is the
    /// documented augment-farkas spin that ignores the theory budget, so it
    /// inherits the parent's wall deadline (a check exits Unknown at the
    /// boundary; Unknown is simply "not proven" to every caller here).
    ///
    /// Mirror the parent solver's combined-theory mode (#8373). This probe is
    /// only reachable when `shared_equalities` is non-empty, i.e. inside a
    /// Nelson-Oppen combination where cross-theory operands (UF applications
    /// such as seq_len/seq_offset, array selects) appear inside the conflict
    /// literals. In standalone mode the inner LRA marks those operands as
    /// "unsupported" and downgrades the probe's simplex Sat/Unsat to Unknown,
    /// so probe-UNSAT is never observed, the minimal shared-equality subset is
    /// never found, and `augment_farkas_with_shared_reasons` falls back to the
    /// full-closure over-approximation — the exact #7956 churn the probe was
    /// added to avoid. Opaque abstraction of the cross-theory operands is a
    /// sound relaxation: relaxation-UNSAT implies the real
    /// (congruence-refined) problem is UNSAT, so any subset the probe proves
    /// sufficient is genuinely sufficient.
    fn build_conflict_probe(&self, literals: &[TheoryLit]) -> Self {
        let mut probe = LiaSolver::new(self.terms());
        probe.conflict_probe = true;
        probe.deadline = self.deadline;
        probe.set_combined_theory_mode(self.combined_theory_mode());
        for lit in literals {
            probe.register_atom(lit.term);
            probe.assert_literal(lit.term, lit.value);
        }
        probe
    }

    /// Whether the #probe-subset-cache batch guess is active for this
    /// solver's probes: `AY_PROBE_SUBSET_CACHE=0|1` force-overrides
    /// (kill/force, process-cached); otherwise the per-solver opt-in set by
    /// `set_probe_subset_cache` decides (default OFF — see `types.rs`).
    fn probe_subset_cache_active(&self) -> bool {
        // B24: the typed field IS the carrier; the env override shim over it
        // is retired.
        self.probe_subset_cache
    }

    pub(super) fn augment_farkas_with_shared_reasons(
        &mut self,
        conflict: TheoryConflict,
    ) -> TheoryConflict {
        // #uflia-verify-only: verification solvers discard the conflict
        // payload — only the result VARIANT is inspected. Skip the (probe-
        // driven) augmentation entirely; the verdict is already decided.
        if self.verify_only {
            return conflict;
        }
        let has_shared = !self.shared_equalities.is_empty();
        let has_dioph = self.dioph_modified_bounds && !self.dioph_cached_reasons.is_empty();
        if !has_shared && !has_dioph {
            return conflict;
        }
        // TEMP-DIAG (#certora-w8): env-gated augmentation telemetry.
        {
            static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *TRACE.get_or_init(|| ay_core::misc_cli_flags().certora_trace) {
                use std::sync::atomic::{AtomicU64, Ordering};
                static CALLS: AtomicU64 = AtomicU64::new(0);
                let n = CALLS.fetch_add(1, Ordering::Relaxed) + 1;
                if n.is_multiple_of(64) {
                    safe_eprintln!(
                        "[AUG-TRACE] augments={} shared_eqs={} conflict_len={}",
                        n,
                        self.shared_equalities.len(),
                        conflict.literals.len()
                    );
                }
            }
        }
        let farkas = conflict.farkas;
        let mut literals = conflict.literals;
        let original_len = literals.len();
        let mut seen: HashSet<TheoryLit> = literals.iter().copied().collect();
        if has_shared {
            // #8147 fix: shared_equalities stores (lhs_var, rhs_var, reasons)
            // where lhs/rhs are *variable* TermIds, but conflict literals use
            // *atom* TermIds (e.g., (<= x 5)). Decompose atoms to extract vars,
            // then use transitive closure through the shared equality graph.
            // Reuse persistent buffer to avoid per-conflict allocation (#8599).
            // Use free function for split-borrow compatibility.
            // The closure: reachability through the shared-equality graph.
            // Sound but blunt — on AUFLIA sequence problems that graph is ONE
            // connected component (seq_len / seq_offset / seq_array all link up),
            // so essentially every shared equality's reasons land in every
            // conflict: measured 92-117 literals on a ~134-var problem. A clause
            // naming most of the assignment excludes ~one model, so CDCL
            // degenerates into model enumeration and the refinement loop never
            // converges (#7956).
            self.reachable_vars_buf.clear();
            for lit in &literals {
                collect_atom_vars_impl(self.terms(), lit.term, &mut self.reachable_vars_buf);
            }
            let mut changed = true;
            while changed {
                changed = false;
                for (lhs, rhs, _reasons) in &self.shared_equalities {
                    let lhs_in = self.reachable_vars_buf.contains(lhs);
                    let rhs_in = self.reachable_vars_buf.contains(rhs);
                    if lhs_in || rhs_in {
                        if lhs_in && self.reachable_vars_buf.insert(*rhs) {
                            changed = true;
                        }
                        if rhs_in && self.reachable_vars_buf.insert(*lhs) {
                            changed = true;
                        }
                    }
                }
            }
            let closure: Vec<usize> = self
                .shared_equalities
                .iter()
                .enumerate()
                .filter(|(_, (lhs, rhs, _))| {
                    self.reachable_vars_buf.contains(lhs) || self.reachable_vars_buf.contains(rhs)
                })
                .map(|(i, _)| i)
                .collect();

            // #shared-eq-core: don't GUESS which of those the conflict needs —
            // PROVE it. The shared equalities are ARITHMETIC facts, so a probe
            // LiaSolver can replay `literals` and add closure equalities until the
            // infeasibility reproduces. Whatever subset reproduces it is, by
            // construction, sufficient: each equality is entailed by its reasons,
            // so the clause stays valid. Anything unproven falls back to the full
            // closure — never to a smaller guess.
            let probed = self.probe_needed_shared_equalities(&literals, &closure);
            // INTERFACE-DIET M0/C5 (verdict-neutral): probe success + core-size
            // telemetry — validates whether reason-minimization is the wall.
            if !closure.is_empty() {
                instrument::bump(&instrument::FARKAS_PROBE_ATTEMPTS);
                instrument::bump_by(&instrument::FARKAS_PROBE_CLOSURE_SUM, closure.len() as u64);
                if let Some(subset) = &probed {
                    instrument::bump(&instrument::FARKAS_PROBE_PROVED);
                    instrument::bump_by(&instrument::FARKAS_PROBE_SUBSET_SUM, subset.len() as u64);
                }
            }
            let selected: Option<HashSet<usize>> =
                probed.map(|v| v.into_iter().collect::<HashSet<usize>>());

            for (idx, (lhs, rhs, reasons)) in self.shared_equalities.iter().enumerate() {
                let include = match &selected {
                    // Proven-sufficient subset of the closure: take exactly these.
                    Some(needed) => needed.contains(&idx),
                    // Unproven: keep the sound closure over-approximation.
                    None => {
                        self.reachable_vars_buf.contains(lhs)
                            || self.reachable_vars_buf.contains(rhs)
                    }
                };
                if include {
                    for reason in reasons {
                        // #8784: skip reason literals no longer live on the DPLL
                        // trail (see `reason_is_live`). A core produced by
                        // `probe_needed_shared_equalities` only ever uses
                        // equalities all of whose reasons pass this, so this
                        // filter cannot silently gut a proven core.
                        if !self.reason_is_live(reason) {
                            continue;
                        }
                        if seen.insert(*reason) {
                            literals.push(*reason);
                        }
                    }
                }
            }
        }
        if has_dioph {
            // Targeted augmentation: only add dioph reasons if the conflict
            // involves variables whose bounds were set by Diophantine solving.
            // The old blanket approach added ALL dioph reasons to ALL conflicts,
            // which weakened learned clauses and degraded CHC interpolation.
            // Reuse persistent buffer to avoid per-conflict allocation (#8599).
            // Use free function for split-borrow compatibility.
            self.conflict_vars_buf.clear();
            for lit in &literals {
                collect_atom_vars_impl(self.terms(), lit.term, &mut self.conflict_vars_buf);
            }
            let dioph_relevant = self
                .conflict_vars_buf
                .iter()
                .any(|v| self.dioph_bound_term_ids.contains(v));
            if dioph_relevant {
                for &(term, value) in &self.dioph_cached_reasons {
                    let lit = TheoryLit::new(term, value);
                    if seen.insert(lit) {
                        literals.push(lit);
                    }
                }
            }
        }
        // #rank-4 increment 2 (adversarial-review fix): keep the certificate
        // ONLY when augmentation appended nothing. The positional certificate
        // covers only the pre-augmentation literal vector and establishes no
        // coefficient for appended shared-equality/Dioph reasons, which may be
        // load-bearing when the simplex builder missed pivoted-away slack
        // reasons (#8147). Dropping the certificate whenever literals were
        // appended keeps the verdict and learned clause intact; the no-append
        // case (still the common one) keeps the certificate.
        match farkas {
            Some(farkas)
                if literals.len() == original_len && farkas.coefficients.len() == original_len =>
            {
                TheoryConflict::with_farkas(literals, farkas)
            }
            _ => TheoryConflict::new(literals),
        }
    }

    /// #8784: Stale-reason guard for LIA conflicts whose reasons can include
    /// EUF-propagated shared-equality literals.
    ///
    /// Returns `true` when every non-sentinel literal is still live — either
    /// (a) directly in LIA's `asserted` trail, or (b) in the underlying LRA
    /// solver's `asserted` / `cross_theory_asserted` trails. Mirrors
    /// `LraSolver::conflict_literals_all_asserted` (farkas_collect.rs:56).
    ///
    /// Background: LIA's `pending_shared_eq_conflict` and
    /// `augment_farkas_with_shared_reasons` build conflicts from
    /// `self.shared_equalities`, whose reasons originate in EUF and so are
    /// never added to LIA's own `asserted` vector. Between the time those
    /// shared equalities arrive and the time the conflict is published,
    /// DPLL(T) backtracking may retract one or more reason atoms. Publishing
    /// such a conflict as a blocking clause is unsound — it can turn a SAT
    /// instance into a false UNSAT (regression on Creusot-style
    /// `seq_dense_ghost_vec.smt2`).
    pub(crate) fn conflict_reasons_all_live(&self, reasons: &[TheoryLit]) -> bool {
        if self.lra.conflict_literals_all_asserted(reasons) {
            return true;
        }
        // LIA's own `asserted` is a Vec (pushed in order), so fall back to a
        // linear scan for any literal the LRA trail did not cover.
        for lit in reasons {
            if lit.term.is_sentinel() {
                continue;
            }
            let lra_live = self
                .lra
                .conflict_literals_all_asserted(std::slice::from_ref(lit));
            if lra_live {
                continue;
            }
            let lia_live = self
                .asserted
                .iter()
                .any(|&(term, value)| term == lit.term && value == lit.value);
            if !lia_live {
                return false;
            }
        }
        true
    }
}

thread_local! {
    /// #probe-subset-cache: the last proven-sufficient shared-equality subset
    /// (as `(lhs, rhs)` TermId pairs — indices shift across rounds because
    /// each lazy round builds a fresh combiner). Thread-local because probes
    /// run on their solver's thread and the hint is heuristic-only: a stale
    /// or foreign entry is verified by an actual probe check before use, so
    /// it can cost at most one wasted check, never a wrong subset.
    static PROBE_SUBSET_HINT: std::cell::RefCell<Vec<(TermId, TermId)>> =
        const { std::cell::RefCell::new(Vec::new()) };

    /// Consecutive EXHAUSTED-scan failures of the forward scan over
    /// `PROBE_SCAN_SWITCH_MIN_ORDER`+ candidate orders (deadline aborts do not
    /// count; a scan success resets it). Probe trajectory state only: saved,
    /// restored and reset with the hint (see [`ProbeStateSnapshot`]).
    static PROBE_SCAN_FAIL_STREAK: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };

    /// Monotone per-attempt count of big exhausted scan failures (same
    /// counting rule as the streak, no reset on success).
    static PROBE_SCAN_BIG_FAIL_TOTAL: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// An exhausted scan only counts (streak, total, `probe_scan_big_fail_record`)
/// when its candidate order was at least this large: a failing scan over a
/// tiny order is cheap. Measured orders: Hash family mostly ~1-3, hard*
/// refutations ~50-500.
const PROBE_SCAN_SWITCH_MIN_ORDER: usize = 16;

/// A DEFINITE infeasibility verdict from a probe check. `Unknown`/`NeedSplit`
/// and budget outcomes decide NOTHING — they mean "not proven", never "proven
/// feasible".
fn probe_verdict_is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_))
}

/// Reset the #probe-subset-cache hint. Called by the UFLIA hybrid at lazy
/// DETOUR entry so a subset proven under a previous attempt (or a previous
/// check-sat) never seeds the first conflicts of a new detour. Also clears
/// the fail streak and total, which are part of the same trajectory state.
///
/// The executor also resets at every external decision query, so a query on a
/// thread that served others before it starts from the same state, and around
/// a same-context probe (with [`save_probe_state`] / [`restore_probe_state`]),
/// so a probe neither inherits nor leaves the enclosing solve's state.
pub fn reset_probe_subset_hint() {
    PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
    PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
    PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.set(0));
}

/// Opaque snapshot of the thread-local probe trajectory state
/// (#detour-snapshot-extend): the #probe-subset-cache hint plus the
/// exhausted-scan fail streak/total. Taken by the UFLIA hybrid at a
/// SPECULATIVE detour-extension decision point and restored when the
/// speculation fails to decide, so the post-detour eager resume observes
/// EXACTLY the probe state it would have seen without the speculation
/// (exact-replay contract). The state is heuristic-only — a stale hint is
/// verified by an actual probe check before use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProbeStateSnapshot {
    hint: Vec<(TermId, TermId)>,
    scan_fail_streak: u32,
    scan_big_fail_total: u64,
}

/// Capture the thread-local probe trajectory state (see
/// [`ProbeStateSnapshot`]).
pub fn save_probe_state() -> ProbeStateSnapshot {
    ProbeStateSnapshot {
        hint: PROBE_SUBSET_HINT.with(|hint| hint.borrow().clone()),
        scan_fail_streak: PROBE_SCAN_FAIL_STREAK.with(std::cell::Cell::get),
        scan_big_fail_total: PROBE_SCAN_BIG_FAIL_TOTAL.with(std::cell::Cell::get),
    }
}

/// Restore a previously captured probe trajectory state (see
/// [`ProbeStateSnapshot`]).
pub fn restore_probe_state(snapshot: ProbeStateSnapshot) {
    PROBE_SUBSET_HINT.with(|hint| *hint.borrow_mut() = snapshot.hint);
    PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(snapshot.scan_fail_streak));
    PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.set(snapshot.scan_big_fail_total));
}

/// A probe trajectory state built from its parts, for tests of the callers
/// that reset, save and restore it (install it with [`restore_probe_state`]).
/// Not a public API.
#[doc(hidden)]
#[must_use]
pub fn probe_state_for_tests(
    hint: Vec<(TermId, TermId)>,
    scan_fail_streak: u32,
    scan_big_fail_total: u64,
) -> ProbeStateSnapshot {
    ProbeStateSnapshot {
        hint,
        scan_fail_streak,
        scan_big_fail_total,
    }
}

/// Probe observability (#uflia-probe-stats): process-global counters for
/// `probe_needed_shared_equalities`, printed to stderr every 1000 probes when
/// `AY_PROBE_STATS` is set. Zero overhead when unset (one cached env read).
///
/// The probe loop runs a FULL LIA check per candidate shared equality, so
/// `checks / probes` is the per-conflict multiplier of the check pipeline —
/// the dominant remaining cost on the SMT-COMP QF_UFLIA wisas family
/// (measured ~5.8 checks/probe at a 98.5% success rate on xs_13_13).
fn probe_stats_record(checks: u64, success: bool, subset_len: usize) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static CHECKS: AtomicU64 = AtomicU64::new(0);
    static PROBES: AtomicU64 = AtomicU64::new(0);
    static SUCCESSES: AtomicU64 = AtomicU64::new(0);
    static SUBSET_LEN: AtomicU64 = AtomicU64::new(0);
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ENABLED.get_or_init(|| ay_core::misc_cli_flags().probe_stats) {
        return;
    }
    CHECKS.fetch_add(checks, Ordering::Relaxed);
    let n = PROBES.fetch_add(1, Ordering::Relaxed) + 1;
    if success {
        SUCCESSES.fetch_add(1, Ordering::Relaxed);
        SUBSET_LEN.fetch_add(subset_len as u64, Ordering::Relaxed);
    }
    // Report interval override for short runs (measurement-only):
    // --probe-stats-every <n> (default 1000).
    static EVERY: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    let every = *EVERY.get_or_init(|| {
        ay_core::misc_cli_flags()
            .probe_stats_every
            .filter(|&v| v > 0)
            .unwrap_or(1000)
    });
    if n.is_multiple_of(every) {
        safe_eprintln!(
            "[PROBE-STATS] probes={} checks={} successes={} subset_len_sum={}",
            n,
            CHECKS.load(Ordering::Relaxed),
            SUCCESSES.load(Ordering::Relaxed),
            SUBSET_LEN.load(Ordering::Relaxed)
        );
    }
}

/// Probe observability: per-process count of big exhausted
/// scan failures, printed on every occurrence when `AY_PROBE_STATS` is set
/// (measurement-only; zero overhead when unset).
fn probe_scan_big_fail_record(order_len: usize) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static BIG_FAILS: AtomicU64 = AtomicU64::new(0);
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ENABLED.get_or_init(|| ay_core::misc_cli_flags().probe_stats) {
        return;
    }
    let n = BIG_FAILS.fetch_add(1, Ordering::Relaxed) + 1;
    safe_eprintln!("[PROBE-BIG-FAIL] n={} order_len={}", n, order_len);
}

/// Extract variable TermIds from an atom (comparison or equality).
/// Free function to allow split-borrow patterns (#8599).
pub(crate) fn collect_atom_vars_impl(terms: &TermStore, atom: TermId, vars: &mut HashSet<TermId>) {
    // A sentinel "literal" names no term: it is the placeholder reason of an
    // axiom / hypothesis bound (Gomory cut, factor-split pin, patch
    // verification pin) that a reason collector let through. It contributes
    // no variable, and indexing the store with it is out of bounds.
    if atom.is_sentinel() {
        return;
    }
    match terms.get(atom) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "<=" | ">=" | "<" | ">" | "=" | "distinct" => {
                for &arg in args {
                    collect_expr_vars_impl(terms, arg, vars);
                }
            }
            "not" => {
                if let Some(&inner) = args.first() {
                    collect_atom_vars_impl(terms, inner, vars);
                }
            }
            _ => {
                vars.insert(atom);
            }
        },
        TermData::Not(inner) => {
            collect_atom_vars_impl(terms, *inner, vars);
        }
        _ => {
            vars.insert(atom);
        }
    }
}

/// Extract variable TermIds from an arithmetic expression.
/// Free function to allow split-borrow patterns (#8599).
fn collect_expr_vars_impl(terms: &TermStore, term: TermId, vars: &mut HashSet<TermId>) {
    match terms.get(term) {
        TermData::Const(_) => {}
        TermData::Var(_, _) => {
            vars.insert(term);
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" => {
                for &arg in args {
                    collect_expr_vars_impl(terms, arg, vars);
                }
            }
            "*" => {
                for &arg in args {
                    if !matches!(terms.get(arg), TermData::Const(_)) {
                        collect_expr_vars_impl(terms, arg, vars);
                    }
                }
            }
            _ => {
                vars.insert(term);
            }
        },
        _ => {
            vars.insert(term);
        }
    }
}

impl LiaSolver<'_> {
    /// Core LIA check logic. Called by `TheorySolver::check()` which wraps the
    /// result to count conflicts.
    pub(super) fn check_inner(&mut self) -> TheoryResult {
        let debug = self.debug_lia_check;
        instrument::bump(&instrument::LIA_CHECK_CALLS);
        // Inc0-0a caller-class partition: conflict-probe and verify-only
        // solvers bump the same headline counter, so the spin-cell 58k is
        // unattributed without this split (see AY_PROBE_STATS: ~5.8
        // checks/probe dominate the wisas family).
        if self.conflict_probe {
            instrument::bump(&instrument::LIA_CHECK_PROBE_CALLS);
        } else if self.verify_only {
            instrument::bump(&instrument::LIA_CHECK_VERIFY_CALLS);
        } else {
            instrument::bump(&instrument::LIA_CHECK_TOP_CALLS);
        }

        // Cached models are only valid for the current asserted set.
        // #lia-dive-repair: keep a stored witness (dive/enumeration
        // lane) for exact re-validation below instead of dropping
        // it here — the executor's final check re-asks `check()`
        // right after the giveup lane stored one, and clearing it
        // unconditionally discarded exactly the model the lane
        // verified (convert-1546: lane success followed by
        // NeedModelEqualities and an overall `unknown`). Mutators
        // (assert_literal/push/pop/reset) already clear it; the
        // re-validation below is the same exact gate as at
        // storage time, so a stale witness can only decline.
        let cached_witness = self.direct_enum_witness.take();

        // #8124: If assert_shared_equality detected an impossible constant
        // equality, report it immediately.
        if let Some(conflict) = self.pending_shared_eq_conflict.take() {
            // #8784: Drop the conflict if any reason literal is stale.
            if !self.conflict_reasons_all_live(&conflict) {
                if debug {
                    safe_eprintln!(
                        "[LIA] Dropping pending shared equality conflict: stale reason ({} lits)",
                        conflict.len()
                    );
                }
            } else {
                if debug {
                    safe_eprintln!(
                        "[LIA] Reporting pending shared equality conflict ({} reasons)",
                        conflict.len()
                    );
                }
                return TheoryResult::Unsat(conflict);
            }
        }

        // #8783: Run algebraic equality detection upfront when shared equalities
        // are present. Gaussian elimination over the shared-equality system can
        // uncover contradictions (e.g., `0 = 1` after substitution) that are not
        // visible from the raw LRA bounds. Without this, `check()` callers that
        // bypass `propagate_equalities()` would miss the conflict and return a
        // spurious SAT. See QF_UFLIA repro `(= (f x) x) /\ (= (f x) (+ x 1))`.
        if !self.shared_equalities.is_empty() {
            let _ = self.detect_algebraic_equalities(debug);
            if let Some(conflict) = self.pending_shared_eq_conflict.take() {
                // #8784: Drop the conflict if any reason literal is stale.
                if !self.conflict_reasons_all_live(&conflict) {
                    if debug {
                        safe_eprintln!(
                            "[LIA] Dropping algebraic-detection conflict from check: stale reason ({} lits)",
                            conflict.len()
                        );
                    }
                } else {
                    if debug {
                        safe_eprintln!(
                            "[LIA] Reporting algebraic-detection conflict from check ({} reasons)",
                            conflict.len()
                        );
                    }
                    return TheoryResult::Unsat(conflict);
                }
            }
        }

        // Handle constant Bool atoms (e.g., term layer folds `X = X` to `true`).
        // Asserting `true` as false (or `false` as true) is an immediate
        // contradiction, detected incrementally at assert time (#C3).
        if let Some(&(_, lit)) = self.const_bool_conflicts.first() {
            return TheoryResult::Unsat(vec![lit]);
        }

        // #lia-dive-repair: a stored witness that still satisfies
        // every asserted literal and shared equality under exact
        // re-evaluation decides Sat directly (restored so
        // `extract_model` reports it). Placed after the cheap
        // conflict detectors above so their verdicts keep
        // precedence in shape, though a fully verified witness
        // and a genuine conflict cannot coexist.
        if let Some(model) = cached_witness {
            if self.stored_witness_still_valid(&model) {
                self.direct_enum_witness = Some(model);
                return TheoryResult::Sat;
            }
        }

        if let Some(conflict) = self.check_affine_disequality_implication(debug) {
            if debug {
                safe_eprintln!(
                    "[LIA] Affine disequality implication detected UNSAT (farkas={})",
                    conflict.farkas.is_some()
                );
            }
            // #rank-4 increment 2: carry the Gaussian-multiplier Farkas
            // certificate when the min-core path produced one. The conflict
            // literals are identical either way (certificates are
            // post-verdict metadata).
            if conflict.farkas.is_some() {
                return TheoryResult::UnsatWithFarkas(conflict);
            }
            return TheoryResult::Unsat(conflict.literals);
        }

        // GCD test: quick check for integer infeasibility
        // For equations like 4x + 4y + 4z - 2w = 49, GCD(4,4,4,2)=2 doesn't divide 49
        if let Some(conflict) = self.gcd_test() {
            if debug {
                safe_eprintln!("[LIA] GCD test detected UNSAT");
            }
            debug_assert!(
                !conflict.literals.is_empty(),
                "BUG: LIA GCD test: returned UnsatWithFarkas with empty conflict literals"
            );
            // #8144: GCD test only depends on the equality literal itself (the
            // divisibility check is a structural property of the equation, not
            // dependent on shared equality bounds). No augmentation needed.
            return TheoryResult::UnsatWithFarkas(conflict);
        }

        // IntSat CDCL probe: run a bounded CDCL-style integer search on the
        // extracted constraint system. This can detect UNSAT faster than simplex
        // for tightly-bounded problems with many integer variables.
        // Only run when shared equalities are not active (N-O complicates the
        // constraint extraction) and the problem is small enough.
        if self.shared_equalities.is_empty() {
            if let intsat_bridge::IntSatProbeResult::Unsat(conflict_lits) = self.intsat_probe() {
                if debug {
                    safe_eprintln!("[LIA] IntSat probe detected UNSAT");
                }
                if !conflict_lits.is_empty() {
                    return TheoryResult::Unsat(conflict_lits);
                }
            }
        }

        // Bounded finite-domain SAT witness search for small QF_LIA puzzle shapes
        // (all-different over tight integer domains plus linear side constraints).
        // Run before the LRA disequality splitter so n-ary `distinct` constraints
        // can be solved as a finite-domain CSP instead of expanded into many
        // branch atoms and weak Farkas conflicts.
        // INTERFACE-DIET C4/R2 (empty-unlocks-Sat site): this path can return
        // `TheoryResult::Sat` from the CSP witness; under a hidden interface the
        // empty `shared_equalities` is not the true interface, so fail-closed to
        // the else-branch (which just skips — the certifier / simplex decide).
        if self.shared_equalities.is_empty() && !self.hidden_interface {
            instrument::bump(&instrument::FINITE_DOMAIN_TRIGGERS);
            match self.try_finite_domain_search() {
                DirectEnumResult::SatWitness => {
                    if debug {
                        safe_eprintln!("[LIA] Finite-domain search found SAT witness");
                    }
                    return TheoryResult::Sat;
                }
                DirectEnumResult::Unsat(reasons) => {
                    if debug {
                        safe_eprintln!("[LIA] Finite-domain search detected UNSAT");
                    }
                    return TheoryResult::Unsat(reasons);
                }
                DirectEnumResult::NoConclusion => {}
            }
        } else {
            // The rusthorn UFLIA regime: shared equalities present ⇒ the
            // bounded-domain CSP witness search is gated off (check.rs:1164).
            instrument::bump(&instrument::FINITE_DOMAIN_SKIPS);
        }

        // Diophantine solver: for equality-dense problems, try variable elimination.
        // #C5: the equality key is served from the incrementally maintained
        // assertion view; clone it into `dioph_equality_key` only on change.
        let (has_equalities, equality_key_changed) = {
            let equality_key = self.equality_key();
            if debug {
                safe_eprintln!(
                    "[LIA] eq_key.len={} dioph_key.len={} eq={}",
                    equality_key.len(),
                    self.dioph_equality_key.len(),
                    self.dioph_equality_key == equality_key
                );
            }
            (
                !equality_key.is_empty(),
                self.dioph_equality_key != equality_key,
            )
        };
        // #C8: A pop/soft_reset since the caches were built requires
        // re-validation against the (possibly truncated) equality set before any
        // reuse. The key comparison above IS that validation: when the set
        // changed, drop the now-stale equality-derived caches here so that
        // neither the should_run_dioph re-solve nor the tightening loop below can
        // observe substitutions/reasons from a popped scope (#3736). When the set
        // is unchanged the caches stay valid and are reused as-is (the win).
        // D2: the caches are also keyed on the bounds folded into them; see
        // `dioph_cache`.
        if self.dioph_needs_revalidation {
            self.revalidate_dioph_caches(equality_key_changed);
        }
        // #8144: Re-enable Dioph when shared equalities are active.
        // fold_fixed_vars_in_equation now returns fold_reasons (Vec<TheoryLit>)
        // containing the bound reasons for every fixed variable, and all callers
        // (two_var.rs, dioph_bridge.rs) include these in conflict clauses.
        // The #8012 guard that skipped Dioph with shared equalities is no longer
        // needed — the fold_reasons mechanism ensures complete conflict clauses.
        let mut should_run_dioph =
            has_equalities && (equality_key_changed || self.dioph_needs_full_check);
        if equality_key_changed {
            self.dioph_equality_key = self.equality_key().to_vec();
        }
        self.dioph_needs_full_check = false;
        // Search-phase deferral (#nip benchmark: the from-scratch Dioph
        // elimination dominated eager solves at ~205ms per decision): defer
        // the full Dioph passes to the post-SAT final check. Sound:
        // needs_final_check_after_sat() == true guarantees a non-search full
        // check runs before any SAT is accepted (the sticky
        // dioph_needs_full_check below forces the deferred pass there);
        // skipping conflict DETECTION mid-search never creates a wrong
        // verdict, it only delays the conflict.
        if self.in_search_phase && should_run_dioph {
            self.dioph_needs_full_check = true;
            should_run_dioph = false;
        }
        if !has_equalities {
            self.clear_dioph_equality_caches();
            self.dioph_modified_bounds = false;
            self.dioph_bound_term_ids.clear();
        }

        if should_run_dioph {
            if let Some(reasons) = self.timed_try_two_variable_solve() {
                if debug {
                    safe_eprintln!("[LIA] 2-variable solver detected UNSAT");
                }
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: LIA 2-var Diophantine: returned empty conflict reasons"
                );
                if let TheoryResult::UnsatWithFarkas(conflict) = self.timed_lra_check() {
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                return TheoryResult::Unsat(reasons);
            }

            if let Some(reasons) = self.timed_try_diophantine_solve() {
                if debug {
                    safe_eprintln!("[LIA] Diophantine solver detected UNSAT");
                }
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: LIA Diophantine: returned empty conflict reasons"
                );
                if let TheoryResult::UnsatWithFarkas(conflict) = self.timed_lra_check() {
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                return TheoryResult::Unsat(reasons);
            }
        }

        // Iterative Dioph tightening loop (Z3's continue_with_check pattern).
        // Reference: Z3 dioph_eq.cpp check() at line 2162.
        // Dioph substitutions are derived only from asserted arithmetic
        // equalities, so they remain valid when Nelson-Oppen shared equalities
        // are present. This keeps UFLIA carry-chain modular contradictions
        // visible instead of falling through to model-equality splitting.
        {
            let max_tighten_rounds = 4;
            // Computed lazily on the first round that actually runs: with
            // no cached substitutions the loop breaks immediately, and the
            // full integer-var scan would be pure overhead per check.
            let mut prev_fixed_count: Option<usize> = None;

            for tighten_round in 0..max_tighten_rounds {
                if self.dioph_cached_substitutions.is_empty() {
                    break;
                }
                let prev_count =
                    *prev_fixed_count.get_or_insert_with(|| self.count_fixed_integer_vars());
                instrument::bump(&instrument::DIOPH_TIGHTEN_ROUNDS);

                let bounds_tightened = self.timed_propagate_bounds_through_substitutions();
                if bounds_tightened {
                    if let TheoryResult::UnsatWithFarkas(conflict) = self.timed_lra_check() {
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                }

                let rows_tightened = self.timed_tighten_tableau_rows_via_dioph();
                if rows_tightened {
                    if let TheoryResult::UnsatWithFarkas(conflict) = self.timed_lra_check() {
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                }

                if !bounds_tightened && !rows_tightened {
                    break;
                }

                let new_fixed_count = self.count_fixed_integer_vars();
                if new_fixed_count <= prev_count {
                    break;
                }

                if debug {
                    safe_eprintln!(
                        "[LIA] Dioph tighten round {}: {} newly fixed vars (was {}, now {})",
                        tighten_round,
                        new_fixed_count - prev_count,
                        prev_count,
                        new_fixed_count
                    );
                }
                prev_fixed_count = Some(new_fixed_count);

                if self.should_timeout() {
                    if debug {
                        safe_eprintln!("[LIA] Timeout during iterative Dioph tightening");
                    }
                    return TheoryResult::Unknown;
                }

                if let Some(reasons) = self.timed_try_diophantine_solve() {
                    if debug {
                        safe_eprintln!(
                            "[LIA] Dioph re-solve (round {}) detected UNSAT",
                            tighten_round
                        );
                    }
                    if let TheoryResult::UnsatWithFarkas(conflict) = self.timed_lra_check() {
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                    return TheoryResult::Unsat(reasons);
                }
            }
        }

        self.gomory_iterations = 0;
        self.hnf_iterations = 0;
        let mut cube_tried = false;
        // Lattice closure before an unbounded split, once per check (lattice_refute_bridge).
        let mut lattice_tried = false;

        loop {
            if self.should_timeout() {
                if debug {
                    safe_eprintln!("[LIA] Timeout, returning Unknown");
                }
                return TheoryResult::Unknown;
            }

            let lra_result = self.timed_lra_check();

            if debug {
                safe_eprintln!(
                    "[LIA] LRA check result: {:?}, gomory_iter={}, hnf_iter={}",
                    lra_result,
                    self.gomory_iterations,
                    self.hnf_iterations
                );
            }

            match lra_result {
                TheoryResult::Unsat(reasons) => {
                    return TheoryResult::Unsat(reasons);
                }
                TheoryResult::UnsatWithFarkas(conflict) => {
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                TheoryResult::Unknown => {
                    if let Some(conflict) = self.gcd_test_tableau() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: tableau GCD test detected UNSAT"
                            );
                        }
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }

                    if let Some(conflict) = self.gcd_accumulative_test() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: accumulative GCD test detected UNSAT"
                            );
                        }
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }

                    let hnf_var = self.integer_vars.iter().copied().find(|&v| {
                        self.lra
                            .get_bounds(v)
                            .is_some_and(|(lb, ub)| lb.is_some() || ub.is_some())
                    });
                    if let Some(var) = hnf_var {
                        if self.hnf_iterations
                            < Self::hnf_iteration_budget(
                                self.count_equalities(),
                                self.integer_vars.len(),
                            )
                            && self.timed_try_hnf_cuts(var)
                        {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Unknown recovery: HNF cuts generated, re-checking"
                                );
                            }
                            continue;
                        }
                    }

                    if self.gomory_iterations < self.max_gomory_iterations {
                        let cuts = self.timed_generate_gomory_cuts();
                        let small_cuts: Vec<_> = cuts
                            .into_iter()
                            .filter(ay_lra::GomoryCut::is_small)
                            .collect();
                        if !small_cuts.is_empty() {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Unknown recovery: adding {} small Gomory cuts",
                                    small_cuts.len()
                                );
                            }
                            for cut in &small_cuts {
                                self.timed_add_gomory_cut(cut, TermId::SENTINEL);
                            }
                            self.gomory_iterations += 1;
                            continue;
                        }
                    }

                    // #6220: Apply the same UNSAT-detection checks used in the Sat path.
                    // When LRA returns Unknown (e.g., ITE/nonlinear terms), the bounds
                    // it established are still valid, so integer gap detection, modular
                    // constraints, and direct enumeration can still detect UNSAT.
                    if let Some(conflict) = self.check_integer_bounds_conflict() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: integer bounds gap detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(conflict.literals);
                    }

                    if let Some(reasons) = self.check_single_equality_modular_constraints() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: modular constraint detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if let Some(reasons) = self.check_modular_constraint_conflict() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: Dioph modular constraint detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    // LRA degrades to Unknown on unsupported (nonlinear /
                    // div / mod) atoms; the polynomial-residual pass can
                    // still derive sound conflicts by expanding products,
                    // substituting LRA-fixed variables, and comparing
                    // canonical residuals (e.g. quadratic accumulator
                    // consecution checks, #9191/#1753/#7897).
                    if let Some(reasons) = self.check_polynomial_residual_conflict() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: polynomial residual conflict detected UNSAT ({} lits)",
                                reasons.len()
                            );
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if self.gomory_iterations == 0 && self.hnf_iterations == 0 {
                        match self.try_direct_enumeration() {
                            DirectEnumResult::Unsat(reasons) => {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Unknown recovery: direct enumeration detected UNSAT"
                                    );
                                }
                                return TheoryResult::Unsat(reasons);
                            }
                            DirectEnumResult::SatWitness => {
                                // LRA said Unknown but enumeration found a SAT witness.
                                // This is safe: the witness satisfies all integer constraints.
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Unknown recovery: direct enumeration found SAT witness"
                                    );
                                }
                                return TheoryResult::Sat;
                            }
                            DirectEnumResult::NoConclusion => {}
                        }
                    }

                    if let Some(split) = self.find_unsplit_integer_var() {
                        if let Some(unsat) = self.lattice_once(&mut lattice_tried, split.variable) {
                            return unsat;
                        }
                        if debug {
                            safe_eprintln!(
                                "[LIA] LRA returned Unknown, splitting unsplit var {:?} at midpoint {}",
                                split.variable, split.value
                            );
                        }
                        instrument::bump(&instrument::SPLITS_ISSUED_UNKNOWN);
                        return TheoryResult::NeedSplit(split);
                    }
                    if debug {
                        safe_eprintln!(
                            "[LIA] LRA returned Unknown, no splittable var, propagating"
                        );
                    }
                    return TheoryResult::Unknown;
                }
                TheoryResult::NeedSplit(split) => {
                    instrument::bump(&instrument::SPLITS_FORWARDED_LRA);
                    return TheoryResult::NeedSplit(split);
                }
                TheoryResult::NeedDisequalitySplit(split) => {
                    if let Some(reasons) = self.check_disequality_vs_modular(&split) {
                        if debug {
                            safe_eprintln!("[LIA] Disequality conflicts with modular constraint");
                        }
                        return TheoryResult::Unsat(reasons);
                    }
                    if let Some((var, _)) = self.check_integer_constraints() {
                        if let Some(unsat) = self.lattice_once(&mut lattice_tried, var) {
                            return unsat;
                        }
                    }
                    return TheoryResult::NeedDisequalitySplit(split);
                }
                TheoryResult::NeedExpressionSplit(split) => {
                    return TheoryResult::NeedExpressionSplit(split);
                }
                TheoryResult::NeedStringLemma(lemma) => {
                    return TheoryResult::NeedStringLemma(lemma);
                }
                TheoryResult::Sat => {
                    if let Some(conflict) = self.check_integer_bounds_conflict() {
                        // Integer-gap conflicts (e.g., x > 0 AND x < 1) use
                        // integer rounding, NOT a linear Farkas argument. Return
                        // plain Unsat to avoid semantic Farkas verification failure
                        // in the incremental DPLL(T) path (#4785).
                        return TheoryResult::Unsat(conflict.literals);
                    }

                    if let Some(reasons) = self.check_single_equality_modular_constraints() {
                        if debug {
                            safe_eprintln!("[LIA] Modular constraint detected UNSAT");
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if let Some(reasons) = self.check_modular_constraint_conflict() {
                        if debug {
                            safe_eprintln!("[LIA] Dioph modular constraint detected UNSAT");
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if self.gomory_iterations == 0 && self.hnf_iterations == 0 {
                        match self.try_direct_enumeration() {
                            DirectEnumResult::Unsat(reasons) => {
                                if debug {
                                    safe_eprintln!("[LIA] Direct enumeration detected UNSAT");
                                }
                                return TheoryResult::Unsat(reasons);
                            }
                            DirectEnumResult::SatWitness => {
                                if debug {
                                    safe_eprintln!("[LIA] Direct enumeration found SAT witness");
                                }
                                return TheoryResult::Sat;
                            }
                            DirectEnumResult::NoConclusion => {
                                if self.should_timeout() {
                                    if debug {
                                        safe_eprintln!("[LIA] Timeout during direct enumeration");
                                    }
                                    return TheoryResult::Unknown;
                                }
                            }
                        }
                    }

                    if let Some((var, value)) = self.check_integer_constraints() {
                        if let Some(unsat) = self.lattice_once(&mut lattice_tried, var) {
                            return unsat;
                        }
                        if let Some(conflict) = self.gcd_test_tableau() {
                            if debug {
                                safe_eprintln!("[LIA] Tableau GCD test detected UNSAT");
                            }
                            return TheoryResult::UnsatWithFarkas(conflict);
                        }

                        if self.try_patching() {
                            if debug {
                                safe_eprintln!("[LIA] Patching succeeded, re-checking");
                            }
                            continue;
                        }

                        // Gomory runs BEFORE the cube test:
                        // `should_try_gomory` blocks cuts once the cube
                        // test has been attempted (#3073), so with the cube
                        // block first this gate was unreachable in the Sat
                        // path and `gomory_iterations` stayed 0 (the
                        // v20_problem__019 split walk then drifted to the
                        // oscillation guard instead of cutting).
                        if self.should_try_gomory(cube_tried) {
                            let cuts = self.timed_generate_gomory_cuts();

                            if debug {
                                safe_eprintln!(
                                    "[LIA] Generated {} Gomory cuts (iter {})",
                                    cuts.len(),
                                    self.gomory_iterations,
                                );
                            }

                            if !cuts.is_empty() {
                                let mut small_cuts = Vec::new();
                                let mut big_cuts = Vec::new();
                                for cut in cuts {
                                    if cut.is_small() {
                                        small_cuts.push(cut);
                                    } else {
                                        big_cuts.push(cut);
                                    }
                                }

                                for cut in &small_cuts {
                                    let from_substituted = cut.source_term.is_some_and(|t| {
                                        self.dioph_safe_dependent_vars.contains(&t)
                                    });
                                    if from_substituted {
                                        self.lra.push();
                                        self.timed_add_gomory_cut(cut, TermId::SENTINEL);
                                        let tentative = self.timed_lra_check();
                                        self.lra.pop();
                                        let made_infeasible = matches!(
                                            tentative,
                                            TheoryResult::Unsat(_)
                                                | TheoryResult::UnsatWithFarkas(_)
                                        );
                                        if made_infeasible {
                                            let base_ok = !matches!(
                                                self.timed_lra_check(),
                                                TheoryResult::Unsat(_)
                                                    | TheoryResult::UnsatWithFarkas(_)
                                            );
                                            if base_ok {
                                                if debug {
                                                    safe_eprintln!(
                                                        "[LIA] Gomory: discarding substituted-row cut"
                                                    );
                                                }
                                                continue;
                                            }
                                        }
                                    }
                                    self.timed_add_gomory_cut(cut, TermId::SENTINEL);
                                }

                                if !big_cuts.is_empty() {
                                    if debug {
                                        safe_eprintln!(
                                            "[LIA] Testing {} big Gomory cuts tentatively",
                                            big_cuts.len()
                                        );
                                    }
                                    self.lra.push();
                                    for cut in &big_cuts {
                                        self.timed_add_gomory_cut(cut, TermId::SENTINEL);
                                    }
                                    let feasible = !matches!(
                                        self.timed_lra_dual_simplex(),
                                        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                                    );
                                    self.lra.pop();

                                    if !feasible {
                                        if debug {
                                            safe_eprintln!(
                                                "[LIA] Big cuts render LP infeasible, keeping them"
                                            );
                                        }
                                        for cut in &big_cuts {
                                            self.timed_add_gomory_cut(cut, TermId::SENTINEL);
                                        }
                                    } else if debug {
                                        safe_eprintln!("[LIA] Big cuts did not help, discarding");
                                    }
                                }

                                self.gomory_iterations += 1;
                                continue;
                            }
                        }
                        if !cube_tried {
                            cube_tried = true;
                            instrument::bump(&instrument::CUBE_TESTS);
                            // The cube test shrinks bounds on any subset of the
                            // integer vars (and pops them on failure) —
                            // conservatively rescan everything (#C4).
                            self.mark_int_bounds_all_dirty();
                            if self.lra.try_cube_test(&self.integer_vars) {
                                if debug {
                                    safe_eprintln!("[LIA] Cube test succeeded, re-checking");
                                }
                                continue;
                            }
                        }

                        let num_equalities = self.count_equalities();
                        let num_vars = self.integer_vars.len();
                        let is_equality_dense = Self::is_equality_dense(num_equalities, num_vars);
                        let max_hnf_per_check =
                            Self::hnf_iteration_budget(num_equalities, num_vars);

                        let pre_hnf_iter = self.hnf_iterations;

                        while self.hnf_iterations < max_hnf_per_check {
                            if self.should_timeout() {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Timeout during HNF cuts, returning Unknown"
                                    );
                                }
                                return TheoryResult::Unknown;
                            }
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Trying HNF cuts (iter {}/{}, {} equalities, {} vars, dense={})",
                                    self.hnf_iterations, max_hnf_per_check,
                                    num_equalities, num_vars, is_equality_dense
                                );
                            }
                            if self.timed_try_hnf_cuts(var) {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] HNF cuts generated, continuing inner HNF loop"
                                    );
                                }
                                continue;
                            }
                            break;
                        }

                        if self.hnf_iterations > pre_hnf_iter {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Generated {} HNF cuts total, re-checking LRA",
                                    self.hnf_iterations - pre_hnf_iter
                                );
                            }
                            continue;
                        }

                        if debug {
                            safe_eprintln!(
                                "[LIA] Falling back to branch-and-bound (gomory={}, hnf={})",
                                self.gomory_iterations,
                                self.hnf_iterations
                            );
                        }
                        debug_assert!(
                            self.integer_vars.contains(&var),
                            "BUG: LIA branch-and-bound: split variable {} is not a tracked integer variable",
                            var.0
                        );
                        let split = Self::create_split_request(var, value);
                        debug_assert!(
                            split.floor < split.ceil,
                            "BUG: LIA branch-and-bound: floor {} >= ceil {} for non-integer value",
                            split.floor,
                            split.ceil
                        );
                        instrument::bump(&instrument::SPLITS_ISSUED_BNB);
                        return TheoryResult::NeedSplit(split);
                    } else {
                        return TheoryResult::Sat;
                    }
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    return TheoryResult::NeedLemmas(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    // #7884: Before forwarding model equality requests from
                    // LRA, check if any integer variable has a non-integer
                    // value. The N-O loop's stale-equality suppression (#1771)
                    // can convert NeedModelEquality to Sat when the equality
                    // is already encoded, skipping the integrality check that
                    // only runs in the Sat branch. Prioritize integer splits
                    // over model equalities to prevent accepting fractional
                    // models.
                    if let Some((var, value)) = self.check_integer_constraints() {
                        if let Some(unsat) = self.lattice_once(&mut lattice_tried, var) {
                            return unsat;
                        }
                        if debug {
                            safe_eprintln!(
                                "[LIA] NeedModelEquality deferred: integer var {:?} has non-integer value, splitting",
                                var
                            );
                        }
                        let split = Self::create_split_request(var, value);
                        instrument::bump(&instrument::SPLITS_ISSUED_MODELEQ);
                        return TheoryResult::NeedSplit(split);
                    }
                    return TheoryResult::NeedModelEquality(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    // #7884: Same integrality guard as NeedModelEquality above.
                    if let Some((var, value)) = self.check_integer_constraints() {
                        if let Some(unsat) = self.lattice_once(&mut lattice_tried, var) {
                            return unsat;
                        }
                        if debug {
                            safe_eprintln!(
                                "[LIA] NeedModelEqualities deferred: integer var {:?} has non-integer value, splitting",
                                var
                            );
                        }
                        let split = Self::create_split_request(var, value);
                        instrument::bump(&instrument::SPLITS_ISSUED_MODELEQ);
                        return TheoryResult::NeedSplit(split);
                    }
                    return TheoryResult::NeedModelEqualities(reqs);
                }
                _ => {
                    // Forward any future TheoryResult variants from LRA unchanged.
                    return lra_result;
                }
            }
        }
    }

    /// Lightweight BCP-time check: keep local arithmetic conflicts and LRA
    /// propagation, but defer expensive Dioph/cut/branch-and-bound work to the
    /// final full `check()`.
    pub(super) fn check_during_propagate_inner(&mut self) -> TheoryResult {
        let debug = self.debug_lia_check;
        // Inc0-0a: BCP-time weak checks are a separate entry point that never
        // reaches check_inner — counted separately for full attribution.
        instrument::bump(&instrument::LIA_CHECK_BCP_CALLS);

        // Cached enumeration models are only valid for the current asserted set.
        self.direct_enum_witness = None;

        // #8124: If assert_shared_equality detected an impossible constant
        // equality, report it immediately.
        if let Some(conflict) = self.pending_shared_eq_conflict.take() {
            // #8784: Drop the conflict if any reason literal is stale.
            if !self.conflict_reasons_all_live(&conflict) {
                if debug {
                    safe_eprintln!(
                        "[LIA] BCP-time: dropping pending shared equality conflict: stale reason ({} lits)",
                        conflict.len()
                    );
                }
            } else {
                if debug {
                    safe_eprintln!(
                        "[LIA] BCP-time: reporting pending shared equality conflict ({} reasons)",
                        conflict.len()
                    );
                }
                return TheoryResult::Unsat(conflict);
            }
        }

        // Handle constant Bool atoms eagerly (incremental, #C3).
        if let Some(&(_, lit)) = self.const_bool_conflicts.first() {
            return TheoryResult::Unsat(vec![lit]);
        }

        // Keep the fast, assignment-independent UNSAT checks at BCP time.
        if let Some(conflict) = self.gcd_test() {
            if debug {
                safe_eprintln!("[LIA] BCP-time GCD test detected UNSAT");
            }
            // #8144: GCD test conflict only depends on the equality literal,
            // no shared equality augmentation needed.
            return TheoryResult::UnsatWithFarkas(conflict);
        }

        // Dioph substitutions are only sound if their equality key is current.
        // Run a BCP-time Dioph scratch analysis when the equality key changes so
        // modular/congruence infeasibility is caught early instead of waiting
        // for the full `check()` — this is decisive for cascade-style
        // benchmarks (#8733) that otherwise spend most of their budget in
        // propagation before the final check. It is ALSO re-checked periodically
        // under an UNCHANGED equality set, because its feasibility half reads
        // bounds the search moves; policy and run live in `dioph_bcp`.
        let (equality_key_empty, needs_bcp_dioph) = self.bcp_dioph_arm();

        // #C8: re-validate the equality-derived caches after a pop/soft_reset.
        // When the equality set changed, drop them before the modular checks
        // (which iterate dioph_cached_substitutions, modular.rs:189) can reuse a
        // popped scope's substitutions (#3736). An unchanged set keeps them.
        // D2: the caches are also keyed on the bounds folded into them; see
        // `dioph_cache`.
        if self.dioph_needs_revalidation {
            self.revalidate_dioph_caches(needs_bcp_dioph);
        }

        if equality_key_empty {
            self.dioph_equality_key.clear();
            self.dioph_needs_full_check = false;
            self.clear_dioph_equality_caches();
            self.dioph_modified_bounds = false;
            self.dioph_bound_term_ids.clear();
        }

        let lra_result = self.timed_lra_check_during_propagate();
        let can_use_current_bounds = !matches!(
            lra_result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        );
        let mut clear_bcp_dioph_after = false;

        // Preserve cheap integer-specific conflicts when the relaxation is
        // not already UNSAT. LRA-derived bounds are still valid for these
        // follow-up checks even when it requests a split or model equality.
        if can_use_current_bounds {
            if needs_bcp_dioph {
                match self.bcp_dioph_run(debug) {
                    dioph_bcp::BcpDiophOutcome::Conflict(reasons) => {
                        return TheoryResult::Unsat(reasons)
                    }
                    dioph_bcp::BcpDiophOutcome::Deferred => {}
                    dioph_bcp::BcpDiophOutcome::Ran => clear_bcp_dioph_after = true,
                }
            }

            if let Some(conflict) = self.check_integer_bounds_conflict() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time integer bounds gap detected UNSAT");
                }
                return TheoryResult::Unsat(conflict.literals);
            }

            if let Some(reasons) = self.check_single_equality_modular_constraints() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time modular constraint detected UNSAT");
                }
                return TheoryResult::Unsat(reasons);
            }

            if let Some(reasons) = self.check_modular_constraint_conflict() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time Dioph modular constraint detected UNSAT");
                }
                return TheoryResult::Unsat(reasons);
            }

            if clear_bcp_dioph_after {
                self.clear_dioph_equality_caches();
                self.dioph_modified_bounds = false;
                self.dioph_bound_term_ids.clear();
            }
        }

        match lra_result {
            TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_) => TheoryResult::Sat,
            TheoryResult::UnsatWithFarkas(conflict) => TheoryResult::UnsatWithFarkas(conflict),
            other => other,
        }
    }
}
