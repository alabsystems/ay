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
        // Verdict readers: `probe_verdict_is_unsat` / `probe_verdict_is_sat`
        // (module level — the #probe-qx minimizer reads verdicts by exactly the
        // same rules).
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
            collect_atom_vars_impl(self.terms, lit.term, &mut conflict_vars);
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
        let mut probe = self.build_conflict_probe(literals, &[]);
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

        // #probe-qx (Junker 2004): the DIVIDE-AND-CONQUER half of
        // #probe-prefix-bisect, replacing the O(|order|) forward scan below
        // with an O(k·log(n/k)) recursion plus two set-level checks. Opt-in
        // (`AY_LIA_PROBE_QX=1`) and only over orders big enough for those two
        // checks to pay for themselves — the trajectory-sensitive Hash SAT
        // greens run candidate orders of ~1-3 and keep the scan bit-for-bit.
        // See `quickxplain_shared_equalities` for the argument; the acceptance
        // rule is identical to the scan's, so both exits here are exactly the
        // scan's own exits (proven subset, or `None` and the caller keeps the
        // sound full-closure over-approximation).
        if matches!(probe_qx_mode(), ProbeQxMode::Quickxplain) && order.len() >= QX_MIN_ORDER {
            match self.quickxplain_shared_equalities(literals, &order, &mut probe_checks) {
                QxOutcome::Proved(subset) => {
                    probe_stats_record(probe_checks, true, subset.len());
                    record_hint(&subset);
                    PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
                    return Some(subset);
                }
                QxOutcome::Refuted => {
                    // The failed-scan exit at ONE check: a definite-Sat full
                    // candidate set proves no subset can refute `literals`.
                    probe_stats_record(probe_checks, false, 0);
                    if self.probe_subset_cache_active() {
                        PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
                    }
                    if order.len() >= PROBE_SCAN_SWITCH_MIN_ORDER {
                        PROBE_SCAN_FAIL_STREAK
                            .with(|streak| streak.set(streak.get().saturating_add(1)));
                        PROBE_SCAN_BIG_FAIL_TOTAL
                            .with(|total| total.set(total.get().saturating_add(1)));
                        probe_scan_big_fail_record(order.len());
                    }
                    return None;
                }
                // Nothing decided (Unknown batch, budget or deadline abort):
                // fall through to the untouched forward scan.
                QxOutcome::Undecided => {}
            }
        }

        // #probe-batch-prescreen (adaptive fail-fast): the scan below is
        // O(|order|) full probe checks when it FAILS — ~89% of scans on the
        // mathsat EufLaArithmetic hard* refutations (224k probe checks /
        // 2000 scans / 11% success measured on hard18). The probe is
        // ADD-ONLY, so TRUE infeasibility is MONOTONE in the asserted set:
        // one seeded batch check of `literals + EVERY candidate` bounds what
        // any subset can do, at ~1/|order| of the scan's checks.
        //
        // #probe-batch-prescreen-exact — the batch verdict is read three
        // ways instead of the old blunt `!is_unsat` (which conflated Sat and
        // Unknown and so occasionally SKIPPED a productive UNKNOWN-batch scan:
        // the hard11/hard14 casualty class):
        //   Sat     -> EXACT fast-fail. A model of the full set models every
        //              subset, so NO subset can refute; skipping drops nothing.
        //              (Rare on the hard* family — their batches are Unknown,
        //              not Sat: sat=0 measured on hard14/hard18/hard11.)
        //   Unsat   -> the full set is infeasible, so SOME subset is; fall
        //              through to the UNCAPPED scan and find it.
        //   Unknown -> the monster full-set system exhausted a branching /
        //              coefficient budget its small incremental subsystems
        //              never hit, so the verdict is UNDECIDED. Rather than
        //              blindly skip (may drop a productive scan whose small
        //              refuting subset the batch could not prove), take a
        //              BOUNDED RESCUE scan of the leading `rescue_cap`
        //              candidates, then fast-fail — recovering the casualties
        //              while still capping the grind at the budget.
        //
        // TRAJECTORY: still deliberately NOT byte-identical when armed (a
        // rescue that exhausts its budget re-routes exactly as the old blind
        // skip did). The adaptive double gate (streak + total, both over big
        // orders only) keeps every measured trajectory-sensitive green
        // byte-identical by never arming there; where it DOES arm, the search
        // has already burned 128 big failed scans — the refutation-grind regime
        // this lever exists for.
        //
        // SOUNDNESS: unchanged in every direction. Every exit either returns
        // `None` (caller keeps the sound full-closure over-approximation, as a
        // failed scan would) or a subset an actual probe check refuted with
        // `literals`. The Sat exact fast-fail and the rescue budget only ever
        // move `None` earlier; no subset is EVER accepted unverified, and no
        // verdict path is touched.
        // #probe-batch-prescreen-exact: the batch verdict decides which of
        // three exits the fail-fast takes. `rescue_cap` caps the forward scan
        // below when the verdict is UNKNOWN (see the match).
        let mut rescue_cap: Option<usize> = None;
        // #probe-qx subsumes the batch check (it runs one as its precondition
        // and only reaches here when that batch was UNDECIDED), so running the
        // pre-screen again would just re-pay an identical check.
        if self.probe_batch_prescreen_active()
            && matches!(probe_qx_mode(), ProbeQxMode::Scan)
            && !self.should_timeout()
        {
            probe_checks += 1;
            let batch = self.probe_prefix_check(literals, &order);
            prescreen_batch_verdict_record(&batch);
            if probe_verdict_is_sat(&batch) {
                // DEFINITE-Sat: a model of `literals + ALL candidates` exists,
                // so it models `literals + ANY subset`; no subset is refutable
                // and the scan is PROVABLY unproductive. Exact fast-fail — this
                // arm never skips a productive scan (contrast the pre-exactness
                // lever, which fast-failed on Unknown too and so occasionally
                // skipped a productive UNKNOWN-batch scan: the hard14/hard11
                // casualty class). Take the failed-scan exit (hint
                // invalidation + switch bookkeeping) at 1 check.
                probe_stats_record(probe_checks, false, 0);
                if self.probe_subset_cache_active() {
                    PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
                }
                if order.len() >= PROBE_SCAN_SWITCH_MIN_ORDER {
                    PROBE_SCAN_FAIL_STREAK
                        .with(|streak| streak.set(streak.get().saturating_add(1)));
                    PROBE_SCAN_BIG_FAIL_TOTAL
                        .with(|total| total.set(total.get().saturating_add(1)));
                    probe_scan_big_fail_record(order.len());
                }
                return None;
            }
            if !probe_verdict_is_unsat(&batch) {
                // UNKNOWN: the monster full-set system exhausted a branching /
                // coefficient budget its small incremental subsystems never
                // hit, so the verdict is UNDECIDED — a blind fast-fail here may
                // skip a productive scan (the casualty class: a truly-UNSAT
                // full set whose infeasibility the batch could not PROVE, but
                // whose small subset the scan can). BOUNDED RESCUE: run the
                // forward scan, but only over the first `PROBE_RESCUE_BUDGET`
                // candidates. Conflict-touching equalities lead `order` and
                // proven subsets are ~5-6 equalities, so a refuting subset — if
                // one exists — almost always lies in that prefix; a scan that
                // exhausts the budget without reproducing infeasibility
                // fast-fails, capping the UNKNOWN-batch cost at the budget
                // instead of O(|order|). SOUND: a subset is still only ever
                // accepted by an actual probe check refuting literals+subset.
                rescue_cap = Some(probe_rescue_budget());
            }
            // UNSAT: the full set is infeasible, so SOME subset is infeasible —
            // fall through to the UNCAPPED scan to find it (rescue_cap = None).
        }

        // Add equalities until the infeasibility reproduces. The check comes
        // AFTER the first add, never before — that is contract 2 (when the
        // cached-subset batch ran above, its members are already asserted
        // and stay in `used`; the scan below skips them).
        let order_len = order.len();
        // #probe-batch-prescreen-exact: count candidates the scan actually
        // asserts (a hinted prefix already sits in `used` and is skipped), so a
        // bounded UNKNOWN-batch rescue can cap the scan at `rescue_cap` NEW
        // checks and then take the exhausted-scan exit below.
        let mut scanned = 0usize;
        // #probe-gallop: when armed, the scan checks at EXPONENTIALLY spaced
        // prefixes (1, 2, 4, 8, ... candidates added since the last check)
        // instead of after every single add — see `probe_qx_mode`. `step` is
        // the current batch size and `pending` the adds since the last check.
        let gallop = matches!(probe_qx_mode(), ProbeQxMode::Gallop) && order_len >= QX_MIN_ORDER;
        let mut step = 1usize;
        let mut pending = 0usize;
        let mut reproduced = false;
        // #probe-gallop-bisect: `used.len()` at the last check that did NOT
        // reproduce the infeasibility — the low end of the window a successful
        // batch check has to be narrowed back down to (see below).
        let mut last_feasible = used.len();
        for i in order {
            if used.contains(&i) {
                continue;
            }
            // #lia-deadline-forward: the forward scan is O(candidates) full
            // probe checks — poll the parent's deadline between adds so a
            // dense probe loop cannot outlive the theory budget. `None`
            // falls back to the sound full-closure augmentation. (A deadline
            // abort is NOT evidence for the #probe-prefix-bisect switch —
            // the streak is untouched.)
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
            scanned += 1;
            pending += 1;
            // #probe-gallop: inside a batch — defer the check to its boundary.
            if gallop && pending < step {
                if let Some(cap) = rescue_cap {
                    if scanned >= cap {
                        break;
                    }
                }
                continue;
            }
            pending = 0;
            probe_checks += 1;
            if probe_verdict_is_unsat(&probe.check()) {
                reproduced = true;
                break;
            }
            // #probe-gallop: this prefix is not (provably) infeasible, so
            // double the next batch. The probe is ADD-ONLY, so every deferred
            // check is a prefix check the scan would also have run — just
            // fewer of them.
            if gallop {
                step = step.saturating_mul(2);
                last_feasible = used.len();
            }
            // Bounded rescue budget hit without reproducing infeasibility: stop
            // and take the exhausted-scan exit (the UNKNOWN batch could not
            // prove feasibility, and no refuting subset lies in the leading
            // `rescue_cap` candidates — treat as a failed scan).
            if let Some(cap) = rescue_cap {
                if scanned >= cap {
                    break;
                }
            }
        }
        // #probe-gallop: the trailing partial batch never reached a boundary,
        // so its prefix — the WHOLE candidate order — is still unchecked. The
        // one-at-a-time scan always ends on a check; without this flush a
        // gallop could report "exhausted" for an order it never asked about.
        if gallop && !reproduced && pending > 0 && !self.should_timeout() {
            probe_checks += 1;
            reproduced = probe_verdict_is_unsat(&probe.check());
        }
        if reproduced {
            // #probe-gallop-bisect: a batch check reproduces the infeasibility
            // somewhere in `(last_feasible, used.len()]`, and everything past
            // the true boundary is DEAD WEIGHT — its reasons are appended to
            // the emitted clause, weakening it (measured: the un-bisected
            // gallop grew the mean proven subset 15.2 -> 17.8 and cost 9
            // QF_UFLIA SAT greens). Binary-search the window back down. Each
            // probe is a from-scratch check of `literals` plus exactly a
            // prefix, so every accepted narrowing is PROVEN, and a window
            // whose narrowings all come back undecided simply keeps the batch
            // boundary the incremental probe already refuted — the acceptance
            // rule holds on either exit.
            if gallop && used.len() - last_feasible > 1 {
                let (mut lo, mut hi) = (last_feasible, used.len());
                while hi - lo > 1 && !self.should_timeout() {
                    let mid = lo + (hi - lo) / 2;
                    probe_checks += 1;
                    if probe_verdict_is_unsat(&self.probe_prefix_check(literals, &used[..mid])) {
                        hi = mid;
                    } else {
                        lo = mid;
                    }
                }
                used.truncate(hi);
            }
            probe_stats_record(probe_checks, true, used.len());
            record_hint(&used);
            PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
            return Some(used);
        }
        probe_stats_record(probe_checks, false, 0);
        // A failed scan invalidates the hint: the conflict landscape has
        // moved (or the closure shrank); a stale hint would keep paying the
        // extra batch check on every future conflict.
        if self.probe_subset_cache_active() {
            PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
        }
        // Exhausted scan: every candidate was asserted and the infeasibility
        // still did not reproduce. Count toward the #probe-prefix-bisect
        // switch only when the scan was expensive enough that the set-level
        // strategy would have saved real work (saturating: the mode
        // predicate only compares >=).
        if order_len >= PROBE_SCAN_SWITCH_MIN_ORDER {
            PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(streak.get().saturating_add(1)));
            PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.set(total.get().saturating_add(1)));
            probe_scan_big_fail_record(order_len);
        }
        None
    }

    /// Whether the #probe-batch-prescreen fail-fast is armed for THIS probe
    /// (see the comment at its call site in
    /// `probe_needed_shared_equalities`; the fail-fast is
    /// trajectory-preserving, so this gate is purely about not paying a
    /// redundant batch check where scans almost always succeed).
    ///
    /// DEFAULT OFF (`AY_PROBE_PRESCREEN` unset or `0`): the scan runs
    /// bit-identically to the pre-lever solver everywhere. `=1` opts in to
    /// the adaptive arming — `PROBE_SCAN_FAIL_STREAK` at
    /// `PROBE_SCAN_FAIL_STREAK_SWITCH` consecutive big exhausted-scan
    /// failures AND `PROBE_SCAN_BIG_FAIL_TOTAL` at
    /// `PROBE_SCAN_FAIL_TOTAL_SWITCH` over the attempt.
    ///
    /// Why opt-in: the adaptive gate provably never arms on any measured
    /// SAT-fast green (Hash top accumulator 62 big fails, wisas xs_22_32 =
    /// 166, bar 384; 44-green sweep conflict-identical), but WITHIN the
    /// hard* refutation family it arms mid-solve and re-routes trajectories.
    ///
    /// CASUALTY CLASS CLOSED (#probe-batch-prescreen-exact): the original
    /// blunt fail-fast (`!is_unsat` → skip) treated a batch-Unknown as a
    /// license to skip the scan, occasionally dropping a PRODUCTIVE scan
    /// whose full-set infeasibility the monster batch could not PROVE — the
    /// hard11/hard14 casualty. The fail-fast now splits the batch verdict
    /// (see the call site): batch-Sat is an EXACT skip (a full-set model
    /// models every subset, so no subset refutes), batch-Unsat runs the
    /// UNCAPPED scan, and batch-Unknown takes a BOUNDED RESCUE scan of the
    /// leading `PROBE_RESCUE_BUDGET` candidates before fast-failing. Measured
    /// (T:60, this tree): the rescue restores hard11 (2-3/3 green vs the
    /// blind arm's 0/3) and preserves the hard14/hard16 speedups (blind ≈
    /// rescue, both < OFF); armed fuzz + soundness gates stay conflict-free.
    ///
    /// STILL opt-in, for a DIFFERENT reason than the casualty: at the current
    /// UFLIA throughput baseline the trio hard16/18/20 decide well over T:20
    /// even WITH the (real) probe speedup — hard16 ≈ 30s, hard18/20 undecided
    /// at T:60 — so arming yields NO net T:20 conversion, only trajectory-
    /// shift risk. Default-on is justified once the throughput baseline brings
    /// the trio's decide times to the T:20 boundary (where the ~6-12x
    /// bounded-rescue probe speedup can carry them across); the exactness
    /// split above makes that flip safe (no green is lost to a mis-skip).
    fn probe_batch_prescreen_active(&self) -> bool {
        static OVERRIDE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if !*OVERRIDE.get_or_init(|| ay_core::misc_cli_flags().probe_prescreen) {
            return false;
        }
        PROBE_SCAN_FAIL_STREAK.with(|streak| streak.get() >= PROBE_SCAN_FAIL_STREAK_SWITCH)
            && PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.get() >= PROBE_SCAN_FAIL_TOTAL_SWITCH)
    }

    /// Build a conflict-probe solver over `literals` with the shared
    /// equalities at `prefix` (indices into `self.shared_equalities`)
    /// batch-asserted, reasons stripped.
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
    fn build_conflict_probe(&self, literals: &[TheoryLit], prefix: &[usize]) -> Self {
        let mut probe = LiaSolver::new(self.terms);
        probe.conflict_probe = true;
        probe.deadline = self.deadline;
        probe.set_combined_theory_mode(self.combined_theory_mode());
        for lit in literals {
            probe.register_atom(lit.term);
            probe.assert_literal(lit.term, lit.value);
        }
        for &i in prefix {
            let (lhs, rhs, _) = &self.shared_equalities[i];
            probe.assert_shared_equality(*lhs, *rhs, &[]);
        }
        probe
    }

    /// #probe-batch-prescreen primitive: one seeded (from-scratch) check of
    /// `literals` plus exactly the shared equalities at `prefix` in a fresh
    /// probe. The caller must distinguish a definite `Sat` (a model of the
    /// FULL set exists — sound checkers cannot contradict it on any subset,
    /// so the scan is decided) from `Unknown`/budget outcomes (nothing is
    /// decided: the large batch system can exhaust branching or coefficient
    /// budgets that the scan's small incremental systems never hit).
    fn probe_prefix_check(&self, literals: &[TheoryLit], prefix: &[usize]) -> TheoryResult {
        let mut probe = self.build_conflict_probe(literals, prefix);
        probe.check()
    }

    /// #probe-qx: minimize the shared-equality reason set with QUICKXPLAIN
    /// (Junker 2004) instead of the linear forward scan — the
    /// divide-and-conquer half of #probe-prefix-bisect that the pre-screen
    /// scaffold above was built for.
    ///
    /// The forward scan asserts candidates one at a time and re-runs a FULL
    /// LIA check after each add, so it pays O(n) checks whenever it fails and
    /// O(prefix) when it succeeds. Measured (T:20 census, 55 QF_UFLIA files
    /// that never reach a candidate model): ~97% of ALL full LIA invocations
    /// are these probe checks, at 8-507 checks per attempt over candidate
    /// orders of 21-509, with only ~40% of attempts proving a subset — i.e.
    /// the bulk of the budget is spent on scans that assert EVERY candidate
    /// and prove nothing.
    ///
    /// QUICKXPLAIN isolates a MINIMAL conflicting subset in O(k·log(n/k))
    /// checks, wrapped in two set-level checks that bound the whole attempt:
    ///
    ///   * PRECONDITION (`literals + ALL candidates`): the recursion is only
    ///     defined when the full candidate set actually refutes `literals`.
    ///     That one check also decides the dominant failure case EXACTLY — a
    ///     definite `Sat` means a model of the full set exists, hence a model
    ///     of every subset, hence NO subset can refute (`Refuted` at one check
    ///     where the scan pays n). An `Unknown` batch decides nothing (the
    ///     monster full-set system can exhaust a branching budget the scan's
    ///     small incremental subsystems never hit), so it yields `Undecided`
    ///     and the caller runs the untouched forward scan.
    ///   * ACCEPTANCE (`literals + exactly the returned subset`): the same
    ///     rule as the scan's — a subset is returned ONLY after a probe check
    ///     actually re-derives UNSAT from it, never by inference from the
    ///     recursion's invariants. Those invariants are only as strong as the
    ///     oracle, and this oracle is partial: an `Unknown` inside the
    ///     recursion is read as "not proven", so the recursion CAN return a
    ///     set that does not in fact refute. The acceptance check catches
    ///     exactly that and falls back.
    ///
    /// SOUNDNESS is therefore the scan's argument unchanged, including both
    /// load-bearing contracts: the result is drawn only from `order` (⊆ the
    /// caller's usable candidates — contract 1) and is never empty (contract
    /// 2 — the recursion bottoms out at a singleton, never at ∅, because the
    /// root call carries no Δ and so never takes the "background already
    /// suffices" exit). TRAJECTORY is deliberately NOT preserved: this returns
    /// a minimal subset where the scan returns a prefix, so the emitted clause
    /// differs — usually smaller, which is the point.
    ///
    /// MEASURED — AND FALSIFIED on this workload (T:20, 17 QF_UFLIA spin
    /// cells, interleaved off/on, `AY_PROBE_STATS`): the precondition batch is
    /// UNDECIDED on 78% of attempts (16152 of 20738) and definite-Sat on
    /// **zero**, so the exact fast-fail this design leans on never fires and
    /// the scan runs anyway, one check poorer. On the 22% the batch DOES
    /// refute, the recursion returns a SINGLETON every single time (4586
    /// proofs, subset_len_sum 4586) — a core the one-at-a-time scan already
    /// finds in its FIRST check, where the recursion pays ~log2(n)+2. Net:
    /// median checks per attempt 17.4 -> 14.5 (1.2x) with the proved/attempt
    /// rate FALLING 0.38 -> 0.25. The lever is kept, measured and gated, so
    /// the next reader does not re-derive it: the obstacle is not the
    /// algorithm but the ORACLE — a full LIA check over a large candidate set
    /// answers `Unknown`, and QUICKXPLAIN's first questions are its largest.
    /// The strategy that fits this oracle is `ProbeQxMode::Gallop`, which asks
    /// only small monotone prefix questions.
    ///
    /// `checks` accumulates the full LIA checks this attempt paid, for the
    /// caller's `probe_stats_record`.
    pub(super) fn quickxplain_shared_equalities(
        &self,
        literals: &[TheoryLit],
        order: &[usize],
        checks: &mut u64,
    ) -> QxOutcome {
        if self.should_timeout() {
            return QxOutcome::Undecided;
        }
        *checks += 1;
        let batch = self.probe_prefix_check(literals, order);
        prescreen_batch_verdict_record(&batch);
        if probe_verdict_is_sat(&batch) {
            qx_stats_record(QxStat::Refuted, *checks, 0);
            return QxOutcome::Refuted;
        }
        if !probe_verdict_is_unsat(&batch) {
            qx_stats_record(QxStat::BatchUnknown, *checks, 0);
            return QxOutcome::Undecided;
        }

        // The recursion may never cost materially more than the scan it
        // replaces: `Unknown` answers inside it break the halving argument, so
        // without a cap a pathological attempt could out-spend the O(n) scan.
        // Exhausting the budget is `Undecided` — the caller's scan then still
        // finds a (prefix) subset, so the cap costs clause QUALITY at worst,
        // never soundness.
        let budget = (order.len() + QX_CHECK_SLACK) as u64;
        let Some(core) = self.qx_recurse(literals, &[], false, order, checks, budget) else {
            qx_stats_record(QxStat::Aborted, *checks, 0);
            return QxOutcome::Undecided;
        };
        // Canonicalize to candidate-order position: the recursion returns the
        // two halves' cores concatenated, and a stable order keeps the emitted
        // clause (and the #probe-subset-cache hint) reproducible.
        let core: HashSet<usize> = core.into_iter().collect();
        let subset: Vec<usize> = order.iter().copied().filter(|i| core.contains(i)).collect();
        if subset.is_empty() {
            // Unreachable by construction (contract 2), but an empty "core"
            // must never reach the caller as a proven subset.
            qx_stats_record(QxStat::Aborted, *checks, 0);
            return QxOutcome::Undecided;
        }
        // ACCEPTANCE: re-derive the infeasibility from `literals` plus exactly
        // this subset. Skipped only when the subset IS the whole candidate
        // set, which the precondition check above already refuted.
        if subset.len() < order.len() {
            if self.should_timeout() {
                qx_stats_record(QxStat::Aborted, *checks, 0);
                return QxOutcome::Undecided;
            }
            *checks += 1;
            if !probe_verdict_is_unsat(&self.probe_prefix_check(literals, &subset)) {
                qx_stats_record(QxStat::VerifyFail, *checks, subset.len());
                return QxOutcome::Undecided;
            }
        }
        qx_stats_record(QxStat::Proved, *checks, subset.len());
        QxOutcome::Proved(subset)
    }

    /// QUICKXPLAIN' (Junker 2004): the subset of `c` that, together with
    /// `literals` and `base`, still refutes.
    ///
    /// `delta_nonempty` records whether the CALLER extended `base` on the way
    /// in (Junker's Δ). When it did, one check of `literals + base` decides
    /// whether the caller's own addition already suffices — the split that
    /// makes the recursion O(k·log(n/k)) instead of O(n). The FIRST half of
    /// `c` is always the half pushed into the background, so the returned core
    /// inherits the caller's ordering bias (conflict-touching equalities lead
    /// `order`, and a core drawn from them keeps the clause relevant).
    ///
    /// `None` = ABORT (deadline or check budget): the caller must not read an
    /// aborted recursion as a proof of anything.
    fn qx_recurse(
        &self,
        literals: &[TheoryLit],
        base: &[usize],
        delta_nonempty: bool,
        c: &[usize],
        checks: &mut u64,
        budget: u64,
    ) -> Option<Vec<usize>> {
        if delta_nonempty {
            // #lia-deadline-forward: every probe check is a full BigRational
            // LIA solve, so poll the parent's deadline before each one.
            if self.should_timeout() || *checks >= budget {
                return None;
            }
            *checks += 1;
            if probe_verdict_is_unsat(&self.probe_prefix_check(literals, base)) {
                return Some(Vec::new());
            }
        }
        if c.len() <= 1 {
            return Some(c.to_vec());
        }
        let (c1, c2) = c.split_at(c.len() / 2);
        let mut background = Vec::with_capacity(base.len() + c1.len());
        background.extend_from_slice(base);
        background.extend_from_slice(c1);
        let d1 = self.qx_recurse(literals, &background, true, c2, checks, budget)?;
        background.truncate(base.len());
        background.extend_from_slice(&d1);
        let d2 = self.qx_recurse(literals, &background, !d1.is_empty(), c1, checks, budget)?;
        let mut core = d1;
        core.extend(d2);
        Some(core)
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
                collect_atom_vars_impl(self.terms, lit.term, &mut self.reachable_vars_buf);
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
                collect_atom_vars_impl(self.terms, lit.term, &mut self.conflict_vars_buf);
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
        // ONLY when augmentation appended nothing. The appended shared-
        // equality/Dioph reasons are load-bearing exactly when the simplex
        // Farkas builder missed pivoted-away slack reasons (#8147) — but
        // `minimize_farkas_conflict` strips every zero-coefficient literal
        // from the learned clause in all builds, so a certificate
        // zero-extended over the appended reasons would delete them and
        // re-create the #8147 false-UNSAT class. Dropping the certificate
        // whenever literals were appended keeps the verdict and the learned
        // clause intact; the no-append case (still the common one) keeps the
        // certificate — a strict improvement over the parent, which dropped
        // it wholesale.
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

    /// #probe-prefix-bisect trigger: consecutive EXHAUSTED-scan failures of
    /// the incremental forward scan (a scan that asserted every candidate
    /// and still could not reproduce the infeasibility — deadline aborts do
    /// not count; only scans over `PROBE_SCAN_SWITCH_MIN_ORDER`+ candidate
    /// orders count). Thread-local for the same reason as the hint:
    /// combiners (and their LIA solvers) are rebuilt per refinement round,
    /// so per-solver state would reset before it could ever trip. Once the
    /// streak reaches `PROBE_SCAN_FAIL_STREAK_SWITCH` AND the attempt total
    /// reaches `PROBE_SCAN_FAIL_TOTAL_SWITCH`, the thread's probes switch
    /// from the incremental scan to the set-level pre-screen (see
    /// `probe_needed_shared_equalities`); scan successes reset the streak
    /// (never the total). Purely a performance trajectory heuristic: every
    /// strategy accepts a subset only after an actual probe check refutes
    /// literals+subset.
    ///
    /// The other half of the strategy — divide-and-conquer instead of a
    /// forward scan — landed as #probe-qx (`quickxplain_shared_equalities`),
    /// which does NOT arm off this streak: the census showed the fail-streak
    /// arming never trips inside a T:20 budget on the spin cells it was meant
    /// for (287 big fails accumulated vs the 384 bar on wisas xs_40_60), and
    /// those cells burn the scan on SUCCESSFUL large-subset attempts the
    /// streak never counts. #probe-qx arms on candidate-order size instead.
    static PROBE_SCAN_FAIL_STREAK: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };

    /// #probe-prefix-bisect: monotone per-attempt count of big exhausted
    /// scan failures (same counting rule as the streak, no reset on
    /// success). See `PROBE_SCAN_FAIL_TOTAL_SWITCH`.
    static PROBE_SCAN_BIG_FAIL_TOTAL: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// #probe-prefix-bisect: consecutive EXPENSIVE exhausted-scan failures after
/// which a thread's probes switch to the set-level strategy. Chosen from
/// measured failure profiles: the mathsat EufLaArithmetic hard* refutations
/// fail ~89% of scans (the streak trips within the first dozen probes),
/// while the trajectory-sensitive Hash SAT greens succeed ~96-100% of
/// probes, keeping their trajectories — and conflict counts — identical.
const PROBE_SCAN_FAIL_STREAK_SWITCH: u32 = 8;

/// #probe-prefix-bisect: an exhausted scan only counts toward the switch
/// when its candidate order was at least this large. The point of the
/// set-level strategy is capping the O(|order|) checks a FAILING scan pays;
/// a failing scan over a tiny order is already cheap, and counting it
/// would let trajectory-sensitive greens with small closures trip the
/// switch on scattered failures (hash_sat_04_19: 550 probes at ~1.4
/// checks/probe, 12 failures — a sat green the streak-only trigger turned
/// unknown). Measured orders: Hash family mostly ~1-3, hard* refutations
/// ~50-500.
const PROBE_SCAN_SWITCH_MIN_ORDER: usize = 16;

/// #probe-prefix-bisect: the switch additionally requires this many big
/// exhausted-scan failures over the whole attempt. The streak alone still
/// tripped on two Hash SAT greens whose closures ARE big (hash_sat_04_13:
/// 62 big fails over its whole 136-conflict solve, orders up to ~59;
/// hash_sat_05_12: 13) and re-routed them 7-17x more conflicts. Measured
/// whole-solve totals on the decided greens that accumulate the most:
/// wisas xs_22_32 = 166 (a 128 bar armed it and re-routed 536 → 485
/// conflicts — favorable but the guard demands identity), hash_sat_04_13
/// = 62; the hard* refutations accumulate 1300-2800 within their T:20/T:60
/// windows (~40-100/s) and cross this bar within seconds. A SAT-fast green
/// cannot legitimately reach 384 big failed probe scans — that volume of
/// failing augment probes IS the refutation-grind signature the fail-fast
/// exists for.
const PROBE_SCAN_FAIL_TOTAL_SWITCH: u64 = 384;

/// #probe-qx: outcome of one QUICKXPLAIN minimization attempt (see
/// `quickxplain_shared_equalities`).
pub(crate) enum QxOutcome {
    /// A subset an actual probe check re-derived UNSAT from, together with the
    /// conflict literals. Drawn only from the candidate order; never empty.
    Proved(Vec<usize>),
    /// The full candidate set has a MODEL together with the conflict literals,
    /// so NO subset can refute them: minimization is provably unproductive.
    Refuted,
    /// Nothing decided — the caller must fall back to the forward scan.
    Undecided,
}

/// Candidate orders below this keep the linear forward scan under BOTH
/// alternative strategies (#probe-qx and #probe-gallop). Neither pays for
/// itself on a short order — QUICKXPLAIN adds two set-level checks around its
/// recursion, and a gallop over an order the scan finishes in a handful of
/// checks saves nothing while still coarsening the proven subset. Same cost
/// model — and the same measured order profile — as
/// `PROBE_SCAN_SWITCH_MIN_ORDER`: the trajectory-sensitive Hash SAT greens run
/// orders of ~1-3, the wisas / Certora spin cells these levers target run
/// 21-509.
const QX_MIN_ORDER: usize = 16;

/// #probe-qx: check budget slack over `|order|`. The recursion is
/// O(k·log(n/k)) only while the oracle is exact; an `Unknown` answer inside it
/// breaks the halving argument, so an attempt is capped at what the scan it
/// replaces would have cost, plus the two set-level checks and a small margin.
const QX_CHECK_SLACK: usize = 8;

/// Which shared-equality minimization strategy the probe uses in place of the
/// one-at-a-time forward scan. Both alternatives are default OFF: each returns
/// a different subset than the scan's prefix, so the emitted clause — and with
/// it the search trajectory — differs.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProbeQxMode {
    /// `AY_LIA_PROBE_QX` unset or `0`: the linear forward scan, unchanged.
    Scan,
    /// `AY_LIA_PROBE_QX=1`: QUICKXPLAIN divide-and-conquer (#probe-qx).
    Quickxplain,
    /// `AY_LIA_PROBE_QX=gallop`: exponential-batch prefix scan (#probe-gallop)
    /// on the SAME add-only incremental probe the scan uses — one check per
    /// 1, 2, 4, 8, ... adds instead of one per add.
    ///
    /// Why a second strategy: measured (T:20, 17 QF_UFLIA spin cells), the
    /// full-candidate-set batch check QUICKXPLAIN needs as its precondition is
    /// UNDECIDED on 78% of attempts and definite-Sat on 0% — the oracle simply
    /// cannot answer set-level questions here, and every core it CAN prove
    /// turns out to be a singleton the one-at-a-time scan already finds in its
    /// first check. The gallop asks only the questions this oracle answers —
    /// the scan's own monotone prefix questions, on the scan's own incremental
    /// probe — and just asks O(log n) of them instead of O(n).
    ///
    /// MEASURED, same 17 cells, interleaved off/on: median checks per probe
    /// attempt 18.9 -> 3.8 (5.0x; per-file 2.3x-68x, every cell improves) at an
    /// UNCHANGED proved/attempt rate (0.366 -> 0.367). QUICKXPLAIN on the same
    /// cells: 17.4 -> 14.5 (1.2x) with the rate FALLING 0.38 -> 0.25.
    ///
    /// WHY IT IS STILL OFF BY DEFAULT: the cheaper probe frees budget but the
    /// proven prefix is not always the scan's, so clauses — and trajectories —
    /// move in both directions. Full QF_UFLIA division (300 files, T:20,
    /// interleaved): 8 conversions, 8 regressions, 0 sat/unsat disagreements.
    /// Verdict-neutral in the aggregate, but not regression-free, and the
    /// losses are SAT-fast files (0.7-8s) whose closures (41-45) overlap the
    /// winners' (26-30), so no order-size arming separates them. Default-on
    /// needs an arming signal that fires only where the budget is already lost.
    Gallop,
}

/// Probe minimization strategy for this process (`--lia-probe-qx`, B73,
/// read once). See [`ProbeQxMode`].
fn probe_qx_mode() -> ProbeQxMode {
    static MODE: std::sync::OnceLock<ProbeQxMode> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| match ay_core::misc_cli_flags().lia_probe_qx.as_deref() {
        Some("quickxplain") => ProbeQxMode::Quickxplain,
        Some("gallop") => ProbeQxMode::Gallop,
        _ => ProbeQxMode::Scan,
    })
}

/// A DEFINITE infeasibility verdict from a probe check. `Unknown`/`NeedSplit`
/// and budget outcomes decide NOTHING — they mean "not proven", never "proven
/// feasible" (see `probe_prefix_check`).
fn probe_verdict_is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_))
}

/// A DEFINITE feasible verdict: a concrete model of the asserted set exists.
/// Only `Sat` qualifies. This is the exactness hinge of both the
/// #probe-batch-prescreen fail-fast and the #probe-qx precondition: a model of
/// `literals + ALL candidates` also models `literals + ANY subset`, so a
/// definite-Sat batch PROVES no subset can refute — the minimization is
/// provably unproductive and skipping it drops nothing.
fn probe_verdict_is_sat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Sat)
}

/// #probe-batch-prescreen-exact: default leading-candidate budget for the
/// bounded rescue scan taken when the full-set batch verdict is UNKNOWN.
/// Conflict-touching equalities lead the candidate order and measured proven
/// subsets are ~5-6 equalities, so a refuting subset — when one exists — almost
/// always lies in the first couple dozen candidates; a scan that exhausts this
/// budget without reproducing infeasibility fast-fails. Overridable per run
/// with `AY_PRESCREEN_RESCUE=<n>` (n=0 restores the old blind fast-fail:
/// UNKNOWN batches skip the scan entirely).
const PROBE_RESCUE_BUDGET_DEFAULT: usize = 24;

/// Leading-candidate budget for the UNKNOWN-batch bounded rescue scan
/// (`AY_PRESCREEN_RESCUE` override, else [`PROBE_RESCUE_BUDGET_DEFAULT`]).
/// Process-cached (one env read).
fn probe_rescue_budget() -> usize {
    // B25: env override retired; the named constant is the value.
    PROBE_RESCUE_BUDGET_DEFAULT
}

/// #probe-batch-prescreen observability: per-process histogram of the full-set
/// batch verdict at the fail-fast (Sat = exact fast-fail, Unsat = uncapped
/// scan, other = UNKNOWN bounded rescue). Printed every 256 armed batches when
/// `AY_PROBE_STATS` is set; zero overhead when unset (one cached env read).
fn prescreen_batch_verdict_record(r: &TheoryResult) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ENABLED.get_or_init(|| ay_core::misc_cli_flags().probe_stats) {
        return;
    }
    static SAT: AtomicU64 = AtomicU64::new(0);
    static UNSAT: AtomicU64 = AtomicU64::new(0);
    static UNKNOWN: AtomicU64 = AtomicU64::new(0);
    let counter = match r {
        TheoryResult::Sat => &SAT,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => &UNSAT,
        _ => &UNKNOWN,
    };
    let n = counter.fetch_add(1, Ordering::Relaxed) + 1;
    let total = SAT.load(Ordering::Relaxed)
        + UNSAT.load(Ordering::Relaxed)
        + UNKNOWN.load(Ordering::Relaxed);
    if total.is_multiple_of(256) || n == 1 {
        safe_eprintln!(
            "[PRESCREEN-BATCH] sat={} unsat={} unknown={}",
            SAT.load(Ordering::Relaxed),
            UNSAT.load(Ordering::Relaxed),
            UNKNOWN.load(Ordering::Relaxed)
        );
    }
}

/// Reset the #probe-subset-cache hint. Called by the UFLIA hybrid at lazy
/// DETOUR entry so a subset proven under a previous attempt (or a previous
/// check-sat) never seeds the first conflicts of a new detour. Also clears
/// the #probe-prefix-bisect fail streak: evidence gathered under a previous
/// attempt's trajectory should not pre-switch the new one.
pub fn reset_probe_subset_hint() {
    PROBE_SUBSET_HINT.with(|hint| hint.borrow_mut().clear());
    PROBE_SCAN_FAIL_STREAK.with(|streak| streak.set(0));
    PROBE_SCAN_BIG_FAIL_TOTAL.with(|total| total.set(0));
}

/// Opaque snapshot of the thread-local probe trajectory state
/// (#detour-snapshot-extend): the #probe-subset-cache hint plus the
/// #probe-prefix-bisect fail streak/total. Taken by the UFLIA hybrid at a
/// SPECULATIVE detour-extension decision point and restored when the
/// speculation fails to decide, so the post-detour eager resume observes
/// EXACTLY the probe state it would have seen without the speculation
/// (exact-replay contract). The state is heuristic-only either way — a
/// stale hint is verified by an actual probe check before use — but the
/// streak/total feed the scan-vs-bisect strategy switch, so leaking a
/// failed extension's counters would re-route the resume's trajectory.
#[derive(Debug, Clone)]
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

/// #probe-qx observability: per-process outcome histogram of QUICKXPLAIN
/// minimization attempts, printed every 256 attempts when `AY_PROBE_STATS` is
/// set. Zero overhead when unset (one cached env read).
fn qx_stats_record(outcome: QxStat, checks: u64, subset_len: usize) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ENABLED.get_or_init(|| ay_core::misc_cli_flags().probe_stats) {
        return;
    }
    static PROVED: AtomicU64 = AtomicU64::new(0);
    static REFUTED: AtomicU64 = AtomicU64::new(0);
    static BATCH_UNKNOWN: AtomicU64 = AtomicU64::new(0);
    static ABORTED: AtomicU64 = AtomicU64::new(0);
    static VERIFY_FAIL: AtomicU64 = AtomicU64::new(0);
    static CHECKS: AtomicU64 = AtomicU64::new(0);
    static SUBSET_LEN: AtomicU64 = AtomicU64::new(0);
    let counter = match outcome {
        QxStat::Proved => &PROVED,
        QxStat::Refuted => &REFUTED,
        QxStat::BatchUnknown => &BATCH_UNKNOWN,
        QxStat::Aborted => &ABORTED,
        QxStat::VerifyFail => &VERIFY_FAIL,
    };
    counter.fetch_add(1, Ordering::Relaxed);
    CHECKS.fetch_add(checks, Ordering::Relaxed);
    SUBSET_LEN.fetch_add(subset_len as u64, Ordering::Relaxed);
    let total = PROVED.load(Ordering::Relaxed)
        + REFUTED.load(Ordering::Relaxed)
        + BATCH_UNKNOWN.load(Ordering::Relaxed)
        + ABORTED.load(Ordering::Relaxed)
        + VERIFY_FAIL.load(Ordering::Relaxed);
    if total.is_multiple_of(256) || total == 1 {
        safe_eprintln!(
            "[QX-STATS] attempts={} proved={} refuted={} batch_unknown={} aborted={} \
             verify_fail={} checks={} subset_len_sum={}",
            total,
            PROVED.load(Ordering::Relaxed),
            REFUTED.load(Ordering::Relaxed),
            BATCH_UNKNOWN.load(Ordering::Relaxed),
            ABORTED.load(Ordering::Relaxed),
            VERIFY_FAIL.load(Ordering::Relaxed),
            CHECKS.load(Ordering::Relaxed),
            SUBSET_LEN.load(Ordering::Relaxed)
        );
    }
}

/// #probe-qx outcome classes counted by [`qx_stats_record`].
enum QxStat {
    Proved,
    Refuted,
    BatchUnknown,
    Aborted,
    VerifyFail,
}

/// #probe-prefix-bisect observability: per-process count of big exhausted
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
        self.direct_enum_witness = None;

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
        if self.dioph_needs_revalidation {
            if equality_key_changed {
                self.dioph_safe_dependent_vars.clear();
                self.dioph_cached_substitutions.clear();
                self.dioph_cached_modular_gcds.clear();
                self.dioph_cached_reasons.clear();
            }
            self.dioph_needs_revalidation = false;
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
            self.dioph_safe_dependent_vars.clear();
            self.dioph_cached_substitutions.clear();
            self.dioph_cached_modular_gcds.clear();
            self.dioph_cached_reasons.clear();
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
            let mut prev_fixed_count = self.count_fixed_integer_vars();

            for tighten_round in 0..max_tighten_rounds {
                if self.dioph_cached_substitutions.is_empty() {
                    break;
                }
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
                if new_fixed_count <= prev_fixed_count {
                    break;
                }

                if debug {
                    safe_eprintln!(
                        "[LIA] Dioph tighten round {}: {} newly fixed vars (was {}, now {})",
                        tighten_round,
                        new_fixed_count - prev_fixed_count,
                        prev_fixed_count,
                        new_fixed_count
                    );
                }
                prev_fixed_count = new_fixed_count;

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
        // propagation before the final check.
        // #C5: served from the incrementally maintained assertion view —
        // no per-BCP O(asserted) re-scan + sort.
        let (equality_key_empty, needs_bcp_dioph) = {
            let equality_key = self.equality_key();
            (
                equality_key.is_empty(),
                !equality_key.is_empty() && self.dioph_equality_key != equality_key,
            )
        };

        // #C8: re-validate the equality-derived caches after a pop/soft_reset.
        // When the equality set changed, drop them before the modular checks
        // (which iterate dioph_cached_substitutions, modular.rs:189) can reuse a
        // popped scope's substitutions (#3736). An unchanged set keeps them.
        if self.dioph_needs_revalidation {
            if needs_bcp_dioph {
                self.dioph_safe_dependent_vars.clear();
                self.dioph_cached_substitutions.clear();
                self.dioph_cached_modular_gcds.clear();
                self.dioph_cached_reasons.clear();
            }
            self.dioph_needs_revalidation = false;
        }

        if equality_key_empty {
            self.dioph_equality_key.clear();
            self.dioph_needs_full_check = false;
            self.dioph_safe_dependent_vars.clear();
            self.dioph_cached_substitutions.clear();
            self.dioph_cached_modular_gcds.clear();
            self.dioph_cached_reasons.clear();
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
                // The cache invalidation MUST run unconditionally: stale Dioph
                // substitutions under an outdated equality key are unsound for
                // any downstream consumer.
                self.dioph_equality_key.clear();
                self.dioph_safe_dependent_vars.clear();
                self.dioph_cached_substitutions.clear();
                self.dioph_cached_modular_gcds.clear();
                self.dioph_cached_reasons.clear();
                self.dioph_modified_bounds = false;
                self.dioph_bound_term_ids.clear();

                // Search-phase deferral (#nip benchmark): the from-scratch
                // BCP-time Dioph solve ran on EVERY equality-key change — on
                // boundary-pattern problems that is every decision (~205ms
                // each, ~100% of solve time). While in the eager SEARCH
                // phase, skip only the expensive solve and leave
                // dioph_needs_full_check sticky: needs_final_check_after_sat
                // == true guarantees the post-SAT full check runs it before
                // any SAT is accepted. Skipping conflict DETECTION mid-search
                // only delays the conflict — it can never accept a wrong SAT.
                const BCP_DIOPH_UNPRODUCTIVE_LIMIT: u32 = 4;
                if self.in_search_phase
                    && self.dioph_bcp_unproductive_streak >= BCP_DIOPH_UNPRODUCTIVE_LIMIT
                {
                    // Adaptive deferral: this search's BCP-time Dioph runs have
                    // been consistently unproductive — stop paying the
                    // from-scratch elimination per decision and let the
                    // post-SAT final check (guaranteed by
                    // needs_final_check_after_sat) cover completeness.
                    // Productive searches (modular-cascade class, #8736) never
                    // reach the limit and keep their early Dioph conflicts.
                    self.dioph_needs_full_check = true;
                } else {
                    if let Some(reasons) = self.timed_try_diophantine_solve() {
                        if debug {
                            safe_eprintln!("[LIA] BCP-time Dioph solve detected UNSAT");
                        }
                        self.dioph_bcp_unproductive_streak = 0;
                        return TheoryResult::Unsat(reasons);
                    }
                    self.dioph_bcp_unproductive_streak =
                        self.dioph_bcp_unproductive_streak.saturating_add(1);

                    // NOTE: nothing between the key comparison above and this
                    // point mutates `asserted`, so the view's equality key is
                    // unchanged and this clone equals the compared key (#C5).
                    self.dioph_equality_key = self.equality_key().to_vec();
                    self.dioph_needs_full_check = true;
                    clear_bcp_dioph_after = true;
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
                self.dioph_safe_dependent_vars.clear();
                self.dioph_cached_substitutions.clear();
                self.dioph_cached_modular_gcds.clear();
                self.dioph_cached_reasons.clear();
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
