// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deletion-based unsat-core minimization for the named-core redirects
//! (#uc-core-minimize).
//!
//! WHY: 2025 UC scoring pays `#named asserts − |core|` per validated unsat
//! answer. On the families that carry most of the QF_Equality ceiling
//! (QG-classification, QF_AX storecomm) the named-core redirect emits a
//! reduction-0 core through two measured mechanisms:
//!
//! - the direct assumption lane proves unsat but a THEORY-level refutation
//!   (the EUF a=b,b=c,a!=c shape) surfaces an EMPTY SAT-level harvest, which
//!   `unsat_core_entries` pads to ALL named assertions;
//! - the direct assumption lane returns Unknown and
//!   `rescue_named_core_redirect_unknown`'s scoped plain re-solve records the
//!   conservative all-assumptions core (measured on both gensys_icl963
//!   [QfUf] and storecomm [QfAx widened to QfAuflia by declared constants]).
//!
//! DESIGN: a deletion loop with geometric chunking and harvest-jump
//! acceleration, run at the named-core redirect chokepoint while the base
//! assertion set is still STRIPPED to the unnamed assertions. Every subset
//! solve proves exactly the printed-core contract ("S conjoined with the
//! unnamed assertions is unsatisfiable"). Two subset-solve engines, chosen by
//! how the original verdict was obtained:
//!
//! - direct-lane unsat, non-array → `check_sat_assuming(S)` (the same
//!   assumption lane that produced the verdict; fast for EUF);
//! - rescue unsat OR array content → `solve_scoped_assumptions(base, S,
//!   plain)` (the scoped plain pipeline; for the rescue case the assumption
//!   lane already demonstrated Unknown, and for array content the assumption
//!   lane re-runs unpollable ITE-lift preprocessing per attempt and churns
//!   to the slice without deciding — see the engine-choice comment in the
//!   loop, #array-deadline-forward).
//!
//! FAIL-CLOSED (generalizes `reverify_minimized_dt_assumption_core`'s
//! discipline, strengthened): a subset is ADOPTED only when a fresh solve of
//! exactly that subset returned unsat. Harvested sub-cores are never trusted
//! directly — a harvest only nominates the NEXT candidate, which must earn
//! adoption through its own solve. The emitted core is always the last
//! solve-verified subset; on zero progress the executor's core bookkeeping is
//! restored byte-identically (padded-superset printing downstream, exactly as
//! before). Soundness is monotone: any solve-verified subset conjoined with
//! the unnamed base is unsat, hence valid to print.
//!
//! BUDGET: wall-clock aware against the live `solve_deadline` (the `-T`
//! absolute deadline installed at executor creation). A margin is reserved
//! for final output, each subset solve runs under a per-attempt budget
//! (probe first, then churn caps sized by content and instance —
//! #uc-minimize-policy P2 + the array ladder) capped by the per-solve slice
//! so one stuck subset cannot eat the whole pass, and the loop stops
//! shrinking when the remaining budget no longer covers 2x the live attempt
//! cap (#uc-minimize-policy P1) — a fat validated core beats a timeout.
//!
//! DETERMINISM: the candidate order is instance-derived (the combined
//! named/assumption vector stable-sorted by term node-count ascending with
//! parse-order tie-break — #uc-minimize-policy P3; harvest jumps are
//! re-canonicalized into that order), and the underlying solves are
//! deterministic (#8529 DetHash*,
//! fresh DpllT per subset solve, deterministic ground budgets). Wall-clock
//! cutoffs are the only nondeterminism and only bind near the deadline.
//!
//! SCOPE: gated to EUF/ArrayEuf content — categories `QfUf`/`QfAx`, plus
//! `QfAuflia` when the static features show pure UF+array content (declared
//! QF_AX benchmarks always widen to QfAuflia because their declared constants
//! set `has_uf`; see `widen_with_uf`). The DT arms keep their own reverify
//! pass untouched; arith reuse later = widen this gate. Skipped under
//! `produce-proofs`/`--self-check`: the subset solves would leave proof
//! traces of the wrong (reduced) problem.

use std::time::Duration;

use ay_core::kani_compat::{DetHashMap, DetHashSet as HashSet};
use ay_core::time::Instant;
use ay_core::{TermData, TermId, TermStore};

use super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

/// Below this much remaining wall budget the pass does not start: the risk of
/// blowing the output window outweighs any shrink.
const MIN_REMAINING_TO_SHRINK: Duration = Duration::from_secs(5);

/// Fuse: abort the whole pass when an attempt overran its per-solve deadline
/// by more than this — the subset-solve engine is not honoring the deadline
/// on this instance, so further attempts risk the output window.
const OVERSHOOT_FUSE: Duration = Duration::from_secs(2);

/// Array-content scoped-engine cap, WIDENED (#array-deadline-forward): the
/// original 5s containment existed because the array solve lanes did not
/// poll the per-solve deadline — a subset re-solve was measured hanging 40+s
/// past its ~8.7s slice inside ONE `ArraySolver::final_check`
/// (`check_row2_extended`'s O(pairs x explain-BFS) loop) until the external
/// -T watchdog killed the already-answered run. With the deadline now
/// forwarded into the ArraySolver (combiner `set_deadline` -> array
/// sub-check-boundary + amortized in-loop polls), attempts stop within the
/// overshoot fuse of their slice, so scoped attempts are safe under the
/// normal slice budget. The cap stays as a BACKSTOP against instances whose
/// rescue is so expensive that even probe attempts are unlikely to decide
/// within a slice — a lost answer still costs more than any reduction gains.
const ARRAY_SCOPED_RESCUE_CAP: Duration = Duration::from_secs(30);

/// Conservative first-attempt probe budget, ALL content
/// (#uc-minimize-policy P2, generalizing #array-deadline-forward): the
/// first attempt runs under `min(slice, max(FIRST_PROBE_FLOOR, 4 x
/// rescue))` instead of the full slice, so an engine that ignores its
/// per-solve deadline on this instance is detected after a bounded probe
/// (the overshoot fuse below aborts the pass), not after a full slice at
/// competition scale.
const FIRST_PROBE_FLOOR: Duration = Duration::from_secs(2);

/// Post-probe per-attempt churn cap (#uc-minimize-policy P2,
/// generalizing #array-deadline-forward): subset attempts are strongly
/// bimodal (measured on the 1200s storecomm 496-named probe: median attempt
/// 0.43s, EVERY adoption <= 1.3s across all sampled instances, while
/// undecidable-in-slice attempts churn to the full 197s slice — 7 churners
/// ate 92% of the pass and the scan stopped at reduction 6 where cvc5
/// demonstrates ~224). Capping the churn cost at 10s lets the deletion scan
/// run ~10x more candidates inside the same wall. Array content: the <600
/// named rung of the size ladder, `min(slice, max(this, 4 x rescue))`
/// (ARRAY_LADDER_* raise the rung with instance size). Non-array content:
/// `min(slice, max(this, 4 x costliest-adoption-observed))` — adaptive
/// difficulty from the only attempt class whose cost is known productive.
/// The normal slice stays the CEILING (min above) — at small -T budgets the
/// slice is already tighter than this cap.
const ATTEMPT_CHURN_CAP: Duration = Duration::from_secs(10);

/// Size-aware array cap ladder (#uc-minimize-policy ladder): adoption cost
/// grows with instance size (per-attempt array rebuild + final_check work
/// scale with the named count), so a flat 10s churn cap that is 8x the
/// slowest SMALL-instance adoption starves the >=1000-named classes into
/// zero adoptions. Rungs by deduplicated named count: <600 named keeps
/// ATTEMPT_CHURN_CAP, 600-999 named pays up to 30s, >=1000 named up to
/// 60s; always `min(slice, max(rung, 4 x rescue))`.
const ARRAY_LADDER_MEDIUM_CAP: Duration = Duration::from_secs(30);
const ARRAY_LADDER_LARGE_CAP: Duration = Duration::from_mins(1);
const ARRAY_LADDER_MEDIUM_NAMED: usize = 600;
const ARRAY_LADDER_LARGE_NAMED: usize = 1000;

/// One-shot ladder escalation (#uc-minimize-policy ladder): if the first
/// ARRAY_ESCALATE_AFTER_ATTEMPTS post-probe attempts produced ZERO
/// adoptions, the rung may be too small for this instance to DECIDE
/// subsets at all — multiply it by ARRAY_LADDER_ESCALATION_FACTOR exactly
/// once. Escalation is count-based and cheap to reach when attempts fail
/// fast; it is harmless there (fast attempts never touch the cap).
const ARRAY_LADDER_ESCALATION_FACTOR: u32 = 3;
const ARRAY_ESCALATE_AFTER_ATTEMPTS: u64 = 8;

/// Hopeless-abort, WALL-based (#uc-minimize-policy ladder): end a
/// zero-adoption pass (answer + padded core kept via the zero-progress
/// restore) once it has spent `shrink_budget /
/// ARRAY_HOPELESS_WALL_DIVISOR`, clamped to [ARRAY_HOPELESS_WALL_MIN_BUDGETS,
/// ARRAY_HOPELESS_WALL_MAX_BUDGETS] x the base post-probe budget, instead
/// of churning the remaining wall to the deadline. WHY wall and not
/// attempt count: cap-churning attempts make any useful count threshold
/// unreachable (probe + 14 x 60s-rung churners exceed every -T budget;
/// measured on the 1226-named storecomm nf class at -T:120 — every
/// post-probe attempt ran its full 18.3s budget, result=unknown, and the
/// pass burned to the headroom stop), while FAST-failing attempts are
/// healthy scan progress a count threshold would behead (measured
/// parse-order storecomm 231-named: 45 cheap fails before the first
/// adoption at attempt 46). The MIN clamp guarantees a few FULL churners'
/// worth of evidence before declaring hopeless (a loaded machine inflates
/// attempt costs; measured: the same 231-named instance adopting at
/// 0.45s/attempt in a quiet window churned 10s attempts under a competing
/// division run). A pass with ANY adoption is never wall-guarded.
const ARRAY_HOPELESS_WALL_DIVISOR: u32 = 3;
const ARRAY_HOPELESS_WALL_MIN_BUDGETS: u32 = 3;
const ARRAY_HOPELESS_WALL_MAX_BUDGETS: u32 = 8;

/// One-shot tail-first order FLIP, non-array content (#uc-minimize-policy
/// P3, gate-driven correction): the ascending scan is right when the tiny
/// members are the deletable ones (measured qg5 gensys_icl001: first chunk
/// adoption at ATTEMPT 1, final core 77/130 — deeper than cvc5's 83
/// minimal), and pathological when the tiny prefix is essential (measured
/// qg5 gensys_icl153/icl630/icl833: chunk collapses to 1 inside the
/// essential prefix and the scan crawls ~90 cheap-SAT singles without ever
/// reaching the deletable large members — 0 adoptions where parse order
/// found 6-13). The two classes separate crisply and EARLY: winners adopt
/// on attempt 1, losers never adopt. With zero adoptions by this attempt
/// count (backoff to chunk=1 costs ~6 attempts, plus a handful of essential
/// singles), reverse the scan once — the deletable large members are then
/// tried first (measured big-first on the loser class: recovers 6-13
/// reduction). Deterministic: triggered by attempt count, not wall clock.
const NON_ARRAY_ORDER_FLIP_AFTER_ATTEMPTS: u64 = 12;

/// Conservative whole-pass budget when NO deadline is installed (interactive
/// / API use without `-T`): bounded politeness, far above typical EUF
/// re-solve costs.
const NO_DEADLINE_BUDGET: Duration = Duration::from_secs(30);

impl Executor {
    /// Shrink a certified UNSAT assumption core by deletion, re-solving
    /// subsets against the current (stripped) base assertions.
    ///
    /// PRECONDITIONS (the two named-core redirect call sites):
    /// - `self.ctx.assertions` holds the UNNAMED-only base;
    /// - `combined` is the full named-plus-user-literal assumption set of the
    ///   check that produced `result`;
    /// - `certify_assumption_core` (and, when it fired, the Unknown rescue)
    ///   has already run, so any surviving `last_assumption_core` is a
    ///   certified starting point;
    /// - `rescue_elapsed` is `Some(duration of the rescue solve)` when the
    ///   unsat came from the scoped-plain rescue rather than the direct
    ///   assumption lane (selects the subset-solve engine and gates the
    ///   array containment rule).
    ///
    /// Returns `result` unchanged (the verdict is never altered); on progress
    /// `last_assumption_core` is pinned to the final solve-verified subset,
    /// on zero progress the core bookkeeping is restored byte-identically.
    pub(crate) fn minimize_assumption_core(
        &mut self,
        combined: &[TermId],
        result: Result<SolveResult>,
        rescue_elapsed: Option<Duration>,
    ) -> Result<SolveResult> {
        let rescued = rescue_elapsed.is_some();
        if !matches!(result, Ok(SolveResult::Unsat(_))) {
            return result;
        }
        // Proof-envelope coherence: subset solves overwrite clause traces /
        // proof state with refutations of REDUCED problems. Under
        // produce-proofs (incl. --self-check, which forces it) the boundary
        // would materialize a wrong proof — skip entirely.
        if self.produce_proofs_enabled() {
            return result;
        }
        // A/B knob (NOT a soundness guard — the pass only shrinks a valid
        // core; disabling it restores the padded-superset behavior).
        if std::env::var_os("AY_NO_UC_MINIMIZE").is_some() {
            return result;
        }

        // Category gate: EUF / ArrayEuf content only for now
        // (#uc-core-minimize). QfAuflia qualifies only when the features show
        // no arithmetic/BV/strings/seq/FP/quantifier content — the shape of a
        // declared QF_AX benchmark widened by its declared constants. The DT
        // arms already carry their own reverify pass and won their division —
        // leave them untouched.
        let mut all = self.ctx.assertions.clone();
        all.extend_from_slice(combined);
        let (category, features) = self.detect_logic_category(&all);
        let euf_like = match category {
            LogicCategory::QfUf | LogicCategory::QfAx => true,
            LogicCategory::QfAuflia => {
                !features.has_int
                    && !features.has_real
                    && !features.has_bv
                    && !features.has_strings
                    && !features.has_seq
                    && !features.has_fpa
                    && !features.has_quantifiers
            }
            _ => false,
        };
        if !euf_like {
            return result;
        }
        // Array containment rule (see ARRAY_SCOPED_RESCUE_CAP): scoped subset
        // re-solves on array content only when the rescue was affordable.
        // Widened from 5s to 30s (#array-deadline-forward) — attempts are now
        // deadline-honoring, so the cap is an expected-value backstop, not a
        // runaway guard.
        if features.has_arrays {
            if let Some(rescue_cost) = rescue_elapsed {
                if rescue_cost > ARRAY_SCOPED_RESCUE_CAP {
                    return result;
                }
            }
        }

        // Canonical instance-derived order: `combined` in parse order,
        // deduplicated by TermId (hash-consed duplicate assert bodies).
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut full: Vec<TermId> = combined
            .iter()
            .copied()
            .filter(|t| seen.insert(*t))
            .collect();
        if full.len() < 2 {
            return result;
        }
        // Tail-first candidate order (#uc-minimize-policy P3), NON-ARRAY
        // content only: stable-sort the candidates by term node-count
        // ASCENDING, so the deletion scan (which deletes prefix chunks
        // first) tries the tiny asserts before the huge ones. On the QG
        // classes the named set splits into tiny per-pair exclusion asserts
        // and a few huge axiom asserts; when the tiny members are the
        // deletable ones the first chunk adopts immediately (measured qg5
        // gensys_icl001: 77/130 final, deeper than cvc5's 83 minimal), and
        // when they are essential the one-shot order FLIP below rescues the
        // scan. ARRAY content keeps parse order: sorting was measured
        // HARMFUL there (storecomm 231-named: parse-order subset attempts
        // decide in 0.02-0.7s and adopt from attempt 46; sorted-order
        // attempts churn to the 10s cap undecided and the pass never
        // adopts) — every array-policy calibration in this file (probe,
        // churn caps, ladder) was measured in parse order.
        // DETERMINISM: node counts are a pure function of the parsed terms
        // and the sort is stable (parse-order tie-break). ORDER
        // PRESERVATION (verified in this file): every candidate is an
        // order-preserving filter/slice of `full` — the `start` filter
        // below, the chunk-deletion concat of `verified` slices, and the
        // harvest-jump re-canonicalization (`verified.iter().filter(...)`)
        // — so the sorted order propagates to every attempt.
        if !features.has_arrays {
            let mut memo: DetHashMap<TermId, u64> = DetHashMap::default();
            let terms = &self.ctx.terms;
            full.sort_by_key(|t| term_node_count(terms, &mut memo, *t));
        }

        // Starting point: the certified harvest when it is a genuine smaller
        // subset (re-canonicalized into parse order), else the full set. The
        // start set is already solve-verified: by `certify_assumption_core`'s
        // recheck (proper subset), by the rescue's scoped solve
        // (all-assumptions core), or by the original solve (full set).
        let full_set: HashSet<TermId> = full.iter().copied().collect();
        let start: Vec<TermId> = match &self.last_assumption_core {
            Some(core) if !core.is_empty() && core.iter().all(|t| full_set.contains(t)) => {
                let core_set: HashSet<TermId> = core.iter().copied().collect();
                if core_set.len() < full.len() {
                    full.iter()
                        .copied()
                        .filter(|t| core_set.contains(t))
                        .collect()
                } else {
                    full.clone()
                }
            }
            _ => full.clone(),
        };

        // Wall-clock budget policy (see module docs).
        let deadline0 = self.solve_deadline.get();
        let now = Instant::now();
        let remaining = deadline0
            .map(|d| d.saturating_duration_since(now))
            .unwrap_or(NO_DEADLINE_BUDGET);
        if remaining < MIN_REMAINING_TO_SHRINK {
            return result;
        }
        let margin = (remaining / 8).clamp(Duration::from_secs(3), Duration::from_secs(10));
        let shrink_budget = remaining.saturating_sub(margin);
        let Some(shrink_deadline) = now.checked_add(shrink_budget) else {
            return result;
        };
        let slice = std::cmp::max(shrink_budget / 6, Duration::from_secs(1));

        // Saved for byte-identical restore on zero progress.
        let original_core = self.last_assumption_core.clone();
        let original_assumptions = self.last_assumptions.clone();
        // The stripped base, captured once for the scoped engine.
        let base_assertions = self.ctx.assertions.clone();

        let trace = std::env::var_os("AY_PHASE_TRACE").is_some();
        let initial_len = start.len();
        let mut verified = start;
        let mut attempts: u64 = 0;
        let mut adopted = false;
        let mut i: usize = 0;
        let mut chunk: usize = (verified.len() / 4).max(1);
        let mut jump: Option<Vec<TermId>> = None;
        // Per-attempt budget policy state (#uc-minimize-policy P1/P2/ladder).
        let n_named = full.len();
        let rescue4 = rescue_elapsed.unwrap_or(Duration::ZERO).saturating_mul(4);
        let base_array_cap = if n_named >= ARRAY_LADDER_LARGE_NAMED {
            ARRAY_LADDER_LARGE_CAP
        } else if n_named >= ARRAY_LADDER_MEDIUM_NAMED {
            ARRAY_LADDER_MEDIUM_CAP
        } else {
            ATTEMPT_CHURN_CAP
        };
        let mut array_cap = base_array_cap;
        let mut escalated_at_attempt: Option<u64> = None;
        let mut max_adoption_cost = Duration::ZERO;
        let mut order_flipped = false;
        // Zero-adoption wall guard bound (see the ladder constants),
        // derived from the PRE-escalation rung so the bound is fixed for
        // the whole pass.
        let base_post_probe = std::cmp::min(slice, std::cmp::max(base_array_cap, rescue4));
        let zero_adoption_wall_cap = (shrink_budget / ARRAY_HOPELESS_WALL_DIVISOR).clamp(
            base_post_probe.saturating_mul(ARRAY_HOPELESS_WALL_MIN_BUDGETS),
            base_post_probe.saturating_mul(ARRAY_HOPELESS_WALL_MAX_BUDGETS),
        );
        let pass_started = Instant::now();
        // Headroom re-derivation (#uc-minimize-policy P1): never START an
        // attempt without room for 2x the LIVE post-probe attempt cap
        // (attempts are budget-capped by P2/the ladder and the relative
        // fuse bounds real cost at ~2x budget), grown to the costliest
        // attempt actually observed. The old rule reserved a full
        // slice.max(rescue) — measured ~190s of wasted tail per
        // deadline-bound storecomm file at -T:1200 (walls 991±4 = 1195 −
        // margin − unspent headroom). Deadline-dishonoring engines (the qg5
        // overshoot class that motivated the fat reserve) are now caught by
        // the cheap P2 probe + OVERSHOOT_FUSE pass-abort and by this floor
        // tracking the observed maximum; gated: zero lost qg5 answers at
        // -T:60/-T:120. The floor is applied at the top of every iteration
        // (the cap can grow via ladder escalation / adoption-cost scaling).
        let mut headroom = Duration::ZERO;

        loop {
            let loop_now = Instant::now();
            // Ladder escalation / hopeless-abort (#uc-minimize-policy
            // ladder), array content only — see the ARRAY_LADDER_ESCALATION
            // constants for the rationale. `adopted` is read-only here; the
            // abort path is exactly the zero-progress restore below.
            if features.has_arrays && !adopted {
                // Wall guard first: bounded waste even when every attempt
                // churns to a large rung (see the ladder constants).
                if loop_now.saturating_duration_since(pass_started) > zero_adoption_wall_cap {
                    if trace {
                        eprintln!(
                            "c phase-trace uc-minimize fuse=hopeless-wall attempts={attempts}"
                        );
                    }
                    break;
                }
                // Escalation stays COUNT-based (design shape); the hopeless
                // decision is WALL-based only. A count-based hopeless clock
                // was measured killing a healthy pass: parse-order storecomm
                // 231-named fast-fails 45 attempts (0.02-0.7s each, cheap
                // REAL scan progress) before its first adoption at attempt
                // 46 — any attempt-count hopeless threshold small enough to
                // bound churner waste beheads that class.
                if escalated_at_attempt.is_none() && attempts > ARRAY_ESCALATE_AFTER_ATTEMPTS {
                    array_cap = base_array_cap.saturating_mul(ARRAY_LADDER_ESCALATION_FACTOR);
                    escalated_at_attempt = Some(attempts);
                    if trace {
                        eprintln!("c phase-trace uc-minimize ladder=escalate cap={array_cap:?}");
                    }
                }
            }
            // One-shot order flip (#uc-minimize-policy P3, see
            // NON_ARRAY_ORDER_FLIP_AFTER_ATTEMPTS): zero adoptions this
            // deep into an ascending scan means the tiny prefix is
            // essential — reverse once so the deletable large members are
            // tried while budget remains. Safe here: no adoption ever
            // happened, so no jump is pending and `verified` still equals
            // the start set; every later candidate is an order-preserving
            // filter/slice of the REVERSED order, so jump
            // re-canonicalization stays coherent.
            if !features.has_arrays
                && !adopted
                && !order_flipped
                && jump.is_none()
                && attempts >= NON_ARRAY_ORDER_FLIP_AFTER_ATTEMPTS
            {
                verified.reverse();
                i = 0;
                chunk = (verified.len() / 4).max(1);
                order_flipped = true;
                if trace {
                    eprintln!("c phase-trace uc-minimize order=flip attempts={attempts}");
                }
            }
            // P1 headroom floor: 2x the live post-probe cap (recomputed —
            // escalation and adoption-cost scaling can raise the cap
            // mid-pass), never below the costliest observed attempt.
            let post_probe_budget = std::cmp::min(
                slice,
                if features.has_arrays {
                    std::cmp::max(array_cap, rescue4)
                } else {
                    std::cmp::max(ATTEMPT_CHURN_CAP, max_adoption_cost.saturating_mul(4))
                },
            );
            headroom = headroom.max(post_probe_budget.saturating_mul(2));
            if loop_now
                .checked_add(headroom)
                .is_none_or(|h| h > shrink_deadline)
            {
                break;
            }
            // RSS guard: repeated subset re-solves grow the hash-consed term
            // store and solver footprint monotonically (in-process stores
            // never shrink). The competition harness pairs the internal
            // `--memory` limit with an external zero-grace RSS watchdog
            // (SIGKILL — a memout DURING shrinking loses the already-decided
            // answer; measured on QF_AX swap under tight per-child limits).
            // Stop shrinking well before that territory.
            if ay_sys::process_memory_exceeded_at_percent(60) {
                if trace {
                    eprintln!("c phase-trace uc-minimize fuse=memory");
                }
                break;
            }
            let (candidate, was_jump) = match jump.take() {
                Some(j) => (j, true),
                None => {
                    if i >= verified.len() {
                        break; // deletion scan complete
                    }
                    let end = (i + chunk).min(verified.len());
                    let mut c: Vec<TermId> = Vec::with_capacity(verified.len() - (end - i));
                    c.extend_from_slice(&verified[..i]);
                    c.extend_from_slice(&verified[end..]);
                    (c, false)
                }
            };
            if candidate.is_empty() {
                // Never propose the empty set: the print contract has no
                // authenticated-empty representation (an empty pinned core
                // pads back to ALL named assertions — worse than a
                // 1-element core).
                if chunk > 1 {
                    chunk = 1;
                    continue;
                }
                break;
            }
            attempts += 1;
            // Per-solve budget policy (#uc-minimize-policy P2 + ladder):
            // every attempt is capped WELL below the slice so one stuck
            // subset cannot eat the pass. Attempt 1 is a conservative probe
            // for ALL content (see FIRST_PROBE_FLOOR) — a cheap canary for
            // deadline honoring before committing post-probe caps.
            // Post-probe, array content pays up to the size-aware ladder
            // rung (see the ARRAY_LADDER_* constants), non-array content up
            // to 4x the costliest ADOPTION observed (floor
            // ATTEMPT_CHURN_CAP). Unknown-at-cap keeps the deleted members
            // — fail-closed, the same direction as a slice timeout.
            let scaled_floor = if attempts == 1 {
                std::cmp::max(FIRST_PROBE_FLOOR, rescue4)
            } else if features.has_arrays {
                std::cmp::max(array_cap, rescue4)
            } else {
                std::cmp::max(ATTEMPT_CHURN_CAP, max_adoption_cost.saturating_mul(4))
            };
            let attempt_budget = std::cmp::min(slice, scaled_floor);
            let attempt_started = Instant::now();
            let per_solve_deadline = attempt_started
                .checked_add(attempt_budget)
                .map_or(shrink_deadline, |d| d.min(shrink_deadline));
            self.solve_deadline.set(Some(per_solve_deadline));
            // Engine choice, array containment policy
            // (#array-deadline-forward): ARRAY content always takes the
            // scoped plain engine, even for direct-lane verdicts. The
            // assumption lane (`solve_auf_lia_with_assumptions`) re-runs its
            // ITE-lifting / eager-fixpoint preprocessing per attempt through
            // ay-core term rewriting that polls NO deadline (measured: a
            // swap sf subset attempt spent 10+s inside
            // `lift_ite_recursive_with_ctx`, ballooned the term store to
            // 8 GB RSS across 5 attempts, and on storeinv ran past the -T
            // watchdog — losing the already-decided unsat), and its subset
            // attempts churn to the full slice without deciding. The scoped
            // plain route (`solve_array_euf` escalation) is deadline-honoring
            // end-to-end after the ArraySolver deadline forward (measured:
            // 52 storecomm attempts, worst overshoot 0.28s, RSS flat at
            // ~150 MB) and DECIDES these subsets in ~0.1-1s. Contract-
            // identical: `check-sat-assuming A` == `check-sat (base AND A)`,
            // and adoption still requires this fresh solve to return unsat.
            let scoped_engine = rescued || features.has_arrays;
            let sub = if scoped_engine {
                // The scoped engine assumes a fresh per-check state (the
                // rescue runs it exactly once per check, right after the
                // entry reset). Repeating it WITHOUT the reset compounds
                // per-check scratch state across attempts — measured RSS
                // blow-up/hang on QF_AX swap subsets that are trivially
                // cheap in a fresh process. Reset before EVERY attempt.
                self.reset_solve_session_state();
                self.solve_scoped_assumptions(
                    &base_assertions,
                    &candidate,
                    Self::solve_current_assertions_with_quantifier_support,
                )
            } else {
                self.check_sat_assuming(&candidate)
            };
            // Adapt the headroom to the costliest attempt observed; the fuse
            // trips (after result processing — a late unsat is still a valid
            // verification) when the engine grossly ignored its per-solve
            // deadline. Array content keeps its own fuse as a WIDENED
            // backstop (#array-deadline-forward): the old absolute cap
            // (max(1s, 10 x rescue)) existed because the array lanes did not
            // poll the deadline and attempt wall time was the only early
            // predictor of the runaway/RSS-burst class (measured: swap sf
            // memout mid-attempt). With the deadline forwarded into the
            // ArraySolver those lanes now stop near their budget, so the
            // array fuse only needs to catch deadline-DISHONORING attempts.
            // Poll GRANULARITY scales with instance size (a fixed-iteration
            // amortization polls less often in wall time as per-iteration
            // work grows; measured: an 861-named storecomm attempt landed
            // 5.3s past its 10s budget from one long inter-poll stretch,
            // and the flat +2s fuse then aborted a healthy pass), so the
            // array threshold is RELATIVE — 2x the attempt's own budget
            // (floor: the generic allowance) — while non-array content
            // keeps the tight generic overshoot fuse.
            let attempt_ended = Instant::now();
            let attempt_elapsed = attempt_ended.saturating_duration_since(attempt_started);
            let array_attempt_cap = std::cmp::max(
                attempt_budget.saturating_mul(2),
                attempt_budget.saturating_add(OVERSHOOT_FUSE),
            );
            let fuse_tripped = if features.has_arrays {
                attempt_elapsed > array_attempt_cap
            } else {
                attempt_ended.saturating_duration_since(per_solve_deadline) > OVERSHOOT_FUSE
            };
            headroom = headroom.max(attempt_elapsed);
            if matches!(sub, Ok(SolveResult::Unsat(_))) {
                // Adaptive-difficulty signal (#uc-minimize-policy P2): the
                // post-probe non-array cap scales from the costliest
                // ADOPTION — the only attempt class whose cost is known to
                // be productive (churners tell us nothing but the cap).
                max_adoption_cost = max_adoption_cost.max(attempt_elapsed);
            }
            if trace {
                // Per-attempt budget-honoring evidence (#array-deadline-forward
                // gate: no attempt overshoots its slice by more than the
                // overshoot fuse). `result` distinguishes a definitive SAT
                // (the deleted members are jointly essential — scan
                // convergence is REAL) from an Unknown (undecided at cap —
                // possibly a deletable member the engine could not decide;
                // #uc-minimize-policy diagnostic).
                eprintln!(
                    "c phase-trace uc-minimize attempt={attempts} budget={:?} elapsed={:?} unsat={} result={}",
                    attempt_budget,
                    attempt_elapsed,
                    matches!(sub, Ok(SolveResult::Unsat(_))),
                    match &sub {
                        Ok(SolveResult::Unsat(_)) => "unsat",
                        Ok(SolveResult::Sat) => "sat",
                        Ok(SolveResult::Unknown) => "unknown",
                        Err(_) => "error",
                    },
                );
            }
            match sub {
                Ok(SolveResult::Unsat(_)) => {
                    // ADOPT: `candidate` is proven unsat together with the
                    // stripped base by THIS exact solve (fail-closed rule).
                    // Its own SAT-level harvest may nominate a smaller jump
                    // candidate — nominated only, adopted only via its own
                    // solve on the next iteration.
                    let harvest = self.last_assumption_core.take();
                    verified = candidate;
                    adopted = true;
                    if was_jump {
                        i = 0;
                        chunk = (verified.len() / 4).max(1);
                    } else {
                        chunk = chunk.saturating_mul(2);
                    }
                    if let Some(h) = harvest {
                        if !h.is_empty() {
                            let vset: HashSet<TermId> = verified.iter().copied().collect();
                            let hset: HashSet<TermId> = h.iter().copied().collect();
                            if hset.len() < verified.len() && h.iter().all(|t| vset.contains(t)) {
                                jump = Some(
                                    verified
                                        .iter()
                                        .copied()
                                        .filter(|t| hset.contains(t))
                                        .collect(),
                                );
                            }
                        }
                    }
                }
                Ok(_) => {
                    // Sat / Unknown (incl. slice timeout): the candidate is
                    // insufficient or undecided — keep the deleted members.
                    if !was_jump {
                        if chunk > 1 {
                            chunk /= 2;
                        } else {
                            i += 1;
                        }
                    }
                }
                Err(_) => {
                    // A subset solve error is unexpected (the full set solved
                    // cleanly). Abort minimization conservatively; the
                    // pin/restore below still leaves a sound core.
                    break;
                }
            }
            if fuse_tripped {
                if trace {
                    eprintln!(
                        "c phase-trace uc-minimize fuse=overshoot attempt_elapsed={attempt_elapsed:?}"
                    );
                }
                break;
            }
        }
        self.solve_deadline.set(deadline0);

        let final_len = verified.len();
        if adopted {
            // Pin the last solve-verified subset (subsequent failed attempts
            // clobbered the bookkeeping — mirrors the certify gate pinning
            // its certified harvest back). `last_assumptions` follows so the
            // executor state reads as if the verified solve were the last
            // check (its harvest ⊆ verified authenticates downstream).
            self.last_assumption_core = Some(verified);
            self.last_assumptions = Some(full);
            self.last_unknown_reason = None;
        } else {
            // Zero progress: byte-identical core bookkeeping restore.
            self.last_assumption_core = original_core;
            self.last_assumptions = original_assumptions;
        }
        self.last_statistics.set_string(
            "solver.uc_minimize",
            format!("start={initial_len} final={final_len} attempts={attempts}"),
        );
        if trace {
            eprintln!(
                "c phase-trace uc-minimize category={category:?} engine={} start={initial_len} \
                 final={final_len} attempts={attempts} adopted={adopted}",
                if rescued || features.has_arrays {
                    "scoped"
                } else {
                    "assumption"
                },
            );
        }
        result
    }
}

/// Memoized term node-count for the tail-first candidate order
/// (#uc-minimize-policy P3): tree size computed over the hash-consed DAG —
/// each distinct subterm's size is computed once (memo), shared subterms
/// COUNT at every occurrence (saturating add, so deeply shared DAGs
/// saturate instead of overflowing). Deterministic: a pure function of the
/// parsed term structure. Iterative post-order — assert bodies on the axiom
/// classes nest deeply enough that recursion would risk the stack.
fn term_node_count(terms: &TermStore, memo: &mut DetHashMap<TermId, u64>, root: TermId) -> u64 {
    fn children(data: &TermData, out: &mut Vec<TermId>) {
        match data {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args) => out.extend_from_slice(args),
            TermData::Let(bindings, body) => {
                out.extend(bindings.iter().map(|(_, t)| *t));
                out.push(*body);
            }
            TermData::Not(t) => out.push(*t),
            TermData::Ite(c, t, e) => out.extend([*c, *t, *e]),
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                out.push(*body);
                out.extend(triggers.iter().flatten().copied());
            }
            // `TermData` is #[non_exhaustive]; future leaf-or-unknown
            // variants count as size 1 (still deterministic).
            _ => {}
        }
    }
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
    let mut kids: Vec<TermId> = Vec::new();
    while let Some((id, expanded)) = stack.pop() {
        if memo.contains_key(&id) {
            continue;
        }
        kids.clear();
        children(terms.get(id), &mut kids);
        if expanded {
            let mut n: u64 = 1;
            for k in &kids {
                n = n.saturating_add(memo.get(k).copied().unwrap_or(1));
            }
            memo.insert(id, n);
        } else {
            stack.push((id, true));
            for k in &kids {
                if !memo.contains_key(k) {
                    stack.push((*k, false));
                }
            }
        }
    }
    memo.get(&root).copied().unwrap_or(1)
}
