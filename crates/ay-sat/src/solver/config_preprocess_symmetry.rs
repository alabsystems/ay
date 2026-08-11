// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root-only symmetry preprocessing.

use super::mutate::AddResult;
use super::*;
use std::collections::BTreeSet;

const SYMMETRY_MAX_VARS: usize = 4_096;
/// Variable ceiling for the CHEAP aux-free-SR / php-matrix route.
///
/// The companion clause cap below was already split by route, but the variable
/// ceiling stayed shared — the same "detection cliff" one dimension over.
/// `detect_php_aux_free_sr` is a single O(clauses) structural scan whose cost
/// does not depend on the variable count, so the tight IR ceiling excluded the
/// larger PHP/coloring instances for no cost reason: at 4_096 vars the family is
/// covered only to ~n=63, so e.g. a 625x24 coloring instance (15_000 vars,
/// 360_625 clauses) was dropped to plain CDCL with `vars 15000 > cap 4096`
/// despite being exactly the structure this route exists to break.
///
/// Soundness is unaffected by widening it, for the same reason the clause cap
/// could be widened: a mis-detected matrix only yields a proof the native SR
/// checker REJECTS, never a false VERIFIED. The clause cap remains the real
/// cost bound. Override for calibration with `AY_SAT_SYMMETRY_DETECTOR_MAX_VARS`.
const SYMMETRY_DETECTOR_MAX_VARS: usize = 1_000_000;
/// Clause cap for routes that may invoke the EXPENSIVE backtracking automorphism
/// finder (`find_composite_generators` / `ir::find_automorphisms`): the composite,
/// SR-tower, DPR, HHW, and default BreakID routes. The IR finder is node-budget
/// bounded but its per-node refinement is O(clauses), so it is kept tightly capped
/// to ensure huge general instances are never slowed by it.
const SYMMETRY_IR_MAX_CLAUSES: usize = 20_000;
/// Clause cap for the CHEAP aux-free-SR / php-matrix route
/// (`detect_php_aux_free_sr`), a single O(clauses) structural scan whose emitted
/// SR units are gated by the native SR checker (the proof is the gate, not the
/// detector). It is sub-millisecond even at n=60 (~110k clauses), so it gets a
/// much larger clause budget than the IR finder; combined with the 4_096 var
/// ceiling this covers the PHP/coloring family up to ~n=63. Before this split the
/// shared 20_000-clause cap silently dropped php_50 (63_801 clauses) to plain CDCL
/// (master-plan G7 "detection cliff"). Soundness is unaffected: a mis-detected
/// matrix only yields a proof the SR checker REJECTS, never a false VERIFIED.
///
/// Raised from 200_000 after it was measured excluding real targets: two of the
/// six official `chnl` instances sit just past it (`chnl-020x101` at 202_202
/// clauses, `chnl-030x091` at 245_882) and were dropped to plain CDCL, where
/// they time out, while the four below the cap solve in 67-1337 ms. Since the
/// route is one linear scan and the proof is the gate, the cap buys nothing at
/// this size. Override with `AY_SAT_SYMMETRY_DETECTOR_MAX_CLAUSES`.
const SYMMETRY_DETECTOR_MAX_CLAUSES: usize = 1_000_000;
/// Size guard for the SIGNED IR search. The search itself is node-budgeted, but
/// building the colored graph and the clause multiset is linear in the formula,
/// so huge instances are kept out until the route earns a default-on.
const SIGNED_SYMMETRY_MAX_VARS: usize = 200_000;
const SIGNED_SYMMETRY_MAX_CLAUSES: usize = 1_000_000;
const SYMMETRY_MAX_PAIRS: usize = 128;
const SYMMETRY_MAX_GROUP_SIZE: usize = 64;
/// Size bound for the orbitope route, which runs BEFORE the caps above and so
/// needs its own. Set far above every instance the route targets (largest:
/// `exam_75_65` at 336_450 clauses, `chnl-030x091` at 245_882) while keeping the
/// corpus's 18 M-clause instances out. See the measurement at the call site.
const ORBITOPE_MAX_CLAUSES: usize = 2_000_000;
const ORBITOPE_MAX_VARS: usize = 1_000_000;

impl Solver {
    /// Detect variable symmetries via BreakID-style iterative refinement and
    /// emit lex-leader SBP clauses for each orbit.
    ///
    /// Returns `(unsat, changed)`.
    #[cfg(test)]
    pub(super) fn preprocess_symmetry(&mut self) -> (bool, bool) {
        self.preprocess_symmetry_interruptible(&|| false)
    }

    /// Callback-aware symmetry preprocessing used by the initial-preprocess
    /// transaction. Cancellation is sampled at read-only phase boundaries and
    /// during candidate-swap verification; no partial set of SBPs is installed.
    pub(super) fn preprocess_symmetry_interruptible<F>(&mut self, should_stop: &F) -> (bool, bool)
    where
        F: Fn() -> bool + ?Sized,
    {
        self.cold.symmetry_stats.begin_run();
        if self.preprocessing_should_stop(should_stop) {
            return (false, false);
        }
        if std::env::var_os("AY_SAT_SYMMETRY_TRACE").is_some() {
            safe_eprintln!(
                "c symmetry-trace: entered: enabled={} oneshot={} incremental={} proof_manager={} lrat={} clause_trace={} vars={} clauses={}",
                self.cold.symmetry_enabled,
                self.cold.symmetry_oneshot,
                self.cold.has_been_incremental,
                self.proof_manager.is_some(),
                self.cold.lrat_enabled,
                self.cold.clause_trace.is_some(),
                self.num_vars,
                self.arena.active_clause_count(),
            );
        }

        // #17: AY_SAT_COMPOSITE_SYMMETRY enables the (default-off, no-proof-only)
        // composite-permutation symmetry path even when the profile leaves
        // symmetry off — for the clique/coloring/PHP family that the single-swap
        // detector cannot break. Cached per process (each run is a fresh process).
        let composite_symmetry = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_COMPOSITE_SYMMETRY").is_some())
        };
        if self.cold.has_been_incremental {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Incremental);
            return (false, false);
        }

        // Orbitope route (SAT-COMP 2026): structure-first row-interchangeable
        // at-most-one matrix detection plus orbitopal unit fixing — the
        // technique the 2026 Main Track winner (satsuma+Kissat) beat plain
        // Kissat with. It runs BEFORE the var/clause caps below because those
        // caps exist for the backtracking IR finder; detection here is one
        // linear scan plus one clause-multiset pass per verified row swap, so
        // it is affordable on full-size industrial instances.
        //
        // It also runs BEFORE the `symmetry_enabled` gate below, which is what
        // `cold.symmetry_enabled` would otherwise deny it: that flag defaults
        // false and the only re-enable (`adaptive.rs`) is guarded by
        // `num_vars < 4096`, while every instance this route targets is larger
        // (exam is 4875-7200 vars). The gate is about the cost of the
        // backtracking IR finder, which this route does not use.
        //
        // The emitted units are satisfiability-preserving but not RUP. They are
        // no longer confined to non-proof runs: under a proof surface the route
        // emits each unit as a DSR `a`-line carrying the row-swap σ-witness
        // (`RowAmoMatrix::sr_steps`), externally verified with `dsr-trim`.
        //
        // Default ON with an explicit `AY_SAT_ORBITOPE=0` opt-out. Previously
        // opt-in via a variable nothing set, so the route never ran outside a
        // hand-written command line.
        let orbitope_route = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| {
                std::env::var("AY_SAT_ORBITOPE").map_or(true, |v| v != "0" && v != "false")
            })
        };
        // Structural routes remove models, so they are valid only for a
        // one-shot solve. `has_been_incremental` is NOT sufficient: it is false
        // during the first solve, which is exactly when the units are added.
        //
        // Size bound: detection is linear in the formula but not free — measured
        // +6.7 s of preprocessing on `satcoin-genesis-UNSAT-7200` (7720 ms vs
        // 1046 ms with the route off), while it is at or below noise on every
        // other instance sampled. Because this route deliberately runs BEFORE the
        // caps further down, without a bound of its own the cost is unbounded on
        // the corpus's 1.7 GB / 18 M-clause instances. The cap is set well above
        // every target: the largest in the family is `exam_75_65` at 336 450
        // clauses and `chnl-030x091` at 245 882.
        let orbitope_fits = self.arena.active_clause_count() <= ORBITOPE_MAX_CLAUSES
            && self.num_vars <= ORBITOPE_MAX_VARS;
        if orbitope_route
            && self.cold.symmetry_oneshot
            && self.cold.symmetry_stats.runs == 1
            && orbitope_fits
        {
            let before = self.cold.symmetry_stats.sb_clauses_added;
            let (unsat, changed) = self.preprocess_symmetry_orbitope();
            let added = self.cold.symmetry_stats.sb_clauses_added - before;
            self.cold.symmetry_stats.record_route(
                "orbitope",
                if unsat {
                    "derived UNSAT".to_string()
                } else if changed {
                    format!("added {added} clauses")
                } else {
                    "ran, found nothing".to_string()
                },
            );
            if unsat || changed {
                return (unsat, changed);
            }
        } else if orbitope_route && self.cold.symmetry_oneshot && !orbitope_fits {
            // Never drop a route silently (master-plan G7).
            safe_eprintln!(
                "c symmetry: skipped (orbitope size): vars {} cap {ORBITOPE_MAX_VARS}, clauses {} cap {ORBITOPE_MAX_CLAUSES}",
                self.num_vars,
                self.arena.active_clause_count(),
            );
        }

        // The aux-free SR route is certifiable and cheap (one O(clauses)
        // structural scan), so like the orbitope route it must not be denied by
        // `symmetry_enabled` — a flag that defaults false and only re-enables
        // below 4096 vars, while the PHP family it targets is far larger.
        let sr_auxfree_enabled = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| {
                std::env::var("AY_SAT_SYMMETRY_SR_AUXFREE")
                    .map_or(true, |v| v != "0" && v != "false")
            })
        };
        let sr_auxfree_enabled = sr_auxfree_enabled && self.cold.symmetry_oneshot;
        // The signed route's flag is read further down, AFTER this gate, so
        // `AY_SAT_SIGNED_SYMMETRY=1` alone never reached it: `symmetry_enabled`
        // defaults false and its only re-enable (`adaptive.rs`) is guarded by
        // `num_vars < 4096`. Verified 2026-08-10 on a 139 160-variable instance:
        // with the flag set, the trace still reports `enabled=false` and
        // `symmetry_sb_cls: 0`.
        //
        // That is not merely a dead switch — it invalidated a recorded verdict.
        // The full-400 A/B that REJECTED signed symmetry (-3 solved) measured a
        // technique that was inert on every instance above 4096 variables, i.e.
        // on most of the corpus. Re-judge that decision now the route can run.
        let signed_enabled = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_SIGNED_SYMMETRY").is_some())
        };
        // Signed lex leaders remove models just like every other structural
        // symmetry route. An environment flag must not silently opt an
        // embedder or assumption solver into that one-shot-only transform.
        let signed_route = signed_enabled && self.cold.symmetry_oneshot;
        if !self.cold.symmetry_enabled
            && !composite_symmetry
            && !sr_auxfree_enabled
            && !signed_route
        {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Disabled);
            return (false, false);
        }

        // Signed-symmetry route: the same IR search AY already ships, but over
        // literal permutations that may flip polarity — the projection that
        // survives competition polarity shuffling. Like the orbitope units, the
        // emitted lex-leader clauses are satisfiability-preserving rather than
        // RUP, so they stay off any proof surface for now.
        // `AY_SAT_SIGNED_SYMMETRY_SR` promotes the route to a certificate-bearing
        // one: each lex-leader clause is written as a DSR `a`-line witnessed by
        // the signed automorphism σ, verified externally by
        // `dsr-trim → drat/lsr → cake_lpr` (a 2026-legal Main Track checker
        // pipeline). Same proof-surface preconditions as the existing DPR/SR
        // symmetry routes: a DRAT proof manager, no LRAT, no clause trace.
        let signed_sr = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_SIGNED_SYMMETRY_SR").is_some())
        } && self.proof_manager.is_some()
            && !self.cold.lrat_enabled
            && self.cold.clause_trace.is_none()
            && crate::proof_capability::symmetry_pr_proof_allowed(
                crate::proof_capability::ProofMode::Drat,
            );
        if signed_route
            && self.cold.symmetry_stats.runs == 1
            && (!self.symmetry_proof_surface_active() || signed_sr)
            && self.num_vars <= SIGNED_SYMMETRY_MAX_VARS
            && self.arena.active_clause_count() <= SIGNED_SYMMETRY_MAX_CLAUSES
        {
            let before = self.cold.symmetry_stats.sb_clauses_added;
            let (unsat, changed) = self.preprocess_symmetry_signed(signed_sr);
            let added = self.cold.symmetry_stats.sb_clauses_added - before;
            self.cold.symmetry_stats.record_route(
                "signed",
                if unsat {
                    "derived UNSAT".to_string()
                } else if changed {
                    format!("added {added} clauses")
                } else {
                    "ran, found nothing".to_string()
                },
            );
            if unsat || changed {
                return (unsat, changed);
            }
        }
        // Proof mode: SBP clauses are RAT w.r.t. the symmetry pivot, but
        // the RAT check can fail when other proof steps (equivalence binaries
        // from congruence) modify the clause set before the checker reaches
        // the SBP addition. CaDiCaL does not have symmetry breaking, so
        // there is no reference for DRAT-compatible SBP emission. Disable
        // symmetry in ALL proof/reconstruction modes (DRAT, LRAT, clause trace)
        // until SBP additions have checker-consumable proof witnesses (#8011).
        //
        // #8011 finding (DO NOT naively lift this for DRAT): the per-generator
        // lex-leader clause `(x_v ∨ ¬x_w)` is satisfiability-preserving but is
        // NOT a RAT addition. It is propagation-redundant (PR) with the symmetry
        // permutation as the witnessing assignment, and the reference DRAT
        // checker (`ay check drat`, RUP+RAT only, no PR) rejects it at the FIRST
        // SBP `a`-line: the RAT resolvents (e.g. with the at-most-one binary
        // `(¬x_v ∨ ¬x_w)` and the at-least-one clause) reduce to non-unit-
        // implied clauses such as `(¬x_w)`. Verified empirically for both
        // polarities, single- and multi-generator, via the ignored harness
        // `symmetry::detector::tests::probe_sbp_drat_rat`. Emitting these as
        // plain DRAT adds therefore yields a proof the checker REJECTS, which is
        // strictly worse than skipping symmetry. A valid DRAT proof needs the
        // Heule-Hunt-Wetzler (2015) image-and-chain derivation per generator
        // (and even then composes only across a symmetry tower, not an arbitrary
        // 96-generator set), or a PR/SR-capable checker.
        // #8011 step 5: the DPR PR route unclamps symmetry on a *plain DRAT*
        // proof surface ONLY. The composite path emits the aux-free `j=0`
        // per-generator lex-leader binaries as DPR `a`-lines (σ-image witness),
        // which the external dpr-trim→cake_lpr loop verifies — AY's internal
        // RUP/RAT checker cannot, hence the registry keeps Symmetry clamped and
        // this is the single sanctioned exception. Requires: composite path on, a
        // DRAT proof manager attached, and NEITHER LRAT nor a clause-trace surface
        // active (PR is not wired for those). When this holds we skip the blanket
        // proof-surface clamp below and take the PR-emitting branch later.
        // #8011 SR route: AY_SAT_SYMMETRY_SR promotes the DPR PR route to a FULL
        // SR (substitution-redundancy) route. Instead of emitting only the aux-free
        // `j=0` binary as DPR and dropping the tower, it emits the WHOLE lex tower
        // (every `j>0` clause + Tseitin defs) as DSR `a`-lines, each with the full
        // automorphism substitution σ as witness. σ remaps the current formula
        // (including prior SBP) onto itself, so the per-generator towers compose.
        // External verification: emitted .sr → dsr-trim → .drat/.lsr → drat-trim →
        // .lrat → cake_lpr. Same proof-surface preconditions as the DPR route.
        let sr_route = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_SYMMETRY_SR").is_some())
        };
        // #8011 AUX-FREE SR route: AY_SAT_SYMMETRY_SR_AUXFREE replaces the
        // lex-leader SR tower (which carries equal-prefix aux `e_j` whose Tseitin
        // clauses dsr-trim rejects under a σ-only witness) with a COMPLETE aux-free
        // SR refutation over the original variables only, for the pigeonhole family
        // — a faithful port of `third_party/dsr-trim/php/php-sr.c`. It out-solves:
        // the emitted units make root propagation derive the empty clause.
        //
        // Default ON with an `AY_SAT_SYMMETRY_SR_AUXFREE=0` opt-out. Unlike the
        // lex-leader routes this one is externally checkable, so there is no
        // reason to keep it behind a variable nothing sets.
        let sr_auxfree_route = sr_auxfree_enabled;
        // HHW route (T2): AY_SAT_SYMMETRY_HHW emits, per gate-verified generator,
        // a Heule-Hunt-Wetzler (CADE 2015 §5) image-and-chain DRAT fragment + the
        // leading lex-leader symmetry clause as PLAIN DRAT (RUP/RAT additions +
        // deletions). Unlike the DPR/SR routes (witnessed `a`-lines checked
        // externally), every HHW step is verifiable by AY's OWN native
        // RUP/RAT DRAT checker (`ay check drat` / `--verify-proof`) — zero
        // external dependencies. Same proof-surface preconditions as the DPR
        // route (DRAT proof manager attached, no LRAT/clause-trace surface).
        let hhw_route_enabled = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_SYMMETRY_HHW").is_some())
        };
        // A DRAT proof surface that can carry witnessed `a`-lines.
        let witnessed_drat_ok = self.proof_manager.is_some()
            && !self.cold.lrat_enabled
            && self.cold.clause_trace.is_none()
            && crate::proof_capability::symmetry_pr_proof_allowed(
                crate::proof_capability::ProofMode::Drat,
            );
        let dpr_pr_route = composite_symmetry && witnessed_drat_ok;
        // The aux-free SR route does NOT ride on `composite_symmetry`. It was
        // chained to it only because it shared `dpr_pr_route`'s preconditions,
        // which made a certifiable route depend on an uncertifiable one's flag —
        // and since that flag now refuses to run under an unchecked proof, the
        // chaining actively blocked the good route. Its real requirement is
        // just: if a proof is being written, it must be a surface that accepts
        // witnessed additions. With no proof at all the units are still sound
        // (they are a complete refutation over the original variables), so the
        // route runs and the emission calls are no-ops.
        let sr_auxfree_supported = !self.symmetry_proof_surface_active() || witnessed_drat_ok;
        // AY_SAT_COMPOSITE_SYMMETRY is documented no-proof-only: the lex-leader
        // clauses it adds are NOT accompanied by checkable proof steps. Combining
        // it with proof emission therefore yields an UNSAT whose certificate a
        // real checker rejects. Measured on SAT-COMP 2026 cb2e8b7f and 965ca988:
        // both `s UNSATISFIABLE`, both rejected by dpr-trim AND by the SR-capable
        // dsr-trim ("No UP contradiction for RAT clause 1631" / "... 277"); both
        // are `s UNKNOWN` without the flag, i.e. solvable ONLY by the uncertified
        // route.
        //
        // The post-solve `--verify-proof` re-check catches this and fails closed
        // ("SOUNDNESS FAILURE ... rejected by internal checker", exit 1) — but
        // `--competition` turns that re-check OFF, and competition mode is exactly
        // how a submission is produced. Without this warning that configuration
        // writes an unverifiable certificate and reports success in silence, which
        // is a disqualified submission rather than a visible failure.
        //
        // Warn rather than refuse: declining here would change the meaning of an
        // existing documented flag. The verdict itself is unaffected.
        // Deliberately keyed on the CONFIGURATION (flag + proof surface), not on
        // which route is selected: the rejected certificates came from runs where
        // symmetry RAN and emitted uncheckable steps, while other instances skip
        // it and merely lose the answer. Both are cases the user needs to see.
        if composite_symmetry && self.symmetry_proof_surface_active() {
            use std::sync::Once;
            static WARNED: Once = Once::new();
            WARNED.call_once(|| {
                safe_eprintln!(
                    "c Warning: AY_SAT_COMPOSITE_SYMMETRY is active WITH proof emission. \
                     Composite symmetry breaking is no-proof-only, so any UNSAT it produces \
                     may carry a certificate that an external checker REJECTS. Re-run without \
                     --competition to let the internal proof re-check gate the result, or \
                     unset AY_SAT_COMPOSITE_SYMMETRY for a certifiable run."
                );
            });
        }
        // The HHW route shares the DPR route's proof-surface preconditions; it is
        // additionally gated by its own env flag and the composite path.
        let hhw_route = hhw_route_enabled && composite_symmetry && dpr_pr_route;
        let sr_route = sr_route && dpr_pr_route;
        let sr_auxfree_route = sr_auxfree_route && sr_auxfree_supported;
        if self.symmetry_proof_surface_active() && !dpr_pr_route && !hhw_route && !sr_auxfree_route
        {
            // Same G7 rule as the size guard below: never drop to plain CDCL
            // without a trace. This skip used to be SILENT, which made a
            // proof-mode run look like a plain search timeout — the instance
            // simply reported UNKNOWN with no indication that symmetry breaking,
            // the only technique that can crack it, had been switched off.
            // Name the failing precondition so the cause is one line, not an
            // afternoon of bisecting env flags.
            safe_eprintln!(
                "c symmetry: skipped (proof surface active): composite={} proof_manager={} lrat={} clause_trace={} pr_allowed={} -> dpr_pr_route={dpr_pr_route} hhw_route={hhw_route}",
                composite_symmetry,
                self.proof_manager.is_some(),
                self.cold.lrat_enabled,
                self.cold.clause_trace.is_some(),
                crate::proof_capability::symmetry_pr_proof_allowed(
                    crate::proof_capability::ProofMode::Drat
                ),
            );
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::ProofMode);
            return (false, false);
        }
        // Route-aware size guard. The aux-free-SR route is a single O(clauses)
        // structural scan and gets the large detector cap; every other route may
        // reach the expensive backtracking IR finder and keeps the tight IR cap.
        // ALWAYS emit a diagnostic on a size skip — never drop to plain CDCL
        // silently (master-plan G7: php_50 used to vanish into CDCL with no trace).
        let clause_cap = if sr_auxfree_route {
            use std::sync::OnceLock;
            static C: OnceLock<usize> = OnceLock::new();
            *C.get_or_init(|| {
                std::env::var("AY_SAT_SYMMETRY_DETECTOR_MAX_CLAUSES")
                    .ok()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(SYMMETRY_DETECTOR_MAX_CLAUSES)
            })
        } else {
            SYMMETRY_IR_MAX_CLAUSES
        };
        let var_cap = if sr_auxfree_route {
            use std::sync::OnceLock;
            static V: OnceLock<usize> = OnceLock::new();
            *V.get_or_init(|| {
                std::env::var("AY_SAT_SYMMETRY_DETECTOR_MAX_VARS")
                    .ok()
                    .and_then(|v| v.parse::<usize>().ok())
                    .unwrap_or(SYMMETRY_DETECTOR_MAX_VARS)
            })
        } else {
            SYMMETRY_MAX_VARS
        };
        let num_vars = self.num_vars;
        let active_clauses = self.arena.active_clause_count();
        if num_vars > var_cap || active_clauses > clause_cap {
            let route = if sr_auxfree_route {
                "aux-free-SR"
            } else {
                "IR"
            };
            if num_vars > var_cap {
                safe_eprintln!(
                    "c symmetry: skipped ({route} route): vars {num_vars} > cap {var_cap}"
                );
            } else {
                safe_eprintln!(
                    "c symmetry: skipped ({route} route): clauses {active_clauses} > cap {clause_cap}"
                );
            }
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::TooLarge);
            return (false, false);
        }

        let clauses = self.snapshot_root_irredundant_clauses_for_symmetry();
        if self.preprocessing_should_stop(should_stop) {
            return (false, false);
        }
        if clauses.len() < 2 {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoActiveClauses);
            return (false, false);
        }

        // Snapshot the user-visible variable count. The composite path may
        // allocate fresh internal aux (equal-prefix) variables for the row
        // lex-leader; those are existentially Tseitin-defined and must NOT leak
        // into the reported model. `num_vars` stays bumped so the solver handles
        // them during search; `user_num_vars` is restored before returning so the
        // emitted v-line is truncated to the original variables (#17 aux-leak fix).
        let user_num_vars_before = self.user_num_vars;

        // BreakID pipeline: refinement → swap verification → orbit extraction → SBP
        let detector = crate::symmetry::detector::SymmetryDetector::new(
            SYMMETRY_MAX_PAIRS,
            SYMMETRY_MAX_GROUP_SIZE,
        );

        // HHW route (T2): per gate-verified generator, emit the Heule-Hunt-Wetzler
        // image-and-chain DRAT fragment + leading lex clause as PLAIN DRAT, then
        // let the residual solve refute and the proof terminate with the empty
        // clause. The native `ay check drat` / `--verify-proof` checker is the
        // trust anchor (no external deps).
        if hhw_route {
            let changed = self.preprocess_symmetry_hhw(&clauses);
            // Aux vars (s_i, x'_i) are solver-internal: restore the user-visible
            // var count so they never appear in a reported model (#17 aux-leak).
            self.user_num_vars = user_num_vars_before;
            return (false, changed);
        }

        // #8011 DPR PR route: emit ONLY the aux-free `j=0` per-generator
        // lex-leader binaries, each as a DPR `a`-line with its σ-image witness.
        // The aux tower (`j>0` + Tseitin defs) is dropped — it is not single-σ-PR
        // — so NO aux variables are allocated and the breaking is binary-only.
        // External verification: emitted .dpr → dpr-trim → .lpr → cake_lpr.
        // #8011 SR route: emit the FULL lex tower as DSR a-lines with σ witnesses
        // and KEEP the aux tower (allocate the fresh equal-prefix vars). Each clause
        // is verified by the external dsr-trim → ... → cake_lpr chain.
        // #8011 AUX-FREE SR route (php-sr.c port). Emit a COMPLETE refutation as
        // DSR `a`-lines over the ORIGINAL variables only — no equal-prefix aux, no
        // lex tower. Each unit is added on the trusted route (verified externally
        // by dsr-trim, not by the internal RUP checker); the accumulated units make
        // root propagation derive the empty clause (which the solver emits as the
        // final `0`). Only fires for the pigeonhole family; otherwise it is a no-op
        // and the solver proceeds with symmetry off (still sound).
        if sr_auxfree_route {
            let auxfree_steps = crate::symmetry::detector::detect_php_aux_free_sr(&clauses);
            self.cold.symmetry_stats.record_route(
                "auxfree-sr",
                match &auxfree_steps {
                    Some(v) => format!("php matrix, {} steps", v.len()),
                    None => "ran, no php matrix".to_string(),
                },
            );
            if let Some(steps) = auxfree_steps {
                let mut changed = false;
                for lc in steps {
                    let crate::symmetry::detector::LexClause::Sr { clause, witness } = lc else {
                        continue;
                    };
                    // Emit the DSR a-line first (records the addition), then add the
                    // unit on the trusted route.
                    if self.proof_emit_add_sr(&clause, &witness).is_err() {
                        break;
                    }
                    let mut lits = clause;
                    match self.add_clause_watched_trusted(&mut lits) {
                        AddResult::Added(_) | AddResult::Unit(_) => {
                            changed = true;
                            self.cold.symmetry_stats.sb_clauses_added =
                                self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                        }
                        // A unit that is immediately falsified at root closes the
                        // proof directly (the solver records the empty clause).
                        AddResult::Empty => return (true, true),
                    }
                }
                // No aux variables were allocated (aux-free); the user-visible var
                // count is unchanged. The empty clause is derived by the root
                // propagation that follows preprocessing.
                return (false, changed);
            }
            // Not a pigeonhole instance. Fall through to the remaining routes
            // rather than returning.
            //
            // This used to `return (false, false)`, which was harmless while the
            // route was opt-in behind a variable nothing set: whoever set it
            // wanted only the PHP route. Now that it is default-on, returning
            // here would make a failed PHP *detection* silently disable ALL
            // symmetry breaking on every non-PHP instance — turning a route
            // meant to add 8 instances into a global regression. Caught by
            // `test_preprocess_symmetry_adds_binary_order_clause_for_swap_pair`,
            // whose 3-variable formula is not a pigeonhole.
            //
            // Falling through is only safe because the routes below re-check
            // the proof surface for themselves; `sr_auxfree_route` widened the
            // proof-surface gate above, so a proof-mode run that reaches here
            // must not be allowed into a route that cannot certify.
            if self.symmetry_proof_surface_active() && !dpr_pr_route && !hhw_route {
                self.cold
                    .symmetry_stats
                    .skip(crate::symmetry::SymmetrySkipReason::ProofMode);
                return (false, false);
            }
        }

        if sr_route {
            let fresh_base = self.num_vars as u32;
            let (tagged, aux) = detector.detect_and_encode_composite_sr(&clauses, fresh_base);
            if aux > 0 {
                self.ensure_num_vars(fresh_base as usize + aux as usize);
            }
            let existing_clause_counts = crate::symmetry::build_formula_counts(&clauses);
            let mut seen: BTreeSet<Vec<u32>> = BTreeSet::new();
            let mut changed = false;
            for lc in tagged {
                let crate::symmetry::detector::LexClause::Sr { clause, witness } = lc else {
                    continue;
                };
                let key = crate::symmetry::canonical_clause_key(&clause);
                if existing_clause_counts.contains_key(&key) || !seen.insert(key) {
                    continue;
                }
                // Emit the DSR a-line FIRST (records the addition), then add the
                // clause on the trusted route (verified externally, not by the
                // internal RUP checker).
                if self.proof_emit_add_sr(&clause, &witness).is_err() {
                    break;
                }
                let mut lits = clause;
                match self.add_clause_watched_trusted(&mut lits) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        changed = true;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
            // Aux vars stay internal-only: restore the user-visible var count.
            self.user_num_vars = user_num_vars_before;
            return (false, changed);
        }

        if dpr_pr_route {
            let fresh_base = self.num_vars as u32;
            let (tagged, _aux) =
                detector.detect_and_encode_composite_with_witness(&clauses, fresh_base);
            // Keep only the PR (j=0 binary) clauses; drop every Aux clause.
            let existing_clause_counts = crate::symmetry::build_formula_counts(&clauses);
            let mut seen: BTreeSet<Vec<u32>> = BTreeSet::new();
            let mut changed = false;
            for lc in tagged {
                let crate::symmetry::detector::LexClause::Pr { clause, witness } = lc else {
                    continue;
                };
                // Dedup against the formula and previously emitted PR binaries.
                let key = crate::symmetry::canonical_clause_key(&clause);
                if existing_clause_counts.contains_key(&key) || !seen.insert(key) {
                    continue;
                }
                // Emit the DPR a-line FIRST (so the proof records the addition),
                // then add the clause to the DB on the trusted route (the PR
                // clause is verified externally, not by the internal RUP checker).
                if self.proof_emit_add_pr(&clause, &witness).is_err() {
                    // Proof I/O failure: stop emitting symmetry; an incomplete
                    // proof must not be trusted. Leave already-added clauses —
                    // they are sound, and finalization checks the I/O-error flag.
                    break;
                }
                let mut lits = clause;
                match self.add_clause_watched_trusted(&mut lits) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        changed = true;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
            // Binary-only: no aux vars allocated, so user_num_vars is unchanged.
            return (false, changed);
        }

        let sbp_clauses = if composite_symmetry {
            // #17 composite path: SOUND BY CONSTRUCTION — gate-verified composite
            // automorphisms, GROUP-level row-interchangeability lex-leader (with
            // fresh equal-prefix aux vars), disjoint-support composition, proven
            // per-involution SBP fallback. Still proof-clamped above (no proof
            // witnesses yet, #8011). Aux variables are allocated from the current
            // var count and must exist before the clauses are added.
            let fresh_base = self.num_vars as u32;
            let (cls, aux) = detector.detect_and_encode_composite(&clauses, fresh_base);
            if aux > 0 {
                self.ensure_num_vars(fresh_base as usize + aux as usize);
            }
            cls
        } else {
            let Some((sbp, det_stats)) = detector.detect_and_encode_interruptible(&clauses, || {
                self.preprocessing_should_stop(should_stop)
            }) else {
                // Detection is read-only until it returns clauses. Discarding
                // partial detector state therefore leaves the formula intact.
                // A local preprocessing deadline is a normal phase truncation;
                // a whole-solve stop is classified by the outer transaction.
                self.user_num_vars = user_num_vars_before;
                return (false, false);
            };
            // Propagate detector stats into symmetry stats.
            self.cold.symmetry_stats.candidate_pairs = self
                .cold
                .symmetry_stats
                .candidate_pairs
                .saturating_add(det_stats.candidate_pairs);
            self.cold.symmetry_stats.pairs_detected = self
                .cold
                .symmetry_stats
                .pairs_detected
                .saturating_add(det_stats.pairs_detected);
            self.cold.symmetry_stats.groups_nontrivial = self
                .cold
                .symmetry_stats
                .groups_nontrivial
                .saturating_add(det_stats.groups_nontrivial);
            self.cold.symmetry_stats.groups_over_budget = self
                .cold
                .symmetry_stats
                .groups_over_budget
                .saturating_add(det_stats.groups_over_budget);
            self.cold.symmetry_stats.largest_group = self
                .cold
                .symmetry_stats
                .largest_group
                .max(det_stats.largest_group);
            sbp
        };

        if sbp_clauses.is_empty() {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return (false, false);
        }

        // Do not begin the mutating SBP installation phase after a stop. Once
        // installation starts it runs atomically so cancellation cannot expose
        // a partial set of symmetry breakers.
        if self.preprocessing_should_stop(should_stop) {
            self.user_num_vars = user_num_vars_before;
            return (false, false);
        }

        // Deduplicate SBP clauses against existing formula.
        let existing_clause_counts = crate::symmetry::build_formula_counts(&clauses);
        let unique_sbps = crate::symmetry::detector::deduplicate_sbp_clauses(
            sbp_clauses,
            &existing_clause_counts,
        );

        let mut changed = false;
        for sbp in unique_sbps {
            let mut clause = sbp;
            debug_assert!(
                !self.symmetry_proof_surface_active(),
                "BUG: symmetry SBP reached a proof/reconstruction surface without \
                 a checker-consumable witness"
            );
            match self.add_clause_watched(&mut clause) {
                AddResult::Added(_) | AddResult::Unit(_) => {
                    changed = true;
                    self.cold.symmetry_stats.sb_clauses_added =
                        self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                }
                AddResult::Empty => return (true, true),
            }
        }

        // Keep any composite-path aux variables internal-only: restore the
        // user-visible var count so they are excluded from the reported model
        // (a no-op when no aux were allocated). #17 aux-leak fix. NOTE: a later
        // ensure_num_vars call elsewhere could re-widen user_num_vars; the full
        // fix (a frozen-internal-var marker) is tracked before any default-on.
        self.user_num_vars = user_num_vars_before;
        (false, changed)
    }

    /// Signed-symmetry route: find automorphisms that may FLIP polarities and
    /// break them with one lex-leader binary per generator.
    ///
    /// Returns `(unsat, changed)`.
    ///
    /// # Why signed
    ///
    /// Every other symmetry path in AY searches sign-preserving variable
    /// permutations. Competition benchmarks are polarity-shuffled, which turns
    /// variable symmetry into signed symmetry, so those paths find nothing.
    /// Measured on `homer11.shuffled` (SAT-COMP 2026 Main): 1-WL refinement with
    /// AY's polarity-split colours discretizes to 440 singleton literal classes
    /// (zero candidate pairs, `symmetry_skip: no-pairs`), while the same
    /// refinement without the split stops at 2 classes of 220 literals. satsuma
    /// reports 8 generators on the same instance.
    ///
    /// # Why the emitted clause is sound
    ///
    /// For a verified automorphism σ, let `v` be the smallest variable σ moves
    /// and compare assignments lexicographically by variable id with `true`
    /// above `false`. Every orbit's lex-greatest model α satisfies
    /// `α ≥ ασ`, hence the first-position consequence `x_v ≥ σ(x_v)`, i.e. the
    /// clause `(x_v ∨ ¬σ(x_v))`. Adding it for any subset of the group therefore
    /// keeps at least one model per orbit. When σ flips `v` itself the clause
    /// degenerates to the unit `x_v` — the classic "you may assume `v` is true
    /// when flipping it is a symmetry".
    fn preprocess_symmetry_signed(&mut self, sr_proof: bool) -> (bool, bool) {
        let clauses = self.snapshot_root_irredundant_clauses_for_symmetry();
        if clauses.len() < 2 {
            return (false, false);
        }
        let node_budget: u64 = std::env::var("AY_SAT_IR_NODE_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8_000);
        let max_gens: usize = std::env::var("AY_SAT_IR_MAX_GENERATORS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(96);
        let formula_counts = crate::symmetry::build_formula_counts(&clauses);
        let generators = crate::symmetry::ir::find_signed_automorphisms(
            &clauses,
            &formula_counts,
            node_budget,
            max_gens,
        );
        if generators.is_empty() {
            // Record that the search RAN and found nothing. Returning silently
            // here is indistinguishable in `--stats` from the route never
            // executing, which is exactly how this route stayed inert while a
            // full-400 A/B "rejected" it.
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoGenerators);
            return (false, false);
        }
        // Substantiality gate. Adding symmetry-breaking clauses perturbs the
        // search trajectory, so an *incidental* symmetry can cost more than it
        // saves: measured on the SAT-COMP 2026 set, `ntil-90d-34` (one
        // generator) went from a 30.5 s solve to a 60 s timeout, while
        // `homer11.shuffled` (96 generators over 220 variables) went from 44.8 s
        // to 1.85 s. Breaking is worth it when the symmetry is global, so
        // require several generators covering a real share of the formula.
        let min_generators: usize = std::env::var("AY_SAT_SIGNED_MIN_GENERATORS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2);
        let min_support_pct: usize = std::env::var("AY_SAT_SIGNED_MIN_SUPPORT_PCT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(10);
        let moved: BTreeSet<Variable> = generators
            .iter()
            .flat_map(|perm| perm.keys().map(|l| l.variable()))
            .collect();
        let support_pct = moved.len().saturating_mul(100) / self.num_vars.max(1);
        if generators.len() < min_generators || support_pct < min_support_pct {
            safe_eprintln!(
                "c symmetry: {n} signed generator(s) over {support_pct}% of variables — \
                 below the breaking threshold, skipped",
                n = generators.len(),
            );
            return (false, false);
        }
        self.cold.symmetry_stats.pairs_detected = self
            .cold
            .symmetry_stats
            .pairs_detected
            .saturating_add(generators.len() as u64);
        safe_eprintln!(
            "c symmetry: {n} signed generator(s) verified",
            n = generators.len()
        );

        let existing = crate::symmetry::build_formula_counts(&clauses);
        let mut seen: BTreeSet<Vec<u32>> = BTreeSet::new();
        let mut changed = false;
        for perm in &generators {
            // Smallest moved variable, and the literal its positive form goes to.
            let Some((&pivot_lit, &image)) = perm
                .iter()
                .filter(|(l, _)| l.is_positive())
                .min_by_key(|(l, _)| l.variable().id())
            else {
                continue;
            };
            let mut clause = if image == pivot_lit.negated() {
                vec![pivot_lit]
            } else {
                vec![pivot_lit, image.negated()]
            };
            let key = crate::symmetry::canonical_clause_key(&clause);
            if existing.contains_key(&key) || !seen.insert(key) {
                continue;
            }
            // On the SR route the clause is certified by σ itself: σ is a
            // verified automorphism, so it remaps the current formula (including
            // any symmetry clause added before it) onto itself, and the
            // per-generator additions compose. The a-line is written BEFORE the
            // clause joins the database, and the clause then goes in on the
            // trusted route because AY's internal RUP/RAT checker cannot replay
            // a substitution witness — `dsr-trim` is the judge.
            let added = if sr_proof {
                let witness = crate::symmetry::signed_sr_witness_tokens(&clause, perm);
                if self.proof_emit_add_sr(&clause, &witness).is_err() {
                    // Incomplete proof must not be trusted: stop emitting.
                    // Clauses already added stay — they are sound — and
                    // finalization checks the I/O-error flag.
                    break;
                }
                self.add_clause_watched_trusted(&mut clause)
            } else {
                self.add_clause_watched(&mut clause)
            };
            match added {
                AddResult::Added(_) | AddResult::Unit(_) => {
                    changed = true;
                    self.cold.symmetry_stats.sb_clauses_added =
                        self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                }
                AddResult::Empty => return (true, true),
            }
        }
        (false, changed)
    }

    /// Orbitope route: detect a row-interchangeable at-most-one matrix inside
    /// the formula and add its orbitopal fixing units.
    ///
    /// Returns `(unsat, changed)`. Every row transposition used is checked
    /// against the whole clause multiset by the detector's sound gate, so a
    /// detection bug can only cost units, never admit a wrong answer.
    fn preprocess_symmetry_orbitope(&mut self) -> (bool, bool) {
        use crate::symmetry::orbitope::{detect_row_amo_matrices, OrbitopeLimits};

        let clauses = self.snapshot_root_irredundant_clauses_for_symmetry();
        if clauses.len() < 2 {
            return (false, false);
        }
        let (matrices, stats) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        self.cold.symmetry_stats.groups_nontrivial = self
            .cold
            .symmetry_stats
            .groups_nontrivial
            .saturating_add(stats.columns);
        self.cold.symmetry_stats.pairs_detected = self
            .cold
            .symmetry_stats
            .pairs_detected
            .saturating_add(stats.verified_swaps);
        let Some(matrix) = matrices.first() else {
            return (false, false);
        };
        self.cold.symmetry_stats.largest_group = self
            .cold
            .symmetry_stats
            .largest_group
            .max(matrix.verified_rows as u64);
        safe_eprintln!(
            "c symmetry: orbitope {rows}x{cols} matrix, {verified} rows verified interchangeable",
            rows = matrix.row_count(),
            cols = matrix.col_count(),
            verified = matrix.verified_rows,
        );

        // Two emission modes for the SAME units.
        //
        // With a proof surface active, each unit must carry the σ-witness that
        // certifies it (`RowAmoMatrix::sr_steps`), and the units must go out in
        // that method's column-ascending/row-descending order — a unit's
        // redundancy depends on the ones already added below it in its column.
        // Without a proof surface there is nothing to certify against, so the
        // cheaper row-major `fixing_units` is used unchanged.
        //
        // Before this split the route was gated off entirely whenever a proof was
        // being written (the `!symmetry_proof_surface_active()` clause at the
        // caller), which meant it never ran in a scored configuration:
        // `competition/prepare_sat26_submission.sh` always passes `--proof`.
        let mut changed = false;
        if self.symmetry_proof_surface_active() {
            for (a, b) in &matrix.synth_amo {
                self.freeze(*a);
                self.freeze(*b);
            }
            for (clause, witness) in matrix.sr_steps() {
                // Emit the DSR a-line first (records the addition), then add the
                // unit on the trusted route — the same order as the aux-free SR
                // path above, so a write failure never leaves the solver holding
                // a unit the proof does not mention.
                if self.proof_emit_add_sr(&clause, &witness).is_err() {
                    break;
                }
                let mut lits = clause;
                match self.add_clause_watched_trusted(&mut lits) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        changed = true;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
        } else {
            // Synthesized at-most-one clauses first: the fixing units are only
            // satisfiability-preserving when each column has at most one true
            // entry, and for the graph-colouring shape the formula does not
            // supply that. `sr_steps` emits the same clauses ahead of the units
            // on the proof route.
            // Freeze every variable the synthesized AMO clauses mention, so BVE
            // cannot eliminate it. Task #18: with these clauses added, some
            // deletion downstream removes a clause the final refutation needs —
            // established by bisect (every addition verifies; the empty clause
            // does not) and by stripping all `d` lines (proof then verifies).
            // The XOR extension guards the same hazard the same way.
            for (a, b) in &matrix.synth_amo {
                self.freeze(*a);
                self.freeze(*b);
            }
            for mut clause in matrix.synth_amo_clauses() {
                match self.add_clause_watched(&mut clause) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        changed = true;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
            for unit in matrix.fixing_units() {
                let mut clause = vec![unit];
                match self.add_clause_watched(&mut clause) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        changed = true;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
        }
        (false, changed)
    }

    /// HHW (Heule-Hunt-Wetzler) DRAT symmetry-breaking route (T2). For each
    /// gate-verified automorphism generator, emit a plain-DRAT image-and-chain
    /// fragment + the leading lex-leader clause, applying the surviving clauses to
    /// the solver DB so the residual solve refutes and the proof terminates with
    /// the empty clause. Generators are applied SEQUENTIALLY over the evolving
    /// formula and gate-checked against it, so an overlap generator (whose support
    /// a prior renaming disturbed) is SKIPPED soundly (HHW §6). Returns whether any
    /// clause was added.
    ///
    /// Soundness: every emitted addition is RUP/RAT-valid against the active set at
    /// the moment it is added (the gate `permutation_preserves_formula` guarantees
    /// each generator is a genuine automorphism); the native DRAT checker is the
    /// final judge. A wrong emit is REJECTED by the checker, never falsely VERIFIED.
    fn preprocess_symmetry_hhw(&mut self, clauses: &[Vec<Literal>]) -> bool {
        // The native checker reads the ORIGINAL CNF. If root simplification has
        // already assigned variables, the snapshot is a REDUCED formula and the
        // σ-image RUP steps would not line up with the original clauses. Require an
        // empty root trail (true for the php/coloring family); otherwise no-op.
        if !self.trail.is_empty() {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return false;
        }

        let detector = crate::symmetry::detector::SymmetryDetector::new(
            SYMMETRY_MAX_PAIRS,
            SYMMETRY_MAX_GROUP_SIZE,
        );
        let generators = detector.find_generators(clauses);
        if generators.is_empty() {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return false;
        }

        // Evolving formula: the gate for each generator is checked against the
        // CURRENT formula (original clauses + already-applied generators' kept
        // clauses), so disjoint generators compose and overlap generators skip.
        let mut cur: Vec<Vec<Literal>> = clauses.to_vec();
        let mut changed = false;
        for g in &generators {
            let counts = crate::symmetry::build_formula_counts(&cur);
            if !crate::symmetry::detector::permutation_preserves_formula(&counts, g) {
                continue; // overlap / non-automorphism of the evolving formula: skip
            }
            let fresh_base = self.num_vars as u32;
            let Some(built) = crate::symmetry::hhw::build_lead(&cur, g, fresh_base) else {
                continue;
            };
            // Allocate the fresh s_i / x'_i for this generator.
            self.ensure_num_vars(built.new_var_count as usize);
            // Emit the partial proof and apply the surviving clauses to the DB.
            if self.apply_hhw_steps(&built).is_err() {
                break; // proof I/O failure: stop; an incomplete proof is not trusted
            }
            // Grow the evolving formula by this generator's KEPT clauses so the
            // next generator is gate-checked against F + these additions.
            for step in &built.steps {
                if let crate::symmetry::hhw::HhwStep::AddKeep(c) = step {
                    cur.push(c.clone());
                }
            }
            changed = true;
            self.cold.symmetry_stats.sb_clauses_added =
                self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
        }
        changed
    }

    /// Emit one generator's HHW partial-proof steps (plain DRAT `a`/`d`-lines via
    /// the proof manager) and add the surviving clauses to the solver DB on the
    /// trusted route. `AddKeep` clauses go to BOTH the proof and the DB; scaffolds
    /// and deletions are proof-only.
    fn apply_hhw_steps(&mut self, built: &crate::symmetry::hhw::HhwLead) -> std::io::Result<()> {
        use crate::proof_manager::ProofAddKind;
        use crate::symmetry::hhw::HhwStep;
        for step in &built.steps {
            match step {
                HhwStep::AddKeep(c) => {
                    // Plain DRAT `a`-line, registered as a trusted transform (the
                    // inline DRUP checker cannot RUP/RAT-verify the blocked gadget
                    // clauses; the post-solve native checker is the gate), then add
                    // to the DB as a trusted axiom (mirrors the SR route pattern).
                    self.proof_emit_add(c, &[], ProofAddKind::TrustedTransform)?;
                    let mut lits = c.clone();
                    if let AddResult::Empty = self.add_clause_watched_trusted(&mut lits) {
                        // A kept clause empty/all-false at root closes the proof.
                        return Ok(());
                    }
                }
                HhwStep::AddScaffold(c) => {
                    self.proof_emit_add(c, &[], ProofAddKind::TrustedTransform)?;
                }
                HhwStep::Delete(c) => {
                    self.proof_emit_delete(c, 0)?;
                }
            }
        }
        Ok(())
    }

    fn snapshot_root_irredundant_clauses_for_symmetry(&self) -> Vec<Vec<Literal>> {
        let mut clauses = Vec::new();

        for clause_idx in self.arena.active_indices() {
            if self.arena.is_dead(clause_idx) || self.arena.is_learned(clause_idx) {
                continue;
            }

            let mut reduced = Vec::with_capacity(self.arena.len_of(clause_idx));
            let mut satisfied = false;

            for &lit in self.arena.literals(clause_idx) {
                match self.lit_value(lit) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => reduced.push(lit),
                }
            }

            if satisfied || reduced.is_empty() {
                continue;
            }

            reduced.sort_unstable_by_key(|lit| lit.raw());
            clauses.push(reduced);
        }

        clauses
    }

    #[inline]
    fn symmetry_proof_surface_active(&self) -> bool {
        self.proof_manager.is_some() || self.cold.lrat_enabled || self.cold.clause_trace.is_some()
    }
}
