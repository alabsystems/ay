// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root-only symmetry preprocessing.

use super::mutate::{AddResult, DeleteResult, ReasonPolicy};
use super::*;
use std::collections::BTreeSet;

mod aux_free_sr_route;
pub(in crate::solver) mod ladder_collapse;

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
/// Soundness is unaffected by widening it because the exact structural detector
/// and family-specific construction do not depend on this ceiling. In no-proof
/// runs those two components are the trust boundary; on a witnessed DRAT surface
/// the external SR checker independently audits their output. The clause cap
/// remains the real cost bound. (B2: edit the constant.)
const SYMMETRY_DETECTOR_MAX_VARS: usize = 1_000_000;
/// Clause cap for routes that may invoke the EXPENSIVE backtracking automorphism
/// finder (`find_composite_generators` / `ir::find_automorphisms`): the composite,
/// HHW, and default BreakID routes. The IR finder is node-budget
/// bounded but its per-node refinement is O(clauses), so it is kept tightly capped
/// to ensure huge general instances are never slowed by it.
const SYMMETRY_IR_MAX_CLAUSES: usize = 20_000;
/// Clause cap for the CHEAP aux-free-SR family recognizers. They perform bounded
/// structural recognition rather than IR search, so they get a much larger
/// clause budget. The recognizers and builders are the soundness boundary when
/// no proof is requested; on a witnessed DRAT surface `dsr-trim` additionally
/// checks every emitted step. Before this split the shared 20_000-clause cap
/// silently dropped php_50 (63_801 clauses) to plain CDCL (master-plan G7
/// "detection cliff").
///
/// Raised from 200_000 after it was measured excluding real targets: two of the
/// six official `chnl` instances sit just past it (`chnl-020x101` at 202_202
/// clauses, `chnl-030x091` at 245_882) and were dropped to plain CDCL, where
/// they time out, while the four below the cap solve in 67-1337 ms. The cap is a
/// resource guard, not a soundness gate. (B2: edit the constant.)
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
        if ay_core::misc_cli_flags().sat_symmetry_trace {
            safe_eprintln!(
                "c symmetry-trace: entered: enabled={} oneshot={} incremental={} proof_manager={} lrat={} clause_trace={} vars={} clauses={}",
                self.cold.symmetry_enabled,
                self.cold.symmetry_oneshot,
                self.cold.has_been_incremental,
                self.proof_manager.is_some(),
                self.cold.lrat_enabled,
                self.has_live_clause_trace(),
                self.num_vars,
                self.arena.active_clause_count(),
            );
        }

        // #17: --sat-composite-symmetry enables the (default-off, no-proof-only)
        // composite-permutation symmetry path even when the profile leaves
        // symmetry off — for the clique/coloring/PHP family that the single-swap
        // detector cannot break.
        let composite_symmetry = ay_core::sat_ab_switches().composite_symmetry;
        if self.cold.has_been_incremental {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Incremental);
            return (false, false);
        }
        let proof_surface_active = self.symmetry_proof_surface_active();
        // The family-specific symmetry proof routes need an actual DRAT
        // writer. Bare LRAT bookkeeping and clause-trace reconstruction cannot
        // represent their additions, so neither may be treated as a supported
        // proof surface merely because proof state is active.
        let plain_drat_surface_ok = self.proof_manager.is_some()
            && !self.cold.lrat_enabled
            && !self.has_live_clause_trace()
            && crate::proof_capability::symmetry_extended_drat_allowed(
                crate::proof_capability::ProofMode::Drat,
            );
        // SR-WITNESSED emission (aux-free WLOG chains, orbitope staircase)
        // has one more precondition: the DECLARED external checker must accept
        // substitution witnesses AND read the surface they are written on.
        // On the DRAT stream only dsr-trim does (drat-trim and dpr-trim are
        // both measured to reject the DSR `a`-lines); on the pseudo-Boolean
        // stream VeriPB does, via `red`. Under any other declaration — or a
        // checker/format mismatch such as `--proof-format drat --proof-checker
        // veripb` — these routes skip cleanly to plain CDCL rather than write a
        // proof the run's own declared checker rejects. HHW is plain RUP/RAT
        // and is deliberately NOT gated on the declared checker.
        let veripb_surface = self
            .proof_manager
            .as_ref()
            .is_some_and(|manager| manager.output().is_veripb());
        let declared_checker_sr_ok =
            crate::proof_capability::declared_checker_accepts_sr_witnesses(veripb_surface);
        let witnessed_drat_ok = plain_drat_surface_ok && declared_checker_sr_ok;

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
        // no longer confined to non-proof runs: under a supported DRAT proof
        // surface the route emits each unit as a DSR `a`-line carrying the
        // row-swap σ-witness (`RowAmoMatrix::sr_steps`), externally verified
        // with `dsr-trim`. LRAT and clause-trace surfaces skip this route.
        //
        // Default ON with an explicit `AY_SAT_ORBITOPE=0` opt-out. Previously
        // opt-in via a variable nothing set, so the route never ran outside a
        // hand-written command line.
        let orbitope_route = {
            // B26: CLI-owned opt-out (--sat-no-orbitope); env retired.
            !ay_core::sat_ab_switches().no_orbitope
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
            && !self.cold.symmetry_orbitope_disabled
            && self.cold.symmetry_oneshot
            && self.cold.symmetry_stats.runs == 1
            && orbitope_fits
            && (!proof_surface_active || witnessed_drat_ok)
        {
            // Ladder-collapse pre-pass (adv_gc family): shuffled sequential
            // at-most-one ladders destroy the syntactic colour symmetry, so
            // the row-swap gate below rejects the first transposition and the
            // matrix route finds nothing. Collapsing each strictly recognized
            // ladder into its pairwise binary closure (plain RUP additions +
            // deletions, BVE-style model reconstruction) restores the
            // symmetry the detector needs. Sound standalone — it runs whether
            // or not the orbitope detection subsequently fires. See
            // `ladder_collapse` for the recognizer's strictness contract.
            let (ladder_unsat, ladder_changed) = self.preprocess_symmetry_ladder_collapse();
            if ladder_unsat {
                return (true, true);
            }
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
            if unsat || changed || ladder_changed {
                return (unsat, changed || ladder_changed);
            }
        } else if orbitope_route && self.cold.symmetry_oneshot && !orbitope_fits {
            // Never drop a route silently (master-plan G7).
            safe_eprintln!(
                "c symmetry: skipped (orbitope size): vars {} cap {ORBITOPE_MAX_VARS}, clauses {} cap {ORBITOPE_MAX_CLAUSES}",
                self.num_vars,
                self.arena.active_clause_count(),
            );
        } else if orbitope_route
            && self.cold.symmetry_oneshot
            && self.cold.symmetry_stats.runs == 1
            && proof_surface_active
            && plain_drat_surface_ok
            && !declared_checker_sr_ok
        {
            // Same G7 rule: the declared checker is the ONLY reason the
            // orbitope route did not run here. Name it so a submission-profile
            // run reads as a deliberate capability skip, not a lost route.
            //
            // Two different reasons land here and the message distinguishes
            // them, because the fix differs: a checker that cannot consume a
            // substitution witness at all needs a different DECLARATION, while
            // a checker that can needs the matching --proof-format. Saying
            // "does not accept DSR substitution witnesses" about dsr-trim on a
            // `.pbp` would be false and would send the reader the wrong way.
            let checker = ay_core::declared_proof_checker();
            if checker.accepts_sr_witnesses() {
                safe_eprintln!(
                    "c symmetry: skipped (orbitope SR): declared proof checker '{}' accepts substitution witnesses but cannot read the emitted proof format (use --proof-format {})",
                    checker.name(),
                    if checker.reads_veripb() { "veripb" } else { "drat" },
                );
            } else {
                safe_eprintln!(
                    "c symmetry: skipped (orbitope SR): declared proof checker '{}' does not accept DSR substitution witnesses",
                    checker.name(),
                );
            }
        }

        // The aux-free SR route is certifiable and cheap (one O(clauses)
        // structural scan), so like the orbitope route it must not be denied by
        // `symmetry_enabled` — a flag that defaults false and only re-enables
        // below 4096 vars, while the PHP family it targets is far larger.
        // B26: CLI-owned opt-out (--sat-no-symmetry-sr-auxfree); env retired.
        let sr_auxfree_enabled = !ay_core::sat_ab_switches().no_symmetry_sr_auxfree;
        let sr_auxfree_enabled = sr_auxfree_enabled && self.cold.symmetry_oneshot;
        // The signed route's flag is read further down, AFTER this gate, so
        // `--sat-signed-symmetry` alone never reached it: `symmetry_enabled`
        // defaults false and its only re-enable (`adaptive.rs`) is guarded by
        // `num_vars < 4096`. Verified 2026-08-10 on a 139 160-variable instance:
        // with the flag set, the trace still reports `enabled=false` and
        // `symmetry_sb_cls: 0`.
        //
        // That is not merely a dead switch — it invalidated a recorded verdict.
        // The full-400 A/B that REJECTED signed symmetry (-3 solved) measured a
        // technique that was inert on every instance above 4096 variables, i.e.
        // on most of the corpus. Re-judge that decision now the route can run.
        let signed_enabled = ay_core::sat_ab_switches().signed_symmetry;
        // Signed lex leaders remove models just like every other structural
        // symmetry route. An environment flag must not silently opt an
        // embedder or assumption solver into that one-shot-only transform.
        let signed_route =
            signed_enabled && self.cold.symmetry_oneshot && !self.cold.symmetry_signed_disabled;
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
        // RUP, so they stay off every proof surface. A former signed-SR route
        // emitted one σ witness per generator, but σ was verified only against
        // the original formula, not against SBPs emitted for earlier generators;
        // that does not establish sequential proof composition.
        if signed_route
            && self.cold.symmetry_stats.runs == 1
            && !proof_surface_active
            && self.num_vars <= SIGNED_SYMMETRY_MAX_VARS
            && self.arena.active_clause_count() <= SIGNED_SYMMETRY_MAX_CLAUSES
        {
            let before = self.cold.symmetry_stats.sb_clauses_added;
            let (unsat, changed) = self.preprocess_symmetry_signed();
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
        // Heule-Hunt-Wetzler (2015) image-and-chain derivation with an
        // evolving-formula gate, or a separately proved family-specific SR
        // construction. A checker format alone does not make per-generator
        // witnesses compose.
        // #8011 AUX-FREE SR route: emit a complete family-specific refutation over
        // original variables only. This replaced the retired generic lex-tower SR
        // experiment: its single σ witness does not certify a tower after the first
        // symmetry-breaking clause has changed the active formula.
        //
        // Default ON with `--sat-no-symmetry-sr-auxfree` as the explicit opt-out.
        // Unlike plain lex leaders this family-specific route is externally
        // checkable on its supported proof surface.
        let sr_auxfree_route = sr_auxfree_enabled && !self.cold.symmetry_auxfree_disabled;
        // HHW route (T2): --sat-symmetry-hhw emits, per gate-verified generator,
        // a Heule-Hunt-Wetzler (CADE 2015 §5) image-and-chain DRAT fragment + the
        // leading lex-leader symmetry clause as PLAIN DRAT (RUP/RAT additions +
        // deletions). Every HHW step is verifiable by AY's OWN native
        // RUP/RAT DRAT checker (`ay check drat` / `--verify-proof`) — zero
        // external dependencies. Requires a DRAT proof manager with no LRAT or
        // clause-trace surface.
        let hhw_route_enabled = ay_core::sat_ab_switches().symmetry_hhw;
        // The aux-free SR route does not ride on `composite_symmetry`. If a proof
        // is being written it needs a witnessed DRAT surface AND a declared
        // checker that consumes DSR witnesses; with no proof the
        // family-specific construction itself is the trust boundary and emission
        // calls are no-ops.
        let sr_auxfree_supported = !proof_surface_active || witnessed_drat_ok;
        // Composite lex leaders remain available without proof. Under a proof
        // surface the only general composite route is HHW; the retired DPR and
        // full-tower SR experiments did not compose across sequential generators.
        // HHW emits plain RUP/RAT DRAT (no SR witnesses), so it needs only the
        // DRAT surface, not the dsr-trim declared-checker capability.
        let hhw_route = hhw_route_enabled && composite_symmetry && plain_drat_surface_ok;
        let sr_auxfree_route = sr_auxfree_route && sr_auxfree_supported;
        if proof_surface_active && !hhw_route && !sr_auxfree_route {
            // Same G7 rule as the size guard below: never drop to plain CDCL
            // without a trace. This skip used to be SILENT, which made a
            // proof-mode run look like a plain search timeout — the instance
            // simply reported UNKNOWN with no indication that symmetry breaking,
            // the only technique that can crack it, had been switched off.
            // Name the failing precondition so the cause is one line, not an
            // afternoon of bisecting env flags.
            safe_eprintln!(
                "c symmetry: skipped (proof surface active): composite={} proof_manager={} lrat={} clause_trace={} extended_drat_allowed={} declared_checker={} accepts_sr_witnesses={declared_checker_sr_ok} hhw_route={hhw_route}",
                composite_symmetry,
                self.proof_manager.is_some(),
                self.cold.lrat_enabled,
                self.has_live_clause_trace(),
                crate::proof_capability::symmetry_extended_drat_allowed(
                    crate::proof_capability::ProofMode::Drat
                ),
                ay_core::declared_proof_checker().name(),
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
        // B2: the AY_SAT_SYMMETRY_DETECTOR_MAX_* env overrides are deleted;
        // the named constants are the single source of truth.
        let clause_cap = if sr_auxfree_route && !hhw_route {
            SYMMETRY_DETECTOR_MAX_CLAUSES
        } else {
            SYMMETRY_IR_MAX_CLAUSES
        };
        let var_cap = if sr_auxfree_route && !hhw_route {
            SYMMETRY_DETECTOR_MAX_VARS
        } else {
            SYMMETRY_MAX_VARS
        };
        let num_vars = self.num_vars;
        let active_clauses = self.arena.active_clause_count();
        if num_vars > var_cap || active_clauses > clause_cap {
            let route = if sr_auxfree_route && !hhw_route {
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

        // #8011 AUX-FREE SR route (php-sr.c/count_p port): emit a complete
        // original-variable DSR refutation, with no equal-prefix aux or lex tower.
        // Each WLOG unit has a single-transposition witness on the trusted route,
        // externally checked by dsr-trim, not internal RUP. Root propagation derives
        // the final empty clause; recognized PHP/matching instances fire, others fall through.
        if sr_auxfree_route {
            let (route_kind, auxfree_steps) = aux_free_sr_route::detect(&clauses);
            self.cold.symmetry_stats.record_route(
                "auxfree-sr",
                match &auxfree_steps {
                    Some(v) => format!("{route_kind}, {} steps", v.len()),
                    None => "ran, no recognised aux-free family".to_string(),
                },
            );
            if let Some(steps) = auxfree_steps {
                let mut changed = false;
                for lc in steps {
                    let crate::symmetry::detector::LexClause::Sr { clause, witness } = lc;
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
            // The large cap above pays only for structural recognition. Once it
            // misses, reapply the tight IR cap before falling through; otherwise
            // default-on aux-free recognition would accidentally authorize the
            // backtracking finder up to the one-million-variable/clause ceilings.
            if num_vars > SYMMETRY_MAX_VARS || active_clauses > SYMMETRY_IR_MAX_CLAUSES {
                if num_vars > SYMMETRY_MAX_VARS {
                    safe_eprintln!(
                        "c symmetry: skipped (IR fallback after aux-free miss): vars {num_vars} > cap {SYMMETRY_MAX_VARS}"
                    );
                } else {
                    safe_eprintln!(
                        "c symmetry: skipped (IR fallback after aux-free miss): clauses {active_clauses} > cap {SYMMETRY_IR_MAX_CLAUSES}"
                    );
                }
                self.cold
                    .symmetry_stats
                    .skip(crate::symmetry::SymmetrySkipReason::TooLarge);
                return (false, false);
            }

            // Falling through is only safe because the routes below re-check the
            // proof surface; a proof-mode run that reaches here must not enter a
            // route without a checker-consumable construction.
            if proof_surface_active && !hhw_route {
                self.cold
                    .symmetry_stats
                    .skip(crate::symmetry::SymmetrySkipReason::ProofMode);
                return (false, false);
            }
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
                !proof_surface_active,
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
    fn preprocess_symmetry_signed(&mut self) -> (bool, bool) {
        let clauses = self.snapshot_root_irredundant_clauses_for_symmetry();
        if clauses.len() < 2 {
            return (false, false);
        }
        let formula_counts = crate::symmetry::build_formula_counts(&clauses);
        // B2: budgets are the shared constants in `symmetry/mod.rs`, the same
        // ones the composite route reads.
        let generators = crate::symmetry::ir::find_signed_automorphisms(
            &clauses,
            &formula_counts,
            crate::symmetry::IR_NODE_BUDGET,
            crate::symmetry::IR_MAX_GENERATORS,
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
        let min_generators: usize = crate::symmetry::SIGNED_MIN_GENERATORS;
        let min_support_pct: usize = crate::symmetry::SIGNED_MIN_SUPPORT_PCT;
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
            let added = self.add_clause_watched(&mut clause);
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
        // With the supported DRAT proof surface active, each unit must carry the
        // σ-witness that certifies it (`RowAmoMatrix::sr_steps`), and the units
        // must go out in that method's column-ascending/row-descending order — a
        // unit's redundancy depends on the ones already added below it in its
        // column. Without a proof surface there is nothing to serialize, so the
        // cheaper row-major `fixing_units` is used unchanged. The caller skips
        // this method for LRAT and clause-trace reconstruction surfaces.
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

    /// Ladder-collapse pre-pass: replace every strictly recognized sequential
    /// at-most-one ladder with the `C(k,2)` pairwise binaries it implies, then
    /// retire its register variables from search with BVE-style model
    /// reconstruction. Returns `(unsat, changed)`.
    ///
    /// Runs only under the orbitope gate (one-shot, first run, size-capped,
    /// plain-DRAT-or-no-proof surface). The additions are ordinary RUP derived
    /// clauses — each binary `(¬x_{σ(i)} ∨ ¬x_{σ(j)})` propagates to a
    /// conflict through the still-present ladder — and the deletions only
    /// weaken the formula, so the pass is sound whether or not the orbitope
    /// detection fires afterwards.
    ///
    /// # Model reconstruction (the SAT path)
    ///
    /// Register variables are marked eliminated, so a model of the collapsed
    /// formula assigns them arbitrarily. The witness entries pushed here
    /// recompute them as the prefix ORs `s_i = x_{σ(1)} ∨ … ∨ x_{σ(i)}` during
    /// the standard reverse replay ([`crate::reconstruct`]):
    ///
    /// * blocks are pushed for `i = k-1` down to `1`, so replay (which
    ///   reverses the stack) visits `s_1` first and each block sees its
    ///   predecessor's FINAL value;
    /// * within a block, the "force false" entries `(¬s_i ∨ ¬x_{σ(j)})` for
    ///   `j > i` replay first, then the "force true" entries
    ///   `(¬x_{σ(i)} ∨ s_i)` and `(¬s_{i-1} ∨ s_i)`. The `j > i+1` entries are
    ///   not formula clauses but implied resolvent-closure clauses (each is
    ///   the chain resolution of `(¬x_{σ(j)} ∨ ¬s_{j-1})` down to `s_i`);
    ///   without them a garbage-true register left over from search could
    ///   survive replay and poison the chain upward, ending with a violated
    ///   `(¬x_{σ(j)} ∨ ¬s_{j-1})` in the ORIGINAL formula. With them:
    ///   - if some `x_{σ(t)}` is true (at most one can be, the derived
    ///     pairwise AMO is part of the collapsed formula the model satisfies),
    ///     every `s_i` with `i < t` is forced false and every `s_i` with
    ///     `i ≥ t` is forced true — exactly the prefix OR;
    ///   - if no base variable is true, no force-false entry fires and the
    ///     force-true entries only propagate values upward, leaving an
    ///     upward-closed register assignment that satisfies every ladder
    ///     clause vacuously.
    ///
    /// Every entry's clause is implied by the ORIGINAL formula, and the
    /// always-on model verification gate (`finalize_sat_model`) remains the
    /// backstop behind this argument.
    pub(in crate::solver) fn preprocess_symmetry_ladder_collapse(&mut self) -> (bool, bool) {
        use crate::proof_manager::ProofAddKind;
        use ladder_collapse::{
            detect_ladders, LadderScanInput, LADDER_COLLAPSE_MAX_TOTAL_BINARIES,
        };

        // Defensive re-check of the caller's surface gate: the derived
        // binaries are emitted with empty hints, which no LRAT or clause-trace
        // surface can represent.
        if self.cold.lrat_enabled || self.has_live_clause_trace() {
            return (false, false);
        }

        // Streaming scan: only clean binary clauses are retained; every other
        // clause merely disqualifies its variables from serving as registers.
        let mut input = LadderScanInput::new(self.num_vars);
        for idx in self.arena.active_indices() {
            if self.arena.is_dead(idx) || self.arena.is_learned(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            let any_assigned = lits.iter().any(|&l| self.lit_value(l).is_some());
            input.add_clause(idx, lits, any_assigned);
        }
        let scan = detect_ladders(&input);
        if scan.ladders.is_empty() {
            return (false, false);
        }

        let mut existing_amo = scan.existing_amo;
        let mut collapsed = 0usize;
        let mut derived_added = 0usize;
        let mut clauses_deleted = 0usize;
        let mut aux_eliminated = 0usize;
        let mut budget_skipped = 0usize;
        for ladder in &scan.ladders {
            let k = ladder.base.len();
            // Pairs still missing from the formula, under the global budget.
            let mut pairs: Vec<(Variable, Variable)> = Vec::with_capacity(k * (k - 1) / 2);
            for i in 0..k {
                for j in (i + 1)..k {
                    let (a, b) = (ladder.base[i], ladder.base[j]);
                    let key = (a.0.min(b.0), a.0.max(b.0));
                    if !existing_amo.contains(&key) {
                        pairs.push((a, b));
                    }
                }
            }
            if derived_added + pairs.len() > LADDER_COLLAPSE_MAX_TOTAL_BINARIES {
                budget_skipped += 1;
                continue;
            }
            // 1. Derive the pairwise closure while the ladder clauses are
            //    still present (each addition is RUP against them).
            for &(a, b) in &pairs {
                existing_amo.insert((a.0.min(b.0), a.0.max(b.0)));
                let mut lits = vec![Literal::negative(a), Literal::negative(b)];
                let _ = self.proof_emit_add_prechecked(&lits, &[], ProofAddKind::Derived);
                match self.add_clause_watched(&mut lits) {
                    AddResult::Added(_) | AddResult::Unit(_) => {
                        derived_added += 1;
                        self.cold.symmetry_stats.sb_clauses_added =
                            self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                    }
                    AddResult::Empty => return (true, true),
                }
            }
            // 2. Delete the ladder clauses (proof `d` lines + watch removal
            //    via the uniform deletion entry point).
            let mut all_deleted = true;
            for &idx in &ladder.clause_ids {
                match self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0) {
                    DeleteResult::Deleted => clauses_deleted += 1,
                    DeleteResult::Skipped => all_deleted = false,
                }
            }
            debug_assert!(
                all_deleted,
                "BUG: ladder-collapse deletion skipped — the recognizer only \
                 admits unassigned clauses, which cannot be reason-protected"
            );
            if !all_deleted {
                // Unreachable by construction; if it ever fires, keep the
                // registers active and push no reconstruction. The surviving
                // clauses still constrain them and the model verification
                // gate covers the deleted ones (worst case: Unknown, never a
                // wrong answer).
                safe_eprintln!(
                    "c symmetry: ladder-collapse: deletion unexpectedly skipped; \
                     registers kept active"
                );
                continue;
            }
            // 3. Reconstruction entries (external index space, like BVE).
            //    Push order is part of the correctness argument — see the
            //    method docs.
            for i in (1..k).rev() {
                let s_i = ladder.aux[i - 1];
                let s_pos = self.externalize(Literal::positive(s_i));
                let s_neg = self.externalize(Literal::negative(s_i));
                let x_i = self.externalize(Literal::negative(ladder.base[i - 1]));
                self.inproc
                    .reconstruction
                    .push_witness_clause(vec![s_pos], vec![x_i, s_pos]);
                if i > 1 {
                    let prev = self.externalize(Literal::negative(ladder.aux[i - 2]));
                    self.inproc
                        .reconstruction
                        .push_witness_clause(vec![s_pos], vec![prev, s_pos]);
                }
                for j in (i + 1)..=k {
                    let x_j = self.externalize(Literal::negative(ladder.base[j - 1]));
                    self.inproc
                        .reconstruction
                        .push_witness_clause(vec![s_neg], vec![s_neg, x_j]);
                }
            }
            // 4. Freeze the base variables (the derived AMO plays the same
            //    role as the orbitope route's synthesized AMO: task #18
            //    established that letting BVE resolve such clauses away can
            //    delete a step the final refutation needs) and retire the
            //    registers exactly like BVE pivots.
            for &x in &ladder.base {
                self.freeze(x);
            }
            for &s in &ladder.aux {
                self.var_lifecycle.mark_eliminated(s.index());
                self.vsids.remove_from_heap(s);
                aux_eliminated += 1;
            }
            collapsed += 1;
        }
        if collapsed > 0 {
            // Learned clauses mentioning a retired register would let BCP
            // assign it behind the reconstruction's back (#8482 — same hazard
            // as BVE, same cure).
            self.flush_learned_with_eliminated_vars();
        }
        self.cold.symmetry_stats.record_route(
            "ladder-collapse",
            format!(
                "{collapsed} of {} ladders collapsed: +{derived_added} binaries, \
                 -{clauses_deleted} ladder clauses, {aux_eliminated} registers retired\
                 {}",
                scan.ladders.len(),
                if budget_skipped > 0 {
                    format!(", {budget_skipped} skipped by binary budget")
                } else {
                    String::new()
                },
            ),
        );
        (false, derived_added > 0 || clauses_deleted > 0)
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
        self.proof_manager.is_some() || self.cold.lrat_enabled || self.has_live_clause_trace()
    }
}
