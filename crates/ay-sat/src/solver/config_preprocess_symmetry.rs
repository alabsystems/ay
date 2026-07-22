// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root-only symmetry preprocessing.

use super::mutate::AddResult;
use super::*;

const SYMMETRY_MAX_VARS: usize = 4_096;
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
const SYMMETRY_DETECTOR_MAX_CLAUSES: usize = 200_000;
const SYMMETRY_MAX_PAIRS: usize = 128;
const SYMMETRY_MAX_GROUP_SIZE: usize = 64;

impl Solver {
    /// Detect variable symmetries via BreakID-style iterative refinement and
    /// emit lex-leader SBP clauses for each orbit.
    ///
    /// Returns `(unsat, changed)`.
    pub(super) fn preprocess_symmetry(&mut self) -> (bool, bool) {
        self.cold.symmetry_stats.begin_run();

        // #17: AY_SAT_COMPOSITE_SYMMETRY enables the (default-off, no-proof-only)
        // composite-permutation symmetry path even when the profile leaves
        // symmetry off — for the clique/coloring/PHP family that the single-swap
        // detector cannot break. Cached per process (each run is a fresh process).
        let composite_symmetry = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_COMPOSITE_SYMMETRY").is_some())
        };
        if !self.cold.symmetry_enabled && !composite_symmetry {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Disabled);
            return (false, false);
        }
        if self.cold.has_been_incremental {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Incremental);
            return (false, false);
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
        let sr_auxfree_route = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| std::env::var_os("AY_SAT_SYMMETRY_SR_AUXFREE").is_some())
        };
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
        let dpr_pr_route = composite_symmetry
            && self.proof_manager.is_some()
            && !self.cold.lrat_enabled
            && self.cold.clause_trace.is_none()
            && crate::proof_capability::symmetry_pr_proof_allowed(
                crate::proof_capability::ProofMode::Drat,
            );
        // The HHW route shares the DPR route's proof-surface preconditions; it is
        // additionally gated by its own env flag and the composite path.
        let hhw_route = hhw_route_enabled && composite_symmetry && dpr_pr_route;
        let sr_route = sr_route && dpr_pr_route;
        let sr_auxfree_route = sr_auxfree_route && dpr_pr_route;
        if self.symmetry_proof_surface_active() && !dpr_pr_route && !hhw_route {
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
            SYMMETRY_DETECTOR_MAX_CLAUSES
        } else {
            SYMMETRY_IR_MAX_CLAUSES
        };
        let num_vars = self.num_vars;
        let active_clauses = self.arena.active_clause_count();
        if num_vars > SYMMETRY_MAX_VARS || active_clauses > clause_cap {
            let route = if sr_auxfree_route {
                "aux-free-SR"
            } else {
                "IR"
            };
            if num_vars > SYMMETRY_MAX_VARS {
                safe_eprintln!(
                    "c symmetry: skipped ({route} route): vars {num_vars} > cap {SYMMETRY_MAX_VARS}"
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
            if let Some(steps) = crate::symmetry::detector::detect_php_aux_free_sr(&clauses) {
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
            // Not a pigeonhole instance: fall through to a no-op (sound). The
            // proof-surface clamp was already bypassed via dpr_pr_route, so just
            // report "no symmetry breaking".
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return (false, false);
        }

        if sr_route {
            let fresh_base = self.num_vars as u32;
            let (tagged, aux) = detector.detect_and_encode_composite_sr(&clauses, fresh_base);
            if aux > 0 {
                self.ensure_num_vars(fresh_base as usize + aux as usize);
            }
            let existing_clause_counts = crate::symmetry::build_formula_counts(&clauses);
            let mut seen: std::collections::BTreeSet<Vec<u32>> = std::collections::BTreeSet::new();
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
            let mut seen: std::collections::BTreeSet<Vec<u32>> = std::collections::BTreeSet::new();
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
            let (sbp, det_stats) = detector.detect_and_encode(&clauses);
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
            sbp
        };

        if sbp_clauses.is_empty() {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
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
