// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified proof emission and forward checking wrappers (#4564).
//!
//! These methods are the **sole authority** for clause mutation verification.
//! All proof-emitting call sites route through here so that the solver-owned
//! `ForwardChecker` sees every derived add, every delete, and every scope
//! transition — regardless of whether the mutation originates from CDCL
//! conflict analysis, inprocessing, or theory lemma injection.
//!
//! ## Design invariant
//!
//! No caller in `crates/ay-sat/src/solver/` should directly call
//! `manager.emit_add()` or `manager.emit_delete()`. Use the wrapper
//! methods on `Solver` instead.
//!
//! ## Forward-check obligation (#4641)
//!
//! Every clause emitted via `proof_emit_add_prechecked` **must** be followed
//! by a forward check (via `add_clause_db_checked`) before the next proof
//! emission. In debug builds, `pending_forward_check` tracks this obligation
//! and fires a `debug_assert!` on violation.
//!
//! ## Proof I/O error handling design (#4674)
//!
//! Callers use `let _ =` to silently drop `io::Result` from proof emission.
//! This is **intentional**: proof I/O failure must not abort a solve in
//! progress. The `ProofManager` tracks I/O errors internally via
//! `has_io_error()` (CaDiCaL fail-close pattern). On solve completion,
//! `finalize_unsat_proof` checks `has_io_error()` and refuses to set the
//! `empty_clause_in_proof` flag if any emission failed. This ensures:
//!
//! - Mid-solve: proof I/O failure degrades to incomplete proof, not panic
//! - Post-solve: UNSAT proofs with I/O errors are correctly flagged as
//!   incomplete rather than silently producing truncated proof files
//! - The `let _ =` pattern is consistent across all 15+ call sites
//!   (mutate.rs, inprocessing.rs, otfs.rs, conflict_analysis.rs, etc.)

use crate::decompose::DecomposeProofEmitContext;
use crate::proof_manager::ProofAddKind;
use crate::Literal;
use ay_core::time::Instant;
use std::io;

use super::Solver;

static EMISSION_TRIAGE_TARGET: std::sync::OnceLock<Option<Vec<i64>>> = std::sync::OnceLock::new();

#[cfg(test)]
mod counted_triage_tests;

fn counted_triage_inactive(target: &std::sync::OnceLock<Option<Vec<i64>>>) -> bool {
    if let Some(cached) = target.get() {
        return cached.is_none();
    }
    if !ay_core::captured_misc_cli_flags().is_some_and(|flags| flags.ab_triage_clause.is_none()) {
        return false;
    }
    // Never parse a target or capture first-use environment inside an owner.
    // A concurrent ordinary initializer may win with Some: that still refuses.
    target.get_or_init(|| None).is_none()
}

impl Solver {
    pub(in crate::solver) fn counted_emission_triage_inactive(&self) -> bool {
        counted_triage_inactive(&EMISSION_TRIAGE_TARGET)
    }

    /// Assert that proof mode has not changed mid-solve.
    ///
    /// `solve_proof_mode` is snapshotted at solve entry (`reset_search_state`).
    /// If it is `Some(b)`, then `proof_manager.is_some()` must still equal `b`.
    /// A mismatch means something toggled proof output during solving, which
    /// would silently corrupt the proof stream.
    ///
    /// This check lives here — in the centralized emission funnel — so that
    /// every proof-sensitive path is covered without per-caller boilerplate.
    #[cfg(debug_assertions)]
    fn assert_proof_mode_stable(&self) {
        if let Some(expected) = self.solve_proof_mode {
            debug_assert_eq!(
                self.proof_manager.is_some(),
                expected,
                "BUG: proof mode changed mid-solve (expected proof_manager.is_some()={expected})",
            );
        }
    }

    /// Whether the declared proof surface honours clause deletion strictly.
    ///
    /// VeriPB is a strict forward checker: a `del spec` removes the constraint
    /// from the database its autoprover reasons with, permanently. DRAT
    /// checkers do not — `drat-trim` silently ignores the deletion of a clause
    /// that is the current propagation reason for its first literal
    /// (drat-trim.c:806-814, mirrored in `ay-drat-check` with the
    /// `pseudo_unit_skips` counter), so on DRAT a root-level fact stays
    /// derivable even after AY deletes the clause that propagated it. On
    /// VeriPB it does not, and every later step that strengthens a clause with
    /// that fact stops being RUP.
    pub(crate) fn proof_honors_strict_deletion(&self) -> bool {
        self.proof_manager
            .as_ref()
            .is_some_and(|manager| manager.output().is_veripb())
    }

    /// State a level-0 fact as an explicit unit clause while the clause that
    /// propagated it is still in the checker's database.
    ///
    /// Call this immediately before a level-0 reason clause is deleted or
    /// replaced. At that instant the reason is still live, and every literal
    /// it depends on is either still propagated by a live clause or has
    /// already been stated by an earlier call, so `{lit}` is RUP and the step
    /// is checkable. One instant later it is not: the fact's only derivation
    /// has been removed from the database, and the strengthenings AY goes on
    /// to emit with that fact become undischargeable proofgoals.
    ///
    /// Surface-scoped on purpose:
    /// - LRAT already carries its own hint-bearing derivation for this
    ///   (`emit_lrat_delete_unit_derivation`, `materialize_level0_unit_proofs`).
    /// - DRAT does not need the step at all, and its byte stream must stay
    ///   identical, so nothing is emitted there.
    pub(crate) fn proof_emit_level0_unit_for_lost_reason(&mut self, lit: Literal) {
        self.proof_emit_level0_unit_supported(lit, None);
    }

    /// `proof_emit_level0_unit_for_lost_reason` with `support`, a live clause
    /// deriving `lit` at root (the one about to be deleted), as the source of
    /// its annotated-RUP hints when it is not `lit`'s reason edge.
    fn proof_emit_level0_unit_supported(&mut self, lit: Literal, support: Option<&[Literal]>) {
        if self.cold.lrat_enabled || !self.proof_honors_strict_deletion() {
            return;
        }
        let var_idx = lit.variable().index();
        // Only ever state a fact that really is root level and really is true
        // under the current assignment: a stale reason edge must not be
        // allowed to turn into a bogus unit clause.
        if var_idx >= self.num_vars
            || self.var_data[var_idx].level != 0
            || self.var_value_from_vals(var_idx) != Some(lit.is_positive())
        {
            return;
        }
        // Once stated, the unit is in the checker's database for the rest of
        // the stream (`VeripbWriter::delete` drops unit deletions), so a
        // second statement of the same fact is a redundant line. Idempotent
        // per variable via the bitset; a root-fixed var never flips polarity,
        // so keying on the variable alone is exact.
        let word = var_idx / 64;
        let bit = 1u64 << (var_idx % 64);
        if self
            .cold
            .veripb_stated_root_units
            .get(word)
            .is_some_and(|w| w & bit != 0)
        {
            return;
        }
        // `--sat-veripb-hints`: annotated from the reason about to be deleted
        // (veripb_hints.rs); as a plain `red` unit the checker proved a goal
        // for every clause holding the literal's negation (on
        // aes_equiv_encry_3_rounds most of what its elaboration spent time on).
        // Otherwise `Derived` (not `TrustedTransform`): the unit is genuinely
        // RUP here, so debug builds run it through the forward checker's RUP
        // check rather than trusting it.
        if self.veripb_state_root_unit(lit, support)
            || self
                .proof_emit_add(&[lit], &[], ProofAddKind::Derived)
                .is_ok()
        {
            if self.cold.veripb_stated_root_units.len() <= word {
                self.cold.veripb_stated_root_units.resize(word + 1, 0);
            }
            self.cold.veripb_stated_root_units[word] |= bit;
        }
    }

    /// State the root-level fact a clause currently derives before that clause
    /// is deleted from the strict-deletion (VeriPB) proof surface.
    ///
    /// The third member of the DRAT-leniency family (after 6aa0bbe61c and
    /// b2875b3b6a): the first fix restates a root fact when the clause being
    /// deleted is recorded as the fact's *reason edge* (`var_data.reason ==
    /// cref`). But a root fact's checker-side derivation can live in a clause
    /// its reason edge does not name:
    ///
    /// - Under jump reasons (#8034, >= 99%-binary formulas, non-LRAT only),
    ///   `enqueue_binary_reason` stores a bit-31 *literal-tagged* reason —
    ///   with ChrBT it does so even for assignments at level 0
    ///   (propagation.rs `assigned_level` computation). Tagged reasons set no
    ///   reason-clause mark and can never compare equal to an arena offset,
    ///   so every `reason == cref` protection is blind to them, and the
    ///   binary clause that actually propagated the fact is freely deletable.
    /// - A reason edge cleared earlier (scoped GC, stale-reason sweeps)
    ///   leaves the fact with `NO_REASON` while its derivation still hangs on
    ///   a live clause.
    ///
    /// DRAT checkers survive all of these because they track their *own*
    /// propagation reasons and silently skip deleting a clause that is the
    /// current reason of its first literal (drat-trim.c:806-814). VeriPB
    /// honours the deletion, the fact becomes underivable, and the next `red`
    /// step whose RUP support (or RAT resolvent) needs the fact dies with
    /// "Proofgoal N could not be autoproven" (observed: b6de3c794e at the
    /// 5000 s budget).
    ///
    /// The trigger condition is representation-independent: a clause is a
    /// live unit-propagation derivation of a root fact iff exactly one of its
    /// literals is root-true and every other literal is root-false. Deleting
    /// any such clause states the fact first, while the clause still
    /// justifies it — making the statement RUP at its stream position. The
    /// per-variable bitset in `proof_emit_level0_unit_for_lost_reason` bounds
    /// the cost at one unit line per root-fixed variable per stream.
    ///
    /// Soundness: the statement is emitted *before* the `del spec`, so the
    /// checker's database at every position remains a superset of what AY
    /// relies on — each retained/added member admitted by a checked step. No
    /// deletion is suppressed and no check is weakened.
    pub(crate) fn proof_emit_root_unit_for_lost_support(&mut self, clause: &[Literal]) {
        if self.cold.lrat_enabled || !self.proof_honors_strict_deletion() {
            return;
        }
        // Empty deletions are protocol-level; unit deletions are dropped by
        // `VeripbWriter::delete`, so the fact they state stays derivable.
        if clause.len() < 2 {
            return;
        }
        if let Some(lit) = self.root_derived_literal(clause) {
            self.proof_emit_level0_unit_supported(lit, Some(clause));
        }
    }

    /// The literal this clause currently unit-derives at root level, if any:
    /// exactly one root-true literal with every other literal root-false.
    fn root_derived_literal(&self, clause: &[Literal]) -> Option<Literal> {
        let mut true_lit = None;
        for &lit in clause {
            let vi = lit.variable().index();
            if vi >= self.num_vars || self.var_data[vi].level != 0 {
                return None;
            }
            match self.var_value_from_vals(vi) {
                Some(value) if value == lit.is_positive() => {
                    if true_lit.is_some() {
                        // Two root-true literals: the clause never fires under
                        // unit propagation at root, so it derives nothing.
                        return None;
                    }
                    true_lit = Some(lit);
                }
                Some(_) => {}        // root-false: exactly what a derivation needs
                None => return None, // unassigned: not a root derivation
            }
        }
        true_lit
    }

    /// Soundness-triage tripwire (--sat-ab-triage-clause "d1,d2,..." DIMACS
    /// lits): dump the live DB, and the call stack that wrote it, the moment
    /// this exact clause is emitted.
    pub(super) fn triage_on_emission(&mut self, clause: &[Literal]) {
        let target = EMISSION_TRIAGE_TARGET.get_or_init(|| {
            ay_core::misc_cli_flags()
                .ab_triage_clause
                .as_deref()
                .map(|s| {
                    let mut v: Vec<i64> =
                        s.split(',').filter_map(|t| t.trim().parse().ok()).collect();
                    v.sort_unstable();
                    v
                })
        });
        if target.is_some() {
            let mut mine: Vec<i64> = clause
                .iter()
                .map(|l| {
                    let v = i64::from(l.variable().0) + 1;
                    if l.is_positive() {
                        v
                    } else {
                        -v
                    }
                })
                .collect();
            mine.sort_unstable();
            if target.as_ref() == Some(&mine) {
                self.dump_live_db_for_triage("target_clause_emission");
            }
        }
    }

    /// Emit a proof addition without mutating the forward checker.
    ///
    /// This is for call sites that already update checker state through a
    /// database mutation path (e.g., `add_clause_db_checked`) in the same step.
    /// Keeping proof I/O centralized avoids direct `manager.emit_add(...)`
    /// usage while preserving "check exactly once" semantics.
    ///
    /// # Contract
    ///
    /// The caller **must** route the same clause through
    /// `add_clause_db_checked` before the next `proof_emit_*` call.
    /// Debug builds enforce this via `pending_forward_check` (#4641).
    #[track_caller]
    pub(crate) fn proof_emit_add_prechecked(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        self.triage_on_emission(clause);
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        #[cfg(debug_assertions)]
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG: previous prechecked clause (id={:?}) was never forward-checked",
            self.cold.pending_forward_check
        );

        // proof-posture-parity (site C): after a compaction under a proof
        // surface, proof lines carry external literals (`i2e`).
        let proof_lits;
        let proof_clause: &[Literal] = if self.cold.proof_vars_compacted {
            proof_lits = self.externalize_lits_for_proof(clause);
            &proof_lits
        } else {
            clause
        };
        // `--sat-veripb-hints`: a derivation whose antecedents were named is
        // written as annotated RUP (veripb_derived.rs), trusted transforms
        // included: the ids are written only once they are checked to refute
        // the clause's negation.
        let hinted = if !matches!(kind, ProofAddKind::Axiom) {
            self.veripb_emit_derived_hinted(clause, proof_clause)
        } else {
            self.veripb_drop_antecedents();
            None
        };
        let id = match hinted {
            Some(written) => {
                written?;
                0
            }
            None => {
                self.note_unhinted_add();
                if let Some(ref mut manager) = self.proof_manager {
                    manager.emit_add(proof_clause, hints, kind)?
                } else {
                    0
                }
            }
        };
        self.note_proof_add();

        // Synchronize solver's clause ID counter with proof writer's ID space.
        // Without this, techniques that emit proof steps (proof_emit_add) BEFORE
        // adding clauses to the DB (add_clause_db_checked) leave next_clause_id
        // behind the proof writer's counter. The subsequent add_clause_db_checked
        // then assigns from the stale next_clause_id, reusing an ID already
        // consumed by the proof writer. This causes LRAT ID collisions where two
        // different clauses share the same LRAT ID — deleting one silently
        // invalidates the other's ID in known_lrat_ids (#8093).
        //
        // Affected techniques: factorize, BVE apply, and any path that calls
        // proof_emit_add for multiple clauses before add_clause_watched.
        //
        // Note: add_learned_clause_inner overrides this by setting next_clause_id
        // back to `id` (not id+1) so that add_clause_db_checked assigns the SAME
        // ID the proof writer used for the learned clause.
        if id != 0 && self.cold.next_clause_id <= id {
            self.cold.next_clause_id = id + 1;
        }

        #[cfg(debug_assertions)]
        if id != 0 {
            self.cold.pending_forward_check = Some(id);
        }

        Ok(id)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    #[track_caller]
    pub(crate) fn proof_emit_add_prechecked_with_decompose_context(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
        context: &DecomposeProofEmitContext,
    ) -> io::Result<u64> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        #[cfg(debug_assertions)]
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG: previous prechecked clause (id={:?}) was never forward-checked",
            self.cold.pending_forward_check
        );

        let proof_lits;
        let proof_clause: &[Literal] = if self.cold.proof_vars_compacted {
            proof_lits = self.externalize_lits_for_proof(clause);
            &proof_lits
        } else {
            clause
        };
        self.veripb_drop_antecedents();
        self.note_unhinted_add();
        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_with_decompose_context(proof_clause, hints, kind, context)?
        } else {
            0
        };
        self.note_proof_add();

        if id != 0 && self.cold.next_clause_id <= id {
            self.cold.next_clause_id = id + 1;
        }

        #[cfg(debug_assertions)]
        if id != 0 {
            self.cold.pending_forward_check = Some(id);
        }

        Ok(id)
    }

    /// Emit a proof addition and forward-check the clause.
    ///
    /// 1. Updates the solver-owned `ForwardChecker` (if enabled).
    /// 2. Emits the addition through `ProofManager` (if present).
    ///
    /// Returns the LRAT clause ID (or 0 if no proof output configured).
    #[track_caller]
    pub(crate) fn proof_emit_add(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        // Forward check first: verify the clause before committing to proof.
        if let Some(ref mut checker) = self.cold.forward_checker {
            match kind {
                ProofAddKind::Axiom => checker.add_original(clause),
                ProofAddKind::Derived => {
                    if !hints.is_empty() && self.cold.lrat_enabled {
                        // The LRAT checker verifies the explicit hint chain.
                        // The forward DRUP checker cannot validate all
                        // LRAT-only derivations, so keep its clause DB in sync
                        // without demanding a DRUP proof here (#7108).
                        checker.add_original(clause);
                    } else {
                        checker.add_derived(clause);
                    }
                }
                ProofAddKind::TrustedTransform => checker.add_trusted_transform(clause),
            }
        }

        // Emit through proof pipeline (sets pending_forward_check in debug).
        let id = self.proof_emit_add_prechecked(clause, hints, kind)?;

        // We already forward-checked above, so clear the pending obligation.
        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }

        Ok(id)
    }

    /// Emit the bounded backward producer's terminal positive-RUP step.
    ///
    /// This intentionally bypasses the generic proof-manager hint
    /// filtering/preflight path: the bounded producer has already enforced
    /// positive, unique, live hints under its own count, byte, and deadline
    /// limits. Keeping this as a distinct funnel prevents ordinary empty
    /// clauses found during search from being mistaken for prevalidated
    /// backward output merely because bounded reconstruction is configured.
    pub(crate) fn proof_emit_bounded_terminal_rup_with_cancellation(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
        keep_going: &dyn Fn() -> bool,
    ) -> io::Result<u64> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        #[cfg(debug_assertions)]
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG: previous prechecked clause (id={:?}) was never forward-checked",
            self.cold.pending_forward_check
        );

        // The ordinary proof funnel registers LRAT-hinted derived clauses as
        // originals with the structural forward checker. Preserve that
        // bookkeeping without invoking its generic hint path.
        if let Some(ref mut checker) = self.cold.forward_checker {
            checker.add_original(&[]);
        }

        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_bounded_empty_rup_step_with_cancellation(hints, deadline, keep_going)?
        } else {
            0
        };
        if id != 0 && self.cold.next_clause_id <= id {
            self.cold.next_clause_id = id + 1;
        }
        Ok(id)
    }

    /// Apply an extension's proof-only script (chunked XOR ladders, task #20).
    ///
    /// Each step reaches the proof stream verbatim and NEVER touches the
    /// clause database: chunked XOR scaffolding references fresh extension
    /// variables above `num_vars` that must not participate in search or
    /// reach a model. Literal order is preserved because RAT additions
    /// (chain-definition clauses) carry their pivot as the FIRST literal.
    /// The internal forward checker registers additions as trusted
    /// transforms — like the SR symmetry route, the external verified chain
    /// (`dsr-trim`) is the certificate-mode trust anchor for these steps.
    pub(crate) fn apply_extension_proof_script(
        &mut self,
        script: Vec<crate::extension::ExtProofStep>,
    ) {
        for step in script {
            match step {
                crate::extension::ExtProofStep::Add(clause) => {
                    let _ = self.proof_emit_add(&clause, &[], ProofAddKind::TrustedTransform);
                }
                crate::extension::ExtProofStep::Delete(clause) => {
                    let _ = self.proof_emit_delete(&clause, 0);
                }
            }
        }
    }

    /// Emit a family-specific symmetry step as a DSR `a`-line.
    ///
    /// Live callers are the separately justified aux-free PHP/matching and
    /// orbitope constructions. The forward RUP/RAT checker cannot verify SR, so
    /// the clause is registered as a `TrustedTransform`; the external verified
    /// chain (`dsr-trim → drat/lsr → cake_lpr`) is the certificate-mode trust
    /// anchor. No-op when no proof manager is attached; in that mode soundness
    /// rests on the family recognizer and constructor before trusted insertion.
    #[track_caller]
    pub(crate) fn proof_emit_add_sr(
        &mut self,
        clause: &[Literal],
        witness: &[Literal],
    ) -> io::Result<()> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        // Defense in depth behind the route gate in
        // `config_preprocess_symmetry`: a live proof surface may only receive
        // an SR-witnessed step when the DECLARED checker can verify it on THIS
        // surface — dsr-trim on the DRAT stream (drat-trim and dpr-trim are
        // measured to reject those `a`-lines), VeriPB on the `.pbp` stream.
        debug_assert!(
            self.proof_manager.as_ref().is_none_or(|manager| {
                crate::proof_capability::declared_checker_accepts_sr_witnesses(
                    manager.output().is_veripb(),
                )
            }),
            "BUG: SR-witnessed emission reached a live proof surface whose declared \
             checker rejects substitution witnesses on that surface"
        );

        if let Some(ref mut checker) = self.cold.forward_checker {
            checker.add_trusted_transform(clause);
        }

        let (proof_lits, proof_witness);
        let (proof_clause, proof_wit): (&[Literal], &[Literal]) = if self.cold.proof_vars_compacted
        {
            proof_lits = self.externalize_lits_for_proof(clause);
            proof_witness = self.externalize_lits_for_proof(witness);
            (&proof_lits, &proof_witness)
        } else {
            (clause, witness)
        };
        self.note_unhinted_add();
        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_sr(proof_clause, proof_wit)?;
        }
        Ok(())
    }

    #[cfg_attr(not(test), allow(dead_code))]
    #[track_caller]
    pub(crate) fn proof_emit_add_with_decompose_context(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
        context: &DecomposeProofEmitContext,
    ) -> io::Result<u64> {
        if let Some(ref mut checker) = self.cold.forward_checker {
            match kind {
                ProofAddKind::Axiom => checker.add_original(clause),
                ProofAddKind::Derived => {
                    if !hints.is_empty() && self.cold.lrat_enabled {
                        checker.add_original(clause);
                    } else {
                        checker.add_derived(clause);
                    }
                }
                ProofAddKind::TrustedTransform => checker.add_trusted_transform(clause),
            }
        }

        let id =
            self.proof_emit_add_prechecked_with_decompose_context(clause, hints, kind, context)?;

        #[cfg(debug_assertions)]
        {
            self.cold.pending_forward_check = None;
        }

        Ok(id)
    }

    pub(crate) fn proof_emit_add_signed_lrat(
        &mut self,
        clause: &[Literal],
        hints: &[i64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        if let Some(ref mut checker) = self.cold.forward_checker {
            match kind {
                ProofAddKind::Axiom => checker.add_original(clause),
                ProofAddKind::Derived => {
                    if !hints.is_empty() && self.cold.lrat_enabled {
                        checker.add_original(clause);
                    } else {
                        checker.add_derived(clause);
                    }
                }
                ProofAddKind::TrustedTransform => checker.add_trusted_transform(clause),
            }
        }

        #[cfg(debug_assertions)]
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG: previous prechecked clause (id={:?}) was never forward-checked",
            self.cold.pending_forward_check
        );

        let proof_lits;
        let proof_clause: &[Literal] = if self.cold.proof_vars_compacted {
            proof_lits = self.externalize_lits_for_proof(clause);
            &proof_lits
        } else {
            clause
        };
        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_signed_lrat_hints(proof_clause, hints, kind)?
        } else {
            0
        };

        if id != 0 && self.cold.next_clause_id <= id {
            self.cold.next_clause_id = id + 1;
        }

        Ok(id)
    }

    /// Emit a proof record for a unit literal and store the returned ID
    /// in the `unit_proof_id` provenance map.
    ///
    /// This is the canonical pattern for inprocessing-derived units:
    /// emit the proof step, then record its LRAT clause ID so that
    /// `collect_level0_lrat_chain` can reference it in future derivations.
    #[track_caller]
    pub(crate) fn proof_emit_unit(
        &mut self,
        unit: Literal,
        hints: &[u64],
        kind: ProofAddKind,
    ) -> u64 {
        let proof_id = self.proof_emit_add(&[unit], hints, kind).unwrap_or(0);
        if proof_id != 0 {
            let vi = unit.variable().index();
            // Guard: only set unit_proof_id if the variable is NOT already
            // assigned at level 0 with the opposite polarity. Without this,
            // derived units from vivification/strengthening can overwrite the
            // proof ID for the variable's CURRENT assignment, causing LRAT
            // hint chains to reference the wrong clause (opposite polarity)
            // when deriving the empty clause (#7108).
            let already_assigned_opposite = vi < self.num_vars
                && self.var_data[vi].level == 0
                && self.var_is_assigned(vi)
                && self.lit_val(unit) < 0;
            if !already_assigned_opposite {
                self.record_unit_proof_id_for_lit(unit, proof_id);
            }
        }
        proof_id
    }

    /// Optional collection can drop an arena row while its exact input proof
    /// row remains live for a later rebuild. Required deletes never use this seam.
    #[cfg(test)]
    pub(super) fn proof_emit_delete_optional_gc(
        &mut self,
        clause: &[Literal],
        clause_id: u64,
    ) -> io::Result<()> {
        if self
            .proof_manager
            .as_ref()
            .is_some_and(|manager| manager.retainable_ledger_original_id(clause_id))
        {
            return Ok(());
        }
        self.proof_emit_delete(clause, clause_id)
    }

    /// Emit a proof deletion and forward-check the clause removal.
    ///
    /// 1. Updates the solver-owned `ForwardChecker` (if enabled).
    /// 2. Emits the deletion through `ProofManager` (if present).
    ///
    /// When `defer_proof_deletions` is true (#8011), the deletion is buffered
    /// instead of emitted immediately. BVE sets this flag so that all resolvent
    /// additions appear in the proof stream before any deletion, preventing
    /// cross-variable ordering violations.
    pub(crate) fn proof_emit_delete(
        &mut self,
        clause: &[Literal],
        clause_id: u64,
    ) -> io::Result<()> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        if self.defer_proof_deletions {
            self.deferred_proof_deletions
                .push((clause.to_vec(), clause_id));
            return Ok(());
        }

        // Strict-deletion surface: if this clause is currently the (possibly
        // only) unit-propagation derivation of a root fact, state the fact
        // while the clause still justifies it. Runs at true write time — after
        // the defer branch — so the unit precedes the `del spec` in the stream.
        self.proof_emit_root_unit_for_lost_support(clause);

        // Forward checker only tracks non-empty clauses; the empty clause
        // is a protocol-level signal (UNSAT proof completion), not a real
        // clause in the forward checker's database.
        if !clause.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(clause);
            }
        }

        let proof_lits;
        let proof_clause: &[Literal] = if self.cold.proof_vars_compacted {
            proof_lits = self.externalize_lits_for_proof(clause);
            &proof_lits
        } else {
            clause
        };
        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_delete(proof_clause, clause_id)
        } else {
            Ok(())
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn proof_emit_delete_with_decompose_context(
        &mut self,
        clause: &[Literal],
        clause_id: u64,
        context: &DecomposeProofEmitContext,
    ) -> io::Result<()> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        if self.defer_proof_deletions {
            self.deferred_proof_deletions
                .push((clause.to_vec(), clause_id));
            return Ok(());
        }

        // Same lost-support protection as `proof_emit_delete` (see there).
        self.proof_emit_root_unit_for_lost_support(clause);

        if !clause.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(clause);
            }
        }

        let proof_lits;
        let proof_clause: &[Literal] = if self.cold.proof_vars_compacted {
            proof_lits = self.externalize_lits_for_proof(clause);
            &proof_lits
        } else {
            clause
        };
        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_delete_with_decompose_context(proof_clause, clause_id, context)
        } else {
            Ok(())
        }
    }

    /// Optional satisfied-arena collection retains only a live input proof row.
    pub(super) fn proof_emit_delete_arena_optional_gc(
        &mut self,
        clause_idx: usize,
        clause_id: u64,
    ) -> io::Result<()> {
        if self
            .proof_manager
            .as_ref()
            .is_some_and(|manager| manager.retainable_ledger_original_id(clause_id))
        {
            return Ok(());
        }
        self.proof_emit_delete_arena(clause_idx, clause_id)
    }

    /// Like [`proof_emit_delete`] but reads literals directly from the arena,
    /// avoiding a `.to_vec()` allocation. Disjoint struct field borrows
    /// (arena vs forward_checker/proof_manager) let the borrow checker accept
    /// a shared arena slice without copying (#5075).
    ///
    /// When `defer_proof_deletions` is true (#8011), the deletion is buffered
    /// (with a copy of the literals, since the arena may be mutated before flush).
    pub(crate) fn proof_emit_delete_arena(
        &mut self,
        clause_idx: usize,
        clause_id: u64,
    ) -> io::Result<()> {
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        if self.defer_proof_deletions {
            let lits = self.arena.literals(clause_idx).to_vec();
            self.deferred_proof_deletions.push((lits, clause_id));
            return Ok(());
        }

        // Same lost-support protection as `proof_emit_delete` (see there).
        // Candidate literal is computed under the shared arena borrow; the
        // statement itself needs `&mut self`, so it happens after.
        if !self.cold.lrat_enabled && self.proof_honors_strict_deletion() {
            let lits = self.arena.literals(clause_idx);
            let derived = if lits.len() >= 2 {
                self.root_derived_literal(lits)
                    .map(|lit| (lit, lits.to_vec()))
            } else {
                None
            };
            if let Some((lit, support)) = derived {
                self.proof_emit_level0_unit_supported(lit, Some(&support));
            }
        }

        let lits = self.arena.literals(clause_idx);
        if !lits.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(lits);
            }
        }

        let proof_lits = if self.cold.proof_vars_compacted {
            Some(self.externalize_lits_for_proof(self.arena.literals(clause_idx)))
        } else {
            None
        };
        if let Some(ref mut manager) = self.proof_manager {
            let lits = match proof_lits.as_deref() {
                Some(ext) => ext,
                None => self.arena.literals(clause_idx),
            };
            manager.emit_delete(lits, clause_id)
        } else {
            Ok(())
        }
    }

    /// Save forward checker state for incremental push.
    pub(crate) fn forward_checker_push(&mut self) {
        #[cfg(debug_assertions)]
        if let Some(ref mut checker) = self.cold.forward_checker {
            checker.push();
        }
    }

    /// Restore forward checker state for incremental pop.
    pub(crate) fn forward_checker_pop(&mut self) {
        #[cfg(debug_assertions)]
        if let Some(ref mut checker) = self.cold.forward_checker {
            checker.pop();
        }
    }

    /// Emit proof for a derived unit, add to clause DB, enqueue, and mark fixed.
    ///
    /// Does NOT propagate. Use this when processing multiple units in batch
    /// (e.g., sweep) where propagation must be deferred until after watch
    /// state is rebuilt. For the common single-unit-then-propagate pattern,
    /// use [`Self::learn_derived_unit`] instead.
    pub(crate) fn enqueue_derived_unit(&mut self, unit: Literal, hints: &[u64]) {
        // When LRAT is enabled but hints are empty (incomplete chain from
        // collect_resolution_chain), downgrade to TrustedTransform to avoid
        // LRAT checker verification failure (#7108).
        let kind = if self.cold.lrat_enabled && hints.is_empty() {
            ProofAddKind::TrustedTransform
        } else {
            ProofAddKind::Derived
        };
        let pid = self.proof_emit_unit(unit, hints, kind);
        if pid != 0 && self.cold.lrat_enabled {
            self.cold.next_clause_id = pid;
        }

        let unit_idx = self.add_clause_db(&[unit], true);
        // Proof units: LBD=0, always passes likely_to_be_kept (#3727).
        self.mark_subsume_dirty_if_kept(unit_idx);

        // Unit clause: reason=None (#6257). Conflict analysis requires
        // reason clauses of length >= 2.
        // Store proof ID for both LRAT and clause-trace resolution chain
        // collection (#6368). Without this, collect_resolution_chain misses
        // unit clause antecedents when clause_trace is enabled but lrat is not.
        if pid != 0 {
            self.record_unit_proof_id_for_lit(unit, pid);
        }
        self.enqueue(unit, None);
        if !self.var_lifecycle.is_inactive(unit.variable().index()) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(unit.variable().index());
            self.l0_gc_dirty[unit.variable().index()] = true;
        }
    }

    /// Like [`Self::enqueue_derived_unit`] for a unit whose proof line was
    /// already emitted (proof id `pid`, 0 when there is no proof surface):
    /// clause DB, unit proof id, enqueue and fixed marking, but no emission.
    /// Sweep uses it: backbone units are certified (core lemmas + RUP unit)
    /// before the clause rewrites, while the clauses the lemmas rest on are
    /// still in the checker's database.
    pub(crate) fn enqueue_derived_unit_with_proof_id(&mut self, unit: Literal, pid: u64) {
        let unit_idx = self.add_clause_db(&[unit], true);
        self.mark_subsume_dirty_if_kept(unit_idx);
        if pid != 0 {
            self.record_unit_proof_id_for_lit(unit, pid);
        }
        self.enqueue(unit, None);
        if !self.var_lifecycle.is_inactive(unit.variable().index()) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(unit.variable().index());
            self.l0_gc_dirty[unit.variable().index()] = true;
        }
    }

    /// Flush all deferred proof deletions (#8011).
    ///
    /// During BVE, proof deletions are buffered so that all resolvent additions
    /// appear in the proof stream before any deletion. This prevents the DRAT
    /// proof from having cross-variable ordering violations where deletions from
    /// variable A's elimination remove clauses needed for variable B's resolvent
    /// RUP derivability.
    ///
    /// Must be called after all BVE resolvents for a round have been added and
    /// before any non-BVE proof emissions occur.
    pub(crate) fn flush_deferred_proof_deletions(&mut self) {
        debug_assert!(
            !self.defer_proof_deletions,
            "BUG: flush_deferred_proof_deletions called while deferral is still active"
        );
        let deletions = std::mem::take(&mut self.deferred_proof_deletions);
        for (lits, clause_id) in &deletions {
            let _ = self.proof_emit_delete(lits, *clause_id);
        }
        // Return the vec for reuse (avoid repeated allocation across BVE rounds).
        self.deferred_proof_deletions = deletions;
        self.deferred_proof_deletions.clear();
    }

    /// Learn a derived unit clause: emit proof, add to clause DB, enqueue,
    /// mark fixed, and propagate.
    ///
    /// This is the canonical pattern for inprocessing-derived unit clauses
    /// (backbone, probe). It encapsulates the proof ID synchronization
    /// between the proof manager and the solver's `next_clause_id` counter,
    /// which otherwise must be manually kept in sync at every call site
    /// (#4631, #4638).
    ///
    /// Returns `true` if level-0 propagation after enqueueing the unit produced
    /// a conflict (i.e., the formula is UNSAT).
    pub(crate) fn learn_derived_unit(&mut self, unit: Literal, hints: &[u64]) -> bool {
        self.enqueue_derived_unit(unit, hints);

        // Propagate the new unit at level 0.
        if let Some(l0_conflict) = self.search_propagate() {
            self.record_level0_conflict_chain(l0_conflict);
            return true;
        }
        false
    }
}
