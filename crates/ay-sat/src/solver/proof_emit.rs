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

impl Solver {
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
    pub(crate) fn proof_emit_add_prechecked(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        // Soundness-triage tripwire (--sat-ab-triage-clause "d1,d2,..." DIMACS
        // lits): dump the live DB the moment this exact clause is emitted.
        {
            use std::sync::OnceLock;
            static TARGET: OnceLock<Option<Vec<i64>>> = OnceLock::new();
            let target = TARGET.get_or_init(|| {
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
        #[cfg(debug_assertions)]
        self.assert_proof_mode_stable();

        #[cfg(debug_assertions)]
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG: previous prechecked clause (id={:?}) was never forward-checked",
            self.cold.pending_forward_check
        );

        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add(clause, hints, kind)?
        } else {
            0
        };

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

        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_with_decompose_context(clause, hints, kind, context)?
        } else {
            0
        };

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
    pub(crate) fn proof_emit_bounded_terminal_rup(
        &mut self,
        hints: &[u64],
        deadline: Option<Instant>,
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
            manager.emit_bounded_empty_rup_step(hints, deadline)?
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

        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_sr(clause, witness)?;
        }
        Ok(())
    }

    #[cfg_attr(not(test), allow(dead_code))]
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

        let id = if let Some(ref mut manager) = self.proof_manager {
            manager.emit_add_signed_lrat_hints(clause, hints, kind)?
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

        // Forward checker only tracks non-empty clauses; the empty clause
        // is a protocol-level signal (UNSAT proof completion), not a real
        // clause in the forward checker's database.
        if !clause.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(clause);
            }
        }

        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_delete(clause, clause_id)
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

        if !clause.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(clause);
            }
        }

        if let Some(ref mut manager) = self.proof_manager {
            manager.emit_delete_with_decompose_context(clause, clause_id, context)
        } else {
            Ok(())
        }
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

        let lits = self.arena.literals(clause_idx);
        if !lits.is_empty() {
            if let Some(ref mut checker) = self.cold.forward_checker {
                checker.delete_clause(lits);
            }
        }

        if let Some(ref mut manager) = self.proof_manager {
            let lits = self.arena.literals(clause_idx);
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
