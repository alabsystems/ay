// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final authority boundary for UNSAT results over nested arrays.

use super::*;

impl Executor {
    /// Fail closed on an UNSAT result for an active nested-array problem.
    ///
    /// The QF_ALIA/AUFLIA combination has a confirmed false-UNSAT reproducer
    /// over `(Array Int (Array Int Int))`. SAT remains available through model
    /// validation; only an UNSAT lacking one of the checked authorities below
    /// is quarantined.
    ///
    /// `hard` is the caller-authored hard-assertion snapshot only when the
    /// verdict rests on those assertions alone. Assumption and optimization
    /// boundaries pass `None`, which disables the entailed-residue rescue.
    pub(in crate::executor) fn quarantine_unverified_nested_array_unsat(
        &mut self,
        roots: &[TermId],
        hard: Option<&[TermId]>,
        result: SolveResult,
    ) -> SolveResult {
        // The final quarantine is the sole owner of this affine handoff.
        self.pending_nested_array_bool_bv_unsat = None;
        let trusted_row_reduction = std::mem::take(&mut self.nested_array_row_reduction_unsat);
        let trusted_ho_seq_unfold = std::mem::take(&mut self.ho_seq_unfold_array_free_unsat);

        if !result.is_unsat() || !StaticFeatures::collect(&self.ctx.terms, roots).has_nested_arrays
        {
            return result;
        }

        // Both markers prove the guarded array structure was eliminated by an
        // equivalence before the authoritative array-free solve. They are
        // consume-once so neither can leak into a later query.
        if trusted_row_reduction || trusted_ho_seq_unfold {
            return result;
        }

        if self.nested_array_unsat_has_current_authority(hard) {
            return result;
        }

        self.reject_unverified_nested_array_unsat()
    }

    /// Check proof/sidecar, residue, and exact-source authorities in order.
    ///
    /// Exact-source sealing stays last because the preceding checks may intern
    /// terms and would immediately stale its complete term-store snapshot.
    fn nested_array_unsat_has_current_authority(&mut self, hard: Option<&[TermId]>) -> bool {
        if self.nested_array_unsat_proof_authority_is_current() {
            return true;
        }

        // Refuting a nested-array-free subset of entailed conjuncts refutes the
        // full hard problem without relying on the guarded combination.
        if hard.is_some_and(|hard| {
            nested_array_residue_rescue_enabled() && self.nested_array_free_residue_unsat(hard)
        }) {
            tracing::debug!(
                "nested-array UNSAT re-derived from a nested-array-free entailed residue; retained"
            );
            return true;
        }

        // The Bool/BV authenticator seals the exact finite-array theorem once;
        // the mandatory mint later moves this evidence into the public token.
        match self.prepare_pending_nested_array_bool_bv_unsat() {
            Ok(retained) => retained,
            Err(error) => {
                tracing::debug!(
                    %error,
                    "nested finite-array Bool/BV authority could not be sealed"
                );
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!("nested finite-array quarantine authority declined: {error}")
                });
                false
            }
        }
    }

    fn reject_unverified_nested_array_unsat(&mut self) -> SolveResult {
        self.replace_last_result_with_unknown(UnknownReason::Incomplete);
        self.set_active_solve_phase(
            "array-combination-quarantine",
            "nested-array-unsat-quarantine",
        );
        self.record_unknown_diagnostic(
            UnknownReason::Incomplete,
            "nested-array UNSAT is quarantined pending a trust-free theory-combination proof",
        );
        tracing::warn!(
            "nested-array UNSAT lacked an authoritative theory-combination proof; degrading to Unknown"
        );
        SolveResult::Unknown
    }

    /// Re-derive a quarantined UNSAT from a nested-array-free entailed residue.
    ///
    /// Every retained conjunct is a consequence of a hard assertion and the
    /// filter only weakens that conjunction. A checked UNSAT for the resulting
    /// non-empty strict subset therefore proves the original hard problem
    /// UNSAT, while avoiding the distrusted nested-array combination entirely.
    fn nested_array_free_residue_unsat(&mut self, hard: &[TermId]) -> bool {
        if self.external_stop_reason().is_some()
            || self.in_nested_array_residue_probe
            || self.is_producing_proofs()
        {
            return false;
        }

        let Some(residue) = self.collect_nested_array_free_residue(hard) else {
            return false;
        };
        if self.residue_probe_failures >= RESIDUE_MAX_FAILURES {
            return false;
        }

        let outer_deadline = self.solve_deadline.get();
        let Some(probe_deadline) = Self::residue_sub_deadline(outer_deadline).or(outer_deadline)
        else {
            self.note_failed_residue_probe();
            return false;
        };
        let remaining = probe_deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            self.note_failed_residue_probe();
            return false;
        }
        let budget_ms = u64::try_from(remaining.as_millis())
            .unwrap_or(u64::MAX)
            .max(1);
        let refuted = self
            .checked_exact_unsat_solve(residue.clone(), budget_ms)
            .is_some_and(|checked| checked.consume(self, &residue));
        if !refuted {
            self.note_failed_residue_probe();
        }
        refuted
    }

    /// Build a bounded, deduplicated strict subset with no nested arrays.
    fn collect_nested_array_free_residue(&mut self, hard: &[TermId]) -> Option<Vec<TermId>> {
        let mut conjuncts = Vec::new();
        for &assertion in hard {
            super::super::quantifier_loop::collect_entailed_conjuncts(
                &mut self.ctx.terms,
                assertion,
                0,
                MAX_RESIDUE_CONJUNCTS,
                &mut conjuncts,
            );
            if conjuncts.len() > MAX_RESIDUE_CONJUNCTS {
                return None;
            }
        }

        let mut residue = Vec::with_capacity(conjuncts.len());
        let mut seen = ay_core::kani_compat::DetHashSet::<TermId>::default();
        let mut dropped_any = false;
        for conjunct in conjuncts {
            if !seen.insert(conjunct) {
                continue;
            }
            if StaticFeatures::collect(&self.ctx.terms, &[conjunct]).has_nested_arrays {
                dropped_any = true;
            } else {
                residue.push(conjunct);
            }
        }
        (!residue.is_empty() && dropped_any).then_some(residue)
    }

    fn note_failed_residue_probe(&mut self) {
        self.residue_probe_failures = self.residue_probe_failures.saturating_add(1);
    }

    /// Give the optional residue probe a quarter of the remaining solve budget,
    /// capped at the independently audited per-probe maximum.
    fn residue_sub_deadline(outer: Option<Instant>) -> Option<Instant> {
        let now = Instant::now();
        let budget = match outer {
            Some(deadline) => (deadline.saturating_duration_since(now) / RESIDUE_BUDGET_SHARE)
                .min(RESIDUE_MAX_BUDGET),
            None => RESIDUE_MAX_BUDGET,
        };
        now.checked_add(budget)
    }
}
