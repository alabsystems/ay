// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final authority boundary for UNSAT results over nested arrays.

use super::*;

impl Executor {
    /// Fail closed on an UNSAT result for an active nested-array problem.
    ///
    /// SAT remains available through model validation; only an UNSAT lacking
    /// one of the checked authorities below is quarantined.
    ///
    /// ORIGIN (`53e9ac3c07`): a confirmed false `unsat` over
    /// `(Array Int (Array Int Int))` in the QF_ALIA/AUFLIA combination,
    /// `repros/cs_stateful-1.i_2.MINIMIZED.smt2`. That reproducer's SOURCE
    /// defect -- a vacuously true `all()` over a GC-compacted, zero-length
    /// pending-theory-conflict slice -- was root-caused and fixed at
    /// `f978212a6f` + `7272612d89`, and the repro now fails closed to timeout
    /// WITHOUT reaching this gate (Round 20 of
    /// the development design notes;
    /// re-measured 2026-09-06 on current main: `interrupted`/`timeout`, no
    /// degrade warning). This is therefore no longer a workaround for one bug.
    /// It is the ENFORCEMENT POINT of the authority ladder below -- what lets a
    /// nested-array UNSAT publish on checked evidence rather than on trust.
    ///
    /// Do NOT answer a withheld verdict by widening the gate. Every narrowing
    /// that shipped bought its verdicts with an independently checked
    /// authority: the ho-seq unfold marker (`7479b26878`), the entailed-residue
    /// rescue (`6d687da43`), the array-to-UF abstraction
    /// (`nested_array_uf_abstraction.rs`: a strict-proof refutation of a
    /// witnessed pure renaming that drops every array axiom, declared array
    /// carriers renamed too, plus independently checked ground axiom instances
    /// since #nested-array-checked-rung), the exact finite
    /// Bool/BV theorem (`233ab32da2`)
    /// and the nested-array-free justification marker (this file's third
    /// consume-once arm), whose obligation was MEASURED array-free on all eight
    /// AUFLIRA nasa files it converts (see
    /// the development design notes).
    /// The exact finite-expansion theorem joined them with
    /// #nested-array-quarantine-datatype-fields: b79271632 certified MODEL_CHECKER_CONSUMER's
    /// `nested_premise_false_unsat` on it while that row's declared carriers
    /// still read as flat, and the theorem re-expands the public roots and
    /// checks an elementary ground contradiction with no theory solver. It
    /// admits a directly nested UNSAT that carries it just the same (pinned
    /// with its negative twins in this module's tests).
    /// Bypassing the gate outright was measured once, on the
    /// 41-instance CHC/Solidity shard that produced 337 quarantine events, and
    /// converted ZERO files
    /// (the development design notes).
    /// The class this still withholds is the one whose refutation reconstructs
    /// to a bare `(step t0 (cl) :rule trust)`, which `--self-check` rejects --
    /// see the quantified pin in `executor_tests::array_soundness`.
    ///
    /// Nested means nested through any carrier: `StaticFeatures` resolves
    /// declared datatype fields, so `(Array I Row)` with an array field in
    /// `Row` is gated exactly like `(Array I (Array J E))`. Before that, a
    /// declared record carrier bypassed this gate: the record-boxed twin of the
    /// quantified pin published `unsat` on `discharged-trust` alone (a fresh
    /// executor re-running the same combination), and a record-boxed form of
    /// the binder-capture defect fixed at `3fac3f55e` published a WRONG `unsat`
    /// the same way (#nested-array-quarantine-datatype-fields; pinned in this
    /// module's tests). A boxed UNSAT now leaves only on the authorities
    /// below, exactly as its directly nested twin does.
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
        let trusted_simplifier_refutation = std::mem::take(&mut self.simplifier_refutation_unsat);
        let trusted_justified_array_free =
            std::mem::take(&mut self.nested_array_free_justification_unsat);

        if !result.is_unsat() || !StaticFeatures::collect(&self.ctx.terms, roots).has_nested_arrays
        {
            return result;
        }

        // All four markers prove the verdict was reached WITHOUT the guarded
        // nested-array combination: the first two because an equivalence
        // eliminated the array structure before the authoritative array-free
        // solve, the third because the quantifier loop's justification registry
        // independently re-decided a NESTED-ARRAY-FREE obligation on a
        // disposable executor and accepted it only against a checked
        // exact-query certificate (see
        // `Justification::publish_if_established`), the fourth because the
        // quantifier preprocessing pipeline refuted the window by rewriting
        // alone before any theory ran (it is reachable only in the shed
        // posture, where its passes are the trusted preprocessing that posture
        // opts into). They are consume-once so none can leak into a later
        // query.
        if trusted_row_reduction
            || trusted_ho_seq_unfold
            || trusted_justified_array_free
            || trusted_simplifier_refutation
        {
            return result;
        }

        if self.nested_array_unsat_has_current_authority(hard) {
            return result;
        }

        self.reject_unverified_nested_array_unsat()
    }

    /// Check proof/sidecar, finite-expansion theorem, residue, array-to-UF
    /// abstraction, and exact-source authorities in order.
    ///
    /// Exact-source sealing stays last because the preceding checks may intern
    /// terms and would immediately stale its complete term-store snapshot.
    fn nested_array_unsat_has_current_authority(&mut self, hard: Option<&[TermId]>) -> bool {
        if self.nested_array_unsat_proof_authority_is_current()
            || self.nested_array_unsat_finite_expansion_theorem_is_current()
        {
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

        // Refuting the array-to-UF abstraction of the whole hard problem
        // refutes the problem itself: the abstraction drops every array axiom
        // and adds back only checked axiom instances, and its renaming witness
        // and instances are re-checked against the exact snapshot the
        // refutation's strict proof is sealed to (see
        // `nested_array_uf_abstraction.rs`).
        if hard.is_some_and(|hard| self.nested_array_uf_abstraction_unsat(hard)) {
            tracing::debug!(
                "nested-array UNSAT re-derived from a strict-proof array-to-UF abstraction; retained"
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

#[cfg(test)]
mod tests;
