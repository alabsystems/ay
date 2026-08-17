// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Premise-forced instance records for checked quantified refutations.

use super::*;

impl Executor {
    /// Register the qpf premise-forced instance for the OUTER
    /// checked-SAT-refutation sidecar (#ppp-c7, L2).
    ///
    /// Called only AFTER the disposable checked ground solve independently
    /// certified `body[binders := literals]` UNSAT. Records `{quantifier,
    /// values, instance, asserted}` — the raw exact substitution the strict
    /// `forall_inst` validator replays, plus the simplified spelling the
    /// lane refuted — for `sealed_instance_root_derivations` to seal into a
    /// c7 instance root. The record is a HINT: sealing independently
    /// replays the substitution and the per-disjunct model-free `false`
    /// verdicts, and every emitted chain step is re-derived by the strict
    /// checker.
    ///
    /// The refutation-driven RE-SOLVE this registration was designed to
    /// feed (the `try_bv_mbqi_refinement` pattern: push the entailed
    /// instance, re-solve the public query, mint the sidecar from the outer
    /// trace) is deliberately NOT performed yet. Measured at this HEAD, the
    /// UFBV route's trace carries original bit-blast gate clauses over SAT
    /// variables absent from `var_to_term` (2-3-literal clauses from
    /// variable 4 up, with only the assertion-level atoms mapped), so the
    /// sidecar can never mint from that trace REGARDLESS of the unit
    /// channels — the named P3b "bit-blast UnmappedVariable" class, scoped
    /// out as its own slice. Re-solving today would mutate the outer
    /// verdict bookkeeping (a guarded lane invariant:
    /// `qpf_probe_refutes_only_a_verified_concrete_instance_and_preserves_outer_state`)
    /// for zero mintable artifact. Gated on the campaign kill switch: with
    /// `--no-quant-unit-authority` nothing is recorded (byte-identical
    /// baseline).
    pub(super) fn qpf_register_premise_forced_instance(
        &mut self,
        quantifier: TermId,
        vars: &[(String, ay_core::Sort)],
        body: TermId,
        literal_subst: &HashMap<String, TermId>,
        asserted: TermId,
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        let Some(values) = vars
            .iter()
            .map(|(name, _)| literal_subst.get(name).copied())
            .collect::<Option<Vec<TermId>>>()
        else {
            return;
        };
        let Some(instance) =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, literal_subst)
        else {
            return;
        };
        self.qpf_premise_forced_instance_records.push(
            crate::executor::QpfPremiseForcedInstanceRecord {
                quantifier,
                values,
                instance,
                asserted,
            },
        );
    }
}
