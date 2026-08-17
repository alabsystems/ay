// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact public-query authority for final internal proof reconstruction.

use super::*;

/// Move-only outer-query authority parked while the named-core completeness
/// rescue performs a nested plain solve on the stripped assertion view.
///
/// The nested solve is verdict work, not a new public query.  In particular,
/// an inner `unknown` must not permanently revoke the still-live outer epoch.
/// Keeping the fields out of the executor during that solve also prevents the
/// inner pipeline from accidentally borrowing authority for the full authored
/// query while only the unnamed base is installed.
pub(in crate::executor) struct ParkedPlainQueryAuthority {
    epoch: UnsatQueryEpoch,
    provenance: crate::executor::theories::solve_harness::ProofProblemAssertionProvenance,
}

impl Executor {
    /// Park an exact, assumption-free public-query epoch before the plain
    /// named-core rescue enters a nested solve.
    ///
    /// `authored_assertions` is the assertion vector saved by the redirect
    /// before it installed its stripped working view.  Refuse to park unless
    /// it is byte-for-byte the immutable epoch scope and all publication
    /// provenance is current.  A failed authentication leaves every field in
    /// place so the caller can continue fail-closed without manufacturing a
    /// token.
    pub(in crate::executor) fn park_plain_query_authority_for_named_core_rescue(
        &mut self,
        authored_assertions: &[TermId],
    ) -> Option<ParkedPlainQueryAuthority> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        let provenance = self.proof_problem_assertion_provenance.as_ref()?;
        let public_assumptions = epoch.assumptions.as_deref()?;
        if !epoch.is_current(self)
            || !public_assumptions.is_empty()
            || epoch.assertions != authored_assertions
            || !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
            || provenance.original_problem_assertions != epoch.assertions
            || self.last_unsat_certificate.is_some()
            || self.pending_nested_array_bool_bv_unsat.is_some()
        {
            return None;
        }

        Some(ParkedPlainQueryAuthority {
            epoch: self.unsat_query_epoch.take()?,
            provenance: self.proof_problem_assertion_provenance.take()?,
        })
    }

    /// Restore a parked outer epoch only after the redirect has reinstated the
    /// exact authored assertion vector.  Nested artifacts and authority are
    /// discarded unconditionally; if any epoch/source/term invariant changed,
    /// restoration declines and the outer result remains uncertifiable.
    pub(in crate::executor) fn restore_plain_query_authority_after_named_core_rescue(
        &mut self,
        parked: ParkedPlainQueryAuthority,
    ) -> bool {
        self.unsat_query_epoch = None;
        self.proof_problem_assertion_provenance = None;
        self.last_unsat_certificate = None;
        self.pending_nested_array_bool_bv_unsat = None;

        let public_assumptions = parked.epoch.assumptions.as_deref();
        if !parked.epoch.is_current(self)
            || public_assumptions != Some(&[][..])
            || parked.epoch.assertions != self.ctx.assertions
            || !parked.epoch.declared_extension.is_empty()
            || !parked.epoch.declared_extension_entries.is_empty()
            || parked.epoch.declared_extension_objectives.is_some()
            || parked.epoch.declared_extension_objective_entries.is_some()
            || parked.provenance.original_problem_assertions != parked.epoch.assertions
        {
            return false;
        }

        self.unsat_query_epoch = Some(parked.epoch);
        self.proof_problem_assertion_provenance = Some(parked.provenance);
        true
    }

    /// Return the exact authored assertions for an assumption-free public
    /// query after a named-core redirect has restored the assertion stack.
    ///
    /// Unlike the general internal-certificate helper below, this deliberately
    /// tolerates the named-core transaction's surviving *tracking* assumption
    /// slot. Those terms add no authority: every one must be an exact epoch
    /// assertion (or an equivalence-exact named rewrite of one), the public
    /// query itself must have no assumptions, and the returned scope is still
    /// only the immutable epoch assertions. Core bookkeeping remains intact.
    pub(in crate::executor) fn authenticated_plain_query_assertions_after_named_core_redirect(
        &self,
    ) -> Option<Vec<TermId>> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        let public_assumptions = epoch.assumptions.as_deref()?;
        if !epoch.is_current(self)
            || !public_assumptions.is_empty()
            || epoch.assertions != self.ctx.assertions
            || !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
            || self
                .proof_problem_assertion_provenance
                .as_ref()
                .is_none_or(|provenance| provenance.original_problem_assertions != epoch.assertions)
        {
            return None;
        }

        if let Some(tracking_assumptions) = self.last_assumptions.as_deref() {
            if !tracking_assumptions.is_empty()
                && (!self.produce_unsat_cores_enabled()
                    || self.last_core_term_to_name.as_ref().is_none_or(|names| {
                        tracking_assumptions.iter().any(|term| {
                            !names.contains_key(term)
                                || !self.query_authorizes_assumption(
                                    *term,
                                    &epoch.assertions,
                                    public_assumptions,
                                )
                        })
                    }))
            {
                return None;
            }
        }
        Some(epoch.assertions.clone())
    }

    /// Return assertions plus bound assumptions only while the public epoch,
    /// term entries, source provenance, and solver-visible assumption slot all
    /// agree exactly. Pareto extensions remain outside this certificate schema.
    pub(in crate::executor) fn authenticated_unsat_query_roots_for_internal_certificate(
        &self,
    ) -> Option<Vec<TermId>> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        if !epoch.is_current(self)
            || !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
            || self
                .proof_problem_assertion_provenance
                .as_ref()
                .is_none_or(|provenance| provenance.original_problem_assertions != epoch.assertions)
        {
            return None;
        }
        let assumptions = epoch.assumptions.as_deref()?;
        if self.last_assumptions.as_deref() != Some(assumptions)
            && !(assumptions.is_empty() && self.last_assumptions.is_none())
        {
            return None;
        }
        let count = epoch.assertions.len().checked_add(assumptions.len())?;
        if count > ay_proof::MAX_BV_LIA_QUERY_ROOTS {
            return None;
        }
        let mut roots = Vec::new();
        roots.try_reserve_exact(count).ok()?;
        roots.extend_from_slice(&epoch.assertions);
        roots.extend_from_slice(assumptions);
        Some(roots)
    }

    /// Named-core solving temporarily widens the assumption slot. Refresh only
    /// after the outer wrapper restored the exact public scope and only when the
    /// caller required the translated strict artifact itself.
    pub(in crate::executor) fn refresh_internal_certificate_after_named_core_redirect(&mut self) {
        if self.strict_unsat_presentation_required() {
            self.refresh_authenticated_bv_lia_internal_certificate_for_publication();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
    use ay_core::Sort;

    fn plain_query_fixture() -> (Executor, Vec<TermId>) {
        let commands = ay_frontend::parse(
            "(set-option :produce-proofs true)\n\
             (declare-const parked_epoch_base Bool)\n\
             (assert parked_epoch_base)",
        )
        .expect("plain-query fixture parses");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("plain-query fixture elaborates");
        let authored = executor.ctx.assertions.clone();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        (executor, authored)
    }

    #[test]
    fn named_core_rescue_restores_only_exact_outer_authority() {
        let (mut executor, authored) = plain_query_fixture();
        executor.ctx.assertions.clear();
        let parked = executor
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .expect("the saved authored stack authenticates while the working stack is stripped");
        assert!(executor.unsat_query_epoch.is_none());
        assert!(executor.proof_problem_assertion_provenance.is_none());

        // Reproduce the inner Unknown finalizer that originally destroyed the
        // outer fields, then leave forged nested authority behind.  Restore
        // must discard those artifacts rather than merge them with the token.
        assert_eq!(
            executor.finalize_unknown_publication(SolveResult::Unknown),
            SolveResult::Unknown
        );
        let nested = executor
            .ctx
            .terms
            .mk_var("nested_rescue_artifact", Sort::Bool);
        let mut nested_epoch = parked.epoch.clone();
        nested_epoch.assertions = vec![nested];
        executor.unsat_query_epoch = Some(nested_epoch);
        executor.proof_problem_assertion_provenance = Some(
            ProofProblemAssertionProvenance::passthrough(&[nested], &[nested]),
        );

        executor.ctx.assertions.clone_from(&authored);
        assert!(executor.restore_plain_query_authority_after_named_core_rescue(parked));
        assert_eq!(
            executor.authenticated_plain_query_assertions_after_named_core_redirect(),
            Some(authored)
        );
        assert!(executor.last_unsat_certificate.is_none());
        assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
    }

    #[test]
    fn named_core_rescue_restore_rejects_stale_query_or_source() {
        let (mut stale_query, authored) = plain_query_fixture();
        stale_query.ctx.assertions.clear();
        let parked = stale_query
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .expect("fresh query authority parks");
        stale_query.advance_query_authority_epoch();
        stale_query.ctx.assertions = authored;
        assert!(!stale_query.restore_plain_query_authority_after_named_core_rescue(parked));
        assert!(stale_query.unsat_query_epoch.is_none());
        assert!(stale_query.proof_problem_assertion_provenance.is_none());

        let (mut stale_source, authored) = plain_query_fixture();
        stale_source.ctx.assertions.clear();
        let parked = stale_source
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .expect("fresh source authority parks");
        stale_source
            .ctx
            .process_command(&ay_frontend::Command::Push(1))
            .expect("push changes the source-context stamp");
        stale_source.ctx.assertions = authored;
        assert!(!stale_source.restore_plain_query_authority_after_named_core_rescue(parked));
        assert!(stale_source.unsat_query_epoch.is_none());
        assert!(stale_source.proof_problem_assertion_provenance.is_none());
    }

    #[test]
    fn named_core_rescue_restore_rejects_reused_root_entry() {
        let (mut executor, _) = plain_query_fixture();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let replaceable = executor
            .ctx
            .terms
            .mk_var("parked_epoch_replaceable", Sort::Bool);
        executor.ctx.assertions.push(replaceable);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let authored = executor.ctx.assertions.clone();
        executor.ctx.assertions.clear();
        let parked = executor
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .expect("fresh term entries park");

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_var("parked_epoch_replacement", Sort::Bool);
        assert_eq!(replacement, replaceable, "the canary reuses the term id");
        executor.ctx.assertions = authored;
        assert!(!executor.restore_plain_query_authority_after_named_core_rescue(parked));
        assert!(executor.unsat_query_epoch.is_none());
        assert!(executor.proof_problem_assertion_provenance.is_none());
    }

    #[test]
    fn named_core_rescue_park_rejects_unbound_assumed_or_forged_scope() {
        let (mut unbound, authored) = plain_query_fixture();
        // Re-open an epoch without binding its public assumption slot.
        unbound.begin_public_solve(false);
        unbound.ctx.assertions.clear();
        assert!(unbound
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .is_none());
        assert!(unbound.unsat_query_epoch.is_some());
        assert!(unbound.proof_problem_assertion_provenance.is_some());

        let (mut assumed, authored) = plain_query_fixture();
        let assumption = assumed.ctx.terms.mk_not_raw(authored[0]);
        // The fixture's empty assumption set is immutable once bound; start a
        // fresh public decision to exercise a genuinely assumption-bearing
        // epoch rather than a rejected rebind of the old one.
        assumed.begin_public_solve(false);
        assumed.bind_unsat_query_assumptions(&[assumption]);
        assumed.ctx.assertions.clear();
        assert!(assumed
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .is_none());
        assert!(assumed.unsat_query_epoch.is_some());
        assert!(assumed.proof_problem_assertion_provenance.is_some());

        let (mut forged, authored) = plain_query_fixture();
        let foreign = forged.ctx.terms.mk_var("parked_epoch_foreign", Sort::Bool);
        forged
            .proof_problem_assertion_provenance
            .as_mut()
            .expect("public solve installs provenance")
            .original_problem_assertions = vec![foreign];
        forged.ctx.assertions.clear();
        assert!(forged
            .park_plain_query_authority_for_named_core_rescue(&authored)
            .is_none());
        assert!(forged.unsat_query_epoch.is_some());
        assert!(forged.proof_problem_assertion_provenance.is_some());
    }
}
