// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Authenticate the source-closed proof premise inventory for one exact
    /// plain public query.
    ///
    /// `exact_roots` and `source_context` originate from an opaque API binding
    /// minted immediately after parsing on this same solver. Raw rebuilt-source
    /// term ids need not equal folded canonical roots; they enter the returned
    /// closure only through the proof provenance installed for this exact query
    /// epoch. Callers must still narrow to the actually checked `Assume` set and
    /// independently recheck the resulting bundle.
    pub(crate) fn exact_plain_query_source_closure(
        &self,
        exact_roots: &[TermId],
        source_context: &SourceContextStamp,
    ) -> Option<Vec<TermId>> {
        let epoch = self.checked_sat_refutation_query_epoch()?;
        if epoch.assertions.as_slice() != exact_roots
            || epoch.assumptions.as_deref() != Some(&[])
            || &epoch.source_context_stamp != source_context
            || self.ctx.assertions.as_slice() != exact_roots
            || self.ctx.source_context_stamp() != *source_context
        {
            return None;
        }
        let provenance = self.proof_problem_assertion_provenance.as_ref()?;
        if provenance.original_problem_assertions.as_slice() != exact_roots {
            return None;
        }
        let mut closure = self.proof_export_scope_assertions();
        let mut seen = HashSet::default();
        closure.retain(|term| seen.insert(*term));
        (!closure.is_empty()).then_some(closure)
    }

    /// Whether the active solve is a public exact-query epoch whose eventual
    /// UNSAT publication must carry authored-scope certification.
    ///
    /// Strict proof checking is the primary lane; sealed independent fallback
    /// certificates remain explicitly classified. Internal disposable solves
    /// have no epoch and cannot borrow this publication requirement as
    /// authority.
    pub(crate) fn active_unsat_query_requires_strict_proof(&self) -> bool {
        // #cert-item-3: the solve's ROLE is DECLARED, not inferred.
        //
        // This used to be `self.unsat_query_epoch.is_some()` alone — "an epoch
        // exists, therefore this decision is public". That inference is what
        // billed every disposable sub-query at public rates: the CHC portfolio
        // opens an epoch per internal lemma exactly as it does for the user's
        // question, so the two were indistinguishable here.
        //
        // The epoch conjunct is RETAINED, not replaced: no epoch still means no
        // publication authority. The role is an ADDITIONAL requirement, and it
        // is fail-safe — `QueryPublicationRole::default()` is `Published`, and
        // every ay-chc call site currently declares `Published` (the shared
        // executor lanes deliberately so: they are reachable from the PDR
        // safety verifier, where a false UNSAT becomes a false `Safe`). So this
        // is behaviour-identical today by construction, and stays that way
        // until a caller is individually audited and declares otherwise.
        self.unsat_query_epoch.is_some()
            && matches!(
                self.query_publication_role.get(),
                crate::executor::query_role::QueryPublicationRole::Published
            )
    }

    /// The EXACT authored assertion vector the active public UNSAT epoch was
    /// opened with — the vector [`Self::authenticate_unsat_query_scope`]
    /// requires an installed proof provenance to equal.
    ///
    /// Read-only, and deliberately sourced from the epoch rather than from
    /// `ctx.assertions`: the working set is rewritten by preprocessing and
    /// appended to by the demand lane, so it is not the thing the authenticator
    /// compares against. Used by #quantified-trace-arming, whose retry has to
    /// install the provenance that `begin_public_solve` self-gated away while
    /// the solve was shedding.
    pub(in crate::executor) fn unsat_query_epoch_authored_assertions(&self) -> Option<Vec<TermId>> {
        self.unsat_query_epoch
            .as_ref()
            .map(|epoch| epoch.assertions.clone())
    }

    /// Consume the one-shot capability for the immediately preceding verdict.
    pub(crate) fn take_unsat_certificate(&mut self) -> Option<UnsatCertificate> {
        self.pending_nested_array_bool_bv_unsat = None;
        let certificate = self.last_unsat_certificate.take()?;
        let epoch = self.unsat_query_epoch.as_ref()?;
        let bound_assumptions = epoch.assumptions.as_deref()?;
        let current = match &certificate.0 {
            UnsatCertificateKind::StrictProof(scope)
            | UnsatCertificateKind::DischargedTrust(scope) => scope.is_current(self),
            UnsatCertificateKind::CheckedSatRefutation { checked, scope } => {
                // Three admissible shapes, strictest first:
                // 1. the solver solved with exactly the bound assumptions;
                // 2. no assumptions anywhere;
                // 3. the FOLDED named-assumption rescue: the redirect solved
                //    `roots = base ++ A` with an empty assumption vector and
                //    bound the epoch the same way, while the outer
                //    `check-sat-assuming A` leaves `last_assumptions = A`.
                //    Sound because `checked.is_current_for` below
                //    authenticates the FULL root vector — including that
                //    exact `A` tail — so the sidecar's theorem IS
                //    `base ∧ A ⊢ ⊥`, precisely the claim the outer command
                //    publishes. The tail comparison is positional and exact;
                //    a permuted, widened, or truncated `A` does not match.
                let solver_assumptions_match = self.last_assumptions.as_deref()
                    == Some(bound_assumptions)
                    || (bound_assumptions.is_empty()
                        && match self.last_assumptions.as_deref() {
                            None => true,
                            Some(last) => !last.is_empty() && epoch.assertions.ends_with(last),
                        });
                let legs = [
                    ("scope", scope.is_current(self)),
                    ("epoch", epoch.is_current(self)),
                    (
                        "ext",
                        epoch.declared_extension.is_empty()
                            && epoch.declared_extension_entries.is_empty()
                            && epoch.declared_extension_objectives.is_none()
                            && epoch.declared_extension_objective_entries.is_none(),
                    ),
                    ("solver_assumptions", solver_assumptions_match),
                    (
                        "provenance",
                        self.proof_problem_assertion_provenance
                            .as_ref()
                            .is_some_and(|provenance| {
                                provenance.original_problem_assertions == epoch.assertions
                            }),
                    ),
                    (
                        "checked_current",
                        checked.is_current_for(
                            &epoch.authority_epoch,
                            &epoch.source_context_stamp,
                            &epoch.assertions,
                            bound_assumptions,
                        ),
                    ),
                ];
                let all = legs.iter().all(|(_, ok)| *ok);
                if !all {
                    probe_cert_reject(|| {
                        format!("take_unsat_certificate CheckedSatRefutation NOT current: {legs:?}")
                    });
                }
                all
            }
            UnsatCertificateKind::CheckedBoolBv(checked) => checked.is_current(self),
            UnsatCertificateKind::CheckedUfLeafBoolBv(checked) => checked.is_current(self),
            UnsatCertificateKind::CheckedBvLia(checked) => checked.is_current(self),
            // The exact semantic family, all seven arms. Each used to spell
            // out `scope_is_current() && evidence.is_current(self)`, which is
            // literally the body of `checked_exact_semantic_is_current` — one
            // definition now, so a new theorem cannot be admitted here under a
            // currentness rule the publication funnel does not also apply.
            UnsatCertificateKind::CheckedExactExists(_)
            | UnsatCertificateKind::CheckedExactForallExists(_)
            | UnsatCertificateKind::CheckedExactClosedForall(_)
            | UnsatCertificateKind::CheckedExactClosedSentence(_)
            | UnsatCertificateKind::CheckedExactForallUfGround(_)
            | UnsatCertificateKind::CheckedExactFiniteExpansion(_)
            | UnsatCertificateKind::CheckedExactRmDomainExpansion(_) => {
                certificate.checked_exact_semantic_is_current(self)
            }
            // #proof-capability B3 — the raw token dies the instant any proof
            // demand appears: consumption re-requires ACTIVE shedding, so the
            // carve-out cannot outlive the mode that authorized it, and a
            // future edit that widens the minting gate still cannot publish a
            // raw UNSAT into a certified-mode session.
            UnsatCertificateKind::CompetitionRaw(scope) => {
                self.competition_shedding_active()
                    && scope.is_current_with_provenance_policy(self, false)
            }
        };
        current.then_some(certificate)
    }
}
