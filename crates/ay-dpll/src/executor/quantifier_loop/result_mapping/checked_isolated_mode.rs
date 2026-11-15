// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which UNSAT certificate classes each checked isolated probe admits.

use ay_core::TermId;

use super::super::{
    CheckedExactUnsat, CheckedGroundDecision, CheckedGroundKind, CheckedGroundSat,
    CheckedGroundUnsat, CheckedIsolatedMode,
};
use crate::executor::unsat_cert::{ProbeUnsatAuthority, UnsatCertificate};
use crate::executor::Executor;
use crate::logic_detection::LogicCategory;

impl CheckedIsolatedMode {
    /// Whether the probe's one-shot UNSAT token is authority for this mode,
    /// given whether the enclosing solve sheds proof work and whether it
    /// accepts a `discharged-trust` refutation as grant authority
    /// ([`Executor::accepts_discharged_trust_grant`]).
    pub(super) fn admits_unsat(
        self,
        certificate: &UnsatCertificate,
        enclosing_sheds: bool,
        enclosing_accepts_trust: bool,
    ) -> bool {
        if certificate.probe_authority() == ProbeUnsatAuthority::DischargedTrust
            && !self.admits_discharged_trust(enclosing_accepts_trust)
        {
            return false;
        }
        match self {
            Self::StrictExactUnsat => certificate.strict_proof_verified(),
            Self::GroundDecision
            | Self::ExactUnsat
            | Self::ExactUnsatWithoutTrustDischarge
            | Self::SatAuthorityDecision => certificate.confirms_checked_unsat_emission(),
            Self::ModelCheckDecision => {
                certificate.confirms_checked_unsat_emission()
                    || (self.admits_shed_raw_unsat(enclosing_sheds)
                        && certificate.is_competition_raw())
            }
        }
    }

    /// Whether a `discharged-trust` UNSAT (its holes discharged by a fresh
    /// executor running the SAME code, `ProbeUnsatAuthority::DischargedTrust`)
    /// is authority for this mode, given whether the enclosing solve accepts
    /// that class as grant authority. It is the one rule
    /// [`Self::admits_unsat`] applies to such a token, whatever presentation
    /// carries it (the bare discharge, or an exact theorem sealing one).
    ///
    /// A sat-authority UNSAT DECIDES that a quantified conjunct holds, and a
    /// published `sat` rests on that decision; a re-solve by the same engine
    /// is not a check of it.
    ///
    /// * The model check's auxiliary solves ([`Self::ModelCheckDecision`])
    ///   refuse it at every rigor: their grant makes the publication gate
    ///   defer without evaluating the emitted model at all. A refused
    ///   refutation leaves the quantifier undetermined, and the pass declines
    ///   to the gate, which decides the conjunct against the emitted model.
    /// * Every other sat-authority probe ([`Self::SatAuthorityDecision`]: the
    ///   gate's confirming obligations, the SAT-certificate producers) admits
    ///   it exactly where a directly published `unsat` on the same class is
    ///   admitted: only while the enclosing solve accepts it as grant
    ///   authority (never under strict proofs or `--rigor strict`), and then
    ///   the consumer learns the class so it can record it.
    ///
    /// A refused UNSAT leaves the obligation undecided, which every such
    /// consumer treats as "not confirmed". Probes whose UNSAT refutes
    /// (publishes `unsat`, or fails a `sat` closed) keep the class, as the
    /// posture's `unsat` admission does.
    pub(super) const fn admits_discharged_trust(self, enclosing_accepts_trust: bool) -> bool {
        match self {
            Self::GroundDecision | Self::ExactUnsat => true,
            Self::SatAuthorityDecision => enclosing_accepts_trust,
            Self::StrictExactUnsat
            | Self::ExactUnsatWithoutTrustDischarge
            | Self::ModelCheckDecision => false,
        }
    }

    /// Whether the probe decides a ground vector in both directions (as
    /// opposed to the UNSAT-only exact modes).
    pub(super) fn is_ground_decision(self) -> bool {
        matches!(
            self,
            Self::GroundDecision | Self::ModelCheckDecision | Self::SatAuthorityDecision
        )
    }

    /// Whether this mode also admits the shed-mode raw UNSAT, given whether
    /// the enclosing solve sheds proof work.
    ///
    /// Only the model check's auxiliary solves do, and only under shedding:
    /// the enclosing solve would publish its own UNSAT raw on the same terms
    /// (`certify_unsat_presentation`'s `CompetitionRaw` carve-out), so an
    /// auxiliary refutation carries exactly the trust the posture already
    /// grants a top-level one. With any proof demand in scope this is false
    /// and the mode certifies exactly like [`Self::GroundDecision`].
    pub(super) fn admits_shed_raw_unsat(self, enclosing_sheds: bool) -> bool {
        enclosing_sheds && matches!(self, Self::ModelCheckDecision)
    }
}

impl Executor {
    /// Decide one exact quantifier-free auxiliary vector of the quantified
    /// model check.
    ///
    /// Identical to [`Self::checked_ground_solve`] except for two UNSAT
    /// admissions: a `discharged-trust` refutation is refused
    /// ([`CheckedIsolatedMode::admits_discharged_trust`]), and the shed-mode
    /// raw admission is taken under proof shedding (see
    /// [`CheckedIsolatedMode::admits_shed_raw_unsat`]). The decision is the
    /// same sealed, non-cloneable token and must still be consumed against
    /// its exact roots.
    pub(in crate::executor) fn checked_model_check_solve(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<CheckedGroundDecision> {
        let (scope, outcome, _authority, _evidence) = self.checked_isolated_solve(
            assertions,
            CheckedIsolatedMode::ModelCheckDecision,
            budget_ms,
        )?;
        Some(match outcome {
            CheckedGroundKind::Sat => CheckedGroundDecision::Sat(CheckedGroundSat { scope }),
            CheckedGroundKind::Unsat => CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }),
        })
    }

    /// [`Self::checked_model_check_solve`] for a REFUTATION probe, with the
    /// authority class that admitted its UNSAT (`Checked` for a SAT). The mode
    /// refuses `discharged-trust` refutations
    /// ([`CheckedIsolatedMode::admits_discharged_trust`]), so an admitted one
    /// reads `Checked`; the class is still returned so the consumer's own
    /// booking stays a second line, never the only one.
    pub(in crate::executor) fn checked_model_check_solve_classified(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<(CheckedGroundDecision, ProbeUnsatAuthority)> {
        // Mutation seam (`trust_forge`): replace this refutation probe by a
        // forged UNSAT of the `discharged-trust` class, judged by the rule
        // `admits_unsat` applies to a real one. The confirm solve never comes
        // through here.
        #[cfg(test)]
        if super::super::trust_forge::forge_model_check_refutation() {
            let mode = CheckedIsolatedMode::ModelCheckDecision;
            return mode
                .admits_discharged_trust(self.accepts_discharged_trust_grant())
                .then(|| {
                    let scope = super::super::CheckedGroundScope::capture(self, &assertions);
                    (
                        CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }),
                        ProbeUnsatAuthority::DischargedTrust,
                    )
                });
        }
        let (scope, outcome, authority, _evidence) = self.checked_isolated_solve(
            assertions,
            CheckedIsolatedMode::ModelCheckDecision,
            budget_ms,
        )?;
        let decision = match outcome {
            CheckedGroundKind::Sat => CheckedGroundDecision::Sat(CheckedGroundSat { scope }),
            CheckedGroundKind::Unsat => CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }),
        };
        Some((decision, authority))
    }

    /// [`Self::checked_ground_solve`] for a probe whose UNSAT CONFIRMS that a
    /// quantified conjunct holds (the negation of a universal's instance under
    /// the emitted model's pins, a symbolic entailment, a finite table's or a
    /// candidate interpretation's residual, a counterexample lemma), so that a
    /// published `sat` rests on it, with the authority class that admitted an
    /// UNSAT (`Checked` for a SAT) so the consumer records what its
    /// confirmation rests on.
    ///
    /// A `discharged-trust` UNSAT is admitted only where the enclosing solve
    /// accepts that class as grant authority
    /// ([`CheckedIsolatedMode::admits_discharged_trust`]); elsewhere the probe
    /// answers `None`, which such a consumer reads as "not confirmed". SAT
    /// admission is unchanged. The decision is the same sealed, non-cloneable
    /// token and must still be consumed against its exact roots.
    pub(in crate::executor) fn checked_sat_authority_ground_solve(
        &mut self,
        assertions: Vec<TermId>,
        _fallback_category: LogicCategory,
        budget_ms: u64,
    ) -> Option<(CheckedGroundDecision, ProbeUnsatAuthority)> {
        // Mutation seam (`trust_forge`): replace this probe by a forged UNSAT
        // of the `discharged-trust` class, judged by the rule `admits_unsat`
        // applies to a real one.
        #[cfg(test)]
        if super::super::trust_forge::forge_sat_authority_probe() {
            let mode = CheckedIsolatedMode::SatAuthorityDecision;
            return mode
                .admits_discharged_trust(self.accepts_discharged_trust_grant())
                .then(|| {
                    let scope = super::super::CheckedGroundScope::capture(self, &assertions);
                    (
                        CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }),
                        ProbeUnsatAuthority::DischargedTrust,
                    )
                });
        }
        let (scope, outcome, authority, _evidence) = self.checked_isolated_solve(
            assertions,
            CheckedIsolatedMode::SatAuthorityDecision,
            budget_ms,
        )?;
        Some(match outcome {
            CheckedGroundKind::Sat => (
                CheckedGroundDecision::Sat(CheckedGroundSat { scope }),
                ProbeUnsatAuthority::Checked,
            ),
            CheckedGroundKind::Unsat => (
                CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }),
                authority,
            ),
        })
    }

    /// Whether a sat-authority probe REFUTES `assertions` (an admitted UNSAT
    /// consumed against them): `Some(class)` with the class it rests on, or
    /// `None`. For a SAT-certificate producer that confirms each obligation
    /// by such a refutation and books a certificate resting on
    /// `discharged-trust` ([`Self::book_trust_resting_certificate`]).
    pub(in crate::executor) fn sat_authority_refutes(
        &mut self,
        assertions: Vec<TermId>,
        fallback_category: LogicCategory,
        budget_ms: u64,
    ) -> Option<ProbeUnsatAuthority> {
        let (decision, class) = self.checked_sat_authority_ground_solve(
            assertions.clone(),
            fallback_category,
            budget_ms,
        )?;
        match decision {
            CheckedGroundDecision::Unsat(checked) => {
                checked.consume(self, &assertions).then_some(class)
            }
            CheckedGroundDecision::Sat(_) => None,
        }
    }

    /// Book a SAT certificate this query minted on at least one
    /// `discharged-trust` refutation, so the publication gate records the
    /// certificate it defers to as resting on one. `rests_on_trust` is the
    /// producer's own accumulation over the refutations its certificate
    /// consumed.
    pub(in crate::executor) fn book_trust_resting_certificate(&mut self, rests_on_trust: bool) {
        if rests_on_trust {
            self.quantified_gate_probe_budget.record_trust_certificate();
        }
    }

    /// [`Self::checked_exact_unsat_solve`] that refuses the `DischargedTrust`
    /// class: every admitted certificate is checked evidence that does not
    /// rest on a fresh run of the same engine re-deriving `unsat` (strict
    /// proof, independently checked refutation, or exact semantic theorem).
    pub(in crate::executor) fn checked_exact_unsat_solve_without_trust_discharge(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<CheckedExactUnsat> {
        let (scope, outcome, authority, evidence) = self.checked_isolated_solve(
            assertions,
            CheckedIsolatedMode::ExactUnsatWithoutTrustDischarge,
            budget_ms,
        )?;
        matches!(outcome, CheckedGroundKind::Unsat).then_some(CheckedExactUnsat {
            scope,
            authority,
            evidence,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::CheckedIsolatedMode;
    use crate::executor::unsat_cert::{ProbeUnsatAuthority, UnsatCertificate};
    use crate::executor::Executor;
    use crate::executor_types::SolveResult;

    const MODES: [CheckedIsolatedMode; 6] = [
        CheckedIsolatedMode::GroundDecision,
        CheckedIsolatedMode::ExactUnsat,
        CheckedIsolatedMode::StrictExactUnsat,
        CheckedIsolatedMode::ExactUnsatWithoutTrustDischarge,
        CheckedIsolatedMode::ModelCheckDecision,
        CheckedIsolatedMode::SatAuthorityDecision,
    ];

    /// A real certificate for an authored contradiction.
    ///
    /// Checked: `p, (not p)`, certified by whatever checked class the
    /// ordinary funnel mints. Trust-discharged: `(< (abs x) 0)` over `Int`,
    /// outside every independent sidecar's fragment (the bounded Bool/BV lanes
    /// abstract the atom and cannot refute it), with the checked SAT sidecar
    /// withheld and the proof a lone `trust` step, so the token is the one a
    /// fresh-executor re-solve mints (`discharged-trust`).
    fn contradiction_certificate(trust_discharged: bool) -> UnsatCertificate {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        executor.ctx.assertions = if trust_discharged {
            let x = terms.mk_var("mode_contract_x", ay_core::Sort::Int);
            let magnitude = terms.mk_abs(x);
            let zero = terms.mk_int(0.into());
            vec![terms.mk_lt(magnitude, zero)]
        } else {
            let p = terms.mk_var("mode_contract_p", ay_core::Sort::Bool);
            let not_p = terms.mk_not_raw(p);
            vec![p, not_p]
        };
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let raw = executor.check_sat().expect("contradictions solve");
        assert!(
            raw.is_unsat(),
            "trust_discharged={trust_discharged}: {raw:?}"
        );
        if trust_discharged {
            executor.last_checked_sat_refutation = None;
            let mut trust_proof = ay_core::Proof::new();
            trust_proof.add_rule_step(
                ay_core::AletheRule::Trust,
                Vec::new(),
                Vec::new(),
                Vec::new(),
            );
            executor.last_proof = Some(trust_proof);
        }
        let published = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(published.is_unsat(), "trust_discharged={trust_discharged}");
        executor
            .take_unsat_certificate()
            .expect("a published UNSAT mints its token")
    }

    /// A REAL `discharged-trust` token: the model check's mode refuses it in
    /// every posture; the sat-authority mode admits it exactly where the
    /// enclosing solve accepts that class as grant authority, so never under
    /// strict rigor. `admits_discharged_trust` is exactly the rule
    /// `admits_unsat` applies to one (the mutation seams in this file judge
    /// forged tokens by it). The ground-decision and exact modes keep their
    /// admission, unchanged.
    #[test]
    fn the_sat_authority_modes_refuse_a_discharged_trust_refutation() {
        let trust = contradiction_certificate(true);
        assert_eq!(
            trust.probe_authority(),
            ProbeUnsatAuthority::DischargedTrust
        );
        assert!(trust.confirms_checked_unsat_emission());
        for mode in MODES {
            for sheds in [false, true] {
                for accepts in [false, true] {
                    assert_eq!(
                        mode.admits_unsat(&trust, sheds, accepts),
                        mode.admits_discharged_trust(accepts),
                        "{mode:?} sheds={sheds} accepts={accepts}"
                    );
                }
            }
        }
        for accepts in [false, true] {
            let model_check = CheckedIsolatedMode::ModelCheckDecision;
            assert!(!model_check.admits_discharged_trust(accepts));
            assert!(!CheckedIsolatedMode::ExactUnsatWithoutTrustDischarge
                .admits_discharged_trust(accepts));
            assert!(CheckedIsolatedMode::GroundDecision.admits_discharged_trust(accepts));
            assert!(CheckedIsolatedMode::ExactUnsat.admits_discharged_trust(accepts));
            assert_eq!(
                CheckedIsolatedMode::SatAuthorityDecision.admits_discharged_trust(accepts),
                accepts
            );
        }
    }

    /// The positive twin: a checked token is still a model-check and a
    /// sat-authority decision, with and without proof shedding, so the refusal
    /// costs only the trust class.
    #[test]
    fn the_sat_authority_modes_still_admit_a_checked_refutation() {
        let checked = contradiction_certificate(false);
        assert_eq!(checked.probe_authority(), ProbeUnsatAuthority::Checked);
        for mode in [
            CheckedIsolatedMode::ModelCheckDecision,
            CheckedIsolatedMode::SatAuthorityDecision,
            CheckedIsolatedMode::GroundDecision,
        ] {
            for accepts in [false, true] {
                assert!(mode.admits_unsat(&checked, false, accepts), "{mode:?}");
                assert!(mode.admits_unsat(&checked, true, accepts), "{mode:?} sheds");
            }
        }
    }

    /// The shed-mode raw admission is reachable from exactly one mode, and
    /// only when the enclosing solve sheds proof work. Every other mode, and
    /// the model-check mode under any proof demand, certifies as before.
    #[test]
    fn only_the_model_check_mode_under_shedding_admits_a_raw_unsat() {
        for mode in [
            CheckedIsolatedMode::GroundDecision,
            CheckedIsolatedMode::ExactUnsat,
            CheckedIsolatedMode::StrictExactUnsat,
            CheckedIsolatedMode::ExactUnsatWithoutTrustDischarge,
            CheckedIsolatedMode::SatAuthorityDecision,
        ] {
            assert!(!mode.admits_shed_raw_unsat(true), "{mode:?} under shedding");
            assert!(!mode.admits_shed_raw_unsat(false), "{mode:?} certified");
        }
        let model_check = CheckedIsolatedMode::ModelCheckDecision;
        assert!(model_check.admits_shed_raw_unsat(true));
        assert!(!model_check.admits_shed_raw_unsat(false));
        assert!(model_check.is_ground_decision());
        assert!(CheckedIsolatedMode::GroundDecision.is_ground_decision());
        assert!(CheckedIsolatedMode::SatAuthorityDecision.is_ground_decision());
        assert!(!CheckedIsolatedMode::ExactUnsat.is_ground_decision());
    }
}
