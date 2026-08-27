// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The justification registry: one place that answers "why may this UNSAT
//! publish?".
//!
//! # Why this exists
//!
//! A quantified UNSAT is refused unless something independent of the
//! (possibly unsound) instance-driven derivation vouches for it. Historically
//! each gate hand-rolled its own answer, so a single logical property had to be
//! re-encoded at every gate that could benefit from it. That is not a
//! stylistic complaint — it is a measured defect. The property "this refutation
//! does not depend on any quantifier instance" had to be written TWICE, at
//! `quantified_semantic_unsat_or_unknown` and again at the CEGQI clash gate,
//! before the #8759-era ghost-pair obligation could publish; a gate that had
//! not been taught the property kept failing closed on a verdict two of its
//! siblings would have accepted.
//!
//! A registry makes the property the unit of reuse instead of the gate:
//! establish each justification ONCE, and let every gate consult the same set.
//! The next gate that needs one costs a call, not a re-derivation.
//!
//! # What a justification is (and is not)
//!
//! Each variant names an INDEPENDENT reason the verdict holds — independent in
//! the strict sense that it does not rest on the enclosing solve's instance
//! set. None of them is a rescue of a doubted verdict: each is a separate
//! derivation that happens to reach the same conclusion. Consulting the
//! registry therefore never widens what publishes; it only stops a gate from
//! discarding a verdict some OTHER gate could already have justified.
//!
//! Every leg fails closed. `establish` returns `None` when nothing applies, and
//! the caller must then degrade exactly as it did before.

use super::Executor;
use crate::logic_detection::LogicCategory;
use ay_core::TermId;

/// An independent reason a quantified UNSAT may be published.
///
/// Ordered cheapest-first in [`Justification::establish`]: every variant below
/// the first hit costs nothing, which matters because these run on the
/// rejection path of a MANDATORY gate (see the certification-cost accounting —
/// the mint is cheap except where it reaches a whole-problem re-solve).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum Justification {
    /// The AUTHORED quantifier-free conjuncts refute on their own.
    ///
    /// Entailment: dropping hypotheses only weakens, so a refutation of a
    /// SUBSET of the authored assertions refutes the authored problem. No
    /// instance and no CE lemma participates, so an instance-driven gate's
    /// concerns are simply inapplicable.
    AuthoredGroundCore,
    /// The quantifier-free core of the pre-instantiation snapshot refutes.
    ///
    /// Weaker provenance than [`Self::AuthoredGroundCore`] (a snapshot, not the
    /// authored roots), so it is consulted second and only where the caller
    /// already holds a snapshot it trusts.
    SnapshotGroundCore,
    /// The core PLUS the instance closure of UNCONDITIONALLY-asserted foralls
    /// refutes. Universal instantiation entails each such instance, so they
    /// hold in every model.
    InstanceClosure,
}

impl Justification {
    /// Consult the registry. `snapshot` is the pre-instantiation view when the
    /// caller has one; `None` disables the two snapshot-provenance legs.
    ///
    /// Cheapest-first and short-circuiting. Returns `None` when no
    /// justification applies — the caller MUST then fail closed unchanged.
    pub(in crate::executor) fn establish(
        exec: &mut Executor,
        snapshot: Option<&[TermId]>,
        category: LogicCategory,
    ) -> Option<Self> {
        if exec.authored_ground_core_refutes() {
            return Some(Self::AuthoredGroundCore);
        }
        let snapshot = snapshot?;
        // Owned: the probes below take `&mut Executor`.
        let snapshot = snapshot.to_vec();
        if exec.ground_core_is_unsat(&snapshot, category) {
            return Some(Self::SnapshotGroundCore);
        }
        if exec.instance_closure_ground_unsat(&snapshot, category) {
            return Some(Self::InstanceClosure);
        }
        None
    }

    /// Consult the registry and PUBLISH the refutation when it answers.
    ///
    /// One call site for what used to be two hand-copied blocks, and the reason
    /// the copies mattered: at the CEGQI-disambiguation arm the consult sat
    /// INSIDE `if clash`, so the registry was reachable only where an
    /// alternative authority (`cegqi_unsat_authority::certify`) had already been
    /// offered first, and was UNREACHABLE from `CERT/degrade@343` — the widest
    /// discard in `classify_quantifier_result`.
    ///
    /// That nesting had no justification of its own. Every variant above is an
    /// INDEPENDENT derivation, re-decided from scratch on a disposable executor
    /// through `checked_ground_solve`; none reads the clash reconstruction, the
    /// CEGQI counterexample lemmas, or the enclosing verdict, so none becomes
    /// less true when the bounded cross-product clash search comes up empty.
    /// Measured on the verification-consumer ext_eq push/pop refutation (#7956): `clash` is
    /// false because picking the refuting instances out of a 4-Seq × N-Int
    /// cross-product is a relevance problem, while the E-matcher had already put
    /// exactly those instances in `active_support_axioms`. With the consult
    /// reachable, [`Self::InstanceClosure`] assembles that 74-formula consequence
    /// set and its fresh re-solve DOES refute it — 6.1 / 8.8 / 9.1 / 9.8 s over
    /// four reps — i.e. above the leg's own 2000 ms allowance, so on that fixture
    /// the registry still fails closed (leg wall 2.00 / 2.14 / 2.08 s over three
    /// reps at the shipped allowance, `decided=false`, nothing published).
    ///
    /// # The allowance is NOT what costs that fixture its verdict
    ///
    /// Measured, and it overturns the obvious next move (shrink the leg's work
    /// until it fits 2000 ms). With the allowance temporarily raised so the leg
    /// DOES establish — `CERT/justified: instance-closure`, the probe's own UNSAT
    /// carrying an `independently-checked` token — the fixture's FIRST
    /// `(check-sat)` still answers `unknown`, in 4 reps of 4. The verdict is
    /// discarded ONE GATE LATER: `finish_quantifier_processing` re-gates a
    /// classified `Unsat` whenever `quantified_proof_translation_incomplete` is
    /// set and the live proof is not strict, routing it into
    /// `quantified_semantic_unsat_or_unknown`, whose four legs all decline for
    /// this shape (no checked-SAT sidecar, no qpf instance authority, the
    /// authored ground core is SAT, no negated-exists shape). So an
    /// infinitely-fast leg would leave this fixture exactly where it is.
    ///
    /// # And there is no cheaper subset to find
    ///
    /// The whole leg cost is the nested ground `check_sat`: scope capture
    /// measures 0.0 ms, the `Context` clone 0.2-1.4 ms, consequence-set assembly
    /// 0.0 ms, and the probe's certification 1-2 ms. Shrinking the set does not reliably
    /// shrink the work, because a subset that does not refute STALLS: the
    /// 7-conjunct minimal ground core alone decides SAT in 14 ms, but adding a
    /// single ext_eq pointwise instance to it leaves the probe undecided for a
    /// full 40 s, and only the exactly-right 12-formula set closes (≈3.0 s, still
    /// above the allowance). A "try a cheap prefix first" ladder therefore cannot
    /// pay for itself — a wrong rung burns its entire slice and buys nothing.
    ///
    /// UNSAT-only and fail-closed: `None` leaves every caller's degrade
    /// byte-identical to before.
    pub(in crate::executor) fn publish_if_established(
        exec: &mut Executor,
        snapshot: Option<&[TermId]>,
        category: LogicCategory,
    ) -> Option<crate::executor_types::SolveResult> {
        let established = Self::establish(exec, snapshot, category)?;
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!("CERT/justified: {}", established.tag());
        }
        exec.last_unknown_reason = None;
        Some(crate::executor_types::SolveResult::unsat())
    }

    /// Stable tag for diagnostics and the certification accounting.
    pub(in crate::executor) fn tag(self) -> &'static str {
        match self {
            Self::AuthoredGroundCore => "authored-ground-core",
            Self::SnapshotGroundCore => "snapshot-ground-core",
            Self::InstanceClosure => "instance-closure",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Justification;
    use crate::executor::Executor;
    use crate::executor_types::{SolveResult, UnknownReason};
    use crate::logic_detection::LogicCategory;

    /// Build a public query whose AUTHORED quantifier-free conjuncts refute on
    /// their own while a `forall` root keeps the problem quantified — the exact
    /// premise [`Justification::AuthoredGroundCore`] names.
    fn contradictory_ground_core_with_a_forall() -> Executor {
        let mut exec = Executor::new();
        let p = exec
            .ctx
            .terms
            .mk_fresh_var("justify_p", ay_core::Sort::Bool);
        let not_p = exec.ctx.terms.mk_not(p);
        let q = exec
            .ctx
            .terms
            .mk_fresh_var("justify_q", ay_core::Sort::Bool);
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("justify_x".to_string(), ay_core::Sort::Int)], q);
        let roots = vec![p, not_p, forall];
        exec.ctx.assertions = roots.clone();
        exec.begin_unsat_query_epoch(&roots);
        exec.bind_unsat_query_assumptions(&[]);
        exec
    }

    /// The registry PUBLISHES: a quantified query whose authored ground core is
    /// independently refutable yields `unsat` with the pending unknown-reason
    /// cleared, so a caller can return it directly.
    ///
    /// MUTATION: make `publish_if_established` return `None` unconditionally,
    /// or drop its `exec.last_unknown_reason = None`, and this fails.
    #[test]
    fn an_established_justification_publishes_unsat_and_clears_the_unknown_reason() {
        let mut exec = contradictory_ground_core_with_a_forall();
        exec.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);

        assert_eq!(
            Justification::establish(&mut exec, None, LogicCategory::QfUf),
            Some(Justification::AuthoredGroundCore),
            "the authored quantifier-free conjuncts p and (not p) refute alone"
        );
        assert_eq!(
            Justification::publish_if_established(&mut exec, None, LogicCategory::QfUf),
            Some(SolveResult::unsat())
        );
        assert_eq!(exec.last_unknown_reason, None);
    }

    /// The registry proposes a VERDICT; it never grants PUBLICATION AUTHORITY.
    ///
    /// Every leg re-decides its obligation on a disposable executor, and
    /// `CheckedGroundDecision` deliberately carries a bit rather than a token —
    /// the probe's own certificate dies with the probe. So an established
    /// justification must leave the ENCLOSING query's `last_unsat_certificate`
    /// exactly as it found it, and the mandatory publication funnel still
    /// decides whether the returned `unsat` reaches the surface.
    ///
    /// That is not a formality: it is the measured reason the #7956 push/pop
    /// fixture answers `unknown` even on runs where `establish` returns
    /// [`Justification::InstanceClosure`]. `CERT/justified: instance-closure`
    /// fires, and then the `quantified_proof_translation_incomplete` re-gate in
    /// `finish_quantifier_processing` turns the classified `Unsat` back into
    /// `Unknown` because no authored-scope artifact accompanies it. Anyone
    /// tempted to "fix" that by minting authority here should read
    /// `publish_if_established` first — the funnel is the firewall, and this
    /// test is the ratchet that keeps the registry on the proposing side of it.
    ///
    /// MUTATION (verified): in `checked_isolated_solve`, keep the disposable
    /// probe's token instead of dropping it — `self.last_unsat_certificate =
    /// token;` — and this test, and only this test, turns red.
    #[test]
    fn an_established_justification_grants_no_publication_authority() {
        let mut exec = contradictory_ground_core_with_a_forall();
        assert!(
            exec.last_unsat_certificate.is_none(),
            "precondition: the fresh query holds no UNSAT certificate"
        );

        assert_eq!(
            Justification::publish_if_established(&mut exec, None, LogicCategory::QfUf),
            Some(SolveResult::unsat()),
            "the authored quantifier-free conjuncts refute, so the registry answers"
        );

        assert!(
            exec.last_unsat_certificate.is_none(),
            "the registry must not install an UNSAT certificate: its evidence is a \
             disposable-probe bit, and the mandatory publication funnel must still \
             mint — or refuse to mint — its own token for the enclosing query"
        );
    }

    /// And it FAILS CLOSED: with a satisfiable authored scope and no snapshot,
    /// nothing is established, nothing is published, and the caller's pending
    /// unknown-reason is left exactly as it was found.
    ///
    /// MUTATION: publish on a `None` justification and this fails.
    #[test]
    fn no_justification_publishes_nothing_and_disturbs_no_pending_reason() {
        let mut exec = Executor::new();
        let p = exec
            .ctx
            .terms
            .mk_fresh_var("justify_sat_p", ay_core::Sort::Bool);
        let roots = vec![p];
        exec.ctx.assertions = roots.clone();
        exec.begin_unsat_query_epoch(&roots);
        exec.bind_unsat_query_assumptions(&[]);
        exec.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);

        assert_eq!(
            Justification::publish_if_established(&mut exec, None, LogicCategory::QfUf),
            None
        );
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::QuantifierUnhandled)
        );
    }
}
