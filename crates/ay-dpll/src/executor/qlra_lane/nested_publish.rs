// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M3a: a nested UNSAT publishes ONLY through its expansion certificate
//! (#qlra-nested-cegqi, plan §4.1 and §9 M3a).
//!
//! The search's `unsat` is a hint about its approximations. The lane asks
//! `install_qlra_expansion_certificate` (executor/proof) to prove the
//! authored roots inconsistent from Γ, install that proof through the strict
//! installation boundary, and then re-validates the exact installed proof at
//! this consumption point (scope, empty clause, strict completeness, stop
//! state), mirroring `cegqi_unsat_authority::publish_installed`. The
//! mandatory certification mint re-checks it once more before the answer
//! leaves the solver. Any failure leaves the verdict `unknown` and hands the
//! query to the legacy path.
//!
//! When the caller DEMANDED a checked certificate (`--proof FILE`,
//! `--strict-proofs`, `:produce-proofs`, self-check), the installed proof
//! must also render as the problem-scoped Alethe document the consumer will
//! receive. Otherwise the lane restores the proof state it found and
//! declines, as the QSAT route's evidence gate does. Measured: on
//! `(exists ((x Real)) (forall ((y Real)) (< y x)))` the certificate's
//! `sko_forall` over a nested binder is outside the certified Skolem
//! printer's scope, so without this gate `--proof FILE` answered `unsat`,
//! refused to write the document and exited 1 with no verdict, where the
//! legacy path answers `unknown`.
//!
//! Before that gate the installed proof gets the authored `assume` spellings
//! every installer that replaces `last_proof` owes it
//! ([`Executor::qlra_presentation_refusal`]); a restoration whose document
//! is not complete and the input's own is reverted, never published or
//! declined on.
//!
//! The same builder backs the quantified-UNSAT firewall's `expansion_cert`
//! leg ([`Executor::try_translate_qlra_expansion_certificate_unsat`]), which
//! consumes a kept [`NestedUnsatLog`] when a refutation reaches the firewall
//! through another route.

use ay_core::term::TermStoreSnapshotStamp;
use ay_core::time::Instant;
use ay_core::TermId;

use super::super::proof::{CertDecline, ExpansionCertReport};
use super::super::qsat_route::ProofStateSnapshot;
use super::super::Executor;
use super::nested::NestedSearch;
use super::LaneSearch;
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::NestedTree;
use crate::cegqi::lra_nested::QlraOutcome;
use crate::executor_types::{Result, SolveResult, UnknownReason};

/// Certificate probe budget when the query has no deadline.
const NO_DEADLINE_CERT_BUDGET_MS: u64 = 10_000;

/// A nested UNSAT the lane could not publish, with its terms still live.
pub(in crate::executor) struct NestedUnsatLog {
    roots: Vec<TermId>,
    tree: NestedTree,
    gamma: Vec<Vec<NInstance>>,
    /// The store as the lane left it: a later rollback below this point
    /// retires the log (its `TermId`s would dangle).
    stamp: TermStoreSnapshotStamp,
}

impl NestedUnsatLog {
    pub(super) fn new(
        roots: Vec<TermId>,
        nested: NestedSearch,
        stamp: TermStoreSnapshotStamp,
    ) -> Self {
        Self {
            roots,
            tree: nested.tree,
            gamma: nested.gamma,
            stamp,
        }
    }
}

fn ms_since(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
}

impl Executor {
    /// Wall granted to one certificate's ground probe: three quarters of what
    /// is left of the query, so a declined certificate still leaves the legacy
    /// path a share.
    fn qlra_cert_probe_budget_ms(&self) -> u64 {
        match self.solve_deadline.get() {
            None => NO_DEADLINE_CERT_BUDGET_MS,
            Some(deadline) => {
                let remaining = deadline.saturating_duration_since(Instant::now());
                u64::try_from((remaining * 3 / 4).as_millis()).unwrap_or(u64::MAX)
            }
        }
    }

    /// Build and install the expansion certificate, recording `qlra.cert_*`
    /// statistics under `key`.
    fn qlra_expansion_certificate(
        &mut self,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        key: &'static str,
        deferred: &mut Option<ay_core::Proof>,
    ) -> std::result::Result<(), CertDecline> {
        let started = Instant::now();
        let mut report = ExpansionCertReport::default();
        let result = match deferred {
            Some(_) => self.install_deferred_expansion_certificate(deferred, &mut report),
            None => {
                let budget_ms = self.qlra_cert_probe_budget_ms();
                self.install_qlra_expansion_certificate(
                    tree,
                    gamma,
                    budget_ms,
                    &mut report,
                    deferred,
                )
            }
        };
        // Wall figures ACCUMULATE across the first pass and its memo retry
        // (a parked candidate is probed on the first pass and installed on
        // the retry); sizes keep the pass that built the candidate.
        self.qlra_add_stat_ms("qlra.cert_probe_ms", report.probe_ms);
        self.qlra_add_stat_ms("qlra.cert_check_ms", report.check_ms);
        self.qlra_add_stat_ms("qlra.cert_ms", ms_since(started));
        let extra = &mut self.last_statistics;
        if report.lemmas > 0 {
            extra.set_int("qlra.cert_lemmas", report.lemmas as u64);
            extra.set_int("qlra.cert_proxies", report.proxies as u64);
        }
        extra.set_int("qlra.cert_steps", report.steps as u64);
        match result {
            Ok(()) => extra.set_string(key, "expansion-installed"),
            Err(decline) => {
                extra.set_string(key, "expansion-declined");
                extra.set_string("qlra.cert_decline", decline.label());
            }
        }
        tracing::debug!(
            target: "ay::qlra",
            "expansion cert: {:?} lemmas={} proxies={} steps={} probe_ms={} check_ms={}",
            result,
            report.lemmas,
            report.proxies,
            report.steps,
            report.probe_ms,
            report.check_ms,
        );
        result
    }

    /// Whether an `unknown` this pass returns is re-asked by the
    /// quantified-trace retry of the same public solve
    /// (`quantified_trace_arming_unknown_retry`), which re-enters the lane
    /// with the authored problem obligation installed.
    fn qlra_trace_retry_will_follow(&mut self) -> bool {
        crate::quant_unit_authority::quantified_shedding_yield_enabled()
            && self.competition_shedding_active()
            && !self.quantified_trace_retry_armed
            && !self.should_abort_theory_loop()
    }

    /// Whether this public solve's lane memo holds a nested UNSAT whose
    /// expansion certificate a shed first pass built, pre-checked and parked
    /// for the trace-armed retry (`qlra_publish_nested_unsat`). The `Unknown`
    /// cascade of `cegar_refine_solve` then runs that retry FIRST: the parked
    /// candidate needs only the authored problem obligation the retry installs,
    /// while the deep-QE retry ahead of it can spend the rest of the deadline
    /// on its elimination probe (measured: mjollnir1/formula_134 parked at
    /// 2.4 s, then sat in `qe::lw` until the 20 s deadline).
    pub(in crate::executor) fn qlra_expansion_candidate_parked(&self) -> bool {
        matches!(
            self.qlra_lane.memo.as_deref(),
            Some(super::QlraLaneMemo {
                search: Some(LaneSearch::Nested(nested)),
                ..
            }) if nested.deferred.is_some()
        )
    }

    /// The proof state to restore if the certificate this pass installs falls
    /// short of a demanded one (`None` when nothing is demanded, so the
    /// default and shed postures pay nothing).
    fn qlra_demanded_snapshot(&self) -> Option<ProofStateSnapshot> {
        self.checked_certificate_demanded()
            .then(|| ProofStateSnapshot::take(self))
    }

    /// A nested UNSAT: publish only through its expansion certificate.
    ///
    /// Returns the pass's answer and whether its terms must be KEPT: an
    /// installed proof holds them, and so does a parked candidate. Under
    /// competition shedding the first pass's strict obligation lacks the
    /// authored roots, so the candidate is built, pre-checked, parked in
    /// `nested.deferred`, and the pass ends `unknown` at once; the
    /// quantified-trace retry that follows such an `unknown`
    /// ([`Self::qlra_trace_retry_will_follow`]) re-enters the lane and
    /// installs the parked candidate through the unchanged strict boundary.
    /// The first pass publishes nothing.
    pub(super) fn qlra_publish_nested_unsat(
        &mut self,
        roots: &[TermId],
        nested: &mut NestedSearch,
    ) -> (Option<Result<SolveResult>>, bool) {
        if roots != self.exact_concrete_authored_scope() {
            self.last_statistics
                .set_string("qlra.cert", "expansion-scope-moved");
            return (None, false);
        }
        let mut deferred = nested.deferred.take();
        let snapshot = self.qlra_demanded_snapshot();
        let result = self.qlra_expansion_certificate(
            &nested.tree,
            &nested.gamma,
            "qlra.cert",
            &mut deferred,
        );
        match result {
            Ok(()) => {}
            Err(CertDecline::ScopePending)
                if deferred.is_some() && self.qlra_trace_retry_will_follow() =>
            {
                nested.deferred = deferred;
                self.last_statistics
                    .set_string("qlra.cert", "expansion-deferred");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return (Some(Ok(SolveResult::Unknown)), true);
            }
            Err(_) => return (None, false),
        }
        // Re-validate the exact installed proof at the consumption point and
        // re-check stop state (`cegqi_unsat_authority::publish_installed`).
        let started = Instant::now();
        let publishable =
            !self.should_abort_theory_loop() && self.authored_scope_strict_proof_installed();
        let recheck_ms = ms_since(started);
        let check_ms = self
            .last_statistics
            .get_int("qlra.cert_check_ms")
            .unwrap_or(0);
        self.last_statistics
            .set_int("qlra.cert_check_ms", check_ms.saturating_add(recheck_ms));
        if !publishable {
            self.last_statistics
                .set_string("qlra.cert", "expansion-unpublished");
            return (None, true);
        }
        if let Some(reason) = self.qlra_presentation_refusal() {
            if let Some(snapshot) = snapshot {
                snapshot.restore(self);
            }
            self.last_statistics.set_string("qlra.cert", reason);
            return (None, true);
        }
        self.last_unknown_reason = None;
        (Some(Ok(SolveResult::unsat())), true)
    }

    /// M3a: with the nested search on (the default), a depth-1 UNSAT the consequence replay
    /// could not certify (with the authored obligation in place, so not a
    /// shedding first pass the retry would answer) gets the nested search
    /// and its expansion certificate. The nested search subsumes the depth-1
    /// shape; its UNSAT publishes only through the certificate. `None` when
    /// the fallback does not apply; otherwise the pass's answer and whether
    /// its terms may be rolled back, with `search` replaced by the nested one.
    pub(super) fn qlra_depth1_expansion_fallback(
        &mut self,
        roots: &[TermId],
        search: &mut Option<LaneSearch>,
    ) -> Option<(Option<Result<SolveResult>>, bool)> {
        if !crate::quant_unit_authority::qlra_nested_enabled()
            || self.qlra_lane.nested_inert
            || !self.expansion_obligation_holds(roots)
        {
            return None;
        }
        self.last_statistics
            .set_string("qlra.depth1_cert", "declined");
        let mut nested = self.qlra_nested_search(roots)?;
        let mut answer = (None, true);
        if let LaneSearch::Nested(inner) = &mut nested {
            if matches!(inner.outcome, QlraOutcome::Unsat) {
                let (published, keep) = self.qlra_publish_nested_unsat(roots, inner);
                answer = (published, !keep);
            }
        }
        *search = Some(nested);
        Some(answer)
    }

    /// The quantified-UNSAT firewall's `expansion_cert` leg: build the
    /// certificate from a kept nested-UNSAT log of THIS query, if one exists
    /// and its terms are still live, and, under a demanded certificate, only
    /// if its document renders. Consumes the log (one attempt).
    pub(in crate::executor) fn try_translate_qlra_expansion_certificate_unsat(&mut self) -> bool {
        if !crate::quant_unit_authority::qlra_nested_enabled() {
            return false;
        }
        let Some(log) = self.qlra_lane.unsat_log.take() else {
            return false;
        };
        if !log.stamp.is_append_only_prefix_of(&self.ctx.terms)
            || log.roots != self.exact_concrete_authored_scope()
            || self.should_abort_theory_loop()
        {
            return false;
        }
        let mut deferred = None;
        let snapshot = self.qlra_demanded_snapshot();
        if self
            .qlra_expansion_certificate(&log.tree, &log.gamma, "qlra.cert_leg", &mut deferred)
            .is_err()
        {
            return false;
        }
        if let Some(reason) = self.qlra_presentation_refusal() {
            if let Some(snapshot) = snapshot {
                snapshot.restore(self);
            }
            self.last_statistics.set_string("qlra.cert_leg", reason);
            return false;
        }
        true
    }

    /// Test probe: `last_proof` re-checks strict-complete over the exact
    /// authored scope (the consumption-point re-validation, read-only).
    #[cfg(test)]
    pub(crate) fn test_installed_proof_is_strict_authored(&mut self) -> bool {
        self.authored_scope_strict_proof_installed()
    }

    /// Test probe: hand a (dummy) parked candidate to the deferred install
    /// while the strict obligation lacks the authored roots. `None` when the
    /// obligation already holds (precondition unmet); otherwise whether the
    /// install declined `scope-pending`, whether the candidate is still
    /// parked, and whether any proof was installed.
    #[cfg(test)]
    pub(crate) fn test_install_parked_while_scope_pending(&mut self) -> Option<(bool, bool, bool)> {
        // The shed first pass's shape: no proof-source provenance, so the
        // strict check's problem obligation is the live (preprocessed)
        // window, which no longer holds the authored root.
        self.proof_problem_assertion_provenance = None;
        let preprocessed = vec![self.ctx.terms.true_term()];
        let window = std::mem::replace(&mut self.ctx.assertions, preprocessed);
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || self.expansion_obligation_holds(&authored) {
            self.ctx.assertions = window;
            return None;
        }
        self.last_proof = None;
        let mut parked = Some(ay_core::Proof::default());
        let mut report = ExpansionCertReport::default();
        let result = self.install_deferred_expansion_certificate(&mut parked, &mut report);
        self.ctx.assertions = window;
        Some((
            result == Err(CertDecline::ScopePending),
            parked.is_some(),
            self.last_proof.is_some(),
        ))
    }

    /// Test probe: `forall_inst` / `sko_forall` / `qnt_neg_exists` steps of
    /// `last_proof` (the certificate's lemma derivations).
    #[cfg(test)]
    pub(crate) fn test_installed_proof_quantifier_steps(&self) -> usize {
        use ay_core::{AletheRule, ProofStep};
        self.last_proof.as_ref().map_or(0, |proof| {
            proof
                .steps
                .iter()
                .filter(|step| {
                    matches!(
                        step,
                        ProofStep::Step {
                            rule: AletheRule::ForallInst
                                | AletheRule::Skolem
                                | AletheRule::QntNegExists,
                            ..
                        }
                    )
                })
                .count()
        })
    }
}
