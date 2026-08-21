// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-authority gate for semantic quantified UNSAT results.

use super::{CheckedGroundDecision, Executor};
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

/// Wall budget for the authored-ground-core re-decision. The core is a strict
/// subset of an already-solved query, so a definitive answer is normally
/// immediate; anything slower fails closed rather than spending the caller's
/// clock. Matches the budget the sibling snapshot probes use.
const GROUND_CORE_PROBE_BUDGET_MS: u64 = 2_000;

impl Executor {
    /// Publish a sound quantified-instance refutation only when no proof
    /// artifact is mandatory. These bounded inner solves currently prove the
    /// mathematical verdict but do not translate their standalone assumptions
    /// back to authored `forall_inst` steps. Mandatory proof modes fail closed;
    /// best-effort/no-proof modes use the same proof-suppressed publisher as the
    /// sealed consequence certificate.
    pub(super) fn quantified_semantic_unsat_or_unknown(
        &mut self,
        missing_proof_reason: UnknownReason,
    ) -> Result<SolveResult> {
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/qsu entry exec={:p} epoch_present={} epoch_current={:?} assumptions_bound={:?}",
                self as *const _,
                self.unsat_query_epoch.is_some(),
                self.checked_sat_refutation_query_scope().is_some(),
                self.checked_sat_refutation_query_assumptions().is_some(),
            );
            self.debug_report_authored_shape_census();
        }
        if self.translated_unsat_proof_required() {
            self.translated_unsat_proof_or_downgrade(missing_proof_reason)
        } else {
            Ok(self.publish_quantified_verdict_only_unsat())
        }
    }

    /// The mandatory-artifact arm: four fail-closed legs, then the downgrade.
    ///
    /// Three of them CONSULT for an artifact that already exists; the fourth
    /// BUILDS one. Every leg's outcome is reported under `--debug-cert` so a
    /// division-wide census can attribute each surviving `unknown` to the exact
    /// leg that declined, rather than to a generic "quantifier unhandled".
    fn translated_unsat_proof_or_downgrade(
        &mut self,
        missing_proof_reason: UnknownReason,
    ) -> Result<SolveResult> {
        {
            // (#bv-mbqi-false-instance-authority, P3b) Before discarding the
            // verdict, consult the checked SAT-refutation sidecar for the
            // EXACT public query. The refutation-driven re-solve can mint a
            // sidecar whose every original clause — including a pushed
            // eval-folded-`false` instance — is strict-authenticated against
            // the authored roots; that token IS a translated authored-scope
            // refutation, and clearing it below would destroy the only
            // artifact this gate exists to demand. The token re-verifies
            // epoch, source stamp, ordered roots, and assumptions at this
            // exact moment, so a disposable inner solve's artifact can never
            // pass. The final publication still runs the ordinary
            // certification funnel, which re-validates the same sidecar.
            // Covered by the #quant-unit-authority kill switch: with the
            // switch off this gate is byte-for-byte the pre-P3b downgrade.
            //
            // (#bitblast-original-clause-authority) When no trace-bound
            // sidecar exists — the UFBV bit-blast route's original gate
            // clauses reference SAT variables absent from `var_to_term`, so
            // one can never mint for that family — a recorded qpf
            // premise-forced instance is re-derived trace-free at this exact
            // moment instead: authored-root membership, strict `forall_inst`
            // substitution replay, and an independently re-lowered,
            // fully-replayed Bool/BV+UF-leaf refutation of the exact
            // instance. Same kill switch, fail-closed on every leg.
            let enabled = crate::quant_unit_authority::quant_unit_authority_enabled();
            let sidecar = enabled && self.checked_sat_refutation_authorizes_current_query();
            let qpf = !sidecar
                && enabled
                && self.checked_qpf_instance_refutation_authorizes_current_query();
            Self::debug_leg(&format_args!(
                "sidecar={sidecar} qpf={qpf} authority_enabled={enabled}"
            ));
            if sidecar || qpf {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#ground-core-authored-scope) A refutation that never used a
            // quantifier is ALREADY authored-scope, so the artifact firewall has
            // nothing to firewall. This arm mirrors
            // `empty_universe_semantic_unsat_or_unknown`: TRY to establish that
            // the verdict is authored-ground, and on success hand it to the
            // ORDINARY publication funnel, which still mints (or refuses to
            // mint) a genuine token. It can therefore only ever turn a
            // firewalled `unknown` into a strictly-certified `unsat`, never
            // widen what publishes.
            //
            // WHY THIS IS NEEDED: the firewall's premise is that these inner
            // solves "do not translate their standalone assumptions back to
            // authored `forall_inst` steps". That premise is false when the
            // contradiction lies wholly inside the authored QUANTIFIER-FREE
            // conjuncts — there are no instances to translate. Without this arm
            // a ground-refutable query degrades to `unknown` merely because a
            // quantifier is present somewhere else in the problem, which is the
            // #8759-era regression this restores.
            let ground_core = self.authored_ground_core_refutes();
            Self::debug_leg(&format_args!("ground_core={ground_core}"));
            if ground_core {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#inc-fparith-negated-exists-inst) Last, and only once the three
            // consulting legs above have all declined: TRY to BUILD the
            // artifact this gate exists to demand, rather than consulting for
            // one. `¬∃x⃗.φ ⊨ ∀x⃗.¬φ ⊨ ¬φ[t⃗]` for ground `t⃗`, so the authored
            // negated existential plus the authored ground conjuncts reduce to
            // a purely GROUND refutation; the translation stitches the probe's
            // strict ground proof onto `qnt_neg_exists` → `forall_inst`
            // derivations over the authored roots and installs it as
            // `last_proof`. On success the ORDINARY publication funnel still
            // mints (or refuses to mint) the token, so this can only turn a
            // firewalled `unknown` into a strictly-certified `unsat`, never
            // widen what publishes.
            let ground_inst = self.try_translate_negated_exists_ground_instantiation_unsat();
            Self::debug_leg(&format_args!("ground_inst={ground_inst}"));
            if ground_inst {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            Self::debug_leg(&format_args!("DOWNGRADE reason={missing_proof_reason:?}"));
            self.clear_cegqi_inner_unsat_artifacts();
            self.last_unknown_reason = Some(missing_proof_reason);
            Ok(SolveResult::Unknown)
        }
    }

    /// `--debug-cert` only: the single stderr channel for this gate's per-leg
    /// attribution. One site, so the whole census reads as one stream.
    fn debug_leg(detail: &std::fmt::Arguments<'_>) {
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!("CERT/qsu leg {detail}");
        }
    }

    /// `--debug-cert` only: name the authored-root shapes this gate is looking
    /// at, so a division-wide census can attribute each downgrade to a shape
    /// rather than to a generic "quantifier unhandled".
    fn debug_report_authored_shape_census(&self) {
        use ay_core::TermData;

        let roots = self
            .authored_hard_unsat_roots_for_isolated_recheck()
            .unwrap_or_else(|| self.ctx.concrete_authored_assertion_terms());
        let mut ground = 0usize;
        let mut forall = 0usize;
        let mut not_exists = 0usize;
        let mut other_quant = 0usize;
        for &root in &roots {
            if !crate::ematching::contains_quantifier(&self.ctx.terms, root) {
                ground += 1;
            } else if matches!(self.ctx.terms.get(root), TermData::Forall(..)) {
                forall += 1;
            } else if matches!(self.ctx.terms.get(root), TermData::Not(inner)
                if matches!(self.ctx.terms.get(*inner), TermData::Exists(..)))
            {
                not_exists += 1;
            } else {
                other_quant += 1;
            }
        }
        eprintln!(
            "CERT/qsu shape roots={} ground={ground} forall={forall} not_exists={not_exists} other_quant={other_quant}",
            roots.len()
        );
    }

    /// Whether the AUTHORED quantifier-free conjuncts alone are UNSAT.
    ///
    /// Entailment: dropping hypotheses only weakens a problem, so a refutation
    /// of a SUBSET of the authored assertions refutes the authored problem.
    /// Nothing here trusts the enclosing (possibly instance-driven) verdict —
    /// the core is re-decided from scratch on a disposable executor through
    /// `checked_ground_solve`, which accepts UNSAT only against a checked
    /// exact-query certificate and binds the result to this query's epoch,
    /// source stamp, ordered roots, and term snapshot.
    ///
    /// Fails closed on every leg: no authored epoch, no quantifier-free core, a
    /// core that is not a strict subset (nothing was dropped, so the ordinary
    /// funnel already had its chance), or any non-UNSAT probe outcome.
    pub(super) fn authored_ground_core_refutes(&mut self) -> bool {
        let debug = ay_core::misc_cli_flags().debug_cert;
        let Some(authored) = self.authored_hard_unsat_roots_for_isolated_recheck() else {
            if debug {
                eprintln!("CERT/ground-core decline: no authored hard scope");
            }
            return false;
        };
        let ground = self.snapshot_ground_core(&authored);
        if debug {
            eprintln!(
                "CERT/ground-core: authored={} ground={}",
                authored.len(),
                ground.len()
            );
        }
        if ground.is_empty() || ground.len() >= authored.len() {
            return false;
        }
        match self.checked_ground_solve(
            ground.clone(),
            LogicCategory::QfUf,
            GROUND_CORE_PROBE_BUDGET_MS,
        ) {
            Some(CheckedGroundDecision::Unsat(checked)) => {
                let consumed = checked.consume(self, &ground);
                if debug {
                    eprintln!("CERT/ground-core: probe UNSAT, consume={consumed}");
                }
                consumed
            }
            Some(CheckedGroundDecision::Sat(_)) => {
                if debug {
                    eprintln!("CERT/ground-core decline: probe SAT");
                }
                false
            }
            None => {
                if debug {
                    eprintln!("CERT/ground-core decline: probe indecisive");
                }
                false
            }
        }
    }
}
