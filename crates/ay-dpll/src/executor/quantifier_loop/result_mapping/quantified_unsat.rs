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
    #[track_caller]
    pub(in crate::executor) fn quantified_semantic_unsat_or_unknown(
        &mut self,
        missing_proof_reason: UnknownReason,
    ) -> Result<SolveResult> {
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/qsu entry from={} exec={:p} epoch_present={} epoch_current={:?} assumptions_bound={:?}",
                std::panic::Location::caller(),
                std::ptr::from_ref(self),
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
            // (#implied-forall-ground-inst) The sibling BUILDER for the dual
            // authored shape — a universal under an implication whose
            // antecedent is authored. Rationale in that lane's module doc.
            let implied_inst = self.try_translate_implied_forall_ground_instantiation_unsat();
            Self::debug_leg(&format_args!("implied_inst={implied_inst}"));
            if implied_inst {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#exists-bridge-chain) The BUILDER for a universal whose body
            // bridges to an existential (`∀v⃗. (A ↔ ∃w⃗. B)`): instantiate
            // the bridge, discharge its antecedent (through a second
            // bridge and a congruence transport when needed), Skolemize
            // the existential one binder at a time, and stitch the ground
            // refutation over the resulting chain. Same contract as the
            // sibling builders: it can only turn a firewalled `unknown`
            // into a strictly-certified `unsat`.
            let bridge_chain = self.try_translate_exists_bridge_chain_unsat();
            Self::debug_leg(&format_args!("bridge_chain={bridge_chain}"));
            if bridge_chain {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#authored-skeleton-refutation) The PROPOSITIONAL builder, and
            // the reason it is a builder and not a relaxation of the
            // `ground_core` leg above. That leg asks `snapshot_ground_core` for
            // the QUANTIFIER-FREE authored roots, so on
            //
            //     (assert (and G E))      ; E = (exists (x) phi)
            //     (assert (not E))        ; the SAME term
            //
            // it sees an EMPTY core (`authored=2 ground=0`) and declines, even
            // though the refutation is `and_pos` on the first root and one
            // resolution against the second. The quantifier is never reasoned
            // about — it occupies an atom position — so the firewall's premise
            // ("these inner solves do not translate their assumptions back to
            // authored steps") is vacuous here: there is nothing to translate.
            // This leg BUILDS that derivation over authored terms only, and
            // hands it to the ordinary funnel, which still mints and re-checks
            // it. It can only turn a firewalled `unknown` into a
            // strictly-certified `unsat`.
            let skeleton = self.try_translate_authored_skeleton_refutation_unsat();
            Self::debug_leg(&format_args!("skeleton={skeleton}"));
            if skeleton {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#qlra-nested-cegqi M3a) The quantified-LRA BUILDER: when the
            // nested search refuted THIS query but its lane pass did not
            // publish (its terms still live), build the expansion
            // certificate — tautological `forall_inst`/`qnt_neg_exists`/`sko`
            // lemmas plus a strict ground refutation of the proxied set — and
            // install it through the strict installation boundary. The
            // ordinary funnel re-checks it; it can only turn a firewalled
            // `unknown` into a strictly-certified `unsat`.
            let expansion_cert = self.try_translate_qlra_expansion_certificate_unsat();
            Self::debug_leg(&format_args!("expansion_cert={expansion_cert}"));
            if expansion_cert {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            // (#qsu-downgrade-is-load-bearing) Every leg declined. Read
            // `withhold_quantified_refutation` before narrowing this gate.
            self.withhold_quantified_refutation(missing_proof_reason)
        }
    }

    /// The downgrade: every leg of [`Self::translated_unsat_proof_or_downgrade`]
    /// declined, so the computed refutation is withheld as `unknown`.
    fn withhold_quantified_refutation(
        &mut self,
        missing_proof_reason: UnknownReason,
    ) -> Result<SolveResult> {
        // (#qsu-downgrade-is-load-bearing) READ THIS BEFORE NARROWING THIS
        // GATE. It has been proposed twice, and what it protects is in
        // ANOTHER MODULE, so nothing here used to say it.
        //
        // What the gate is: `translated_unsat_proof_required()` is
        // dominated by `active_unsat_query_requires_strict_proof()`, which
        // is `unsat_query_epoch.is_some() && role == Published` — "this is
        // the user's own question". MEASURED in default posture on both
        // files this gate discards (AUFLIA `smt4883783982334591882`, UFBV
        // `345_oggenc`): `CERT/qsu required epoch_role=true
        // self_check=false script_pp=false artifact_req=false`. So every
        // disjunct that names an actual document demand is FALSE and the
        // arm is entered purely because the query is public. That reads
        // like a syntactic proxy for "a document was demanded", and it is
        // tempting to narrow it to the four real demands.
        //
        // WHY THAT IS NOT SAFE. The deferred-trust rescue in
        // `unsat_cert::reconfirms_unsat_within` admits a refutation whose
        // proof carries a trust step by RE-SOLVING the authored assertions
        // in a fresh `Executor`, and it deliberately accepts a twin proof
        // that plain strict REJECTS — a trust-kind rejection is documented
        // there as the arm's ENTRY CONDITION, not evidence against it. Its
        // whole claim to independence is that a fresh executor, sharing no
        // state, re-derives `unsat` on its own. THIS GATE IS WHAT MAKES
        // THAT CLAIM TRUE FOR QUANTIFIED REFUTATIONS: the nested re-solve
        // takes the identical route to this identical gate and downgrades,
        // so the rescue declines.
        //
        // MEASURED, with a scaffold that bypasses this downgrade. Bypassing it
        // for the outer query ALONE changes nothing — the funnel still
        // answers `unknown` ("deferred-trust discharge failed: no collected
        // trust clause is a standalone theory tautology (collected 1) AND
        // the authored assertions could not be independently re-solved as
        // UNSAT"). Bypassing it in the NESTED solve as well flips AUFLIA
        // `smt4883783982334591882` to `unsat` with
        // `unsat_admission=discharged-trust` and writes this certificate:
        //
        //     (step t0 (cl) :rule hole)
        //
        // The empty clause, derived from nothing. The corroboration that
        // admitted it was this same lane re-running the same instantiation
        // heuristic on the same problem, which for this class carries no
        // independent content at all.
        //
        // So the legs of `translated_unsat_proof_or_downgrade` are not a formality
        // standing between a sound verdict and publication — they are the only route by
        // which a quantified refutation acquires evidence that is not itself.
        // Narrowing this gate does not convert these files; it converts the
        // rescue into self-corroboration. A file that reaches this downgrade
        // needs a PRODUCER for its shape, which is what each leg is.
        // Step (4) re-deciding the quantifier-free core the `ground_core` leg refuted is NOT
        // this self-corroboration (`unsat_cert/ground_core_corroboration.rs`).
        Self::debug_leg(&format_args!("DOWNGRADE reason={missing_proof_reason:?}"));
        self.clear_cegqi_inner_unsat_artifacts();
        self.last_unknown_reason = Some(missing_proof_reason);
        // Only the artifact is missing: every caller reaches this downgrade holding a
        // computed refutation (`quantified_semantic_unsat_or_unknown`'s no-artifact
        // branch publishes the same verdict as `unsat`). SAT producers must not
        // spend the rest of the pass re-solving the refuted query.
        self.quantified_refutation_withheld = true;
        Ok(SolveResult::Unknown)
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
            .or_else(|| self.authored_hard_unsat_hypotheses_for_isolated_recheck())
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
        self.authored_ground_core_refutation = None;
        let debug = ay_core::misc_cli_flags().debug_cert;
        // (#uc-named-core-ground-scope) The assumption-free accessor first, so
        // an ordinary `(check-sat)` keeps the exact scope it always had; the
        // hypothesis accessor is the fallback that keeps a `:produce-unsat-cores`
        // script — whose named assertions the core redirect relocates INTO the
        // assumption vector — from losing this leg entirely. Both vectors are
        // hypotheses of the same query, so the subset entailment below is
        // unchanged either way.
        let Some(authored) = self
            .authored_hard_unsat_roots_for_isolated_recheck()
            .or_else(|| self.authored_hard_unsat_hypotheses_for_isolated_recheck())
        else {
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
                self.note_justified_obligation_shape(consumed, &ground);
                // #ground-core-corroboration: the funnel's deferred-trust step
                // (4) re-decides this quantifier-free core, not the quantified
                // scope whose nested solve cannot re-certify it at depth 1.
                if consumed {
                    self.authored_ground_core_refutation = Some(ground.into_boxed_slice());
                }
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

#[cfg(test)]
#[path = "quantified_unsat/refutation_withheld_tests.rs"]
mod refutation_withheld_tests;
