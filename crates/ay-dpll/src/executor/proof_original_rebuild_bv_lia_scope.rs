// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored-scope binding for the final BV/LIA certificate fallback.

use super::*;
use crate::executor_types::{SolveResult, UnknownReason};

impl Executor {
    fn authenticated_plain_authored_roots_for_seq_unknown_discharge(&self) -> Vec<TermId> {
        let Some(roots) = self.authenticated_plain_query_assertions_after_named_core_redirect()
        else {
            return Vec::new();
        };
        // Native API callers intentionally have no parsed SMT-LIB surface AST.
        // Authority here comes from the exact public epoch, its entry stamps,
        // and the independently installed proof-source provenance checked by
        // `authenticated_plain_query_assertions_after_named_core_redirect`.
        // Requiring `assertions_parsed` would therefore reject TrustVC's native
        // terms while adding no protection against generated roots.  Keep the
        // exact provenance equality explicit: this lane accepts neither a
        // prefix nor a solver-extended working set.
        (self.proof_original_problem_assertions() == roots)
            .then_some(roots)
            .unwrap_or_default()
    }

    /// Recompute the immutable, provenance-aligned authored roots that authorize
    /// the internal-certificate BV/LIA fallback. This mirrors the bounded-work,
    /// non-empty-source, and exact index-alignment gates of the ordinary rebuild.
    /// Exact public assumptions are appended only through the authenticated
    /// query epoch; every mismatch yields an empty vector and fails closed.
    pub(in crate::executor) fn authenticated_authored_roots_for_internal_certificate(
        &self,
    ) -> Vec<TermId> {
        let parsed = self.ctx.assertions_parsed();
        // This scope binding traverses the parsed stack exactly once, in the
        // audit walk itself; it clones nothing. It used to charge three passes
        // to mirror the ordinary rebuild's gate, which double-billed work the
        // rebuild already charges for itself.
        if parsed.is_empty()
            || !self.proof_source_work.spend(
                crate::executor::proof_trust_surgery_surface_audit::ProofSourcePass::InternalCertificateScope,
                parsed,
            )
        {
            return Vec::new();
        }
        let originals = self.proof_original_problem_assertions();
        if originals.len() != parsed.len() {
            return Vec::new();
        }
        let Some(roots) = self.authenticated_unsat_query_roots_for_internal_certificate() else {
            return Vec::new();
        };
        roots
            .starts_with(&originals)
            .then_some(roots)
            .unwrap_or_default()
    }

    /// Re-run the bounded fallback after an outer wrapper restores the exact
    /// public assertion/assumption scope. This cannot borrow a named-core
    /// redirect's temporary window, and replacement still requires strict replay.
    pub(in crate::executor) fn refresh_authenticated_bv_lia_internal_certificate_for_publication(
        &mut self,
    ) {
        let Some(mut proof) = self.last_proof.take() else {
            return;
        };
        self.rebuild_authenticated_bv_lia_internal_certificate_last_resort(&mut proof);
        self.last_proof = Some(proof);
    }

    /// Discharge an exact sequence-extensionality companion theorem when
    /// quantified search stopped at an incompleteness `Unknown`. For a
    /// provisional UNSAT, first independently authenticate the complete exact
    /// BV/LIA root set, falling back to the sequence theorem only when BV/LIA
    /// authentication explicitly declines the fragment.
    ///
    /// This is deliberately a provisional result transition, not a publication
    /// bypass. The caller immediately routes it through the unchanged self-check
    /// and mandatory UNSAT certification funnels. Every decline preserves the
    /// original result and diagnostic state.
    pub(in crate::executor) fn try_complete_authenticated_seq_extensional_result(
        &mut self,
        proposed: SolveResult,
    ) -> SolveResult {
        let typed_quantifier_unknown = proposed.is_unknown()
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierDeferred
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            );
        // A nested core-tracking rescue's raw UNSAT carries no authority into
        // this restored whole-query boundary.  Re-prove every exact matching
        // UNSAT independently rather than inspecting or inheriting that
        // nested proof state.  SAT is never eligible.
        if (!typed_quantifier_unknown && !proposed.is_unsat()) || self.should_abort_theory_loop() {
            return proposed;
        }
        // A provisional solver UNSAT under an explicit translated-proof
        // contract must keep the ordinary reconstruction pipeline's first
        // refusal. The exact BV/LIA/Seq certificates used below are native
        // authority and deliberately render as an honest Alethe `hole`; using
        // one here can overwrite an externally surfaceable proof (or convert
        // its precise wire rejection into a native-only artifact). A typed
        // quantifier Unknown still needs this completion so the publication
        // gate can report that exact native theorem honestly.
        if proposed.is_unsat() && self.strict_unsat_presentation_required() {
            return proposed;
        }

        // The provisional UNSAT recovery is a last resort, not a competing
        // proof producer. Preserve an existing complete proof whenever its
        // reachable assumptions are already authorized by the ordinary
        // publication scope and datatype-aware strict replay accepts it. This
        // keeps specialized BvBitBlast and datatype certificates intact.
        if proposed.is_unsat() {
            let legitimate: Vec<TermId> = self.proof_legit_assume_set().into_iter().collect();
            if self.last_proof.as_ref().is_some_and(|proof| {
                ay_proof::validate_reachable_assumes_in_problem_scope(proof, &legitimate).is_ok()
                    && self
                        .check_proof_strict_with_datatypes(proof)
                        .is_ok_and(|quality| quality.is_complete())
                    && Self::proof_derives_empty_clause(proof)
            }) {
                return proposed;
            }
        }

        let authenticated_scope =
            self.authenticated_plain_authored_roots_for_seq_unknown_discharge();
        let Some(roots) = collect_bounded_bv_lia_roots(&self.ctx.terms, &authenticated_scope)
        else {
            return proposed;
        };
        let recognized = if proposed.is_unsat() {
            match ay_proof::authenticate_bv_lia_unsat_query(&self.ctx.terms, &roots, None) {
                Ok(_) => Some((roots, TheoryLemmaKind::BvLiaTautology)),
                Err(error) if error.is_capability_decline() => {
                    ay_proof::recognize_seq_extensional_companion_contradiction(
                        &self.ctx.terms,
                        &roots,
                    )
                    .map(|selected| {
                        (
                            selected.into(),
                            TheoryLemmaKind::SeqExtensionalCompanionContradiction,
                        )
                    })
                }
                Err(_) => None,
            }
        } else {
            ay_proof::recognize_seq_extensional_companion_contradiction(&self.ctx.terms, &roots)
                .map(|selected| {
                    (
                        selected.into(),
                        TheoryLemmaKind::SeqExtensionalCompanionContradiction,
                    )
                })
        };
        let Some((selected, kind)) = recognized else {
            return proposed;
        };
        let Some(candidate) =
            self.build_authenticated_bv_lia_refutation(&selected, kind, &authenticated_scope)
        else {
            return proposed;
        };

        // Candidate construction interns raw negations. Re-authenticate the
        // epoch and exact term-entry stamps after that mutation, then replay
        // through the executor's mandatory datatype-aware strict checker.
        if self.should_abort_theory_loop()
            || self.authenticated_plain_authored_roots_for_seq_unknown_discharge()
                != authenticated_scope
        {
            return proposed;
        }
        let Ok(quality) = self.check_proof_strict_with_datatypes(&candidate) else {
            return proposed;
        };
        if !quality.is_complete()
            || !Self::proof_derives_empty_clause(&candidate)
            || self.should_abort_theory_loop()
            || self.authenticated_plain_authored_roots_for_seq_unknown_discharge()
                != authenticated_scope
        {
            return proposed;
        }

        // Replace every proof/SAT-side cache as one lifecycle unit. In
        // particular, never let `--self-check` consult a success bit left by a
        // different proof or let an obsolete model coexist with this UNSAT.
        self.proof_check_result = None;
        self.proof_check_ok = false;
        self.last_proof_quality = None;
        #[cfg(feature = "proof-checker")]
        {
            self.run_internal_proof_check(&candidate);
            if !self.proof_check_ok {
                self.proof_check_result = None;
                return proposed;
            }
        }
        #[cfg(not(feature = "proof-checker"))]
        if self.self_check() {
            return proposed;
        }
        self.populate_proof_quality_stats(&quality);
        self.last_proof_quality = Some(quality);
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_sat_certificate = None;
        self.last_unsat_certificate = None;
        self.pending_nested_array_bool_bv_unsat = None;
        self.clear_quantified_sat_authority();
        self.last_model = None;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.last_proof = Some(candidate);
        self.last_unknown_reason = None;
        self.last_unknown_origin = None;
        SolveResult::unsat()
    }

    /// Exact native proof identity used by the self-check Seq exception.
    /// Ordinary Seq proofs remain uncheckable; this accepts only the canonical
    /// five-premise theorem reconstructed from the current public epoch.
    pub(in crate::executor) fn is_current_authenticated_seq_extensional_companion_proof(
        &self,
        proof: &Proof,
    ) -> bool {
        let scope = self.authenticated_plain_authored_roots_for_seq_unknown_discharge();
        let Some(roots) = collect_bounded_bv_lia_roots(&self.ctx.terms, &scope) else {
            return false;
        };
        let Some(selected) =
            ay_proof::recognize_seq_extensional_companion_contradiction(&self.ctx.terms, &roots)
        else {
            return false;
        };
        let count = selected.len();
        if !proof.named_steps.is_empty() || proof.steps.len() != count * 2 + 1 {
            return false;
        }
        if !proof.steps[..count]
            .iter()
            .zip(selected.iter())
            .all(|(step, root)| matches!(step, ProofStep::Assume(found) if found == root))
        {
            return false;
        }
        let ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        } = &proof.steps[count]
        else {
            return false;
        };
        if theory != "BV_LIA"
            || farkas.is_some()
            || lia.is_some()
            || *kind != TheoryLemmaKind::SeqExtensionalCompanionContradiction
            || clause.len() != count
            || !clause.iter().zip(selected.iter()).all(
                |(literal, root)| matches!(self.ctx.terms.get(*literal), TermData::Not(inner) if inner == root),
            )
        {
            return false;
        }
        for index in 0..count {
            let ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } = &proof.steps[count + 1 + index]
            else {
                return false;
            };
            if *pivot != selected[index]
                || *clause1 != ProofId((count + index) as u32)
                || *clause2 != ProofId(index as u32)
                || clause.len() != count - index - 1
                || !clause.iter().zip(selected[index + 1..].iter()).all(
                    |(literal, root)| matches!(self.ctx.terms.get(*literal), TermData::Not(inner) if inner == root),
                )
            {
                return false;
            }
        }
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &scope).is_ok()
            && self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
            && Self::proof_derives_empty_clause(proof)
    }
}
