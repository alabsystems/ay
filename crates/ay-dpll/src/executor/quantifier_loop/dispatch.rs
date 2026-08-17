// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic-category dispatch and E-matching refinement for quantifier solving.
//!
//! `solve_for_category` mirrors the main dispatch table in `executor.rs` for
//! re-solving during CEGQI and E-matching refinement loops.
//! `try_ematching_refinement_round` runs one interleaved E-matching round
//! using the fresh EUF model after a SAT solve.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;
use crate::quantifier_manager::QuantifierManager;

/// Result of one interleaved E-matching refinement round.
pub(in crate::executor) struct EmatchingRefinementRound {
    pub added: usize,
    pub reached_limit: bool,
    pub has_uninstantiated: bool,
    pub instances_created: u64,
}

impl Executor {
    /// Dispatch to the appropriate theory solver for the given logic category.
    ///
    /// Must mirror the main dispatch table in `executor.rs` check_sat_internal.
    /// Missing categories here cause CEGQI refinement to silently return Unknown (#5989).
    pub(in crate::executor) fn solve_for_category(
        &mut self,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        if ay_core::misc_cli_flags().f1_diag {
            let result = self.solve_for_category_inner(category);
            if let Ok(r) = &result {
                eprintln!(
                    "--f1-diag: solve_for_category({category:?}) -> {r:?} model_present={}",
                    self.last_model.is_some()
                );
            }
            return result;
        }
        self.solve_for_category_inner(category)
    }

    fn solve_for_category_inner(&mut self, category: LogicCategory) -> Result<SolveResult> {
        // Refinement rounds append fresh ground instances after the ordinary
        // pre-dispatch pass. Non-owning routes must close those roots here;
        // owning routes run exact closure on their post-preprocessing surface.
        let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        if features.has_arrays && !self.should_defer_finite_array_extensionality_to_route(category)
        {
            let _ = self.add_finite_index_array_closure();
        }

        let result = match category {
            LogicCategory::Propositional => self.solve_propositional(),
            LogicCategory::QfUf | LogicCategory::Uf => self.solve_euf(),
            LogicCategory::QfAx => self.solve_array_euf(),
            LogicCategory::QfLra | LogicCategory::Lra => self.solve_lra(),
            LogicCategory::QfLia | LogicCategory::Lia => self.solve_lia(),
            LogicCategory::QfNia | LogicCategory::QfEia | LogicCategory::Nia => self.solve_nia(),
            LogicCategory::QfNra | LogicCategory::Nra => self.solve_nra(),
            LogicCategory::QfLira | LogicCategory::Lira => self.solve_lira(),
            LogicCategory::QfNira | LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfUfnra | LogicCategory::Ufnra => self.solve_uf_nra(),
            LogicCategory::QfUfnia | LogicCategory::Ufnia => self.solve_uf_nia(),
            // NIRA routing: solve_uf_nia() lacks LRA, so Real constraints
            // produce false SAT. Return Unknown for NIRA variants (#8200).
            LogicCategory::QfUfnira | LogicCategory::Ufnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfUflia | LogicCategory::Uflia => self.solve_auf_lia(),
            LogicCategory::QfUflra | LogicCategory::Uflra => self.solve_uf_lra(),
            LogicCategory::QfAuflia | LogicCategory::Auflia => self.solve_auf_lia(),
            LogicCategory::QfAuflra | LogicCategory::Auflra => self.solve_auf_lra(),
            LogicCategory::QfAuflira | LogicCategory::Auflira => self.solve_auflira(),
            LogicCategory::QfSeq => self.solve_seq(),
            LogicCategory::QfSeqBv => self.solve_seq(),
            LogicCategory::QfSeqlia => self.solve_seq_lia(),
            LogicCategory::QfSet | LogicCategory::QfSetlia => self.solve_set_lia(),
            LogicCategory::QfMultiset | LogicCategory::QfMslia => self.solve_multiset_lia(),
            LogicCategory::QfMap | LogicCategory::QfMaplia => self.solve_map_lia(),
            LogicCategory::QfS => self.solve_strings(),
            LogicCategory::QfSlia => self.solve_strings_lia(),
            LogicCategory::QfSnia => {
                let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia()
                }
            }
            LogicCategory::QfBv => self.solve_bv(),
            LogicCategory::QfAbv => self.solve_abv(),
            LogicCategory::QfUfbv => self.solve_ufbv(),
            LogicCategory::QfAufbv => self.solve_aufbv(),
            LogicCategory::QfBvLia => self.solve_bv_lia_bridge(),
            LogicCategory::QfBvLiaIndep => self.solve_bv_lia_indep(),
            LogicCategory::QfFp => self.solve_fp(),
            LogicCategory::QfBvfp => self.solve_bvfp(),
            LogicCategory::QfAbvfp => self.solve_abvfp(),
            LogicCategory::QfDt => self.solve_dt(),
            LogicCategory::DtAuflia => self.solve_dt_auflia(),
            LogicCategory::DtAuflra => self.solve_dt_auflra(),
            LogicCategory::DtAuflira => self.solve_dt_auflira(),
            LogicCategory::DtUfbv => self.solve_dt_ufbv(),
            LogicCategory::DtAufbv => self.solve_dt_aufbv(),
            LogicCategory::DtAx => self.solve_dt_ax(),
            // Quantified DT logics (#7150): route to DT-combined solvers
            LogicCategory::Ufdt => self.solve_dt(),
            LogicCategory::Aufdt => self.solve_dt_ax(),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => self.solve_dt_auflia(),
            LogicCategory::Ufdtlra => self.solve_dt_auflra(),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self.solve_dt_auflira(),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
        };
        self.fail_close_incomplete_finite_array_sat(result)
    }

    /// Phase B1c (#3325): Run one E-matching refinement round using the fresh EUF model.
    ///
    /// Returns metadata for the E-matching round, or `None` if no model is available.
    pub(in crate::executor) fn try_ematching_refinement_round(
        &mut self,
        original_assertions: &[TermId],
        cegqi_ce_lemma_ids: &[TermId],
    ) -> Option<EmatchingRefinementRound> {
        // Deadline/interrupt guard (#quantifier-deadline): if the budget is
        // exhausted, return a round flagged `reached_limit = true` with no new
        // instantiations. The interleaved caller folds this into
        // `state.reached_instantiation_limit`, which classify_quantifier_result
        // routes to Unknown(QuantifierRoundLimit) — never a finalized Sat. We
        // deliberately do NOT return `None` here, because `None` breaks the
        // interleaved loop WITHOUT setting the limit flag and could leave a
        // truncated run classified as a final Sat.
        let should_stop = self.make_should_stop();
        if should_stop() {
            return Some(EmatchingRefinementRound {
                added: 0,
                reached_limit: true,
                has_uninstantiated: true,
                instances_created: 0,
            });
        }

        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());
        euf_model_ref?;

        // Counterexample lemmas are temporary validity-check assumptions, not
        // authored ground evidence. If `not B(ce)` enters the E-matching
        // index, the same universal can bind its variable to `ce` and add
        // `B(ce)`, manufacturing an UNSAT conflict with its own search
        // assumption. The setup path keeps this list CE-exclusive by omitting
        // any TermId that was already a genuine assertion, so exact-root
        // removal cannot hide user input or a sound prior instance.
        let ce_only: HashSet<TermId> = cegqi_ce_lemma_ids.iter().copied().collect();
        let mut combined_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|term| !ce_only.contains(term))
            .collect();
        for &a in original_assertions {
            if contains_quantifier(&self.ctx.terms, a) && !combined_assertions.contains(&a) {
                combined_assertions.push(a);
            }
        }

        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        // Fresh round group: each interleaved refinement round runs over a
        // re-cloned, mutated `ctx.assertions` slice (different EUF model, growing
        // ground base) that may not extend the prior round's slice. Reset the
        // index/eqclasses so they are an exact function of `combined_assertions`
        // (the seen memo persists across the epoch).
        qm.begin_round_group();

        let mut ematching_result = qm.run_ematching_round(
            &mut self.ctx.terms,
            &combined_assertions,
            euf_model_ref,
            &should_stop,
        );
        self.materialize_exact_ematching_instances(
            &mut ematching_result.instantiations,
            &mut ematching_result.unconditional_forall_roots,
            &mut ematching_result.unconditional_forall_instantiations,
        );
        self.register_ematching_proof_provenance(
            &ematching_result.unconditional_forall_instantiations,
        );

        let mut existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut added = 0usize;
        let reached_limit = ematching_result.reached_limit;
        let has_uninstantiated = ematching_result.has_uninstantiated;
        let instances_created = ematching_result.instantiations.len() as u64;

        for inst in ematching_result.instantiations {
            if !existing.insert(inst) {
                continue;
            }
            self.ctx.assertions.push(inst);
            added += 1;
            // Record the sound support-axiom subset for the just-added instance
            // so subsequent conflict-verification gates in this same ground solve
            // can reprove conflicts that depend on it (guard (ii) holds: it is
            // now in ctx.assertions).
            if ematching_result.unconditional_forall_roots.contains(&inst) {
                self.push_active_support_axiom(inst);
            }
        }

        Some(EmatchingRefinementRound {
            added,
            reached_limit,
            has_uninstantiated,
            instances_created,
        })
    }
}
