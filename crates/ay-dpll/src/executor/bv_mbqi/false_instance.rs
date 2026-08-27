// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Evaluation and proof-authority capture for one ground BV-MBQI instance.
//!
//! A definitively false instance may be folded to the literal `false` before
//! reaching SAT, losing its authored origin. The retained record therefore
//! carries the exact raw substitution replayed by `forall_inst`, while the
//! sealed-token consumer independently checks both that substitution and the
//! model-free fold. Strict proof checking then re-proves the fold bridge.

use ay_core::TermId;

use super::{EvalValue, Executor, HashMap, HashSet};
use crate::executor::model::Model;

impl Executor {
    pub(super) fn observe_bv_mbqi_instance(
        &mut self,
        quantifier: TermId,
        body: TermId,
        substitution: &HashMap<String, TermId>,
        binding: &[TermId],
        ground_body: TermId,
        empty_model: &Model,
        outputs: (
            &mut HashSet<TermId>,
            &mut Vec<TermId>,
            &mut Vec<crate::ematching::ForallInstantiationProvenance>,
        ),
    ) -> bool {
        let (seen_instantiations, new_instantiations, refinement_provenance) = outputs;
        // Model-less rounds constant-fold against the empty model instead:
        // fully interpreted closed instances get a definite verdict, while
        // anything needing a model value fails closed to `Unknown`.
        let eval = match self.last_model {
            Some(ref model) => self.evaluate_term(model, ground_body),
            None => self.evaluate_term(empty_model, ground_body),
        };
        match eval {
            EvalValue::Bool(true) => true,
            EvalValue::Bool(false) => {
                if seen_instantiations.insert(ground_body) {
                    new_instantiations.push(ground_body);
                    // Every pushed instance is a `forall_inst` consequence of
                    // an authored universal, and that justification needs no
                    // model: the model only guided the CHOICE of binding.
                    // Without this record the proof layer cannot see where a
                    // model-relative counterexample came from, so a genuine
                    // refutation was demoted to Unknown (the wide-binder
                    // regression). Records carry no authority of their own —
                    // `CheckedInstanceDerivation::seal` replays the exact
                    // substitution, so a wrong record can only decline.
                    if crate::quant_unit_authority::consequence_replay_enabled() {
                        refinement_provenance.push(
                            crate::ematching::ForallInstantiationProvenance {
                                quantifier,
                                binding: binding.to_vec(),
                                instance: ground_body,
                            },
                        );
                    }
                    self.record_bv_mbqi_false_instance(
                        quantifier,
                        body,
                        substitution,
                        binding,
                        ground_body,
                        empty_model,
                    );
                }
                false
            }
            _ => false,
        }
    }

    fn record_bv_mbqi_false_instance(
        &mut self,
        quantifier: TermId,
        body: TermId,
        substitution: &HashMap<String, TermId>,
        binding: &[TermId],
        ground_body: TermId,
        empty_model: &Model,
    ) {
        // (#bv-mbqi-false-instance-authority, P3b) Producer provenance is
        // recorded at the push site and keyed by the SAT-visible term after
        // Boolean folding. A model-relative counterexample is not a fold
        // claim, so independently require a model-free `false` evaluation.
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || !matches!(
                self.evaluate_term(empty_model, ground_body),
                EvalValue::Bool(false)
            )
        {
            return;
        }
        let Some(instance) =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, substitution)
        else {
            return;
        };
        let asserted = self.ctx.terms.false_term();
        self.bv_mbqi_false_instance_records
            .push(crate::executor::BvMbqiFalseInstanceRecord {
                quantifier,
                values: binding.to_vec(),
                instance,
                asserted,
            });
    }
}
