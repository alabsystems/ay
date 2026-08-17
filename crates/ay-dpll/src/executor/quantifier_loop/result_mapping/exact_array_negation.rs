// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent replay and SAT-only authorization of exact array negation.

use ay_core::TermId;

use super::checked_model_rewrite::CheckedModelRewriteSatAuthority;
use crate::ematching::contains_quantifier;
use crate::executor::quantifier_loop::ExactArrayNegationEvidence;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

#[must_use = "checked array-negation SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactArrayNegationSatAuthority {
    checked: CheckedModelRewriteSatAuthority,
}

impl CheckedExactArrayNegationSatAuthority {
    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &mut Executor,
    ) -> Option<(
        Box<[TermId]>,
        crate::executor::model::QuantifiedGrantModelEpoch,
    )> {
        self.checked.into_current_roots(executor)
    }
}

impl Executor {
    /// Route the exact rewrite after all nested probes.
    ///
    /// Only a retained `Sat` can consume the independently replayed,
    /// model-checked evidence. An `Unsat` proof over the rewritten root has no
    /// translated proof of the authored quantified root, so it must fail
    /// closed rather than inherit the ground solver's verdict.
    pub(super) fn route_exact_array_negation_result(
        &mut self,
        result: &mut Result<SolveResult>,
        original: Option<&[TermId]>,
        evidence: Option<&ExactArrayNegationEvidence>,
    ) {
        let (Some(original), Some(evidence)) = (original, evidence) else {
            return;
        };
        if matches!(&*result, Ok(SolveResult::Sat)) {
            if self.authenticate_exact_array_negation_sat(original, evidence) {
                self.defer_model_validation = false;
                self.last_model_validated = true;
            } else {
                *result = self.cegqi_fail_closed_unknown();
            }
        } else if matches!(&*result, Ok(SolveResult::Unsat(_))) {
            *result = self.cegqi_fail_closed_unknown();
        }
    }

    pub(super) fn authenticate_exact_array_negation_sat(
        &mut self,
        original: &[TermId],
        evidence: &ExactArrayNegationEvidence,
    ) -> bool {
        let Some(model_roots) = self.replay_exact_array_negation_evidence(original, evidence)
        else {
            return false;
        };
        let authority_roots = self.independent_gate_query_roots();
        if authority_roots != original {
            return false;
        }
        let Some(checked) = CheckedModelRewriteSatAuthority::for_current(
            self,
            &authority_roots,
            &model_roots,
            "exact-array-negation",
        ) else {
            return false;
        };
        self.install_exact_array_negation_sat_authority(CheckedExactArrayNegationSatAuthority {
            checked,
        })
    }

    fn replay_exact_array_negation_evidence(
        &mut self,
        original: &[TermId],
        evidence: &ExactArrayNegationEvidence,
    ) -> Option<Vec<TermId>> {
        if evidence.original_assertions.as_ref() != original
            || evidence.rewritten_assertions.len() != original.len()
            || evidence.record.assertion_index >= original.len()
        {
            return None;
        }

        let record = &evidence.record;
        if original[record.assertion_index] != record.original
            || evidence.rewritten_assertions[record.assertion_index] != record.rewritten
            || self.ctx.terms.entry_stamp(record.original) != Some(record.original_entry)
            || self.ctx.terms.entry_stamp(record.rewritten) != Some(record.rewritten_entry)
        {
            return None;
        }

        let mut quantified_indices = original
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, root)| contains_quantifier(&self.ctx.terms, *root));
        if quantified_indices.next() != Some((record.assertion_index, record.original))
            || quantified_indices.next().is_some()
        {
            return None;
        }

        for (index, (&source, &rewritten)) in original
            .iter()
            .zip(evidence.rewritten_assertions.iter())
            .enumerate()
        {
            if self.ctx.terms.entry_stamp(source).is_none()
                || self.ctx.terms.entry_stamp(rewritten).is_none()
                || contains_quantifier(&self.ctx.terms, rewritten)
                || (index != record.assertion_index && source != rewritten)
            {
                return None;
            }
        }

        let canonical = self.replay_exact_top_level_array_negation(record.original)?;
        (canonical == record.rewritten).then(|| evidence.rewritten_assertions.to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_arrays::{ArrayInterpretation, ArrayModel};
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::{Sort, TermData};
    use ay_frontend::parse;

    use crate::executor::model::{EvalValue, Model};

    fn exact_fixture() -> (Executor, Vec<TermId>, ExactArrayNegationEvidence) {
        let commands = parse(
            r#"
            (set-logic ALIA)
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (declare-const p Bool)
            (assert p)
            (assert (not (forall ((i Int)) (= (select a i) (select b i)))))
        "#,
        )
        .expect("fixture parses");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("fixture executes")
            .is_empty());
        let original = executor.ctx.assertions.clone();
        let evidence = executor
            .rewrite_exact_top_level_array_negation()
            .expect("fixture is exact");
        (executor, original, evidence)
    }

    fn retained_array_model(
        executor: &Executor,
        evidence: &ExactArrayNegationEvidence,
        lhs_default: &str,
        rhs_default: &str,
    ) -> Model {
        let TermData::Not(equality) = executor.ctx.terms.get(evidence.record.rewritten) else {
            panic!("rewrite root must be a negated equality");
        };
        let TermData::App(symbol, arguments) = executor.ctx.terms.get(*equality) else {
            panic!("rewrite payload must be an equality");
        };
        assert_eq!(symbol.name(), "=");
        assert_eq!(arguments.len(), 2);

        let interpretation = |default: &str| ArrayInterpretation {
            default: Some(default.to_string()),
            stores: Vec::new(),
            index_sort: Some(Sort::Int),
            element_sort: Some(Sort::Int),
        };
        let mut model = Model::empty();
        model.array_model = Some(ArrayModel {
            array_values: HashMap::from_iter([
                (arguments[0], interpretation(lhs_default)),
                (arguments[1], interpretation(rhs_default)),
            ]),
            ..Default::default()
        });
        model
            .completed_values
            .insert(evidence.original_assertions[0], EvalValue::Bool(true));
        model
    }

    #[test]
    fn replay_accepts_only_the_exact_ordered_one_to_one_rewrite() {
        let (mut executor, original, evidence) = exact_fixture();
        assert_eq!(
            executor.replay_exact_array_negation_evidence(&original, &evidence),
            Some(evidence.rewritten_assertions.to_vec())
        );

        let mut wrong_index = evidence.clone();
        wrong_index.record.assertion_index = 0;
        assert!(executor
            .replay_exact_array_negation_evidence(&original, &wrong_index)
            .is_none());

        let mut wrong_replacement = evidence.clone();
        wrong_replacement.record.rewritten = original[0];
        wrong_replacement.record.rewritten_entry = executor
            .ctx
            .terms
            .entry_stamp(original[0])
            .expect("ground sibling is current");
        wrong_replacement.rewritten_assertions[1] = original[0];
        assert!(executor
            .replay_exact_array_negation_evidence(&original, &wrong_replacement)
            .is_none());

        let mut reordered = original.clone();
        reordered.swap(0, 1);
        assert!(executor
            .replay_exact_array_negation_evidence(&reordered, &evidence)
            .is_none());
    }

    #[test]
    fn replay_rejects_a_second_quantified_root_even_with_valid_primary_evidence() {
        let (mut executor, original, evidence) = exact_fixture();
        let second = original[1];
        let mut expanded_original = original;
        expanded_original.push(second);
        let mut forged = evidence;
        forged.original_assertions = expanded_original.clone().into_boxed_slice();
        let mut rewritten = forged.rewritten_assertions.to_vec();
        rewritten.push(second);
        forged.rewritten_assertions = rewritten.into_boxed_slice();
        assert!(executor
            .replay_exact_array_negation_evidence(&expanded_original, &forged)
            .is_none());
    }

    #[test]
    fn checked_model_rejects_false_rewrite_and_token_tracks_exact_model() {
        let (mut rejecting, roots, evidence) = exact_fixture();
        rejecting.independent_gate_authored_assertions = Some(roots.clone());
        rejecting.last_model = Some(retained_array_model(&rejecting, &evidence, "0", "0"));
        assert!(
            !rejecting.authenticate_exact_array_negation_sat(&roots, &evidence),
            "equal arrays falsify the rewritten inequality"
        );
        assert!(!rejecting.mbqi_sat_cert_grant_active);

        let (mut accepted, roots, evidence) = exact_fixture();
        accepted.independent_gate_authored_assertions = Some(roots.clone());
        accepted.last_model = Some(retained_array_model(&accepted, &evidence, "0", "1"));
        assert!(accepted.authenticate_exact_array_negation_sat(&roots, &evidence));
        assert!(accepted.has_current_model_bound_quantified_sat_authority(&roots));

        let exact_model = accepted.last_model.take();
        accepted.last_model = exact_model.clone();
        assert!(
            !accepted.has_current_model_bound_quantified_sat_authority(&roots),
            "a semantic model clone must not inherit the exact rewrite token"
        );
        accepted.last_model = exact_model;
        assert!(
            accepted.has_current_model_bound_quantified_sat_authority(&roots),
            "moving the sealed model back preserves the exact rewrite token"
        );
    }

    #[test]
    fn rewritten_unsat_cannot_escape_the_sat_only_authority_lane() {
        let (mut executor, roots, evidence) = exact_fixture();
        let mut result = Ok(SolveResult::unsat());
        executor.route_exact_array_negation_result(&mut result, Some(&roots), Some(&evidence));

        assert!(matches!(result, Ok(SolveResult::Unknown)));
        assert!(!executor.mbqi_sat_cert_grant_active);
    }
}
