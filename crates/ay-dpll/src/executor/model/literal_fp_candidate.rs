// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct scalar witnesses for literal FP definitions. This proposes model
//! DATA, never UNSAT, never a refutation or a replacement validation authority.

use super::evaluation_copies::EvaluationCopyScope;
use super::{EvalValue, Executor, Model};
use crate::executor_types::UnknownOrigin;
use ay_core::term::{reserve_map_counted, Symbol, TermConstructionAdmission};
use ay_core::{Sort, TermData, TermId};
use std::sync::Arc;

fn stopped(exec: &Executor) -> UnknownOrigin {
    exec.evaluation_stop_origin()
        .unwrap_or_else(|| exec.record_evaluation_stop(UnknownOrigin::IncompleteSolverLane))
}

/// Recognize closed IEEE numeral syntax, including the canonical form emitted
/// by the rewriter. Inspect borrowed IDs/metadata before any numeric copy.
fn literal_definition(
    exec: &Executor,
    root: TermId,
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<(TermId, TermId)>, UnknownOrigin> {
    owner.admit(1, 0).map_err(|_| stopped(exec))?;
    let terms = &exec.ctx.terms;
    let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
        return Ok(None);
    };
    if name.as_ref() != "="
        || args.len() != 2
        || terms.sort(root) != &Sort::Bool
        || terms.is_declared_function("=")
    {
        return Ok(None);
    }
    for (var, rhs) in [(args[0], args[1]), (args[1], args[0])] {
        let TermData::Var(name, _) = terms.get(var) else {
            continue;
        };
        let Sort::FloatingPoint(..) = terms.sort(var) else {
            continue;
        };
        owner.admit(name.len(), 0).map_err(|_| stopped(exec))?;
        let Some(info) = exec.ctx.symbol_info_by_identity(name.as_ref()) else {
            continue;
        };
        if info.term != Some(var)
            || !info.arg_sorts.is_empty()
            || terms.sort(var) != terms.sort(rhs)
        {
            continue;
        }
        if !crate::preprocess::fp_literal::is_value(terms, rhs, owner).map_err(|_| stopped(exec))? {
            continue;
        }
        owner.check().map_err(|_| stopped(exec))?;
        return Ok(Some((var, rhs)));
    }
    Ok(None)
}

impl Executor {
    /// Literal definitions often already supply a complete witness. Construct
    /// it before eager FP circuitry, retaining the SAME query's read counter,
    /// source fence, stop and paid DATA. This precheck uses the exact rewrite
    /// boundary's outputs, retaining any unrepresented canonical obligations.
    /// It grants no SAT authority: the ordinary funnel checks all originals.
    pub(in crate::executor) fn try_literal_fp_model(
        &self,
        original_fp_assertions: &[TermId],
    ) -> Result<Option<Model>, UnknownOrigin> {
        let scope = EvaluationCopyScope::enter(self)?;
        let admission = scope.read_admission(self);
        let owner: &dyn TermConstructionAdmission = &admission;
        let mut model = Model::empty();
        // An identical literal definition supplies the identical value. Keep
        // this syntactic memo under the SAME construction admission; repeated
        // assertions must not repeatedly decode arbitrary-width numerals.
        // Different right-hand sides still take the semantic conflict check.
        let mut literal_rhs = ay_core::kani_compat::DetHashMap::default();
        for &root in &self.ctx.assertions {
            let Some((var, rhs)) = literal_definition(self, root, owner)? else {
                continue;
            };
            if literal_rhs.get(&var) == Some(&rhs) {
                continue;
            }
            if model.construction_owner.is_none() && !self.bind_model_construction_owner(&mut model)
            {
                return self.evaluation_stop_origin().map_or(Ok(None), Err);
            }
            let value = self.evaluate_term(&model, rhs);
            owner.check().map_err(|_| stopped(self))?;
            let EvalValue::Fp(ref fp) = value else {
                continue;
            };
            if self.ctx.terms.sort(var) != &Sort::FloatingPoint(fp.eb(), fp.sb()) {
                continue;
            }
            if let Some(EvalValue::Fp(previous)) = model.completed_values.get(&var) {
                let equal =
                    super::recovery_admission::admitted_fp_equal(previous, fp, |work, bytes| {
                        owner.admit(work, bytes).is_ok()
                    });
                owner.check().map_err(|_| stopped(self))?;
                if equal != Some(true) {
                    return Ok(None);
                }
                literal_rhs.insert(var, rhs);
                continue;
            }
            if !super::recovery_admission::admit_eval_value_copy(&value, |work, bytes| {
                owner.admit(work, bytes).is_ok()
            }) {
                return Err(stopped(self));
            }
            reserve_map_counted(&mut model.completed_values, 1, owner)
                .map_err(|_| stopped(self))?;
            reserve_map_counted(&mut literal_rhs, 1, owner).map_err(|_| stopped(self))?;
            super::eval_memo_clear();
            model.revoke_all_quantified_model_seals();
            model.completed_values.insert(var, value);
            literal_rhs.insert(var, rhs);
        }
        if model.completed_values.is_empty() {
            return Ok(None);
        }
        let roots = self.literal_fp_advisory_roots(original_fp_assertions, owner)?;
        if !self.independent_evaluator_confirms(&model, &roots)? {
            owner.check().map_err(|_| stopped(self))?;
            return Ok(None);
        }
        owner
            .admit(
                1,
                size_of::<super::evaluation_copies::RetainedEvaluationMemory>()
                    + 2 * size_of::<usize>(),
            )
            .map_err(|_| stopped(self))?;
        let Some(memory) = scope.retain_data_memory(self) else {
            return self.evaluation_stop_origin().map_or(Ok(None), Err);
        };
        model._scalar_candidate_memory = Some(Arc::new(memory));
        owner.check().map_err(|_| stopped(self))?;
        Ok(Some(model))
    }

    fn literal_fp_advisory_roots(
        &self,
        original_fp_assertions: &[TermId],
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Vec<TermId>, UnknownOrigin> {
        if original_fp_assertions.len() != self.ctx.assertions.len() {
            return Err(stopped(self));
        }
        let mut rewritten = ay_core::kani_compat::DetHashMap::default();
        reserve_map_counted(&mut rewritten, original_fp_assertions.len(), owner)
            .map_err(|_| stopped(self))?;
        for (&input, &output) in original_fp_assertions.iter().zip(&self.ctx.assertions) {
            owner.admit(1, 0).map_err(|_| stopped(self))?;
            if rewritten
                .insert(input, output)
                .is_some_and(|previous| previous != output)
            {
                return Err(stopped(self));
            }
        }
        // This is the canonical authored-base + deduplicated-assumptions
        // collector, not merely the current rewritten assertion stack.
        let mut roots = self.independent_gate_query_roots()?;
        for root in &mut roots {
            owner.admit(1, 0).map_err(|_| stopped(self))?;
            if let Some(&output) = rewritten.get(root) {
                *root = output;
            }
        }
        owner.check().map_err(|_| stopped(self))?;
        Ok(roots)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    fn execute(input: &str) -> (Executor, Vec<String>) {
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&parse(input).unwrap()).unwrap();
        (exec, outputs)
    }

    #[test]
    fn literal_fp_candidate_checks_original_wide_remainder_without_bit_blasting() {
        let input = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../ay-model-check/tests/fixtures/wide-fp-remainder-odd-divisor.smt2"
        ));
        let (exec, outputs) = execute(input);
        assert_eq!(outputs, ["sat"]);
        assert_eq!(
            exec.last_statistics.get_int("fp.literal_model.bindings"),
            Some(2)
        );
        assert_eq!(exec.validate_model().unwrap().checked, 3);
        assert!(exec.last_model_validated);
        assert!(exec
            .last_model
            .as_ref()
            .unwrap()
            ._scalar_candidate_memory
            .is_some());
    }

    #[test]
    fn literal_fp_candidate_keeps_the_existing_eleven_assertion_budget() {
        let input = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../ay-model-check/tests/fixtures/wide-fp-remainder.smt2"
        ));
        let (exec, outputs) = execute(input);
        assert_eq!(outputs, ["sat"]);
        assert!(exec.last_model_validated);
        assert_eq!(exec.validate_model().unwrap().checked, 11);
    }

    #[test]
    fn literal_fp_candidate_preserves_field_only_results_with_huge_finite_exponents() {
        let input = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../ay-model-check/tests/fixtures/wide-fp-remainder-special-fields.smt2"
        ));
        let (exec, outputs) = execute(input);
        assert_eq!(outputs, ["sat"]);
        assert!(exec.last_model_validated);
        assert_eq!(exec.validate_model().unwrap().checked, 8);
    }

    #[test]
    fn literal_fp_candidate_never_publishes_a_false_or_conflicting_witness() {
        for body in [
            "(assert (= x ((_ to_fp 5 11) RNE 5.0)))
             (assert (= x ((_ to_fp 5 11) RNE 4.0)))",
            "(assert (= x ((_ to_fp 5 11) RNE 5.0)))
             (assert (= (fp.rem x ((_ to_fp 5 11) RNE 3.0)) ((_ to_fp 5 11) RNE 2.0)))",
        ] {
            let (exec, outputs) = execute(&format!(
                "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11)) {body} (check-sat)"
            ));
            assert_eq!(outputs, ["unsat"]);
            assert!(exec.last_model.is_none());
        }
    }

    #[test]
    fn literal_fp_candidate_keeps_scope_and_does_not_treat_disjuncts_as_pins() {
        let (exec, outputs) = execute(
            "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11))
             (push) (assert (= x ((_ to_fp 5 11) RNE 5.0))) (check-sat) (pop)
             (push) (assert (= x ((_ to_fp 5 11) RNE 4.0))) (check-sat) (pop)
             (assert (or (= x ((_ to_fp 5 11) RNE 1.0)) (= x ((_ to_fp 5 11) RNE 5.0))))
             (assert (= (fp.rem x ((_ to_fp 5 11) RNE 3.0)) ((_ to_fp 5 11) RNE (- 1.0))))
             (check-sat)",
        );
        assert_eq!(outputs, ["sat", "sat", "sat"]);
        assert!(exec.last_model_validated);
        assert_eq!(exec.validate_model().unwrap().checked, 2);
    }

    #[test]
    fn literal_fp_candidate_cannot_bypass_the_original_resource_stop() {
        use std::sync::atomic::{AtomicBool, Ordering};
        let (mut exec, _) = execute(
            "(set-logic QF_FP)
             (declare-const x (_ FloatingPoint 5 11))
             (assert (= x ((_ to_fp 5 11) RNE 5.0)))",
        );
        let stopped = Arc::new(AtomicBool::new(true));
        exec.set_interrupt(Arc::clone(&stopped));
        assert_eq!(
            exec.execute(&ay_frontend::Command::CheckSat).unwrap(),
            Some("unknown".into())
        );
        assert!(exec.last_model.is_none());
        stopped.store(false, Ordering::SeqCst);
        assert_eq!(
            exec.execute(&ay_frontend::Command::CheckSat).unwrap(),
            Some("sat".into())
        );
        assert!(exec.last_model_validated);
    }

    #[test]
    fn literal_fp_candidate_preserves_assumptions_outside_the_rewrite_window() {
        let (exec, outputs) = execute(
            "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11))
             (assert (= x ((_ to_fp 5 11) RNE 5.0)))
             (check-sat-assuming ((not (= x ((_ to_fp 5 11) RNE 5.0)))))
             (check-sat)",
        );
        assert_eq!(outputs, ["unsat", "sat"]);
        assert!(exec.last_model_validated);
    }

    fn invalid_witness_query() -> Executor {
        let (mut exec, _) = execute(
            "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11))
             (assert (= x ((_ to_fp 5 11) RNE 5.0)))
             (assert (= (fp.rem x ((_ to_fp 5 11) RNE 3.0))
                        ((_ to_fp 5 11) RNE 2.0)))",
        );
        exec.begin_external_decision_query(false);
        exec.independent_gate_authored_assertions = Some(exec.ctx.assertions.clone());
        exec
    }

    #[test]
    fn literal_fp_candidate_does_not_drop_unrepresented_authored_roots() {
        let mut exec = invalid_witness_query();
        let inputs = [exec.ctx.assertions[0]];
        // Simulate an earlier preprocessing window with only the defining pin.
        // The contradictory authored root is not covered by this rewrite pair.
        exec.ctx.assertions.truncate(1);
        let mut rewriter = ay_fp::rewriter::FpRewriter::new();
        exec.ctx.assertions[0] = rewriter.rewrite(&mut exec.ctx.terms, inputs[0]);
        assert!(exec.try_literal_fp_model(&inputs).unwrap().is_none());
    }

    #[test]
    fn literal_fp_advisory_acceptance_cannot_authorize_sat_for_false_originals() {
        use crate::executor_types::SolveResult;
        let mut exec = invalid_witness_query();
        let inputs = exec.ctx.assertions.clone();
        let mut rewriter = ay_fp::rewriter::FpRewriter::new();
        for root in &mut exec.ctx.assertions {
            *root = rewriter.rewrite(&mut exec.ctx.terms, *root);
        }
        // Deliberately corrupt the advisory rewrite of the contradictory
        // remainder claim. This must NEVER bypass the original-root gate.
        exec.ctx.assertions[1] = exec.ctx.terms.mk_bool(true);
        let model = exec.try_literal_fp_model(&inputs).unwrap().unwrap();
        exec.last_model = Some(model);
        exec.last_model_validated = false;
        assert_eq!(
            exec.emit_sat_verdict(SolveResult::Sat, &inputs).unwrap(),
            SolveResult::Unknown
        );
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());
    }

    #[test]
    fn literal_fp_candidate_preserves_ieee_triples_and_negative_zero() {
        let (exec, outputs) = execute(
            "(set-logic QF_FP) (declare-const x (_ FloatingPoint 5 11))
             (declare-const y (_ FloatingPoint 5 11))
             (assert (= x (fp #b0 #b10001 #b0100000000)))
             (assert (= y (_ -zero 5 11)))
             (assert (= (fp.rem y x) y)) (check-sat)",
        );
        assert_eq!(outputs, ["sat"]);
        assert_eq!(
            exec.last_statistics.get_int("fp.literal_model.bindings"),
            Some(2)
        );
        assert_eq!(exec.validate_model().unwrap().checked, 3);
    }
}
