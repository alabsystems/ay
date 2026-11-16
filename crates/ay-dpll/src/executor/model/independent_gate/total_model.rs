// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified SAT funnel never confirms a model that leaves a constant
//! the quantifier preprocessing removed without a value (2026-09-25 verify of
//! the quantifier repair, B3).
//!
//! A quantified assertion can hold under a model that gives one of its free
//! constants no value — `(or (= (* v w) 0) …)` with `w = 0` holds for every
//! `v` whatever `z` is — and the quantified gate confirmed such a model once
//! the affine elimination had removed `z` from the formula the solver
//! decided. The answer was `sat` with `confirmed-sat`, and `(get-model)` then
//! failed with "sat accepted without a total model". Model completion now
//! gives every constant the preprocessing removed the canonical default
//! before the gates run (`model/completion/preprocess_eliminated.rs`); a
//! constant the confirmed model still leaves open gets its default here and
//! the model is gated again ([`Executor::complete_partial_quantified_model`]);
//! the refusal withdraws the `sat` when neither could (a sort with no
//! canonical default, a lane that withheld it, a default the gates reject),
//! instead of confirming a model that is not total.

use ay_core::{Sort, TermId};

use super::super::EvalValue;
use super::{contains_quantifier, independent_gate_query_roots, Executor, SolveResult};
use crate::executor_types::Result;

/// The default a missing constant gets before the model is gated again.
enum GapDefault {
    /// A scalar or uninterpreted element, through the completion slot.
    Scalar(EvalValue),
    /// A datatype constant: its rendering and ground value.
    Datatype(String, ay_model_check::ModelValue),
}

impl Executor {
    /// `result`, re-gated over a model completed with the canonical default of
    /// every declared constant the query mentions and the confirmed model
    /// leaves without a value (2026-09-29, fix-up session 4). A ground
    /// assertion can hold whatever such a constant is — `(not (null (cons x
    /// xs)))` under `∀l. null l = (l = nil)` holds for every `x` — so the
    /// gates confirmed the model with `x` unassigned, main printed `sat` and
    /// then "sat accepted without a total model", and the refusal below
    /// withdrew the `sat` (the UFDT `nunchaku2067278` corpus file). The
    /// completed model goes through the strict validation and the quantified
    /// gate again, and the independent gate after them, exactly as any model:
    /// a default that falsifies or leaves undecided some assertion is not
    /// confirmed, and the refusal still withdraws the `sat`. Only when the
    /// quantified gate confirmed the model by its own nested solves (the
    /// refusal's `every_constant` scope); a certificate lane's sealed model is
    /// completed before the seal instead.
    pub(in crate::executor) fn complete_partial_quantified_model(
        &mut self,
        result: SolveResult,
    ) -> Result<SolveResult> {
        if result != SolveResult::Sat
            || self.quantified_model_confirmation.is_none()
            || self.in_quantified_model_gate
        {
            return Ok(result);
        }
        let Ok(query_roots) = independent_gate_query_roots(self) else {
            return Ok(SolveResult::Unknown);
        };
        let missing = self.constants_without_value(&query_roots, true);
        if missing.is_empty() {
            return Ok(result);
        }
        // Every missing constant needs a default, or none is completed: a
        // partial completion leaves the refusal below to withdraw the `sat`.
        let guard = super::super::rendered_dt_guard::RenderedDatatypeGuard::new(self);
        let mut defaults = Vec::with_capacity(missing.len());
        for &term in &missing {
            let sort = self.ctx.terms.sort(term);
            let default = match self.unconstrained_default_value(sort) {
                Some(value) => GapDefault::Scalar(value),
                None => match self.datatype_default(sort, &guard) {
                    Some((rendered, value)) => GapDefault::Datatype(rendered, value),
                    None => return Ok(result),
                },
            };
            defaults.push((term, default));
        }
        // Scalars and elements go to the completion slot, which the strict
        // validation below keeps; that validation rebuilds the datatype model
        // from the assertions, so a datatype default is installed after it,
        // before the quantified gate and the independent gate check it.
        let (scalars, datatypes): (Vec<_>, Vec<_>) = defaults
            .into_iter()
            .partition(|(_, default)| matches!(default, GapDefault::Scalar(_)));
        let Some(mut model) = self.last_model.take() else {
            return Ok(result);
        };
        let inserted = scalars.iter().all(|(term, default)| match default {
            GapDefault::Scalar(value) => {
                Self::insert_completed_value(&self.ctx.terms, &mut model, *term, value)
            }
            GapDefault::Datatype(..) => true,
        });
        self.last_model = Some(model);
        if !inserted {
            return Ok(result);
        }
        super::super::eval_memo_clear();
        self.last_model_validated = false;
        self.last_statistics.set_int(
            "model_completion.confirmed_gap_defaults",
            missing.len() as u64,
        );
        let gated = self.finalize_sat_model_validation()?;
        if gated != SolveResult::Sat {
            return Ok(gated);
        }
        if let Some(model) = self.last_model.as_mut() {
            for (term, default) in datatypes {
                if let GapDefault::Datatype(rendered, value) = default {
                    // The shape `apply_exact_datatype_cell_completions`
                    // installs: the ground value every evaluator reads, and
                    // its pin. Fill-only: a value the rebuilt model now has
                    // stays.
                    if model.dt_ground.contains_key(&term) || model.dt_pins.contains_key(&term) {
                        continue;
                    }
                    model.revoke_all_quantified_model_seals();
                    model.dt_ground.insert(term, value);
                    model.dt_pins.insert(term, EvalValue::Element(rendered));
                }
            }
        }
        super::super::eval_memo_clear();
        Ok(self.apply_quantified_model_failclosed_gate(gated))
    }

    /// The canonical constructor value of datatype `sort` (a nullary
    /// constructor when there is one) as the model's rendering and ground
    /// value, when that rendering parses back under the exact datatype guard.
    fn datatype_default(
        &self,
        sort: &Sort,
        guard: &super::super::rendered_dt_guard::RenderedDatatypeGuard,
    ) -> Option<(String, ay_model_check::ModelValue)> {
        if !matches!(sort, Sort::Datatype(_)) && self.datatype_sort_name(sort).is_none() {
            return None;
        }
        let rendered = self.canonical_default_value(sort);
        let value = self.parse_rendered_dt_value_cached(&rendered, sort, guard)?;
        Some((rendered, value))
    }

    /// `result`, unless it is a `Sat` over a quantified query whose emitted
    /// model has no value for a declared constant the query mentions — any
    /// such constant when the quantified gate confirmed the model by its own
    /// nested solves, one the quantifier preprocessing removed when a
    /// certificate was handed off — then the `sat` is withdrawn.
    pub(in crate::executor) fn refuse_partial_quantified_model(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        let every_constant = self.quantified_model_confirmation.is_some();
        // The same scope as the quantified gate itself: never inside its own
        // nested confirmation solves.
        if result != SolveResult::Sat
            || (!every_constant && self.preprocess_eliminated_constants.is_empty())
            || self.in_quantified_model_gate
        {
            return result;
        }
        let Ok(query_roots) = independent_gate_query_roots(self) else {
            return SolveResult::Unknown;
        };
        if !query_roots
            .iter()
            .any(|&root| contains_quantifier(&self.ctx.terms, root))
        {
            return result;
        }
        let Some(term) = self.constant_without_value(&query_roots, every_constant) else {
            return result;
        };
        let name = self.format_term(term);
        self.last_statistics
            .set_string("model_check_gate.quantified", "partial-model-failclosed");
        self.last_statistics.set_string(
            "model_check_gate.quantified_reason",
            format!("no model value for {name}"),
        );
        self.downgrade_sat_after_gate(
            "the emitted model has no value for a constant the quantifier \
             preprocessing removed — a model that is not total is not confirmed",
        );
        SolveResult::Unknown
    }

    /// The first ordinary declared constant (not an array: its value is its
    /// interpretation, completed and printed by its own machinery) that
    /// `query_roots` or the assertions mention, that the emitted model gives
    /// no value, and — unless `every_constant` — that the quantifier
    /// preprocessing removed.
    fn constant_without_value(
        &self,
        query_roots: &[TermId],
        every_constant: bool,
    ) -> Option<TermId> {
        self.constants_without_value(query_roots, every_constant)
            .into_iter()
            .next()
    }

    /// Every such constant, in term order.
    fn constants_without_value(&self, query_roots: &[TermId], every_constant: bool) -> Vec<TermId> {
        let Some(model) = self.last_model.as_ref() else {
            return Vec::new();
        };
        let occurring = self.collect_occurring_vars(query_roots);
        let mut missing: Vec<TermId> = Vec::new();
        for (surface_name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty()
                || matches!(info.sort, Sort::Array(_))
                || !self.is_ordinary_free_primary_declaration(surface_name, info)
            {
                continue;
            }
            let Some(term) = info.term else {
                continue;
            };
            if (every_constant || self.preprocess_eliminated_constants.contains(&term))
                && occurring.contains(&term)
                && matches!(self.evaluate_term(model, term), EvalValue::Unknown)
            {
                missing.push(term);
            }
        }
        missing.sort_by_key(|term| term.index());
        missing.dedup();
        missing
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::Model;
    use super::{EvalValue, Executor, SolveResult};

    /// The executor of a B3 witness, with `z` (a Boolean here: an `Int`
    /// without an arithmetic model reads as 0) recorded as removed by the
    /// preprocessing and an emitted model that gives it no value.
    fn witness_with_partial_model() -> (Executor, ay_core::TermId) {
        let commands = ay_frontend::parse(
            "(set-logic ALL) (declare-fun w () Int) (declare-fun z () Bool)
             (assert (forall ((v Int)) (or (= (* v w) 0) (= (+ (* 2 v) (ite z 1 0)) 1))))",
        )
        .expect("fixture parses");
        let mut exec = Executor::new();
        for command in &commands {
            exec.execute(command).expect("fixture executes");
        }
        let z = exec
            .ctx
            .symbol_info("z")
            .and_then(|info| info.term)
            .expect("z is declared");
        exec.preprocess_eliminated_constants = vec![z];
        exec.last_model = Some(Model::empty());
        (exec, z)
    }

    /// Completion normally fills such a constant before the gates (measured:
    /// every sort a removed constant took in the probes got its default, so
    /// no source file reaches this); when it could not, the funnel must not
    /// confirm the partial model.
    #[test]
    fn a_model_without_a_value_for_an_eliminated_constant_is_refused() {
        let (mut exec, z) = witness_with_partial_model();
        let roots = exec.independent_gate_query_roots().unwrap();
        assert!(
            roots
                .iter()
                .any(|&root| super::contains_quantifier(&exec.ctx.terms, root)),
            "the query is quantified: {roots:?}"
        );
        assert!(
            exec.collect_occurring_vars(&roots).contains(&z),
            "z occurs in the query"
        );
        let info = exec.ctx.symbol_info("z").expect("z is declared");
        assert!(
            exec.is_ordinary_free_primary_declaration("z", info),
            "z is an ordinary declaration"
        );
        let model = exec.last_model.as_ref().expect("model installed");
        assert!(
            matches!(exec.evaluate_term(model, z), EvalValue::Unknown),
            "the model gives z no value"
        );
        assert_eq!(
            exec.refuse_partial_quantified_model(SolveResult::Sat),
            SolveResult::Unknown,
            "a sat whose model gives the eliminated z no value is not confirmed"
        );
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some("partial-model-failclosed")
        );
    }

    #[test]
    fn a_total_model_passes_the_refusal() {
        let (mut exec, z) = witness_with_partial_model();
        let mut model = exec.last_model.take().expect("model installed");
        assert!(Executor::insert_completed_value(
            &exec.ctx.terms,
            &mut model,
            z,
            &EvalValue::Bool(false)
        ));
        exec.last_model = Some(model);
        assert_eq!(
            exec.refuse_partial_quantified_model(SolveResult::Sat),
            SolveResult::Sat
        );
    }
}
