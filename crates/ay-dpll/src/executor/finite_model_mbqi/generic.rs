// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The generic quantified model check (roadmap component QM, model-check
//! half; critic C3).
//!
//! The legacy pass in the parent module is the same argument restricted to
//! universals over floating-point binders with finite-sorted pins. This pass
//! lifts both restrictions:
//!
//! * **binders of any sort.** `P ∧ ¬matrix[sk]` UNSAT with fresh `sk` proves
//!   `forall x̄. matrix` in every model of `P` whatever the binder sorts, and
//!   `P ∧ matrix[t̄]` UNSAT at ANY ground `t̄` proves it false there. Neither
//!   needs the carrier to be fixed; only turning a probe's witness into a term
//!   does, and that falls back to a pinned representative or a fresh constant;
//! * **the whole candidate model is fixed** — scalars, the partition of every
//!   uninterpreted sort, and every uninterpreted function applied in a body as
//!   a table plus an else value (`interpretation.rs`, `tables.rs`).
//!
//! A quantifier the fixed model satisfies is replaced by its constant; the
//! residual is then solved and the staged witness is checked against both the
//! substituted and the original residual before any authority is installed. A
//! universal that the fixed model violates yields a counterexample instance
//! for the existing refinement loop, exactly as the legacy pass does, and only
//! for a universal the problem entails (a top-level conjunct, or an `exists`
//! whose negation-dual is one — the `(assert (not (exists …)))` spelling).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;

use super::interpretation::{is_element_sort, scalar_value_term, Interpretation};
use super::leaves::certified_nodes;
use super::witness::PassOutcome;
use super::{replace_subterms, trace, AuthoredUniversal, LaneBudget, TruthOutcome};
use crate::ematching::subst_vars;
use crate::executor::model::{EvalValue, Model};
use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;
use crate::executor::unsat_cert::ProbeUnsatAuthority;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

use super::budget::MAX_FINITE_MODEL_ROUNDS;

/// The working state a declined refinement must leave exactly as it found
/// it: the pass is a SAT producer, and a decline has to be invisible to the
/// caller's own channels that run next.
struct RefinementCheckpoint {
    assertions: Vec<TermId>,
    last_model: Option<Model>,
    last_model_validated: bool,
    last_result: Option<SolveResult>,
    last_unknown_reason: Option<crate::executor_types::UnknownReason>,
    unlicensed_instance_conjoined: bool,
}

impl RefinementCheckpoint {
    fn take(executor: &Executor) -> Self {
        Self {
            assertions: executor.ctx.assertions.clone(),
            last_model: executor.last_model.clone(),
            last_model_validated: executor.last_model_validated,
            last_result: executor.last_result.clone(),
            last_unknown_reason: executor.last_unknown_reason,
            unlicensed_instance_conjoined: executor.unlicensed_instance_conjoined,
        }
    }

    /// Undo the instances and the re-solves. An instance-driven refutation
    /// also left UNSAT-only artifacts (measured: an LRAT certificate under an
    /// explicit proof request), which no later producer may reuse.
    fn restore(self, executor: &mut Executor, refuted: bool) {
        executor.ctx.assertions = self.assertions;
        executor.last_model = self.last_model;
        executor.last_model_validated = self.last_model_validated;
        executor.last_result = self.last_result;
        executor.last_unknown_reason = self.last_unknown_reason;
        executor.unlicensed_instance_conjoined = self.unlicensed_instance_conjoined;
        crate::executor::model::eval_memo_clear();
        if refuted {
            executor.clear_cegqi_inner_unsat_artifacts();
        }
    }
}

impl Executor {
    /// Is `assertions` refuted by a model-check auxiliary solve? The same
    /// admission as the legacy pass (`finite_model_refutes`): a refutation
    /// resting on `discharged-trust` decides nothing.
    fn qmc_refutes(&mut self, assertions: Vec<TermId>, budget: LaneBudget) -> bool {
        self.finite_model_refutes(assertions, budget)
    }

    /// Terms for the binders of `leaf` from one witness of `assertions`.
    ///
    /// A scalar binder gets its literal. An uninterpreted-sort binder gets
    /// the pinned representative its witness element equals INSIDE THE SAME
    /// probe model, or a fresh constant when it equals none. Any term is
    /// sound here: every use either certifies a value by a checked UNSAT or
    /// asserts an instance of an entailed universal.
    fn qmc_binder_terms(
        &mut self,
        assertions: Vec<TermId>,
        leaf: &AuthoredUniversal,
        skolems: &[TermId],
        interp: &Interpretation,
        budget: LaneBudget,
    ) -> Option<Vec<TermId>> {
        let mut targets = skolems.to_vec();
        let mut rep_slices: Vec<(usize, usize)> = Vec::with_capacity(skolems.len());
        for (_, sort) in &leaf.vars {
            let reps = interp.representatives(sort);
            rep_slices.push((targets.len(), reps.len()));
            targets.extend_from_slice(reps);
        }
        let values =
            self.probe_finite_witness_values(assertions, &targets, budget.sub_solve_ms())?;
        let mut binding = Vec::with_capacity(skolems.len());
        for (i, (_, sort)) in leaf.vars.iter().enumerate() {
            let value = &values[i];
            let term = if is_element_sort(self, sort) {
                let (start, len) = rep_slices[i];
                let reps = interp.representatives(sort);
                let found = (0..len)
                    .find(|&j| matches!((&values[start + j], value), (EvalValue::Element(a), EvalValue::Element(b)) if a == b));
                match found {
                    Some(j) => reps[j],
                    None => self.ctx.terms.mk_fresh_var("qmc!elem", sort.clone()),
                }
            } else {
                let value = match value {
                    EvalValue::Unknown => self.unconstrained_default_value(sort)?,
                    known => known.clone(),
                };
                scalar_value_term(&mut self.ctx.terms, sort, &value)?
            };
            binding.push(term);
        }
        Some(binding)
    }

    /// `body[x̄ := binding]`, in the ORIGINAL vocabulary.
    fn qmc_instance(&mut self, leaf: &AuthoredUniversal, binding: &[TermId]) -> TermId {
        let subst: HashMap<String, TermId> = leaf
            .vars
            .iter()
            .map(|(name, _)| name.clone())
            .zip(binding.iter().copied())
            .collect();
        subst_vars(&mut self.ctx.terms, leaf.body, &subst)
    }

    /// The truth value `leaf` has in every model of the fixed interpretation.
    fn qmc_truth_value(
        &mut self,
        leaf: &AuthoredUniversal,
        interp: &Interpretation,
        budget: LaneBudget,
    ) -> TruthOutcome {
        if budget.spent()
            || interp
                .symbolic_owner
                .as_ref()
                .is_some_and(|owner| !owner.pay_for(self, 0, 0))
        {
            return TruthOutcome::Unknown;
        }
        let (matrix_sk, skolems) = self.finite_model_skolemize(leaf);
        let Some(fixed) = interp.substitute_symbolic(&mut self.ctx.terms, matrix_sk) else {
            return TruthOutcome::Unknown;
        };
        let with = |extra: TermId| {
            let mut v = interp.pins.clone();
            v.push(extra);
            v
        };
        if leaf.universal {
            let negated = self.ctx.terms.mk_not(fixed);
            if self.qmc_refutes(with(negated), budget) {
                return TruthOutcome::Determined(true);
            }
            let Some(binding) =
                self.qmc_binder_terms(with(negated), leaf, &skolems, interp, budget)
            else {
                return TruthOutcome::Unknown;
            };
            let instance = self.qmc_instance(leaf, &binding);
            if leaf.refinable {
                // A conjunct the fixed model violates can only make the
                // residual unsatisfiable; certifying `false` would decline
                // the pass, where the instance moves the candidate model.
                return TruthOutcome::Refine(instance);
            }
            let Some(fixed_instance) = interp.substitute_symbolic(&mut self.ctx.terms, instance)
            else {
                return TruthOutcome::Unknown;
            };
            if self.qmc_refutes(with(fixed_instance), budget) {
                return TruthOutcome::Determined(false);
            }
            return TruthOutcome::Refine(instance);
        }
        let Some(binding) = self.qmc_binder_terms(with(fixed), leaf, &skolems, interp, budget)
        else {
            return if self.qmc_refutes(with(fixed), budget) {
                TruthOutcome::Determined(false)
            } else {
                TruthOutcome::Unknown
            };
        };
        let instance = self.qmc_instance(leaf, &binding);
        if leaf.dual_refinable {
            // The problem entails `forall x̄. (not body)` and the fixed model
            // has a point where `body` holds: `(not body)[t̄]` is a consequence
            // of the problem that this candidate violates.
            return TruthOutcome::Refine(self.ctx.terms.mk_not(instance));
        }
        let Some(fixed_instance) = interp.substitute_symbolic(&mut self.ctx.terms, instance) else {
            return TruthOutcome::Unknown;
        };
        let negated_instance = self.ctx.terms.mk_not(fixed_instance);
        if self.qmc_refutes(with(negated_instance), budget) {
            TruthOutcome::Determined(true)
        } else {
            TruthOutcome::Unknown
        }
    }

    /// ONE generic certificate pass; mints no authority and asserts nothing.
    fn qmc_certificate_pass(
        &mut self,
        round: usize,
        roots: &[TermId],
        universals: &[AuthoredUniversal],
        instances: &mut Vec<TermId>,
        budget: LaneBudget,
        symbolic_owner: Option<&crate::executor::model::SymbolicAdmission>,
    ) -> PassOutcome {
        if budget.spent() {
            return PassOutcome::Declined;
        }
        let Some(mut interp) = self.model_check_interpretation(universals, roots) else {
            trace(|| format!("qmc round {round}: no candidate model"));
            return PassOutcome::Declined;
        };
        let mut original_refinement = None;
        if let Some(original) = interp.without_array_defaults() {
            let mut original_instances = Vec::new();
            let outcome = self.qmc_certificate_with_interpretation(
                round,
                roots,
                universals,
                &mut original_instances,
                budget,
                &original,
            );
            match outcome {
                PassOutcome::Certified(model) => return PassOutcome::Certified(model),
                PassOutcome::Refined => original_refinement = Some(original_instances),
                PassOutcome::Declined => {}
            }
            trace(|| {
                format!(
                    "qmc round {round}: trying closed-array candidate; remaining={}ms",
                    budget.remaining_ms()
                )
            });
        }
        let mut array_instances = Vec::new();
        let outcome = self.qmc_certificate_with_interpretation(
            round,
            roots,
            universals,
            &mut array_instances,
            budget,
            &interp,
        );
        if matches!(&outcome, PassOutcome::Certified(_)) {
            return outcome;
        }
        if let Some(owner) = symbolic_owner {
            if let Some(candidate) = self.qmc_symbolic_candidate(roots, owner) {
                interp.symbolic = candidate;
                interp.symbolic_owner = Some(owner.clone());
                trace(|| format!("qmc round {round}: trying authored symbolic function bodies"));
                let mut symbolic_instances = Vec::new();
                let symbolic_outcome = self.qmc_certificate_with_interpretation(
                    round,
                    roots,
                    universals,
                    &mut symbolic_instances,
                    budget,
                    &interp,
                );
                if matches!(&symbolic_outcome, PassOutcome::Certified(_)) && owner.pay(0, 0) {
                    return symbolic_outcome;
                }
                interp.symbolic = Default::default();
                interp.symbolic_owner = None;
            }
            if !owner.pay(0, 0) {
                return PassOutcome::Declined;
            }
        }
        if let Some(positive) = interp.with_true_boolean_tables(&mut self.ctx.terms) {
            trace(|| format!("qmc round {round}: trying constant-true Boolean functions"));
            let mut positive_instances = Vec::new();
            let positive_outcome = self.qmc_certificate_with_interpretation(
                round,
                roots,
                universals,
                &mut positive_instances,
                budget,
                &positive,
            );
            if matches!(&positive_outcome, PassOutcome::Certified(_)) {
                return positive_outcome;
            }
        }
        // Keep the existing proposals and their refinement preference first.
        // Extra numeric defaults spend the SAME query-owned wall budget and
        // grant only through the unchanged complete interpretation checker.
        if !budget.spent() {
            if let Some(zero) = interp.with_zero_numeric_defaults(&mut self.ctx.terms) {
                trace(|| format!("qmc round {round}: trying zero numeric function defaults"));
                let mut zero_instances = Vec::new();
                let zero_outcome = self.qmc_certificate_with_interpretation(
                    round,
                    roots,
                    universals,
                    &mut zero_instances,
                    budget,
                    &zero,
                );
                if matches!(&zero_outcome, PassOutcome::Certified(_)) {
                    return zero_outcome;
                }
                if !budget.spent() {
                    if let Some(positive) = zero.with_true_boolean_tables(&mut self.ctx.terms) {
                        let mut positive_instances = Vec::new();
                        let positive_outcome = self.qmc_certificate_with_interpretation(
                            round,
                            roots,
                            universals,
                            &mut positive_instances,
                            budget,
                            &positive,
                        );
                        if matches!(&positive_outcome, PassOutcome::Certified(_)) {
                            return positive_outcome;
                        }
                    }
                }
            }
        }
        if let Some(original_instances) = original_refinement {
            // The additional candidate supplies authority only after all
            // existing checks succeed. Otherwise retain the original model's
            // licensed instances and refinement preference unchanged.
            instances.extend(original_instances);
            PassOutcome::Refined
        } else {
            instances.extend(array_instances);
            outcome
        }
    }

    fn qmc_certificate_with_interpretation(
        &mut self,
        round: usize,
        roots: &[TermId],
        universals: &[AuthoredUniversal],
        instances: &mut Vec<TermId>,
        budget: LaneBudget,
        interp: &Interpretation,
    ) -> PassOutcome {
        if budget.spent()
            || interp
                .symbolic_owner
                .as_ref()
                .is_some_and(|owner| !owner.pay_for(self, 0, 0))
            || !interp.symbolic.is_current(self)
        {
            return PassOutcome::Declined;
        }
        let mut values: HashMap<TermId, TermId> = HashMap::default();
        let mut refined = false;
        trace(|| {
            let pins: Vec<String> = interp
                .pins
                .iter()
                .map(|&pin| ay_proof::render_term_canonical(&self.ctx.terms, pin))
                .collect();
            format!("qmc round {round}: pins {pins:?}")
        });
        for leaf in universals {
            let outcome = self.qmc_truth_value(leaf, &interp, budget);
            trace(|| {
                let label = match &outcome {
                    TruthOutcome::Determined(value) => format!("determined {value}"),
                    TruthOutcome::Refine(instance) => format!(
                        "refine {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, *instance)
                    ),
                    TruthOutcome::Unknown => "unknown".to_string(),
                };
                format!("qmc round {round}: node {:?} {label}", leaf.node)
            });
            match outcome {
                TruthOutcome::Determined(value) => {
                    let constant = self.ctx.terms.mk_bool(value);
                    values.insert(leaf.node, constant);
                }
                TruthOutcome::Refine(instance) if leaf.refinable || leaf.dual_refinable => {
                    instances.push(instance);
                    refined = true;
                }
                TruthOutcome::Refine(_) | TruthOutcome::Unknown => {
                    trace(|| format!("qmc round {round}: node {:?} undetermined", leaf.node));
                    return PassOutcome::Declined;
                }
            }
        }
        if refined {
            return PassOutcome::Refined;
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let residual: Vec<TermId> = roots
            .iter()
            .map(|&root| replace_subterms(&mut self.ctx.terms, root, &values, &mut memo))
            .collect();
        let Some(mut confirm): Option<Vec<TermId>> = residual
            .iter()
            .map(|&root| interp.substitute_symbolic(&mut self.ctx.terms, root))
            .collect()
        else {
            return PassOutcome::Declined;
        };
        confirm.extend_from_slice(&interp.pins);
        let outcome = match self.checked_model_check_solve(confirm.clone(), budget.sub_solve_ms()) {
            Some(CheckedGroundDecision::Sat(checked)) => checked
                .consume(self, &confirm)
                .then(|| self.qmc_prepare_witness(&confirm, &residual, &interp, budget))
                .flatten()
                .map_or(PassOutcome::Declined, PassOutcome::certified),
            Some(CheckedGroundDecision::Unsat(_)) | None => PassOutcome::Declined,
        };
        trace(|| {
            format!(
                "qmc round {round}: all determined; confirm={}",
                outcome.label()
            )
        });
        outcome
    }

    /// Stage the witness: the legacy preparation over the substituted
    /// residual and pins, then the tables, then the ORIGINAL residual must
    /// evaluate to `true` under the staged model with those tables — the
    /// model that will be printed and gated.
    fn qmc_prepare_witness(
        &mut self,
        confirm: &[TermId],
        residual: &[TermId],
        interp: &Interpretation,
        budget: LaneBudget,
    ) -> Option<Model> {
        let mut model = self.finite_model_prepare_witness(confirm, &interp.completions, budget)?;
        let mut array_defaults = Vec::new();
        for table in &interp.tables {
            if interp.symbolic.contains(&table.symbol) {
                continue;
            }
            if matches!(table.result_sort, ay_core::Sort::Array(_)) && table.rows.is_empty() {
                array_defaults.push((
                    table.symbol.clone(),
                    table.arg_sorts.clone(),
                    table.result_sort.clone(),
                    table.default,
                ));
                continue;
            }
            if self
                .install_model_check_total_uf(
                    &mut model,
                    table.symbol.name(),
                    &table.arg_sorts,
                    &table.result_sort,
                    &table.rows,
                    table.default,
                )
                .is_none()
            {
                trace(|| format!("qmc: table {:?} not installable", table.symbol));
                return None;
            }
        }
        if !array_defaults.is_empty() {
            if self
                .install_model_check_array_defaults(&mut model, array_defaults)
                .is_none()
            {
                trace(|| "qmc: closed-array candidate package not installable".to_string());
                return None;
            }
        }
        if !interp.symbolic.is_empty() {
            self.install_model_check_symbolic_ufs(
                &mut model,
                interp.symbolic.clone(),
                interp.symbolic_owner.as_ref()?,
            )?;
        }
        let holds = if interp.symbolic.is_empty() {
            residual
                .iter()
                .all(|&root| matches!(self.evaluate_term(&model, root), EvalValue::Bool(true)))
        } else {
            self.symbolic_residual_holds(&model, residual)
                && interp
                    .symbolic_owner
                    .as_ref()
                    .is_some_and(|owner| owner.pay(0, 0))
        };
        if !holds {
            trace(|| "qmc: staged model falsifies the original residual".to_string());
            return None;
        }
        Some(model)
    }

    /// Establish and INSTALL generic quantified SAT authority for the current
    /// authored window with one pass and no refinement. Adds no assertions and
    /// runs no outer re-solve, so it is safe inside the emission funnel.
    pub(in crate::executor) fn try_model_check_sat_certificate(&mut self) -> bool {
        if self.should_abort_theory_loop() || !self.finite_model_plain_sat_scope() {
            return false;
        }
        let Some(budget) = self.finite_model_lane_open() else {
            return false;
        };
        let symbolic_scope = crate::executor::model::SymbolicRecoveryScope::enter(
            self,
            Box::new(move |_, _| !budget.spent()),
        );
        let symbolic_owner = symbolic_scope.as_ref().map(|scope| scope.admission());
        let roots = match self.independent_gate_query_roots() {
            Ok(roots) => roots,
            Err(_) => {
                return false;
            }
        };
        let Some(universals) = self.qmc_leaves(&roots) else {
            self.finite_model_lane_settle(budget, false);
            return false;
        };
        let nodes = certified_nodes(&universals);
        let mut instances = Vec::new();
        let trust_mark = self.finite_model_trust_mark();
        let outcome = self.qmc_certificate_pass(
            0,
            &roots,
            &universals,
            &mut instances,
            budget,
            symbolic_owner.as_ref(),
        );
        self.finite_model_lane_settle(budget, matches!(outcome, PassOutcome::Certified(_)));
        match outcome {
            PassOutcome::Certified(model) => {
                let admission = self.finite_model_pass_trust(trust_mark);
                self.qmc_install(&roots, &nodes, *model, admission)
            }
            PassOutcome::Refined | PassOutcome::Declined => false,
        }
    }

    /// Install the certified pass's authority. `admission` is
    /// `DischargedTrust` when any refutation the pass consumed was admitted
    /// only as `discharged-trust`, and the installer refuses such a pass.
    fn qmc_install(
        &mut self,
        roots: &[TermId],
        nodes: &[TermId],
        model: Model,
        admission: ProbeUnsatAuthority,
    ) -> bool {
        let Some(evidence) =
            super::super::bv_mbqi::checked_full_domain_sat_authority(self, roots, nodes)
        else {
            trace(|| "qmc: authority roots do not cover".to_string());
            return false;
        };
        let installed =
            self.install_finite_model_full_domain_sat_authority(evidence, model, admission);
        trace(|| format!("qmc: installed={installed} admission={admission:?}"));
        installed
    }

    /// The generic model check with counterexample refinement.
    ///
    /// `trigger_quants` only decide whether to engage; the obligations are
    /// read off the authored window, which is what the resulting authority is
    /// bound to.
    pub(in crate::executor) fn try_model_check_forall_refinement(
        &mut self,
        trigger_quants: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        if trigger_quants.is_empty() || !self.finite_model_plain_sat_scope() {
            return None;
        }
        let budget = self.finite_model_lane_open()?;
        let symbolic_scope = crate::executor::model::SymbolicRecoveryScope::enter(
            self,
            Box::new(move |_, _| !budget.spent()),
        );
        let symbolic_owner = symbolic_scope.as_ref().map(|scope| scope.admission());
        let roots = match self.independent_gate_query_roots() {
            Ok(roots) => roots,
            Err(_) => {
                return None;
            }
        };
        let Some(universals) = self.qmc_leaves(&roots) else {
            self.finite_model_lane_settle(budget, false);
            return None;
        };
        self.revoke_bv_full_domain_sat_authority();
        let checkpoint = RefinementCheckpoint::take(self);
        let mut certified = false;
        let mut refuted = false;
        let outcome = self.qmc_refinement_rounds(
            &roots,
            &universals,
            category,
            budget,
            &mut certified,
            &mut refuted,
            symbolic_owner.as_ref(),
        );
        self.finite_model_lane_settle(budget, certified);
        if outcome.is_none() {
            checkpoint.restore(self, refuted);
        }
        outcome
    }

    fn qmc_refinement_rounds(
        &mut self,
        roots: &[TermId],
        universals: &[AuthoredUniversal],
        category: LogicCategory,
        budget: LaneBudget,
        certified: &mut bool,
        refuted: &mut bool,
        symbolic_owner: Option<&crate::executor::model::SymbolicAdmission>,
    ) -> Option<Result<SolveResult>> {
        let nodes = certified_nodes(universals);
        for round in 0..MAX_FINITE_MODEL_ROUNDS {
            self.last_statistics.quantifier_mbqi_rounds += 1;
            if self.should_abort_theory_loop() {
                return None;
            }
            let mut new_instances = Vec::new();
            let trust_mark = self.finite_model_trust_mark();
            match self.qmc_certificate_pass(
                round,
                roots,
                universals,
                &mut new_instances,
                budget,
                symbolic_owner,
            ) {
                PassOutcome::Declined => return None,
                PassOutcome::Certified(model) => {
                    *certified = true;
                    let admission = self.finite_model_pass_trust(trust_mark);
                    return self
                        .qmc_install(roots, &nodes, *model, admission)
                        .then_some(Ok(SolveResult::Sat));
                }
                PassOutcome::Refined => {}
            }
            trace(|| format!("qmc round {round}: {} new instance(s)", new_instances.len()));
            if new_instances.is_empty() {
                return None;
            }
            // Same licence as the legacy pass: every instance is a ground
            // consequence of an entailed universal, conjoined as a top-level
            // fact outside the E-matching licence (#degrade277-narrow).
            self.unlicensed_instance_conjoined = true;
            self.ctx.assertions.extend(new_instances);
            let (detected, _) = self.detect_logic_category(&self.ctx.assertions);
            let re_category = if matches!(detected, LogicCategory::Other) {
                category
            } else {
                detected
            };
            // The model check is a SAT producer. A refutation its instances
            // expose is genuine (every instance is a consequence), but it is
            // handed back only where the posture publishes UNSAT without a
            // certificate. Otherwise the caller's certified refutation
            // channels run exactly as they did before this pass (measured:
            // the witnessed-forall empty-universe decision lost its strict
            // proof to a verdict-only refutation when this returned it).
            match self.solve_for_category(re_category) {
                Ok(SolveResult::Sat) => {}
                Ok(SolveResult::Unsat(_)) if self.competition_shedding_active() => {
                    return Some(Ok(SolveResult::unsat()));
                }
                Ok(SolveResult::Unsat(_)) => {
                    *refuted = true;
                    return None;
                }
                _ => return None,
            }
        }
        None
    }
}

#[cfg(test)]
mod array_defaults_tests;
