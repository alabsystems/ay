// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGQI arithmetic refinement and neighbor enumeration.
//!
//! Multi-round counterexample-guided quantifier instantiation: extract model values
//! for CE variables, compute selection terms via `ArithInstantiator`, create ground
//! instantiations, and re-solve. Includes neighbor enumeration fallback for integer
//! variables where bound extraction fails (div/mod patterns).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId};

use super::super::model::EvalValue;
use super::super::Executor;
use crate::cegqi::arith::ArithInstantiator;
use crate::cegqi::CegqiInstantiator;
use crate::ematching::{contains_quantifier, subst_vars};
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;

#[cfg(test)]
use super::unsupported_arith::unsupported_int_div_mod_mentions_ce_var;
use super::unsupported_arith::{term_mentions_any, unsupported_arith_mentions_ce_var};

impl Executor {
    /// Attempt multi-round CEGQI arithmetic refinement.
    ///
    /// Extract model values for CE variables, use `ArithInstantiator` to compute
    /// selection terms, create ground instantiations, and re-solve. If still SAT,
    /// extract new model and repeat up to `MAX_CEGQI_ROUNDS` times.
    ///
    /// Returns `Some(result)` if refinement was attempted and produced a result,
    /// or `None` if refinement was not applicable (no model, no arithmetic vars).
    ///
    /// `snapshot` is the pre-instantiation assertion snapshot
    /// (`refinement_assertions` in the caller): it enables the quantified-CE
    /// decider legs inside `disambiguate_cegqi_unsat` (their quantifier-coverage,
    /// conjunctive-position, and independent-UNSAT gates need the snapshot;
    /// `None` disables them and fails closed to Unknown).
    #[allow(clippy::used_underscore_items)]
    pub(super) fn try_cegqi_arith_refinement(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        snapshot: Option<&[TermId]>,
    ) -> Option<Result<SolveResult>> {
        const MAX_CEGQI_ROUNDS: usize = 8;

        self.last_model.as_ref()?;

        // Bail early on nonlinear or div/mod terms under linear logic (#6042, #6889).
        // Integer div/mod creates opaque auxiliary variables in LIA preprocessing
        // that prevent CEGQI bound extraction from converging. Each refinement
        // round runs a full branch-and-bound pipeline, causing severe slowdown.
        if matches!(
            category,
            LogicCategory::QfLia | LogicCategory::Lia | LogicCategory::QfLra | LogicCategory::Lra
        ) {
            let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
            if (features.has_nonlinear_int
                || features.has_nonlinear_real
                || features.has_int_div_mod)
                && unsupported_arith_mentions_ce_var(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                    cegqi_state,
                )
            {
                self.record_unknown_from_origin(UnknownOrigin::CegqiRefinement);
                return Some(Ok(SolveResult::Unknown));
            }
        }

        let mut prev_instantiation_count = self.ctx.assertions.len();
        let mut seen_instantiations: HashSet<TermId> = HashSet::default();

        // Deadline/interrupt closure (#quantifier-deadline): each CEGQI round
        // runs a full theory solve, so a wall-clock budget can be overrun by
        // many rounds. The closure owns its snapshots (no borrow of `self`).
        let should_stop = self.make_should_stop();

        for _round in 0..MAX_CEGQI_ROUNDS {
            // Stop refining once the budget is spent. We are in the SAT-from-
            // ground-solve path: returning Unknown(Timeout) instead of
            // continuing prevents both an overrun and a truncated final Sat.
            if should_stop() {
                self.last_unknown_reason = Some(UnknownReason::Timeout);
                return Some(Ok(SolveResult::Unknown));
            }
            // Clone model to avoid overlapping borrows: last_model is borrowed
            // immutably for the model reference, but instantiate_cegqi_round
            // needs &mut self to modify ctx.assertions.
            let model = match self.last_model.clone() {
                Some(m) => m,
                None => break,
            };

            let any_added =
                self.instantiate_cegqi_round(cegqi_state, &model, &mut seen_instantiations);

            if !any_added {
                if _round == 0 {
                    return None;
                }
                break;
            }

            if self.ctx.assertions.len() == prev_instantiation_count {
                break;
            }
            prev_instantiation_count = self.ctx.assertions.len();

            match self.solve_for_category(category) {
                Ok(SolveResult::Unsat(_)) => {
                    // The pre-instantiation snapshot (threaded from
                    // `classify_quantifier_result`'s `refinement_assertions`)
                    // enables the quantified-CE-lemma decider legs inside
                    // disambiguation — in particular the UNSAT leg
                    // (`universal_false_at_ground_witness`), which is the only
                    // route that DECIDES the RED S3 ∀∃ perfect-square
                    // alternation unsat on this path.
                    return Some(self.disambiguate_cegqi_unsat(
                        category,
                        ce_lemma_ids,
                        ce_lemma_groups,
                        false,
                        cegqi_state,
                        snapshot,
                    ));
                }
                Ok(SolveResult::Sat) => continue,
                other => return Some(other),
            }
        }

        // Neighbor enumeration fallback for integer variables.
        if let Some(result) = self.try_cegqi_neighbor_enumeration(
            cegqi_state,
            category,
            &mut seen_instantiations,
            ce_lemma_ids,
            ce_lemma_groups,
            snapshot,
        ) {
            return Some(result);
        }

        self.record_unknown_from_origin(UnknownOrigin::CegqiRefinement);
        Some(Ok(SolveResult::Unknown))
    }

    /// Execute one CEGQI refinement round: extract model values for CE variables,
    /// compute selection terms via `ArithInstantiator`, and create ground instantiations.
    ///
    /// Returns `true` if any new instantiation was added.
    #[allow(clippy::used_underscore_items)]
    fn instantiate_cegqi_round(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        model: &super::super::model::Model,
        seen_instantiations: &mut HashSet<TermId>,
    ) -> bool {
        let mut any_instantiation_added = false;

        // SOUNDNESS (#cegqi-ce-var-selection): a CEGQI instantiation term `t` for
        // `forall x. phi(x)` must be GROUND with respect to the counterexample
        // variables — it may reference problem constants/terms but never a CE
        // variable. When the selection algorithm picks another CE variable (e.g.
        // for `(forall (a b Int) (= a b))` the negated body `(not (= e_a e_b))`
        // yields, for `e_a`, the strict bounds `e_a > e_b` / `e_a < e_b`, whose
        // unit-coefficient selection term is the bound term `e_b`), the resulting
        // "instance" `phi(e_b, e_a) = (= e_b e_a)` still contains free CE
        // variables and contradicts the CE lemma `(not (= e_a e_b))` trivially.
        // That spurious UNSAT is then read by `disambiguate_cegqi_unsat` as
        // "forall valid -> SAT", a wrong-SAT (the forall is genuinely UNSAT:
        // a=0,b=1). The concrete model value of the CE variable is itself a
        // counterexample witness, so we substitute it (a genuine ground term)
        // whenever a selection term mentions any CE variable, turning the
        // instance into the concrete `phi(<counterexample>)` (here `(= 0 1)` =
        // false), which drives the problem to a SOUND UNSAT.
        let all_ce_vars: HashSet<TermId> = cegqi_state
            .iter()
            .flat_map(|(_, inst)| inst.ce_variables().values().copied())
            .collect();

        for (quant_id, inst) in cegqi_state {
            if !inst.is_forall() {
                continue;
            }

            let mut var_values: HashMap<String, TermId> = HashMap::default();

            for (var_name, &ce_var) in inst.ce_variables() {
                let eval = self.evaluate_term(model, ce_var);
                let sort = self.ctx.terms.sort(ce_var).clone();
                let is_integer = matches!(sort, Sort::Int);

                let mut arith = ArithInstantiator::new();

                let assertion_ids: Vec<TermId> = self.ctx.assertions.clone();
                for &assertion in &assertion_ids {
                    arith.process_assertion(&mut self.ctx.terms, assertion, ce_var);
                }

                let model_value: num_rational::BigRational = match &eval {
                    EvalValue::Rational(r) => r.clone(),
                    _ => continue,
                };

                // Populate model values on bounds for tightest-bound selection
                // and rho computation (Reynolds et al. FMSD 2017).
                for bound in &mut arith.lower_bounds {
                    if let EvalValue::Rational(r) = self.evaluate_term(model, bound.term) {
                        bound.model_value = Some(r);
                    }
                }
                for bound in &mut arith.upper_bounds {
                    if let EvalValue::Rational(r) = self.evaluate_term(model, bound.term) {
                        bound.model_value = Some(r);
                    }
                }

                let selection = arith
                    .select_term(&mut self.ctx.terms, ce_var, &model_value, is_integer)
                    .filter(|&sel| !term_mentions_any(&self.ctx.terms, sel, &all_ce_vars));
                if let Some(selection) = selection {
                    var_values.insert(var_name.clone(), selection);
                } else {
                    // No selection term, or the selection still mentions a CE
                    // variable (degenerate var-var selection). Fall back to the
                    // concrete model value of this CE variable — a genuine
                    // ground counterexample witness — so the instance is
                    // CE-variable-free and sound (#cegqi-ce-var-selection).
                    let fallback = if is_integer {
                        let int_val = model_value.numer().clone() / model_value.denom();
                        self.ctx.terms.mk_int(int_val)
                    } else {
                        self.ctx.terms.mk_rational(model_value.clone())
                    };
                    var_values.insert(var_name.clone(), fallback);
                }
            }

            if let Some(ground_inst) =
                inst._create_model_instantiation(&mut self.ctx.terms, &var_values)
            {
                if seen_instantiations.insert(ground_inst)
                    && self.append_cegqi_ground_instance(*quant_id, &var_values, ground_inst)
                {
                    any_instantiation_added = true;
                }
            }
        }

        any_instantiation_added
    }

    /// Append one CEGQI instance together with its semantic and proof
    /// provenance.
    ///
    /// `setup_cegqi_for_unhandled` creates `cegqi_state` only for a `forall`
    /// admitted by `entailed_forall_set`; consequently every exact ground
    /// instance here is a consequence of the asserted problem.  Keep the term,
    /// conflict-verification support tag, and strict `forall_inst` metadata at
    /// one write-side chokepoint so no consumer has to infer provenance from a
    /// live assertion's shape.
    fn append_cegqi_ground_instance(
        &mut self,
        quantifier: TermId,
        values: &HashMap<String, TermId>,
        instance: TermId,
    ) -> bool {
        let (vars, body) = match self.ctx.terms.get(quantifier).clone() {
            TermData::Forall(vars, body, _) => (vars, body),
            _ => return false,
        };
        let binding = vars
            .iter()
            .map(|(name, sort)| {
                values
                    .get(name)
                    .copied()
                    .filter(|&value| self.ctx.terms.sort(value) == sort)
            })
            .collect::<Option<Vec<_>>>();
        let Some(binding) = binding else {
            return false;
        };
        let binder_values: HashMap<String, TermId> = vars
            .iter()
            .zip(&binding)
            .map(|((name, _), &value)| (name.clone(), value))
            .collect();
        let expected = subst_vars(&mut self.ctx.terms, body, &binder_values);
        if expected != instance || contains_quantifier(&self.ctx.terms, instance) {
            return false;
        }

        // Public quantified solves require a strict proof.  Keep the exact
        // simultaneous substitution as the solver-visible assertion in that
        // mode: simplifying constructors can otherwise turn `(< 0 0)` into
        // `false`, which is equivalent but is not a legal Alethe `forall_inst`
        // conclusion.  Unsupported nested binders/lets fail closed.
        let solver_instance = if self.produce_proofs_enabled() {
            match self.exact_forall_instance(quantifier, &binding) {
                Some(exact) => exact,
                None => {
                    self.quantified_proof_translation_incomplete = true;
                    instance
                }
            }
        } else {
            instance
        };
        let record = crate::ematching::ForallInstantiationProvenance {
            quantifier,
            binding,
            instance: solver_instance,
        };
        self.register_ematching_proof_provenance(std::slice::from_ref(&record));
        let added = if self.ctx.assertions.contains(&solver_instance) {
            false
        } else {
            self.ctx.assertions.push(solver_instance);
            true
        };
        self.push_active_support_axiom(solver_instance);
        added
    }

    /// Neighbor enumeration fallback for CEGQI: try instantiating with values
    /// near the model value (v±1, v±2, ..., v±4) for integer CE variables.
    #[allow(clippy::used_underscore_items)]
    fn try_cegqi_neighbor_enumeration(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        seen_instantiations: &mut HashSet<TermId>,
        ce_lemma_ids: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        snapshot: Option<&[TermId]>,
    ) -> Option<Result<SolveResult>> {
        const MAX_NEIGHBOR_DISTANCE: i64 = 4;

        let model = self.last_model.as_ref()?;

        let mut int_ce_vars: Vec<(String, TermId, num_bigint::BigInt)> = Vec::new();
        for (_quant_id, inst) in cegqi_state {
            if !inst.is_forall() {
                continue;
            }
            for (var_name, &ce_var) in inst.ce_variables() {
                let sort = self.ctx.terms.sort(ce_var).clone();
                if !matches!(sort, Sort::Int) {
                    continue;
                }
                if let EvalValue::Rational(r) = self.evaluate_term(model, ce_var) {
                    let int_val = r.numer().clone() / r.denom();
                    int_ce_vars.push((var_name.clone(), ce_var, int_val));
                }
            }
        }

        if int_ce_vars.is_empty() {
            return None;
        }

        // Deadline/interrupt closure (#quantifier-deadline): each neighbor
        // offset runs a full theory solve; guard so the budget bounds the
        // fallback. Routes to Unknown(Timeout), never a finalized Sat.
        let should_stop = self.make_should_stop();

        for distance in 1..=MAX_NEIGHBOR_DISTANCE {
            for offset in &[distance, -distance] {
                if should_stop() {
                    self.last_unknown_reason = Some(UnknownReason::Timeout);
                    return Some(Ok(SolveResult::Unknown));
                }
                let mut any_new = false;

                for (quant_id, inst) in cegqi_state {
                    if !inst.is_forall() {
                        continue;
                    }

                    let mut var_values: HashMap<String, TermId> = HashMap::default();

                    for (var_name, _ce_var, base_val) in &int_ce_vars {
                        let neighbor_val = base_val + num_bigint::BigInt::from(*offset);
                        let neighbor_term = self.ctx.terms.mk_int(neighbor_val);
                        var_values.insert(var_name.clone(), neighbor_term);
                    }

                    if let Some(ground_inst) =
                        inst._create_model_instantiation(&mut self.ctx.terms, &var_values)
                    {
                        if seen_instantiations.insert(ground_inst)
                            && self.append_cegqi_ground_instance(
                                *quant_id,
                                &var_values,
                                ground_inst,
                            )
                        {
                            any_new = true;
                        }
                    }
                }

                if !any_new {
                    continue;
                }

                let re_result = self.solve_for_category(category);
                match re_result {
                    Ok(SolveResult::Unsat(_)) => {
                        // Snapshot threaded through — decider legs enabled; see
                        // the identical note in the refinement loop above.
                        return Some(self.disambiguate_cegqi_unsat(
                            category,
                            ce_lemma_ids,
                            ce_lemma_groups,
                            false,
                            cegqi_state,
                            snapshot,
                        ));
                    }
                    Ok(SolveResult::Sat) => {
                        continue;
                    }
                    other => {
                        return Some(other);
                    }
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_proof::ProofStep;

    #[test]
    fn cegqi_ground_instance_writer_records_positive_authorized_support() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let p_x = exec.ctx.terms.mk_app(
            Symbol::Named("cegqi_writer_p".to_string()),
            vec![x],
            Sort::Bool,
        );
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], p_x);
        exec.set_produce_proofs(true);
        exec.ctx.assertions.push(forall);
        exec.install_proof_source_provenance(&[forall]);
        let zero = exec.ctx.terms.mk_int(0.into());
        let p_zero = exec.ctx.terms.mk_app(
            Symbol::Named("cegqi_writer_p".to_string()),
            vec![zero],
            Sort::Bool,
        );
        let mut values = HashMap::default();
        values.insert("x".to_string(), zero);
        let proof_steps_before = exec.proof_tracker.num_steps();

        let one = exec.ctx.terms.mk_int(1.into());
        let bogus = exec.ctx.terms.mk_app(
            Symbol::Named("cegqi_writer_p".to_string()),
            vec![one],
            Sort::Bool,
        );
        assert!(
            !exec.append_cegqi_ground_instance(forall, &values, bogus),
            "a mismatched claimed instance must not receive authority"
        );
        assert_eq!(exec.ctx.assertions, vec![forall]);
        assert!(exec.active_support_axioms.is_empty());
        assert_eq!(exec.proof_tracker.num_steps(), proof_steps_before);

        assert!(exec.append_cegqi_ground_instance(forall, &values, p_zero));

        assert_eq!(exec.ctx.assertions, vec![forall, p_zero]);
        assert_eq!(exec.active_support_axioms.len(), 1);
        let support = exec.active_support_axioms[0];
        assert_eq!(support.term, p_zero);
        assert!(support.value, "CEGQI instances are positive consequences");
        let proof = exec.proof_tracker.take_proof();
        assert!(proof.steps.iter().any(|step| {
            matches!(step, ProofStep::Resolution { clause, .. } if clause == &[p_zero])
        }));
        assert!(
            !exec.append_cegqi_ground_instance(forall, &values, p_zero),
            "the authority chokepoint must reject duplicate assertion writes"
        );
        assert_eq!(exec.ctx.assertions, vec![forall, p_zero]);
        assert_eq!(exec.active_support_axioms.len(), 1);
    }

    #[test]
    fn cegqi_unsupported_arith_guard_ignores_ground_mod_unrelated_to_ce_vars() {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let predicate = terms.mk_app(Symbol::Named("p".to_string()), vec![x], Sort::Bool);
        let x_lt_zero = terms.mk_lt(x, zero);
        let body = terms.mk_or(vec![x_lt_zero, predicate]);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");

        let a = terms.mk_var("a", Sort::Int);
        let five = terms.mk_int(5.into());
        let ground_mod = terms.mk_app(Symbol::Named("mod".to_string()), vec![a, five], Sort::Int);

        assert!(
            !unsupported_arith_mentions_ce_var(&terms, &[ground_mod], &[(forall, inst)]),
            "ground div/mod elsewhere in the problem must not block unrelated CEGQI refinement"
        );
    }

    #[test]
    fn cegqi_unsupported_arith_guard_blocks_mod_over_ce_var() {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let ce_x = *inst
            .ce_variables()
            .get("x")
            .expect("x counterexample variable");
        let five = terms.mk_int(5.into());
        // SYMBOLIC divisor: the CE var itself divides — the bail must stay.
        let sym_div = terms.mk_app(
            Symbol::Named("mod".to_string()),
            vec![five, ce_x],
            Sort::Int,
        );
        let state = [(forall, inst)];

        assert!(
            unsupported_arith_mentions_ce_var(&terms, &[sym_div], &state),
            "CEGQI refinement should still fail closed when div/mod has a symbolic divisor"
        );
        assert!(unsupported_int_div_mod_mentions_ce_var(
            &terms,
            &[sym_div],
            &state
        ));
    }

    /// Rank-9 step 2: a NONZERO CONSTANT divisor over a CE-var dividend no
    /// longer bails (the rank-3 mod_div_elim constant path handles those
    /// exactly), while a literal-ZERO constant divisor keeps the bail
    /// (underspecified semantics, #57).
    #[test]
    fn cegqi_constant_nonzero_divisor_over_ce_var_is_supported() {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let ce_x = *inst
            .ce_variables()
            .get("x")
            .expect("x counterexample variable");
        let two = terms.mk_int(2.into());
        let const_div = terms.mk_app(Symbol::Named("div".to_string()), vec![ce_x, two], Sort::Int);
        let state = [(forall, inst)];
        assert!(
            !unsupported_arith_mentions_ce_var(&terms, &[const_div], &state),
            "nonzero-constant-divisor div over a CE var must not bail (rank-9 step 2)"
        );
        assert!(!unsupported_int_div_mod_mentions_ce_var(
            &terms,
            &[const_div],
            &state
        ));
    }

    #[test]
    fn cegqi_zero_constant_divisor_over_ce_var_keeps_bail() {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let ce_x = *inst
            .ce_variables()
            .get("x")
            .expect("x counterexample variable");
        let zero_div = terms.mk_app(
            Symbol::Named("div".to_string()),
            vec![ce_x, zero],
            Sort::Int,
        );
        let state = [(forall, inst)];
        assert!(
            unsupported_arith_mentions_ce_var(&terms, &[zero_div], &state),
            "literal-zero divisor must keep the fail-closed bail (#57 semantics)"
        );
        assert!(unsupported_int_div_mod_mentions_ce_var(
            &terms,
            &[zero_div],
            &state
        ));
    }

    #[test]
    fn predispatch_div_guard_ignores_supported_ce_nonlinearity() {
        let mut terms = ay_core::TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let ce_x = *inst
            .ce_variables()
            .get("x")
            .expect("x counterexample variable");
        let product = terms.mk_mul(vec![ce_x, ce_x]);

        // This unrelated ground term makes StaticFeatures::has_int_div_mod
        // true, but its nonzero constant divisor is supported and it has no CE
        // dependency. The narrow pre-dispatch guard must therefore ignore the
        // separate CE-dependent nonlinear product.
        let a = terms.mk_var("a", Sort::Int);
        let five = terms.mk_int(5.into());
        let ground_mod = terms.mk_app(Symbol::Named("mod".to_string()), vec![a, five], Sort::Int);
        let state = [(forall, inst)];
        let roots = [ground_mod, product];

        assert!(
            unsupported_arith_mentions_ce_var(&terms, &roots, &state),
            "the general linear-logic refinement guard still sees CE nonlinearity"
        );
        assert!(
            !unsupported_int_div_mod_mentions_ce_var(&terms, &roots, &state),
            "the div/mod liveness guard must not conflate unrelated operations"
        );
    }
}
