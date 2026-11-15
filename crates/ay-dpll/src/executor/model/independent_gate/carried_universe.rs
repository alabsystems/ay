// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified-SAT gate's own check of a finite-universe certificate over
//! the sorts that datatype values carry.
//!
//! A finite-universe SAT certificate (the MBQI EPR lane) argues that a
//! universal over an uninterpreted sort `U` holds because it holds at every
//! element of `U`'s universe. That argument is only as good as the universe it
//! enumerates. When a datatype has a field of sort `U`, the emitted model's
//! datatype values hold `U` elements of their own — `a0 = w(@U!3)` — that no
//! ground `U`-term names, and a universal that is false exactly there was
//! published as `confirmed-sat` (2026-09-23 hunt, D1).
//!
//! So the gate does not take the certificate's word for such a universal. It
//! names the emitted model's universe itself — every ground `U`-term plus a
//! selector term for every `U` element held in a ground datatype value, found
//! by following each value's constructor with the independent evaluator — and
//! evaluates the universal's body at each element, again independently. A
//! false instance is a caught invalid model; anything it cannot settle is not
//! certified.

use super::{
    contains_quantifier, EvalOutcome, Executor, GateViewCacheSession, IndependentModelView,
    ModelValue, SolveResult, Sort, TermData, TermId,
};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

/// Most instances the gate evaluates for one carried-sort universal.
const MAX_CARRIED_UNIVERSE_INSTANCES: usize = 4_096;

/// What the gate's own check says about the quantified leaves whose binder
/// sorts a datatype value carries.
pub(super) enum CarriedUniverseCheck {
    /// No quantified leaf binds a sort that a value in the query carries.
    NotCarried,
    /// Every such leaf holds at every element of the emitted model's universe.
    Confirmed,
    /// This leaf is false at an element the emitted model's universe holds.
    Refuted(TermId),
    /// The universe or an instance could not be settled exactly.
    Unchecked(&'static str),
}

/// Terms naming the elements of the emitted model's universes, per sort.
struct UniverseNames {
    /// Required names: every one must have an element value.
    named: DetHashMap<Sort, Vec<TermId>>,
    /// Optional names from the EUF model, for the elements it records beyond
    /// `named`.
    recorded: DetHashMap<Sort, Vec<TermId>>,
}

impl Executor {
    /// Check, over the emitted model's universe, every quantified leaf of
    /// `query_roots` that binds a sort some value in the query carries (see
    /// [`Executor::sort_carries_any_of`]).
    pub(super) fn carried_universe_check(
        &mut self,
        query_roots: &[TermId],
    ) -> CarriedUniverseCheck {
        let _caches = GateViewCacheSession::new();
        let mut leaves: Vec<TermId> = Vec::new();
        for &root in query_roots {
            if !contains_quantifier(&self.ctx.terms, root) {
                continue;
            }
            let mut conjuncts = Vec::new();
            crate::executor::quantifier_loop::collect_and_conjuncts(
                &self.ctx.terms,
                root,
                &mut conjuncts,
            );
            if conjuncts.is_empty() {
                conjuncts.push(root);
            }
            for c in conjuncts {
                if contains_quantifier(&self.ctx.terms, c) && !leaves.contains(&c) {
                    leaves.push(c);
                }
            }
        }
        let mut outcome = CarriedUniverseCheck::NotCarried;
        for leaf in leaves {
            let bound = self.bound_plain_uninterpreted_sorts(leaf);
            if bound.is_empty() || !self.query_carries_any(query_roots, &bound) {
                continue;
            }
            match self.check_carried_universal(query_roots, leaf) {
                CarriedUniverseCheck::Confirmed | CarriedUniverseCheck::NotCarried => {
                    outcome = CarriedUniverseCheck::Confirmed;
                }
                failed => return failed,
            }
        }
        outcome
    }

    /// The MBQI SAT certificate's handoff through the public funnel.
    ///
    /// A finite-domain argument over a sort that datatype values carry is
    /// only as good as the universe it enumerated, and one that missed the
    /// elements held in datatype fields published a wrong `sat` as certified
    /// (D1). So the certificate is taken for every other quantified leaf,
    /// while a leaf over a carried sort is checked here over the emitted
    /// model's universe: a false instance is a caught invalid model, and a
    /// universe or instance this cannot settle is not certified either.
    pub(super) fn mbqi_certificate_handoff(
        &mut self,
        result: SolveResult,
        query_roots: &[TermId],
    ) -> SolveResult {
        let (label, detail) = match self.carried_universe_check(query_roots) {
            CarriedUniverseCheck::NotCarried | CarriedUniverseCheck::Confirmed => {
                self.last_statistics
                    .set_string("model_check_gate.quantified", "deferred-certified-mbqi-sat");
                return result;
            }
            CarriedUniverseCheck::Refuted(leaf) => {
                let term = self.format_term(leaf);
                self.report_caught_invalid_model(leaf, &term);
                self.last_statistics
                    .set_string("model_check_gate.quantified_assertion", term);
                (
                    "refuted-carried-universe",
                    "a certified quantified assertion is falsified at an element that a \
                     datatype value of the emitted model carries",
                )
            }
            CarriedUniverseCheck::Unchecked(reason) => {
                self.last_statistics
                    .set_string("model_check_gate.quantified_reason", reason);
                (
                    "carried-universe-failclosed",
                    "a certified quantified assertion over a sort that datatype values \
                     carry could not be checked over the emitted model's universe",
                )
            }
        };
        if self.publish_evaluation_stop() {
            return SolveResult::Unknown;
        }
        self.last_statistics
            .set_string("model_check_gate.quantified", label);
        self.downgrade_sat_after_gate(detail);
        SolveResult::Unknown
    }

    /// Every plain uninterpreted sort bound anywhere in `term`.
    fn bound_plain_uninterpreted_sorts(&self, term: TermId) -> DetHashSet<Sort> {
        let mut sorts: DetHashSet<Sort> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    for (_, sort) in vars {
                        if self.is_plain_uninterpreted_sort(sort) {
                            sorts.insert(sort.clone());
                        }
                    }
                    stack.push(*body);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        sorts
    }

    /// Whether some term of `roots` has a sort whose values carry one of
    /// `sorts`.
    fn query_carries_any(&self, roots: &[TermId], sorts: &DetHashSet<Sort>) -> bool {
        let mut seen_sorts: DetHashSet<Sort> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let sort = self.ctx.terms.sort(t);
            if seen_sorts.insert(sort.clone()) && self.sort_carries_any_of(sort, sorts) {
                return true;
            }
            match self.ctx.terms.get(t) {
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        false
    }

    /// The independent evaluator's value of `term` under the emitted model.
    fn independent_value(&self, term: TermId) -> Option<ModelValue> {
        let model = self.last_model.as_ref()?;
        let view = IndependentModelView::new(self, model);
        view.ensure_def_index().ok()?;
        match ay_model_check::evaluate_term(&self.ctx.terms, &view, term) {
            EvalOutcome::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Check one carried-sort leaf: a top-level universal over plain
    /// uninterpreted sorts with a quantifier-free body, evaluated at every
    /// element of the emitted model's universe of each binder sort.
    fn check_carried_universal(
        &mut self,
        query_roots: &[TermId],
        leaf: TermId,
    ) -> CarriedUniverseCheck {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(leaf).clone() else {
            return CarriedUniverseCheck::Unchecked(
                "a carried binder sort outside a top-level universal",
            );
        };
        if contains_quantifier(&self.ctx.terms, body)
            || vars
                .iter()
                .any(|(_, sort)| !self.is_plain_uninterpreted_sort(sort))
        {
            return CarriedUniverseCheck::Unchecked(
                "a carried binder sort in an unsupported universal shape",
            );
        }
        let sorts: DetHashSet<Sort> = vars.iter().map(|(_, sort)| sort.clone()).collect();
        let names = match self.carried_universe_names(query_roots, &sorts) {
            Ok(names) => names,
            Err(reason) => return CarriedUniverseCheck::Unchecked(reason),
        };
        let mut universe_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
        for (_, sort) in &vars {
            match self.sort_universe_representatives(sort, &names) {
                Ok(universe) => universe_per_var.push(universe),
                Err(reason) => return CarriedUniverseCheck::Unchecked(reason),
            }
        }
        let total = universe_per_var
            .iter()
            .try_fold(1usize, |acc, universe| acc.checked_mul(universe.len()));
        if total.is_none_or(|n| n > MAX_CARRIED_UNIVERSE_INSTANCES) {
            return CarriedUniverseCheck::Unchecked("the carried universe is too large");
        }
        let binders: Vec<String> = vars.iter().map(|(name, _)| name.clone()).collect();
        let mut indices = vec![0usize; vars.len()];
        loop {
            let subst: DetHashMap<String, TermId> = binders
                .iter()
                .enumerate()
                .map(|(i, name)| (name.clone(), universe_per_var[i][indices[i]]))
                .collect();
            let instance = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
            match self.independent_value(instance) {
                Some(ModelValue::Bool(true)) => {}
                Some(ModelValue::Bool(false)) => return CarriedUniverseCheck::Refuted(leaf),
                _ => return CarriedUniverseCheck::Unchecked("an instance is not evaluable"),
            }
            let mut carry = true;
            for i in (0..indices.len()).rev() {
                if !carry {
                    break;
                }
                indices[i] += 1;
                if indices[i] < universe_per_var[i].len() {
                    carry = false;
                } else {
                    indices[i] = 0;
                }
            }
            if carry {
                return CarriedUniverseCheck::Confirmed;
            }
        }
    }

    /// Terms naming the emitted model's universe of each of `sorts`: the
    /// ground terms of the query plus a selector term for every element a
    /// ground datatype value carries (followed with the independent
    /// evaluator; `Err` when a value cannot be followed), and separately the
    /// EUF model's terms for the elements it records beyond those (a selector
    /// at a foreign constructor, a solver term). The latter names are
    /// optional: one the independent evaluator cannot read is skipped, and its
    /// element must then be named by another term.
    fn carried_universe_names(
        &mut self,
        query_roots: &[TermId],
        sorts: &DetHashSet<Sort>,
    ) -> Result<UniverseNames, &'static str> {
        let Some(carriers) = self.binder_universe_carriers(query_roots, sorts) else {
            return Err("the binder universe is not generated by ground terms");
        };
        let carried =
            self.carried_binder_field_terms(&carriers, sorts, &mut |exec, tester| match exec
                .independent_value(tester)
            {
                Some(ModelValue::Bool(holds)) => Some(holds),
                _ => None,
            });
        if !carried.complete {
            return Err("a carried datatype value could not be followed");
        }
        let mut named =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, query_roots);
        for (sort, fields) in carried.by_sort {
            named.entry(sort).or_default().extend(fields);
        }
        let recorded = self.euf_universe_representatives(sorts, &named);
        Ok(UniverseNames { named, recorded })
    }

    /// One term per distinct element of `sort`'s universe, ordered by element;
    /// `Err` when a required name has no element value, the universe is empty,
    /// or the EUF model records an element no term names.
    fn sort_universe_representatives(
        &self,
        sort: &Sort,
        names: &UniverseNames,
    ) -> Result<Vec<TermId>, &'static str> {
        let mut by_value: DetHashMap<String, TermId> = DetHashMap::default();
        for &t in names.named.get(sort).into_iter().flatten() {
            let Some(ModelValue::Uninterpreted(element)) = self.independent_value(t) else {
                return Err("a universe term has no element value");
            };
            by_value.entry(element).or_insert(t);
        }
        for &t in names.recorded.get(sort).into_iter().flatten() {
            if let Some(ModelValue::Uninterpreted(element)) = self.independent_value(t) {
                by_value.entry(element).or_insert(t);
            }
        }
        let Sort::Uninterpreted(name) = sort else {
            return Err("a binder sort is not uninterpreted");
        };
        let unnamed: Vec<&String> = self
            .last_model
            .as_ref()
            .and_then(|model| model.euf_model.as_ref())
            .and_then(|euf| euf.sort_elements.get(name))
            .into_iter()
            .flatten()
            .filter(|element| !by_value.contains_key(*element))
            .collect();
        if !unnamed.is_empty() {
            return Err("the model holds an element no term names");
        }
        if by_value.is_empty() {
            return Err("the binder universe is empty");
        }
        let mut representatives: Vec<(String, TermId)> = by_value.into_iter().collect();
        representatives.sort();
        Ok(representatives.into_iter().map(|(_, t)| t).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::CarriedUniverseCheck;
    use crate::executor::Executor;
    use ay_frontend::Command;

    fn load(smt: &str) -> Executor {
        let commands = ay_frontend::parse(smt).expect("fixture parses");
        let mut exec = Executor::new();
        for command in &commands {
            let output = exec.execute(command).expect("fixture executes");
            assert!(output.is_none(), "fixture must not contain a query command");
        }
        exec
    }

    /// The D1 model: four distinct `W` values hold a third `U` element in a
    /// `w` field, so `forall x:U. x = u0 or x = u1` is false in it. The model
    /// comes from solving the ground part alone, the kind of model the
    /// certificate used to accept; the gate must refute it.
    #[test]
    fn a_universal_false_at_a_carried_field_is_refuted() {
        let mut exec = load(
            r#"
            (set-logic ALL)
            (declare-sort U 0)
            (declare-datatypes ((W 0)) (((w (g U)) (w2))))
            (declare-const u0 U)
            (declare-const u1 U)
            (declare-const a0 W)
            (declare-const a1 W)
            (declare-const a2 W)
            (declare-const a3 W)
            (assert (distinct a0 a1 a2 a3))
            (assert (forall ((x U)) (or (= x u0) (= x u1))))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        let ground = roots[0];
        let universal = roots[1];
        exec.ctx.assertions = vec![ground];
        let verdict = exec
            .execute(&Command::CheckSat)
            .expect("ground part solves");
        assert_eq!(verdict.as_deref(), Some("sat"), "four W values exist");
        assert!(
            exec.last_model.is_some(),
            "the ground solve keeps its model"
        );
        exec.ctx.assertions = roots.clone();
        match exec.carried_universe_check(&roots) {
            CarriedUniverseCheck::Refuted(leaf) => assert_eq!(leaf, universal),
            CarriedUniverseCheck::NotCarried => panic!("U is carried by W's field g"),
            CarriedUniverseCheck::Confirmed => {
                panic!("a model with four W values cannot satisfy |U| <= 2")
            }
            CarriedUniverseCheck::Unchecked(reason) => {
                panic!("the carried universe must be checkable here: {reason}")
            }
        }
    }

    /// A universal over a sort no value carries is not this check's business:
    /// the certificate handoff stays as it was.
    #[test]
    fn a_sort_no_value_carries_is_not_checked_here() {
        let mut exec = load(
            r#"
            (set-logic UF)
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-const u U)
            (assert (P u))
            (assert (forall ((x U)) (P x)))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        assert!(matches!(
            exec.carried_universe_check(&roots),
            CarriedUniverseCheck::NotCarried
        ));
    }
}
