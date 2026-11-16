// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Free symbols the quantifier preprocessing removes from every assertion
//! (2026-09-25 verify of the quantifier repair, B3).
//!
//! The preprocessing rewrites each quantified assertion into an equivalent
//! one. When no rewritten assertion mentions a declared constant any more —
//! the affine elimination turns `(forall v. (or (= (* v w) 0) (= (+ (* 2 v)
//! z) 1)))` into `(= w 0)` — no value of it changes the formula the solver
//! decides, so the model the solver returns has none, and the gates, which
//! check the authored assertion, confirmed it with `z` unassigned. `(get-model)`
//! then failed with "sat accepted without a total model". Output completion
//! gives every constant only a quantified assertion mentions the canonical
//! default before the gates check the model
//! ([`Executor::complete_quantified_only_gaps`]); a constant recorded here is
//! also completed inside a certificate lane's sealed model, where the
//! certified formula does not mention it.

use ay_arrays::ArrayInterpretation;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::{EvalValue, Model};
use crate::executor::Executor;

mod quantified_only_functions;

impl Executor {
    /// Record every `Var` of `before` (the assertions' symbols ahead of the
    /// quantifier preprocessing) that no assertion mentions after it.
    pub(in crate::executor) fn record_preprocess_eliminated_constants(
        &mut self,
        before: &HashSet<TermId>,
    ) {
        let after = self.collect_occurring_vars(&[]);
        let mut eliminated: Vec<TermId> = before
            .iter()
            .copied()
            .filter(|var| !after.contains(var))
            .collect();
        eliminated.sort_by_key(|var| var.index());
        for var in eliminated {
            if !self.preprocess_eliminated_constants.contains(&var) {
                self.preprocess_eliminated_constants.push(var);
            }
        }
    }

    /// Whether `var` was removed from every assertion by the quantifier
    /// preprocessing of this public decision and occurs in none of
    /// `extra_roots` (the `check-sat-assuming` assumptions, which the rewrites
    /// did not see).
    pub(in crate::executor) fn is_preprocess_eliminated_constant(
        &self,
        var: TermId,
        extra_roots: &[TermId],
    ) -> bool {
        self.preprocess_eliminated_constants.contains(&var)
            && !self.roots_mention_var(extra_roots, var)
    }

    /// Give the canonical default to every gap variable (a declared constant
    /// the assertions mention that has no value) that the assertions and
    /// `extra_roots` mention only under a quantifier. The model the solver
    /// returned leaves it open because the formula it decided no longer
    /// constrains it — the affine elimination turns `(forall v. (or (= a (+
    /// (* v (ite p 0 2)) (- v) (f a))) (< 3 a)))` into a formula whose `p`
    /// the ground simplification folds away (w1_62501_00208) — and the
    /// quantified gate, which confirms those assertions by nested solves over
    /// the model, now checks the default instead of confirming the universal
    /// with `p` unassigned and leaving `(get-model)` nothing to print (B3).
    /// A constant a ground assertion mentions is left to the ordinary
    /// candidate completion: the gates cannot confirm that assertion without
    /// its value, so it never reaches `sat` unassigned. Functions only a
    /// quantified assertion applies get the same treatment
    /// ([`Self::complete_quantified_only_functions`]); the count covers both.
    pub(in crate::executor) fn complete_quantified_only_gaps(
        &self,
        model: &mut Model,
        gap_vars: &[TermId],
        extra_roots: &[TermId],
    ) -> usize {
        let functions = self.complete_quantified_only_functions(model, extra_roots);
        if gap_vars.is_empty() {
            return functions;
        }
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let ground = self.vars_outside_quantifiers(&roots);
        let mut filled = 0usize;
        for &var in gap_vars {
            if ground.contains(&var)
                || self.recorded_var_substitutions.contains_key(&var)
                || !matches!(self.evaluate_term(model, var), EvalValue::Unknown)
            {
                continue;
            }
            let Some(default) = self.unconstrained_default_value(self.ctx.terms.sort(var)) else {
                continue;
            };
            if Self::insert_completed_value(&self.ctx.terms, model, var, &default) {
                filled += 1;
            }
        }
        filled + functions
    }

    /// The canonical value of a declared array constant that no exact root
    /// mentions: `((as const (Array I E)) d)`, `d` the element sort's
    /// canonical default. The formula does not constrain the array, so any
    /// value is a witness; without one a sealed quantified model printed
    /// `(error "model value for array A is not available")` after `sat` —
    /// main's constant-interpretation certificate on `(forall v. (not (= (f v)
    /// v)))` beside an unused `A`, both postures, and on the family files
    /// (w1_62501_00318, `--z3-mode`) where the elimination turns main's wrong
    /// `unsat` into `sat` (2026-09-28, fix-up session 3). Only element sorts
    /// whose default names no element of an uninterpreted sort or datatype: such
    /// a value would add an element to the printed universe the certificate
    /// never saw. An array the model already interprets, or whose extraction
    /// dropped a conflicting cell, is left alone.
    pub(in crate::executor) fn unmentioned_array_default(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(array_sort) = sort else {
            return None;
        };
        if !matches!(
            array_sort.element_sort,
            Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::BitVec(_)
                | Sort::String
                | Sort::FloatingPoint(..)
        ) {
            return None;
        }
        if model.array_model.as_ref().is_some_and(|arrays| {
            arrays.array_values.contains_key(&term) || arrays.is_withheld(&term)
        }) {
            return None;
        }
        Some(ArrayInterpretation {
            default: Some(self.canonical_default_value(&array_sort.element_sort)),
            stores: Vec::new(),
            index_sort: Some(array_sort.index_sort.clone()),
            element_sort: Some(array_sort.element_sort.clone()),
        })
    }

    /// Every `Var` reachable from `roots` without entering a quantifier body.
    fn vars_outside_quantifiers(&self, roots: &[TermId]) -> HashSet<TermId> {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut vars: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(_, _) => {
                    vars.insert(t);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        vars
    }

    /// Whether `var` occurs anywhere below `roots`, quantifier bodies and
    /// `let` bindings included.
    fn roots_mention_var(&self, roots: &[TermId], var: TermId) -> bool {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if t == var {
                return true;
            }
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::{EvalValue, Model};
    use crate::executor::Executor;

    /// An array constant no root mentions gets the constant default before the
    /// seal (fix-up session 3: main's const-interp certificate printed `(error
    /// "model value for array A is not available")` after `sat`); one whose
    /// default would name an uninterpreted element, or that a root mentions,
    /// is left alone.
    #[test]
    fn preseal_completion_gives_an_unmentioned_array_the_constant_default() {
        let commands = ay_frontend::parse(
            "(set-logic ALL) (declare-sort U 0) (declare-fun f (Int) Int)
             (declare-fun A () (Array Int Int)) (declare-fun B () (Array Int U))
             (declare-fun C () (Array Int Int))
             (assert (forall ((v Int)) (not (= (f v) v))))
             (assert (= (select C 0) 1))",
        )
        .expect("fixture parses");
        let mut exec = Executor::new();
        for command in &commands {
            exec.execute(command).expect("fixture executes");
        }
        let term = |exec: &Executor, name: &str| {
            exec.ctx
                .symbol_info(name)
                .and_then(|info| info.term)
                .expect("declared")
        };
        let (a, b, c) = (term(&exec, "A"), term(&exec, "B"), term(&exec, "C"));
        let roots = exec.ctx.assertions.clone();
        let mut candidate = Model::empty();
        assert!(exec.complete_quantified_output_model_before_seal(&mut candidate, &roots));
        let arrays = candidate
            .array_model
            .as_ref()
            .expect("the unmentioned A gets a value");
        let a_value = arrays.array_values.get(&a).expect("A is completed");
        assert_eq!(a_value.default.as_deref(), Some("0"));
        assert_eq!(a_value.stores, [] as [(String, String); 0]);
        assert!(
            !arrays.array_values.contains_key(&b),
            "a default of U would add an element to the printed universe"
        );
        assert!(
            !arrays.array_values.contains_key(&c),
            "C occurs in a root: the formula constrains it"
        );
    }

    /// A certificate lane seals the model its producer checked; a constant
    /// the quantifier preprocessing removed from every assertion is not in
    /// the certified formula however the authored roots spell it, so the
    /// pre-seal completion gives it the canonical default (a Boolean here: an
    /// `Int` without an arithmetic model already reads as 0).
    #[test]
    fn preseal_completion_fills_a_constant_the_preprocessing_removed() {
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
        let roots = exec.ctx.assertions.clone();
        let mut candidate = Model::empty();
        assert!(exec.complete_quantified_output_model_before_seal(&mut candidate, &roots));
        assert!(
            matches!(exec.evaluate_term(&candidate, z), EvalValue::Unknown),
            "z occurs in the roots: without the record it is left to the theorem"
        );
        exec.preprocess_eliminated_constants = vec![z];
        let mut candidate = Model::empty();
        assert!(exec.complete_quantified_output_model_before_seal(&mut candidate, &roots));
        assert_eq!(
            exec.evaluate_term(&candidate, z),
            EvalValue::Bool(false),
            "the removed z gets the canonical default before the seal"
        );
    }
}
