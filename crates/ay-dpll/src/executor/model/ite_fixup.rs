// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-simplex ITE model consistency pass (#8373).
//!
//! After the simplex solver finds a satisfying assignment, the LRA model maps
//! term IDs to rational values. However, these values are assigned to individual
//! variables without knowledge of ITE-level branch constraints. For example:
//!
//!   `(ite (= x 1.0) (= y 0.0) (= y 1.0))`
//!
//! The simplex model may assign `y = 0.5` which satisfies the linear constraints
//! but violates both branches of the ITE. The model evaluator then picks a
//! branch based on the condition value and finds the branch equality unsatisfied.
//!
//! This module walks ITE-containing assertions after model extraction and patches
//! the LRA model to ensure active-branch equalities are satisfied. This is the
//! model-construction fix for the ITE gap — as opposed to the SAT-fallback
//! workaround in the validation pipeline.

use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_rational::BigRational;

use super::{EvalValue, Executor, Model, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};

impl Executor {
    /// Fix up LRA model values to satisfy ITE branch equalities.
    ///
    /// For each assertion containing ITE subterms, evaluates the ITE condition
    /// and patches the LRA model so that variables in the active branch have
    /// values consistent with the branch constraint.
    ///
    /// This is a no-op when no LRA model exists (pure SAT, BV-only, etc.).
    pub(in crate::executor) fn fix_ite_model_values(&mut self) {
        let model = match &self.last_model {
            Some(m) if m.lra_model.is_some() || m.lia_model.is_some() => m,
            _ => return,
        };

        // Collect patches first, then apply (to avoid borrow issues).
        let mut patches: Vec<(TermId, BigRational)> = Vec::new();

        let assertions = self.flatten_assertion_conjunctions();
        for &assertion in &assertions {
            self.collect_ite_patches(model, assertion, &mut patches);
        }

        if patches.is_empty() {
            return;
        }

        // Apply patches to the LRA model.
        let model = self.last_model.as_mut().expect("checked above");
        if let Some(ref mut lra_model) = model.lra_model {
            for (term, value) in &patches {
                lra_model.values.insert(*term, value.clone());
            }
        }
        if let Some(ref mut lia_model) = model.lia_model {
            for (term, value) in &patches {
                if matches!(self.ctx.terms.sort(*term), Sort::Int) {
                    if let Some(int_val) = value.to_integer_if_whole() {
                        lia_model.values.insert(*term, int_val);
                    }
                }
            }
        }
    }

    /// Walk a term tree and collect LRA model patches for ITE branches.
    ///
    /// When an ITE condition can be evaluated, determines which branch is active
    /// and extracts equalities from it. For each equality `(= var value)` where
    /// `var` is a variable and `value` can be evaluated, patches the variable's
    /// model value.
    fn collect_ite_patches(
        &self,
        model: &Model,
        term: TermId,
        patches: &mut Vec<(TermId, BigRational)>,
    ) {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term) {
                TermData::Ite(cond, then_br, else_br) => {
                    // Evaluate the condition to determine which branch is active.
                    let cond_val = self.evaluate_term(model, *cond);
                    let active_branch = match cond_val {
                        EvalValue::Bool(true) => Some(*then_br),
                        EvalValue::Bool(false) => Some(*else_br),
                        _ => None,
                    };

                    if let Some(branch) = active_branch {
                        // Check if the active branch evaluates to false — if so,
                        // we need to patch the model.
                        let branch_val = self.evaluate_term(model, branch);
                        if matches!(branch_val, EvalValue::Bool(false)) {
                            self.extract_equality_patches(model, branch, patches);
                        }
                        // Also recurse into the active branch for nested ITEs.
                        self.collect_ite_patches(model, branch, patches);
                    }
                    // Do NOT recurse into the inactive branch — its constraints
                    // are irrelevant.
                }
                TermData::App(sym, args) => {
                    match sym.name() {
                        "and" => {
                            // Recurse into conjuncts.
                            for &arg in args {
                                self.collect_ite_patches(model, arg, patches);
                            }
                        }
                        "or" => {
                            // For disjunctions, only patch if we can determine which
                            // disjunct is active from the SAT model.
                            for &arg in args {
                                self.collect_ite_patches(model, arg, patches);
                            }
                        }
                        _ => {
                            // Non-ITE applications: recurse into args looking for
                            // nested ITEs.
                            for &arg in args {
                                self.collect_ite_patches(model, arg, patches);
                            }
                        }
                    }
                }
                TermData::Not(inner) => {
                    self.collect_ite_patches(model, *inner, patches);
                }
                TermData::Let(_, body) => {
                    self.collect_ite_patches(model, *body, patches);
                }
                // Leaves: nothing to do.
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                // Catch future variants.
                _ => {}
            }
        })
    }

    /// Extract equality patches from a branch term.
    ///
    /// Handles:
    /// - `(= var constant)` — patches var to constant
    /// - `(= var expr)` — patches var to evaluated expr value
    /// - `(and (= var1 val1) (= var2 val2))` — patches multiple vars
    fn extract_equality_patches(
        &self,
        model: &Model,
        branch: TermId,
        patches: &mut Vec<(TermId, BigRational)>,
    ) {
        match self.ctx.terms.get(branch) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];
                // Try both directions: (= var expr) and (= expr var)
                if let Some(patch) = self.try_equality_patch(model, lhs, rhs) {
                    patches.push(patch);
                } else if let Some(patch) = self.try_equality_patch(model, rhs, lhs) {
                    patches.push(patch);
                }
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                for &arg in args {
                    self.extract_equality_patches(model, arg, patches);
                }
            }
            _ => {}
        }
    }

    /// Try to create a model patch from `(= var_term value_term)`.
    ///
    /// Returns `Some((var_term_id, value))` if `var_term` is a Real/Int-sorted
    /// variable and `value_term` can be evaluated to a rational.
    fn try_equality_patch(
        &self,
        model: &Model,
        var_term: TermId,
        value_term: TermId,
    ) -> Option<(TermId, BigRational)> {
        // Check that var_term is a variable with arithmetic sort.
        let sort = self.ctx.terms.sort(var_term);
        if !matches!(sort, Sort::Real | Sort::Int) {
            return None;
        }
        if !matches!(self.ctx.terms.get(var_term), TermData::Var(_, _)) {
            return None;
        }

        // Evaluate the value term to get the target value.
        match self.evaluate_term(model, value_term) {
            EvalValue::Rational(r) => Some((var_term, r)),
            _ => {
                // The value term might be a constant that doesn't need model lookup.
                match self.ctx.terms.get(value_term) {
                    TermData::Const(Constant::Int(n)) => {
                        Some((var_term, BigRational::from(n.clone())))
                    }
                    TermData::Const(Constant::Rational(r)) => Some((var_term, r.0.clone())),
                    _ => None,
                }
            }
        }
    }
}

/// Extension trait for BigRational to convert to BigInt when the value is integral.
trait BigRationalExt {
    fn to_integer_if_whole(&self) -> Option<num_bigint::BigInt>;
}

impl BigRationalExt for BigRational {
    fn to_integer_if_whole(&self) -> Option<num_bigint::BigInt> {
        if self.is_integer() {
            Some(self.numer().clone())
        } else {
            None
        }
    }
}
