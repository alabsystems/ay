// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counter-Example Guided Quantifier Instantiation (CEGQI)
//!
//! This module implements CEGQI for quantified arithmetic formulas that E-matching
//! cannot handle (formulas without ground terms to match against).
//!
//! # Algorithm
//!
//! From Reynolds et al. "Solving Linear Arithmetic Using Counterexample-Guided
//! Instantiation" (FMSD 2017):
//!
//! 1. **Negate the quantifier body**: For `forall x. phi(x)`, create `~phi(e)`
//!    where `e` is a fresh constant ("counterexample variable")
//! 2. **Check satisfiability**: If `~phi(e)` is UNSAT, the quantifier is valid
//! 3. **Extract model**: If SAT, get model `M` with assignment `e = v`
//! 4. **Compute selection term**: Find `t` such that `phi(t)` is implied
//! 5. **Add instantiation**: Assert `phi(t)` and repeat
//!
//! # Architecture
//!
//! - `CegqiInstantiator`: Main orchestrator for CEGQI
//! - `ArithInstantiator`: Theory-specific instantiation for LIA/LRA
//!
//! # Usage
//!
//! CEGQI is invoked after E-matching fails to fully instantiate quantified formulas.
//! It complements E-matching rather than replacing it.

pub(crate) mod arith;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use crate::ematching::subst_vars;

/// Red zone size for `stacker::maybe_grow` in CEGQI term analysis recursion (#8414).
const CEGQI_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for CEGQI term analysis recursion.
const CEGQI_STACK_SIZE: usize = 1024 * 1024;

/// Main orchestrator for CEGQI
///
/// Handles:
/// - Counterexample lemma creation (negating quantifier body)
/// - Variable ordering for elimination
/// - Solved form tracking (var -> substitution term)
/// - Instantiation construction
pub(crate) struct CegqiInstantiator {
    /// The quantified formula being processed
    quantifier: TermId,
    /// Mapping from bound variable name to CE variable
    bound_to_ce: HashMap<String, TermId>,
    /// True if this is a forall quantifier, false if exists
    is_forall: bool,
}

impl CegqiInstantiator {
    /// Create a new CEGQI instantiator for a quantified formula
    ///
    /// # Arguments
    /// * `quantifier` - Term ID of a forall/exists formula
    /// * `terms` - Term store for creating new terms
    ///
    /// # Returns
    /// A new instantiator, or None if the term is not a quantified formula
    pub(crate) fn new(quantifier: TermId, terms: &mut TermStore) -> Option<Self> {
        // Check that this is a quantified formula
        // TermData::Forall and Exists are tuple variants: (Vec<(String, Sort)>, TermId)
        let data = terms.get(quantifier);
        let (vars, is_forall) = match data {
            TermData::Forall(vars, _body, _) => (vars.clone(), true),
            TermData::Exists(vars, _body, _) => (vars.clone(), false),
            _ => return None,
        };

        // Create counterexample variables for each bound variable
        let mut bound_to_ce = HashMap::default();

        for (name, sort) in &vars {
            // Create a fresh CE constant for this bound variable
            let ce_name = format!("__ce_{name}");
            let ce_var = terms.mk_var(&ce_name, sort.clone());
            bound_to_ce.insert(name.clone(), ce_var);
        }

        Some(Self {
            quantifier,
            bound_to_ce,
            is_forall,
        })
    }

    /// Create the counterexample lemma for CEGQI
    ///
    /// For `forall x. phi(x)`: creates `~phi(e)` where `e` is the CE variable.
    /// If this is SAT, we get a counterexample to guide instantiation.
    ///
    /// For `exists x. phi(x)`: creates `phi(e)` (no negation).
    /// If this is SAT, we found a witness for the existential.
    ///
    /// # Returns
    /// Term ID of the CE lemma, or None if construction fails
    pub(crate) fn create_ce_lemma(&self, terms: &mut TermStore) -> Option<TermId> {
        // Get quantifier body and determine if it's forall or exists
        let data = terms.get(self.quantifier);
        let (body, is_forall) = match data {
            TermData::Forall(_, body, _) => (*body, true),
            TermData::Exists(_, body, _) => (*body, false),
            _ => return None,
        };

        // Substitute bound variables with CE variables
        let substituted = self.substitute_vars(body, terms)?;

        // For forall: negate to find counterexamples
        // For exists: keep as-is to find witnesses
        if is_forall {
            Some(terms.mk_not(substituted))
        } else {
            Some(substituted)
        }
    }

    /// Substitute bound variables with counterexample variables.
    fn substitute_vars(&self, term: TermId, terms: &mut TermStore) -> Option<TermId> {
        Some(subst_vars(terms, term, &self.bound_to_ce))
    }

    /// Returns true if this is a forall quantifier, false for exists
    ///
    /// This is used by the executor to correctly map CE lemma results:
    /// - forall: UNSAT on CE lemma → SAT (quantifier holds)
    /// - exists: SAT on CE lemma → SAT (witness found)
    pub(crate) fn is_forall(&self) -> bool {
        self.is_forall
    }

    /// Returns the mapping from bound variable names to CE variables
    ///
    /// Used by the executor to extract CE variable model values after solving,
    /// and by the quantified-CE-lemma rebuilder to substitute binders with
    /// their CE variables.
    pub(crate) fn ce_variables(&self) -> &HashMap<String, TermId> {
        &self.bound_to_ce
    }

    /// Create a ground instantiation of the quantifier body using an explicit
    /// substitution map (bound variable name -> ground term).
    ///
    /// This is the CEGQI refinement step: after solving with a CE lemma yields
    /// SAT (counterexample found), the executor extracts model values for CE
    /// variables and passes them as ground terms here. The result `phi(t)` is
    /// added to assertions before re-solving.
    pub(crate) fn _create_model_instantiation(
        &self,
        terms: &mut TermStore,
        var_values: &HashMap<String, TermId>,
    ) -> Option<TermId> {
        let body = match terms.get(self.quantifier) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => *body,
            _ => return None,
        };

        // Reuse the existing substitution walker by creating a temporary
        // instantiator whose bound_to_ce maps to value terms instead of CE vars.
        let temp = Self {
            quantifier: self.quantifier,
            bound_to_ce: var_values.clone(),
            is_forall: self.is_forall,
        };
        temp.substitute_vars(body, terms)
    }
}

/// Check if a term is a good candidate for CEGQI
///
/// Returns true if:
/// 1. It's a quantified formula (forall/exists)
/// 2. Every bound variable has arithmetic sort (Int/Real)
/// 3. The body involves arithmetic (LIA/LRA) without patterns for E-matching
///
/// # Arguments
/// * `terms` - Term store
/// * `term` - Term to check
pub(crate) fn is_cegqi_candidate(terms: &TermStore, term: TermId) -> bool {
    let data = terms.get(term);

    match data {
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            // Arithmetic CEGQI only supports quantifiers whose binders are all
            // arithmetic-sorted. If any bound variable has a non-arithmetic
            // sort (Seq, Array, Datatype, UF sort, ...), refinement cannot
            // extract model values or compute selection terms soundly for the
            // full quantified body, and CE lemmas can over-constrain the
            // problem (#7883/#7885/#7886/#7887).
            has_only_arithmetic_bound_vars(vars)
                && involves_arithmetic(terms, *body)
                && !has_bound_dependent_bool_uf(terms, *body, vars)
        }
        _ => false,
    }
}

fn has_only_arithmetic_bound_vars(vars: &[(String, Sort)]) -> bool {
    vars.iter()
        .all(|(_, sort)| matches!(sort, Sort::Int | Sort::Real))
}

/// True when the quantifier body applies a non-theory Bool symbol (an
/// uninterpreted predicate) to a term mentioning a bound variable. Such
/// quantifiers are excluded from arithmetic CEGQI (no bound extraction is
/// possible through an opaque Bool UF); the finite-domain expander uses the
/// same predicate to recognize the shapes that would otherwise fail closed to
/// `Unknown(QuantifierUnhandled)` and grant them the extended bounded-Int
/// expansion budget (rank-9 step 1).
pub(crate) fn has_bound_dependent_bool_uf(
    terms: &TermStore,
    term: TermId,
    vars: &[(String, Sort)],
) -> bool {
    let var_names: Vec<&str> = vars.iter().map(|(name, _)| name.as_str()).collect();
    has_bound_dependent_bool_uf_rec(terms, term, &var_names)
}

fn has_bound_dependent_bool_uf_rec(terms: &TermStore, term: TermId, var_names: &[&str]) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if !is_cegqi_theory_bool_symbol(name)
                && matches!(terms.sort(term), Sort::Bool)
                && args
                    .iter()
                    .any(|&arg| contains_bound_var_name(terms, arg, var_names))
            {
                return true;
            }
            args.iter()
                .any(|&arg| has_bound_dependent_bool_uf_rec(terms, arg, var_names))
        }
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| has_bound_dependent_bool_uf_rec(terms, arg, var_names)),
        TermData::Not(inner) => has_bound_dependent_bool_uf_rec(terms, *inner, var_names),
        TermData::Ite(cond, then_term, else_term) => {
            has_bound_dependent_bool_uf_rec(terms, *cond, var_names)
                || has_bound_dependent_bool_uf_rec(terms, *then_term, var_names)
                || has_bound_dependent_bool_uf_rec(terms, *else_term, var_names)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| has_bound_dependent_bool_uf_rec(terms, *value, var_names))
                || has_bound_dependent_bool_uf_rec(terms, *body, var_names)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            has_bound_dependent_bool_uf_rec(terms, *body, var_names)
        }
        TermData::Const(_) | TermData::Var(_, _) => false,
        _ => false,
    }
}

fn is_cegqi_theory_bool_symbol(name: &str) -> bool {
    matches!(
        name,
        "=" | "<" | "<=" | ">" | ">=" | "and" | "or" | "=>" | "xor" | "distinct" | "not" | "is_int"
    )
}

fn contains_bound_var_name(terms: &TermStore, term: TermId, var_names: &[&str]) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => var_names.contains(&name.as_str()),
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| contains_bound_var_name(terms, arg, var_names)),
        TermData::Not(inner) => contains_bound_var_name(terms, *inner, var_names),
        TermData::Ite(cond, then_term, else_term) => {
            contains_bound_var_name(terms, *cond, var_names)
                || contains_bound_var_name(terms, *then_term, var_names)
                || contains_bound_var_name(terms, *else_term, var_names)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| contains_bound_var_name(terms, *value, var_names))
                || contains_bound_var_name(terms, *body, var_names)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            contains_bound_var_name(terms, *body, var_names)
        }
        TermData::Const(_) => false,
        _ => false,
    }
}

/// Check if a term involves arithmetic operations (LIA/LRA).
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn involves_arithmetic(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(CEGQI_STACK_RED_ZONE, CEGQI_STACK_SIZE, || {
        let data = terms.get(term);

        match data {
            TermData::Const(c) => {
                use ay_core::term::Constant;
                matches!(c, Constant::Int(_) | Constant::Rational(_))
            }
            // Bare variables do not make a formula arithmetic. CEGQI only handles
            // variables when they appear inside arithmetic operators/comparisons
            // or arithmetic equalities.
            TermData::Var(_, _) => false,
            TermData::App(Symbol::Named(name), args) => {
                // Check for arithmetic operators
                let is_arith_op = matches!(
                    name.as_str(),
                    "+" | "-" | "*" | "/" | "div" | "mod" | "<" | "<=" | ">" | ">="
                );
                if is_arith_op {
                    return true;
                }
                // Equality over arithmetic-sorted terms is part of the supported
                // arithmetic CEGQI fragment, including pure UF equalities such as
                // f(x) = x with x:Int.
                if name == "="
                    && args.len() == 2
                    && args
                        .iter()
                        .any(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
                {
                    return true;
                }
                // Recurse into arguments
                args.iter().any(|&a| involves_arithmetic(terms, a))
            }
            TermData::App(_, args) => args.iter().any(|&a| involves_arithmetic(terms, a)),
            TermData::Not(inner) => involves_arithmetic(terms, *inner),
            TermData::Ite(c, t, e) => {
                involves_arithmetic(terms, *c)
                    || involves_arithmetic(terms, *t)
                    || involves_arithmetic(terms, *e)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, t)| involves_arithmetic(terms, *t))
                    || involves_arithmetic(terms, *body)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                involves_arithmetic(terms, *body)
            }
            // Future TermData variants: conservatively not arithmetic.
            _ => false,
        }
    }) // stacker::maybe_grow
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
