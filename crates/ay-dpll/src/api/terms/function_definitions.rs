// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native non-recursive function definitions and body substitution.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::super::types::{
    FuncDecl, FuncDeclIdentity, NativeDefinitionIdentity, SolverError, Term,
};
use super::super::{DefinedFun, Solver};

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Define a non-recursive function for inline expansion (#8613).
    ///
    /// This is the programmatic equivalent of SMT-LIB `(define-fun ...)`.
    /// When the returned `FuncDecl` is applied via [`try_apply`], the body
    /// is expanded inline (via parameter term substitution) rather than
    /// creating an uninterpreted function application. This avoids the
    /// quantifier overhead of encoding spec functions as UF + axiom.
    ///
    /// The `body_fn` closure receives fresh parameter variables and must
    /// return the body term built from those parameters.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ay_dpll::api::{Logic, SolveResult, Solver, Sort, Term};
    ///
    /// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    /// let x = solver.declare_const("x", Sort::Int);
    ///
    /// // define-fun sum(a: Int, b: Int) -> Int = a + b
    /// let sum = solver.try_define_fun(
    ///     "sum",
    ///     &[("a", Sort::Int), ("b", Sort::Int)],
    ///     Sort::Int,
    ///     |solver, params| {
    ///         let a = params[0];
    ///         let b = params[1];
    ///         solver.try_add(a, b)
    ///     },
    /// ).unwrap();
    ///
    /// // sum(x, 1) = x + 1 — the application is expanded inline
    /// let one = solver.int_const(1);
    /// let result = solver.try_apply(&sum, &[x, one]).unwrap();
    /// let five = solver.int_const(5);
    /// let eq = solver.try_eq(result, five).unwrap();
    /// solver.try_assert_term(eq).unwrap();
    ///
    /// // x + 1 = 5 => x = 4
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if `body_fn` returns an error, or if the body's
    /// sort does not match `return_sort`.
    ///
    /// [`try_apply`]: Solver::try_apply
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_define_fun<F>(
        &mut self,
        name: &str,
        params: &[(&str, Sort)],
        return_sort: Sort,
        body_fn: F,
    ) -> Result<FuncDecl, SolverError>
    where
        F: FnOnce(&mut Self, &[Term]) -> Result<Term, SolverError>,
    {
        // Check before invoking the caller's closure: a rejected definition
        // must not consume terms or allow arbitrary closure side effects.
        self.reject_reused_native_function_name(name, "define_fun")?;

        // Create fresh variables for each parameter
        let mut param_terms = Vec::with_capacity(params.len());
        let mut param_entries = Vec::with_capacity(params.len());
        for &(param_name, ref param_sort) in params {
            let term_sort = self.lower_live_sort(param_sort);
            let var_id = self.terms_mut().mk_fresh_var(param_name, term_sort);
            let var_name = match self.terms().get(var_id) {
                TermData::Var(fresh_name, _) => fresh_name.clone(),
                _ => param_name.to_string(),
            };
            param_terms.push(self.wrap_term(var_id));
            param_entries.push((var_name, var_id));
        }

        // Build the body using the parameter variables
        let body = body_fn(self, &param_terms)?;

        // The body builder has mutable access to the solver and may itself
        // introduce declarations. Re-check before installing this definition
        // so a closure cannot create a same-name alias after the entry check.
        self.reject_reused_native_function_name(name, "define_fun")?;

        // Verify the body sort matches the declared return sort
        let body_id = self.resolve_term("define_fun", body)?;
        let body_sort = self.terms().sort(body_id).clone();
        let expected_sort = self.lower_live_sort(&return_sort);
        if body_sort != expected_sort {
            return Err(SolverError::SortMismatch {
                operation: "define_fun",
                expected: "matching return sort",
                got: vec![body_sort],
            });
        }

        // Store the definition for inline expansion during try_apply
        let domain: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        let identity = NativeDefinitionIdentity::fresh();
        self.defined_funs.insert(
            name.to_string(),
            DefinedFun {
                params: param_entries,
                body: body_id,
                return_sort: expected_sort,
                assertion_derived: false,
                identity: FuncDeclIdentity::NativeDefinition(identity.clone()),
            },
        );
        self.executor.invalidate_for_native_api_mutation();

        Ok(FuncDecl::with_native_definition_identity(
            name.to_string(),
            domain,
            return_sort,
            identity,
        ))
    }

    /// Define a non-recursive function from an already-built body term.
    ///
    /// This is the lower-level form used by facade translators that already
    /// create parameter terms before translating the body. Each parameter term
    /// must be a variable term, and the body should be built using those same
    /// parameter terms. Applications via [`try_apply`] expand inline.
    ///
    /// Most direct API users should prefer [`try_define_fun`], which creates
    /// the parameter variables and passes them to a body-building closure.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if any parameter is not a
    /// variable term, or [`SolverError::SortMismatch`] if `body` does not have
    /// `return_sort`.
    ///
    /// [`try_apply`]: Solver::try_apply
    /// [`try_define_fun`]: Solver::try_define_fun
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        return_sort: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        self.reject_reused_native_function_name(name, "define_fun")?;

        let param_ids = params
            .iter()
            .map(|(_, param)| self.resolve_term("define_fun", *param))
            .collect::<Result<Vec<_>, _>>()?;
        let body_id = self.resolve_term("define_fun", body)?;

        let mut param_entries = Vec::with_capacity(params.len());
        let mut domain = Vec::with_capacity(params.len());

        for ((param_name, _), param_id) in params.iter().zip(param_ids) {
            let sort = self.terms().sort(param_id).clone();
            let var_name = match self.terms().get(param_id) {
                TermData::Var(fresh_name, _) => fresh_name.clone(),
                _ => {
                    return Err(SolverError::InvalidArgument {
                        operation: "define_fun",
                        message: format!("parameter '{param_name}' must be a variable term"),
                    });
                }
            };
            param_entries.push((var_name, param_id));
            domain.push(sort);
        }

        let body_sort = self.terms().sort(body_id).clone();
        let expected_sort = self.lower_live_sort(&return_sort);
        if body_sort != expected_sort {
            return Err(SolverError::SortMismatch {
                operation: "define_fun",
                expected: "matching return sort",
                got: vec![body_sort],
            });
        }

        let identity = NativeDefinitionIdentity::fresh();
        self.defined_funs.insert(
            name.to_string(),
            DefinedFun {
                params: param_entries,
                body: body_id,
                return_sort: expected_sort,
                assertion_derived: false,
                identity: FuncDeclIdentity::NativeDefinition(identity.clone()),
            },
        );
        self.executor.invalidate_for_native_api_mutation();

        Ok(FuncDecl::with_native_definition_identity(
            name.to_string(),
            domain,
            return_sort,
            identity,
        ))
    }

    pub(in crate::api) fn substitute_defined_fun_body(
        &mut self,
        term: TermId,
        subst: &HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&replacement) = subst.get(&term) {
            return replacement;
        }

        match self.terms().get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(symbol, args) => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|&arg| self.substitute_defined_fun_body(arg, subst))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = self.terms().sort(term).clone();
                    self.terms_mut().mk_app(symbol, new_args, sort)
                }
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<_> = bindings
                    .iter()
                    .map(|(name, value)| {
                        (
                            name.clone(),
                            self.substitute_defined_fun_body(*value, subst),
                        )
                    })
                    .collect();
                let new_body = self.substitute_defined_fun_body(body, subst);
                if new_bindings == bindings && new_body == body {
                    term
                } else {
                    self.terms_mut().mk_let(new_bindings, new_body)
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.substitute_defined_fun_body(inner, subst);
                if new_inner == inner {
                    term
                } else {
                    self.terms_mut().mk_not(new_inner)
                }
            }
            TermData::Ite(cond, then_term, else_term) => {
                let new_cond = self.substitute_defined_fun_body(cond, subst);
                let new_then = self.substitute_defined_fun_body(then_term, subst);
                let new_else = self.substitute_defined_fun_body(else_term, subst);
                if new_cond == cond && new_then == then_term && new_else == else_term {
                    term
                } else {
                    self.terms_mut().mk_ite(new_cond, new_then, new_else)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.substitute_defined_fun_body(body, subst);
                let new_triggers: Vec<Vec<TermId>> = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|&t| self.substitute_defined_fun_body(t, subst))
                            .collect()
                    })
                    .collect();
                if new_body == body && new_triggers == triggers {
                    term
                } else {
                    self.terms_mut()
                        .mk_forall_with_triggers(vars, new_body, new_triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.substitute_defined_fun_body(body, subst);
                let new_triggers: Vec<Vec<TermId>> = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|&t| self.substitute_defined_fun_body(t, subst))
                            .collect()
                    })
                    .collect();
                if new_body == body && new_triggers == triggers {
                    term
                } else {
                    self.terms_mut()
                        .mk_exists_with_triggers(vars, new_body, new_triggers)
                }
            }
            other => {
                unreachable!("unhandled TermData variant in define-fun substitution: {other:?}")
            }
        }
    }
}
