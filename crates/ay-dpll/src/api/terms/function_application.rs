// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native function application and declaration-handle authentication.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};

use super::super::types::{
    FrontendFuncDeclIdentity, FuncDecl, FuncDeclIdentity, SolverError, Term,
};
use super::super::{DefinedFun, Solver};

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Apply a declared function to arguments, creating an application term.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUflia);
    /// let x = solver.declare_const("x", Sort::Int);
    ///
    /// let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    /// let fx = solver.apply(&f, &[x]);
    /// # let _ = fx;
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The number of arguments doesn't match the function's arity
    /// - Argument sorts don't match the function's domain sorts
    ///
    /// Use [`Self::try_apply`] for a fallible version.
    pub fn apply(&mut self, func: &FuncDecl, args: &[Term]) -> Term {
        self.try_apply(func, args).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible version of [`apply`](Solver::apply). Returns an error instead of panicking.
    ///
    /// For functions registered via [`try_define_fun`], the body is expanded
    /// inline using parameter term substitution. For functions registered via
    /// [`try_declare_fun`], an uninterpreted function application is created.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if the number of arguments doesn't
    /// match the function's arity.
    ///
    /// Returns [`SolverError::SortMismatch`] if any argument's sort doesn't match
    /// the corresponding domain sort.
    ///
    /// [`try_define_fun`]: Solver::try_define_fun
    /// [`try_declare_fun`]: Solver::try_declare_fun
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_apply(&mut self, func: &FuncDecl, args: &[Term]) -> Result<Term, SolverError> {
        if args.len() != func.domain.len() {
            return Err(SolverError::InvalidArgument {
                operation: "apply",
                message: format!(
                    "function {} expects {} args, got {}",
                    func.name,
                    func.domain.len(),
                    args.len()
                ),
            });
        }

        let arg_ids = args
            .iter()
            .map(|arg| self.resolve_term("apply", *arg))
            .collect::<Result<Vec<_>, _>>()?;

        for (&arg_id, expected_sort) in arg_ids.iter().zip(func.domain.iter()) {
            let actual_sort = self.terms().sort(arg_id).clone();
            let expected_core = self.lower_live_sort(expected_sort);
            if actual_sort != expected_core {
                return Err(SolverError::SortMismatch {
                    operation: "apply",
                    expected: "matching domain sort",
                    got: vec![actual_sort],
                });
            }
        }

        // Check if this is a defined function (#8613) — expand inline
        if let Some(def) = self.defined_funs.get(&func.name).cloned() {
            if !self.defined_function_handle_matches(func, &def) {
                return Err(SolverError::InvalidArgument {
                    operation: "apply",
                    message: format!(
                        "function handle for '{}' does not match its registered definition",
                        func.name
                    ),
                });
            }
            let subst: HashMap<TermId, TermId> = def
                .params
                .iter()
                .zip(arg_ids.iter())
                .map(|((_, param), &arg_id)| (*param, arg_id))
                .collect();
            let result = self.substitute_defined_fun_body(def.body, &subst);
            return Ok(self.wrap_term(result));
        }

        if !self.function_handle_is_registered(func) {
            return Err(SolverError::InvalidArgument {
                operation: "apply",
                message: format!(
                    "function handle for '{}' does not match a registered native declaration",
                    func.name
                ),
            });
        }

        // Otherwise create an uninterpreted function application.
        //
        // Keep the conservative shadow latch for components that use it as an
        // additional guard. The core application itself is now independently
        // protected by `func.core_name`, so it cannot be mistaken for the
        // builtin integrality predicate. (#isint-shadow)
        if func.name == "is_int" {
            self.terms_mut().mark_is_int_shadowed();
        }
        let result_sort = self.lower_live_sort(&func.range);
        let result =
            self.terms_mut()
                .mk_app(Symbol::Named(func.core_name.clone()), arg_ids, result_sort);
        Ok(self.wrap_term(result))
    }

    pub(super) fn reject_reused_native_function_name(
        &self,
        name: &str,
        operation: &'static str,
    ) -> Result<(), SolverError> {
        if self.defined_funs.contains_key(name) || self.executor.context().has_symbol_binding(name)
        {
            return Err(SolverError::InvalidArgument {
                operation,
                message: format!(
                    "function name '{name}' is already in use; native function overloading is not supported"
                ),
            });
        }
        Ok(())
    }

    fn function_handle_is_registered(&self, func: &FuncDecl) -> bool {
        let Some(FuncDeclIdentity::Frontend(identity)) = func.identity.as_ref() else {
            return false;
        };
        if let Some(registered) = self.native_fun_signatures.get(&func.name) {
            let registered_domain: Vec<Sort> = registered
                .domain
                .iter()
                .map(|sort| self.lower_live_sort(sort))
                .collect();
            let registered_range = self.lower_live_sort(&registered.range);
            let exact_native_match = registered.identity == *identity
                && registered.core_name == func.core_name
                && self.frontend_declaration_is_live(
                    &func.core_name,
                    identity,
                    &registered_domain,
                    &registered_range,
                )
                && native_signature_accepts_instance(
                    &registered.domain,
                    &registered.range,
                    &func.domain,
                    &func.range,
                );
            if exact_native_match {
                return true;
            }
            // A datatype member may overload the same public spelling with a
            // different exact signature. The unrelated native registration
            // must not mask the member's declaration identity; continue to
            // the strict datatype core/kind/signature authentication below.
        }

        // Datatype operation handles are adopted by `try_declare_fun` without
        // recording a second native declaration. Preserve that exact,
        // registered member contract while rejecting every missing user UF.
        let term_domain: Vec<Sort> = func
            .domain
            .iter()
            .map(|sort| self.lower_live_sort(sort))
            .collect();
        let term_range = self.lower_live_sort(&func.range);
        let ctx = self.executor.context();
        ctx.is_datatype_member_name(&func.name)
            && self.frontend_declaration_is_live(
                func.core_name(),
                identity,
                &term_domain,
                &term_range,
            )
            && self
                .registered_function_binding(&func.name, &func.domain, &func.range)
                .is_some_and(|(core_name, current)| {
                    core_name == func.core_name && current == *identity
                })
    }

    pub(in crate::api) fn function_handle_is_current(&self, func: &FuncDecl) -> bool {
        self.defined_funs
            .get(&func.name)
            .is_some_and(|definition| self.defined_function_handle_matches(func, definition))
            || self.function_handle_is_registered(func)
    }

    pub(in crate::api) fn core_name_requires_authenticated_handle(&self, core_name: &str) -> bool {
        let ctx = self.executor.context();
        ctx.symbols_iter()
            .any(|(surface, info)| ctx.symbol_identity_name(surface, info) == core_name)
    }

    fn defined_function_handle_matches(&self, func: &FuncDecl, definition: &DefinedFun) -> bool {
        func.identity.as_ref() == Some(&definition.identity)
            && definition.params.len() == func.domain.len()
            && definition
                .params
                .iter()
                .zip(func.domain.iter())
                .all(|((_, param), expected)| {
                    self.terms().sort(*param) == &self.lower_live_sort(expected)
                })
            && definition.return_sort == self.lower_live_sort(&func.range)
    }

    /// Resolve a public function spelling and exact API signature to the exact
    /// private declaration installed by the frontend.
    pub(super) fn registered_function_binding(
        &self,
        name: &str,
        domain: &[Sort],
        range: &Sort,
    ) -> Option<(String, FrontendFuncDeclIdentity)> {
        let term_domain: Vec<Sort> = domain
            .iter()
            .map(|sort| self.lower_live_sort(sort))
            .collect();
        let term_range = self.lower_live_sort(range);
        let ctx = self.executor.context();
        let mut matches = ctx.symbols_iter().filter(|(surface, info)| {
            surface.as_str() == name && info.arg_sorts == term_domain && info.sort == term_range
        });
        let (surface, info) = matches.next()?;
        let core_name = ctx.symbol_identity_name(surface, info).to_string();
        let declaration_id = info.declaration_id().clone();
        let declaration_kind = info.declaration_kind();
        if matches.any(|(surface, info)| {
            ctx.symbol_identity_name(surface, info) != core_name
                || info.declaration_id() != &declaration_id
                || info.declaration_kind() != declaration_kind
        }) {
            return None;
        }
        // A core spelling is the only identity retained by an App. Refuse to
        // authenticate it if any live binding assigns that spelling to a
        // different declaration, even at another public surface alias.
        if ctx.symbols_iter().any(|(surface, info)| {
            ctx.symbol_identity_name(surface, info) == core_name
                && (info.declaration_id() != &declaration_id
                    || info.declaration_kind() != declaration_kind)
        }) {
            return None;
        }
        Some((
            core_name,
            FrontendFuncDeclIdentity::new(
                ctx.source_context_stamp(),
                declaration_id,
                declaration_kind,
            ),
        ))
    }

    pub(super) fn frontend_function_handle_is_live(&self, func: &FuncDecl) -> bool {
        let term_domain: Vec<Sort> = func
            .domain
            .iter()
            .map(|sort| self.lower_live_sort(sort))
            .collect();
        let term_range = self.lower_live_sort(&func.range);
        self.frontend_function_handle_matches_exact_signature(func, &term_domain, &term_range)
    }

    pub(super) fn frontend_function_handle_matches_exact_signature(
        &self,
        func: &FuncDecl,
        term_domain: &[Sort],
        term_range: &Sort,
    ) -> bool {
        let Some(FuncDeclIdentity::Frontend(identity)) = func.identity.as_ref() else {
            return false;
        };
        self.frontend_declaration_is_live(func.core_name(), identity, term_domain, term_range)
    }

    fn frontend_declaration_is_live(
        &self,
        core_name: &str,
        identity: &FrontendFuncDeclIdentity,
        term_domain: &[Sort],
        term_range: &Sort,
    ) -> bool {
        let ctx = self.executor.context();
        if !identity
            .context_stamp()
            .is_same_context(&ctx.source_context_stamp())
            || ctx.effective_declaration_kind(identity.declaration_id())
                != Some(identity.declaration_kind())
        {
            return false;
        }

        let mut exact_signature_found = false;
        for (surface, info) in ctx.symbols_iter() {
            if ctx.symbol_identity_name(surface, info) != core_name {
                continue;
            }
            if info.declaration_id() != identity.declaration_id()
                || info.declaration_kind() != identity.declaration_kind()
            {
                // One core spelling cannot safely denote two declarations.
                return false;
            }
            exact_signature_found |= info.arg_sorts == term_domain && info.sort == *term_range;
        }
        exact_signature_found
    }
}

fn native_signature_accepts_instance(
    declared_domain: &[Sort],
    declared_range: &Sort,
    handle_domain: &[Sort],
    handle_range: &Sort,
) -> bool {
    if declared_domain.len() != handle_domain.len() {
        return false;
    }
    let mut type_bindings: HashMap<String, Sort> = HashMap::default();
    declared_domain
        .iter()
        .zip(handle_domain)
        .all(|(declared, actual)| {
            native_sort_accepts_instance(declared, actual, &mut type_bindings)
        })
        && native_sort_accepts_instance(declared_range, handle_range, &mut type_bindings)
}

fn native_sort_accepts_instance(
    declared: &Sort,
    actual: &Sort,
    type_bindings: &mut HashMap<String, Sort>,
) -> bool {
    match declared {
        Sort::TypeVar(name) => match type_bindings.get(name) {
            Some(bound) => bound == actual,
            None => {
                type_bindings.insert(name.clone(), actual.clone());
                true
            }
        },
        Sort::Array(declared_array) => match actual {
            Sort::Array(actual_array) => {
                native_sort_accepts_instance(
                    &declared_array.index_sort,
                    &actual_array.index_sort,
                    type_bindings,
                ) && native_sort_accepts_instance(
                    &declared_array.element_sort,
                    &actual_array.element_sort,
                    type_bindings,
                )
            }
            _ => false,
        },
        Sort::Seq(declared_element) => match actual {
            Sort::Seq(actual_element) => {
                native_sort_accepts_instance(declared_element, actual_element, type_bindings)
            }
            _ => false,
        },
        _ => declared == actual,
    }
}
