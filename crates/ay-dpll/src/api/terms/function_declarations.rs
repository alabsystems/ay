// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native function declarations and public aliases.

use ay_core::Sort;
use ay_frontend::Command;

use super::super::types::{FuncDecl, NativeReplayEventKind, SolverError, SortExt};
use super::super::{NativeFunctionRegistration, Solver};

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Declare a function (n-arity) with the given name, domain, and range sorts.
    ///
    /// The function is registered with the SMT context so it appears in models.
    /// Use `Solver::apply` to create application terms.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUflia);
    /// let x = solver.declare_const("x", Sort::Int);
    ///
    /// let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    /// let fx = solver.apply(&f, &[x]);
    ///
    /// let one = solver.int_const(1);
    /// let x_plus_1 = solver.add(x, one);
    /// let eq_term = solver.eq(fx, x_plus_1);
    /// solver.assert_term(eq_term);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to declare the function. Use [`try_declare_fun`]
    /// for a fallible version that returns an error instead.
    ///
    /// [`try_declare_fun`]: Solver::try_declare_fun
    pub fn declare_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.try_declare_fun(name, domain, range)
            .unwrap_or_else(|e| panic!("Failed to declare function '{name}': {e}"))
    }

    /// Try to declare a function (n-arity) with the given name, domain, and range sorts.
    ///
    /// Fallible version of [`declare_fun`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to declare the function.
    ///
    /// [`declare_fun`]: Solver::declare_fun
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        if let Some(existing) = self.native_fun_signatures.get(name) {
            if existing.domain == domain && existing.range == range {
                let handle = FuncDecl::with_frontend_identity(
                    name.to_string(),
                    existing.core_name.clone(),
                    domain.to_vec(),
                    range,
                    existing.identity.clone(),
                );
                if self.frontend_function_handle_is_live(&handle) {
                    return Ok(handle);
                }
                return Err(SolverError::InvalidArgument {
                    operation: "declare_fun",
                    message: format!("function '{name}' has stale native declaration metadata"),
                });
            }
            return Err(SolverError::InvalidArgument {
                operation: "declare_fun",
                message: format!(
                    "function name '{name}' is already in use with a different native signature"
                ),
            });
        }
        // #reserved-ops: ADOPT an identical-signature redeclaration of a
        // datatype constructor/selector/tester. Embedders (deductive-checks's encoder
        // in particular) declare the EXACT native member names after
        // `try_declare_datatype` to obtain `FuncDecl` handles over the same
        // symbols — the documented handle contract. The SMT-LIB TEXT path
        // rejects any such declaration (`DatatypeMemberCollision`: a textual
        // `declare-fun is-Cons`/`hd` forges the builtin — a confirmed
        // wrong-UNSAT class), so the programmatic path pre-empts the gate
        // here: if the name is a registered member AND the requested
        // signature matches the registered one exactly, return the handle
        // WITHOUT mutating the context (the symbol is already registered;
        // nothing changed, so no replay event is recorded either). A
        // mismatched signature falls through to the executor and is rejected
        // by the gate.
        {
            let term_domain: Vec<Sort> = domain
                .iter()
                .map(|sort| self.lower_live_sort(sort))
                .collect();
            let term_range = self.lower_live_sort(&range);
            let ctx = self.executor.context();
            if ctx.is_datatype_member_name(name)
                && ctx.has_symbol_with_signature(name, &term_domain, &term_range)
            {
                let (core_name, identity) = self
                    .registered_function_binding(name, domain, &range)
                    .ok_or_else(|| SolverError::InvalidArgument {
                        operation: "declare_fun",
                        message: format!(
                            "datatype function '{name}' has no unique registered core identity"
                        ),
                    })?;
                return Ok(FuncDecl::with_frontend_identity(
                    name.to_string(),
                    core_name,
                    domain.to_vec(),
                    range,
                    identity,
                ));
            }
        }

        // The native API constructs core applications directly from a
        // `FuncDecl`; unlike the SMT-LIB elaborator, it has no expected-sort
        // context in which to resolve an overloaded surface name.  Allowing a
        // second declaration (or a declaration that shadows an inline
        // definition) would therefore collapse distinct functions onto the
        // same `Symbol::Named` identity. `FuncDecl` therefore retains the
        // frontend-assigned declaration identity independently of this public
        // spelling.
        self.reject_reused_native_function_name(name, "declare_fun")?;

        // Build the DeclareFun command to register the function with the SMT context
        let domain_sorts: Vec<_> = domain.iter().map(SortExt::to_command_sort).collect();
        let range_sort = range.to_command_sort();
        let cmd = Command::DeclareFun(name.to_string(), domain_sorts, range_sort);

        // Execute the command to register the function
        // This makes it appear in ctx.symbol_iter() for model printing
        self.executor.execute_native_global_declaration(&cmd)?;
        let (core_name, identity) = self
            .registered_function_binding(name, domain, &range)
            .ok_or_else(|| SolverError::InvalidArgument {
                operation: "declare_fun",
                message: format!(
                    "function '{name}' was registered without a unique core declaration identity"
                ),
            })?;
        self.native_fun_signatures.insert(
            name.to_string(),
            NativeFunctionRegistration {
                domain: domain.to_vec(),
                range: range.clone(),
                core_name: core_name.clone(),
                identity: identity.clone(),
            },
        );
        self.record_native_replay_event(NativeReplayEventKind::DeclareFun {
            name: name.to_string(),
            domain: domain.to_vec(),
            range: range.clone(),
        });

        Ok(FuncDecl::with_frontend_identity(
            name.to_string(),
            core_name,
            domain.to_vec(),
            range,
            identity,
        ))
    }

    /// Register a caller-visible SMT-LIB name for an already-declared native
    /// function whose core identity is carried by `decl`.
    ///
    /// This is a narrow adapter hook for compatibility layers that preserve a
    /// declaration's public symbol separately from its collision-proof native
    /// identity. It records no second declaration and no replay event.
    #[doc(hidden)]
    pub fn try_register_native_function_alias(
        &mut self,
        surface_name: &str,
        decl: &FuncDecl,
    ) -> Result<(), SolverError> {
        let arg_sorts: Vec<_> = decl
            .domain
            .iter()
            .map(|sort| self.lower_live_sort(sort))
            .collect();
        let ret_sort = self.lower_live_sort(&decl.range);
        if !self.frontend_function_handle_matches_exact_signature(decl, &arg_sorts, &ret_sort) {
            return Err(SolverError::InvalidArgument {
                operation: "register_native_function_alias",
                message: format!(
                    "function handle '{}' does not match a registered native declaration",
                    decl.name
                ),
            });
        }
        self.executor
            .register_native_global_function_alias(
                surface_name.to_string(),
                decl.core_name.clone(),
                arg_sorts,
                ret_sort,
            )
            .map_err(|error| SolverError::InvalidArgument {
                operation: "register_native_function_alias",
                message: error.to_string(),
            })
    }

    /// Register a caller-visible alias with an exact public sort signature.
    ///
    /// This hidden adapter hook is used by the Z3 5.0.0 parser context to
    /// retain `FiniteSet` identity over a native declaration's lowered engine
    /// signature.
    #[doc(hidden)]
    pub fn try_register_native_public_function_alias(
        &mut self,
        surface_name: &str,
        decl: &FuncDecl,
        public_arg_sorts: Vec<ay_frontend::PublicSort>,
        public_sort: ay_frontend::PublicSort,
    ) -> Result<(), SolverError> {
        let arg_sorts: Option<Vec<_>> = public_arg_sorts
            .iter()
            .map(ay_frontend::PublicSort::engine_sort)
            .collect();
        let ret_sort = public_sort.engine_sort();
        let declaration_matches = arg_sorts.as_ref().is_some_and(|arg_sorts| {
            ret_sort.as_ref().is_some_and(|ret_sort| {
                decl.domain
                    .iter()
                    .map(|sort| self.lower_live_sort(sort))
                    .eq(arg_sorts.iter().cloned())
                    && self.lower_live_sort(&decl.range) == *ret_sort
                    && self
                        .frontend_function_handle_matches_exact_signature(decl, arg_sorts, ret_sort)
            })
        });
        if !declaration_matches {
            return Err(SolverError::InvalidArgument {
                operation: "register_native_public_function_alias",
                message: format!(
                    "function handle '{}' does not match a registered native declaration",
                    decl.name
                ),
            });
        }
        self.executor
            .register_native_global_public_function_alias(
                surface_name.to_string(),
                decl.core_name.clone(),
                public_arg_sorts,
                public_sort,
            )
            .map_err(|error| SolverError::InvalidArgument {
                operation: "register_native_public_function_alias",
                message: error.to_string(),
            })
    }
}
