// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term construction for AY Solver API.
//!
//! Variable declaration, datatypes, arrays, constants, booleans,
//! quantifiers, comparisons, arithmetic, and sort conversions.

mod arithmetic;
mod arrays;
mod boolean;
mod comparisons;
mod compat;
mod constants;
mod conversions;
mod datatypes;
mod quantifiers;

#[allow(deprecated)]
pub use compat::AstKind;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use ay_core::term::{Symbol, TermData};
use ay_core::{DatatypeSort, Sort, TermId, TermStore};
use ay_frontend::{is_reserved_symbol, Command};

use super::types::{FuncDecl, NativeReplayEventKind, SolverError, SortExt, Term};
use super::Solver;

// All public methods in this module are convenience wrappers that intentionally
// panic on error. Each has a fallible `try_*` counterpart.
#[allow(clippy::panic, deprecated)]
impl Solver {
    // =========================================================================
    // Variable declaration
    // =========================================================================

    /// Declare a constant (0-arity function) with the given name and sort.
    ///
    /// The `name` is used for model extraction (see [`Solver::get_model`]).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ay_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let y = solver.declare_const("y", Sort::Int);
    /// # let _ = (x, y);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `name` is already bound to a function or a different constant
    /// sort. Repeating the exact declaration is idempotent. The sole surface
    /// refinement accepted is a same-named `Uninterpreted("T")` placeholder to
    /// a concrete `Datatype` named `T`; the reverse spelling reuses the term but
    /// retains its more informative datatype metadata.
    pub fn declare_const(&mut self, name: &str, sort: Sort) -> Term {
        self.try_declare_const(name, sort)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Fallible variant of [`declare_const`](Self::declare_const).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] for reserved names, declaration
    /// collisions, or an inconsistent repeated declaration.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_const(&mut self, name: &str, sort: Sort) -> Result<Term, SolverError> {
        if is_reserved_symbol(name) {
            return Err(SolverError::InvalidArgument {
                operation: "declare_const",
                message: format!("symbol name '{name}' is reserved"),
            });
        }
        // Looking up the exact native identity through the reverse index keeps
        // repeated declaration O(1); scanning `var_names` (or every overload
        // of a surface name) would make large declaration sets quadratic.
        if let Some(&term_id) = self.var_terms_by_name.get(name) {
            match self.var_sorts.get(&term_id) {
                Some(existing_sort) if existing_sort == &sort => return Ok(Term(term_id)),
                // The verification-consumer `__upgraded` path intentionally replaces an
                // opaque placeholder with its full datatype definition. Both
                // use one core uninterpreted carrier, but this is a deliberately
                // NARROW surface upgrade: `as_term_sort` also collapses distinct
                // Char/Int, finite-domain, type-variable, nested-array, and
                // same-named-but-different-datatype sorts. Accepting every equal
                // core lowering would erase the bounds/schema metadata that the
                // native API must preserve.
                Some(Sort::Uninterpreted(existing_name)) if matches!(&sort, Sort::Datatype(datatype) if datatype.name == *existing_name) =>
                {
                    self.var_sorts.insert(term_id, sort);
                    return Ok(Term(term_id));
                }
                // An opaque spelling after the concrete definition is the same
                // placeholder relationship in reverse. Reuse the identity, but
                // NEVER downgrade the stored datatype schema.
                Some(Sort::Datatype(existing_datatype)) if matches!(&sort, Sort::Uninterpreted(name) if *name == existing_datatype.name) =>
                {
                    return Ok(Term(term_id));
                }
                Some(existing_sort) => {
                    return Err(SolverError::InvalidArgument {
                        operation: "declare_const",
                        message: format!(
                            "constant '{name}' is already declared with sort {existing_sort}, not {sort}"
                        ),
                    });
                }
                None => {
                    return Err(SolverError::InvalidArgument {
                        operation: "declare_const",
                        message: format!("native constant '{name}' is missing its sort metadata"),
                    });
                }
            }
        }
        if self.executor.context().has_symbol_binding(name) {
            return Err(SolverError::InvalidArgument {
                operation: "declare_const",
                message: format!("symbol '{name}' is already bound to a different declaration"),
            });
        }

        let term_sort = sort.as_term_sort();
        // A compatibility adapter can retain this display name under a
        // different private declaration identity. `mk_var` would silently
        // return that adapter term (even at another sort), so a genuinely new
        // native declaration always gets its own core identity.
        let term_id = self.terms_mut().mk_fresh_named_var(name, term_sort.clone());
        self.var_names.insert(term_id, name.to_string());
        self.var_terms_by_name.insert(name.to_string(), term_id);
        self.var_sorts.insert(term_id, sort);
        // Register the symbol in the context so it appears in models. Native
        // declarations are context-global even when created inside push/pop.
        self.executor
            .register_native_global_symbol(name.to_string(), term_id, term_sort.clone());
        self.record_native_replay_event(NativeReplayEventKind::DeclareConst {
            name: name.to_string(),
            term: term_id,
            sort: self.terms().sort(term_id).clone(),
        });
        Ok(Term(term_id))
    }

    /// Declare a constant with a fresh term identity while retaining a
    /// caller-visible display name.
    ///
    /// `identity_name` is the declaration key used by model bookkeeping and
    /// replay; it must be unique in this solver.  This is primarily for API
    /// adapters such as the Z3 C surface, where declarations may share a
    /// printed name while differing by symbol kind or sort.  The ordinary
    /// [`declare_const`](Self::declare_const) intentionally keeps its
    /// name-interning behavior.
    ///
    /// # Panics
    ///
    /// Panics if `identity_name` is already registered in this solver.
    pub fn declare_const_with_fresh_identity(
        &mut self,
        _display_name: &str,
        identity_name: &str,
        sort: Sort,
    ) -> Term {
        self.try_declare_const_with_fresh_identity(_display_name, identity_name, sort)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Fallible variant of
    /// [`declare_const_with_fresh_identity`](Self::declare_const_with_fresh_identity).
    ///
    /// The private core identity is security-relevant; the adapter-owned
    /// display name may use any spelling because it is not stored in the core
    /// term DAG.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_const_with_fresh_identity(
        &mut self,
        _display_name: &str,
        identity_name: &str,
        sort: Sort,
    ) -> Result<Term, SolverError> {
        if is_reserved_symbol(identity_name) {
            return Err(SolverError::InvalidArgument {
                operation: "declare_const_with_fresh_identity",
                message: format!("symbol identity '{identity_name}' is reserved"),
            });
        }
        if self.var_terms_by_name.contains_key(identity_name)
            || self.executor.context().has_symbol_binding(identity_name)
        {
            return Err(SolverError::InvalidArgument {
                operation: "declare_const_with_fresh_identity",
                message: format!("native constant identity '{identity_name}' is already in use"),
            });
        }
        let term_sort = sort.as_term_sort();
        // Keep the private declaration identity in the core DAG.  Datatype
        // constructors and several theory paths are keyed by core symbol text;
        // storing `display_name` here would let an adapter constant named like
        // a constructor inherit constructor semantics.  API adapters retain
        // and project the caller-visible spelling from their own declaration
        // metadata (the Z3 compatibility layer does this for AST/model text).
        let term_id = self
            .terms_mut()
            .mk_fresh_named_var(identity_name, term_sort.clone());
        // Model extraction is keyed by declaration identity, not display
        // text: two C-API constants may intentionally share a printed name.
        self.var_names.insert(term_id, identity_name.to_string());
        self.var_terms_by_name
            .insert(identity_name.to_string(), term_id);
        self.var_sorts.insert(term_id, sort);
        self.executor.register_native_global_symbol(
            identity_name.to_string(),
            term_id,
            term_sort.clone(),
        );
        self.record_native_replay_event(NativeReplayEventKind::DeclareConst {
            name: identity_name.to_string(),
            term: term_id,
            sort: self.terms().sort(term_id).clone(),
        });
        Ok(Term(term_id))
    }

    /// Declare an integer constant (0-arity) variable.
    pub fn int_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Int)
    }

    /// Declare a real constant (0-arity) variable.
    pub fn real_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Real)
    }

    /// Declare a boolean constant (0-arity) variable.
    pub fn bool_var(&mut self, name: &str) -> Term {
        self.declare_const(name, Sort::Bool)
    }

    /// Declare a bitvector constant (0-arity) variable with the specified width.
    pub fn bv_var(&mut self, name: &str, width: u32) -> Term {
        self.declare_const(name, Sort::bitvec(width))
    }

    /// Create a fresh variable (guaranteed unique) that is *not* registered for model extraction.
    ///
    /// This is primarily useful for constructing quantified formulas, where bound variables
    /// should not appear as top-level symbols in models.
    pub fn fresh_var(&mut self, prefix: &str, sort: Sort) -> Term {
        self.try_fresh_var(prefix, sort)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Fallible variant of [`fresh_var`](Self::fresh_var).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fresh_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        // `mk_fresh_var` emits `<prefix>_<id>`. Check that generated namespace,
        // rather than the bare prefix, so ordinary prefixes such as `select`
        // remain legal while `__ay` cannot mint an internal-looking identity.
        if is_reserved_symbol(&format!("{prefix}_")) {
            return Err(SolverError::InvalidArgument {
                operation: "fresh_var",
                message: format!("fresh-variable prefix '{prefix}' enters a reserved namespace"),
            });
        }
        let term_sort = sort.as_term_sort();
        Ok(Term(self.terms_mut().mk_fresh_var(prefix, term_sort)))
    }

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
        if let Some((existing_domain, existing_range)) = self.native_fun_signatures.get(name) {
            if existing_domain == domain && existing_range == &range {
                return Ok(FuncDecl {
                    name: name.to_string(),
                    domain: domain.to_vec(),
                    range,
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
            let term_domain: Vec<Sort> = domain.iter().map(Sort::as_term_sort).collect();
            let term_range = range.as_term_sort();
            let ctx = self.executor.context();
            if ctx.is_datatype_member_name(name)
                && ctx.has_symbol_with_signature(name, &term_domain, &term_range)
            {
                return Ok(FuncDecl {
                    name: name.to_string(),
                    domain: domain.to_vec(),
                    range,
                });
            }
        }

        // The native API constructs core applications directly from a
        // `FuncDecl`; unlike the SMT-LIB elaborator, it has no expected-sort
        // context in which to resolve an overloaded surface name.  Allowing a
        // second declaration (or a declaration that shadows an inline
        // definition) would therefore collapse distinct functions onto the
        // same `Symbol::Named` identity.  Fail closed until `FuncDecl` carries
        // an opaque declaration identity of its own.
        self.reject_reused_native_function_name(name, "declare_fun")?;

        // Build the DeclareFun command to register the function with the SMT context
        let domain_sorts: Vec<_> = domain.iter().map(SortExt::to_command_sort).collect();
        let range_sort = range.to_command_sort();
        let cmd = Command::DeclareFun(name.to_string(), domain_sorts, range_sort);

        // Execute the command to register the function
        // This makes it appear in ctx.symbol_iter() for model printing
        self.executor.execute_native_global_declaration(&cmd)?;
        self.native_fun_signatures
            .insert(name.to_string(), (domain.to_vec(), range.clone()));
        self.record_native_replay_event(NativeReplayEventKind::DeclareFun {
            name: name.to_string(),
            domain: domain.to_vec(),
            range: range.clone(),
        });

        Ok(FuncDecl {
            name: name.to_string(),
            domain: domain.to_vec(),
            range,
        })
    }

    /// Register a caller-visible SMT-LIB name for an already-declared native
    /// function whose core identity is `decl.name()`.
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
        let arg_sorts = decl.domain.iter().map(Sort::as_term_sort).collect();
        let ret_sort = decl.range.as_term_sort();
        let declaration_matches = self
            .executor
            .context()
            .symbol_info_by_identity(&decl.name)
            .is_some_and(|info| info.arg_sorts == arg_sorts && info.sort == ret_sort);
        if !declaration_matches {
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
                decl.name.clone(),
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
        self.executor
            .register_native_global_public_function_alias(
                surface_name.to_string(),
                decl.name.clone(),
                public_arg_sorts,
                public_sort,
            )
            .map_err(|error| SolverError::InvalidArgument {
                operation: "register_native_public_function_alias",
                message: error.to_string(),
            })
    }

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
            let term_sort = param_sort.as_term_sort();
            let var_id = self.terms_mut().mk_fresh_var(param_name, term_sort);
            let var_name = match self.terms().get(var_id) {
                TermData::Var(fresh_name, _) => fresh_name.clone(),
                _ => param_name.to_string(),
            };
            param_terms.push(Term(var_id));
            param_entries.push((var_name, var_id));
        }

        // Build the body using the parameter variables
        let body = body_fn(self, &param_terms)?;

        // The body builder has mutable access to the solver and may itself
        // introduce declarations. Re-check before installing this definition
        // so a closure cannot create a same-name alias after the entry check.
        self.reject_reused_native_function_name(name, "define_fun")?;

        // Verify the body sort matches the declared return sort
        let body_sort = self.terms().sort(body.0).clone();
        let expected_sort = return_sort.as_term_sort();
        if body_sort != expected_sort {
            return Err(SolverError::SortMismatch {
                operation: "define_fun",
                expected: "matching return sort",
                got: vec![body_sort],
            });
        }

        // Store the definition for inline expansion during try_apply
        let domain: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        self.defined_funs.insert(
            name.to_string(),
            super::DefinedFun {
                params: param_entries,
                body: body.0,
                return_sort: expected_sort,
                assertion_derived: false,
            },
        );
        self.executor.invalidate_for_native_api_mutation();

        Ok(FuncDecl {
            name: name.to_string(),
            domain,
            range: return_sort,
        })
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

        let mut param_entries = Vec::with_capacity(params.len());
        let mut domain = Vec::with_capacity(params.len());

        for &(param_name, param) in params {
            let sort = self.terms().sort(param.0).clone();
            let var_name = match self.terms().get(param.0) {
                TermData::Var(fresh_name, _) => fresh_name.clone(),
                _ => {
                    return Err(SolverError::InvalidArgument {
                        operation: "define_fun",
                        message: format!("parameter '{param_name}' must be a variable term"),
                    });
                }
            };
            param_entries.push((var_name, param.0));
            domain.push(sort);
        }

        let body_sort = self.terms().sort(body.0).clone();
        let expected_sort = return_sort.as_term_sort();
        if body_sort != expected_sort {
            return Err(SolverError::SortMismatch {
                operation: "define_fun",
                expected: "matching return sort",
                got: vec![body_sort],
            });
        }

        self.defined_funs.insert(
            name.to_string(),
            super::DefinedFun {
                params: param_entries,
                body: body.0,
                return_sort: expected_sort,
                assertion_derived: false,
            },
        );
        self.executor.invalidate_for_native_api_mutation();

        Ok(FuncDecl {
            name: name.to_string(),
            domain,
            range: return_sort,
        })
    }

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

        for (arg, expected_sort) in args.iter().zip(func.domain.iter()) {
            let actual_sort = self.terms().sort(arg.0).clone();
            let expected_core = expected_sort.as_term_sort();
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
            let signature_matches = def.params.len() == func.domain.len()
                && def
                    .params
                    .iter()
                    .zip(func.domain.iter())
                    .all(|((_, param), expected)| {
                        self.terms().sort(*param) == &expected.as_term_sort()
                    })
                && def.return_sort == func.range.as_term_sort();
            if !signature_matches {
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
                .zip(args.iter())
                .map(|((_, param), arg)| (*param, arg.0))
                .collect();
            return Ok(Term(self.substitute_defined_fun_body(def.body, &subst)));
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
        // A USER function named `is_int` builds `App(Named("is_int"), ..)` —
        // byte-identical to the builtin integrality predicate the `is_int`
        // quantifier eliminator (ay-dpll::qe::isint) matches structurally. The
        // C-API / programmatic path (`Z3_mk_app` over a user `Z3_mk_func_decl`)
        // bypasses the SMT-LIB elaborator's shadow marking, so mark the store
        // HERE too: applying integrality (critical-residue) reasoning to a free
        // predicate fabricates its semantics — a confirmed wrong-UNSAT class
        // (`ForAll([x], is_int(x))` over the UF decided `unsat` where z3
        // exhibits the model `is_int ≡ λx.true`). The genuine builtin is created
        // via `Solver::is_int` (`mk_is_int`), never through this UF-apply path,
        // so this cannot mis-fire on the real builtin. (#isint-shadow)
        if func.name == "is_int" {
            self.terms_mut().mark_is_int_shadowed();
        }
        let arg_ids: Vec<_> = args.iter().map(|t| t.0).collect();
        let result_sort = func.range.as_term_sort();
        Ok(Term(self.terms_mut().mk_app(
            Symbol::Named(func.name.clone()),
            arg_ids,
            result_sort,
        )))
    }

    fn reject_reused_native_function_name(
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
        if let Some((domain, range)) = self.native_fun_signatures.get(&func.name) {
            return native_signature_accepts_instance(domain, range, &func.domain, &func.range);
        }

        // Datatype operation handles are adopted by `try_declare_fun` without
        // recording a second native declaration. Preserve that exact,
        // registered member contract while rejecting every missing user UF.
        let term_domain: Vec<Sort> = func.domain.iter().map(Sort::as_term_sort).collect();
        let term_range = func.range.as_term_sort();
        let ctx = self.executor.context();
        ctx.is_datatype_member_name(&func.name)
            && ctx.has_symbol_with_signature(&func.name, &term_domain, &term_range)
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
