// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Declare a datatype (algebraic data type).
    ///
    /// This registers the datatype sort and its constructors, selectors, and
    /// testers with the SMT context. Currently AY treats datatypes as
    /// uninterpreted sorts with UF-encoded operations.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{
    ///     DatatypeConstructor, DatatypeField, DatatypeSort, Logic, SolveResult, Solver, Sort,
    /// };
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    ///
    /// // A simple OptionBool datatype: none | some(value: Bool)
    /// let option_bool = DatatypeSort {
    ///     name: "OptionBool".to_string(),
    ///     constructors: vec![
    ///         DatatypeConstructor {
    ///             name: "none".to_string(),
    ///             fields: vec![],
    ///         },
    ///         DatatypeConstructor {
    ///             name: "some".to_string(),
    ///             fields: vec![DatatypeField {
    ///                 name: "value".to_string(),
    ///                 sort: Sort::Bool,
    ///             }],
    ///         },
    ///     ],
    /// };
    /// solver.declare_datatype(&option_bool);
    ///
    /// let x = solver.declare_const("x", Sort::Datatype(option_bool.clone()));
    /// let true_val = solver.bool_const(true);
    /// let some_true = solver.datatype_constructor(&option_bool, "some", &[true_val]);
    /// let eq_term = solver.eq(x, some_true);
    /// solver.assert_term(eq_term);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Note
    ///
    /// Call this once per datatype before using `datatype_constructor`,
    /// `datatype_selector`, or `datatype_tester` methods.
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to declare the datatype.
    /// Use [`try_declare_datatype`] for a fallible version that returns an error instead.
    ///
    /// [`try_declare_datatype`]: Solver::try_declare_datatype
    pub fn declare_datatype(&mut self, dt: &DatatypeSort) {
        self.try_declare_datatype(dt)
            .unwrap_or_else(|e| panic!("Failed to declare datatype '{}': {}", dt.name, e));
    }

    /// Try to declare a user-defined datatype (algebraic data type).
    ///
    /// Fallible version of `declare_datatype`. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to declare the datatype.
    ///
    /// `declare_datatype`: Solver::declare_datatype
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_datatype(&mut self, dt: &DatatypeSort) -> Result<(), SolverError> {
        use ay_frontend::command::{ConstructorDec, DatatypeDec, SelectorDec};

        let constructors: Vec<ConstructorDec> = dt
            .constructors
            .iter()
            .map(|ctor| ConstructorDec {
                name: ctor.name.clone(),
                selectors: ctor
                    .fields
                    .iter()
                    .map(|field| SelectorDec {
                        name: field.name.clone(),
                        sort: field.sort.to_command_sort(),
                    })
                    .collect(),
            })
            .collect();

        let datatype_dec = DatatypeDec {
            constructors,
            type_params: Vec::new(),
        };
        let cmd = Command::DeclareDatatype(dt.name.clone(), datatype_dec);
        self.executor.execute_native_global_declaration(&cmd)?;
        self.record_native_replay_event(NativeReplayEventKind::DeclareDatatype {
            datatype: dt.clone(),
        });
        Ok(())
    }

    /// Build a datatype constructor application term.
    ///
    /// Creates a term representing a constructor application. For nullary constructors
    /// (no arguments), this creates a constant term. For constructors with fields,
    /// this creates a function application.
    ///
    /// # Arguments
    ///
    /// * `dt` - The datatype definition containing this constructor.
    /// * `ctor` - The constructor name (must be declared for this datatype via `declare_datatype`).
    /// * `args` - Arguments matching the constructor's field types, in order.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{
    ///     DatatypeConstructor, DatatypeField, DatatypeSort, Logic, SolveResult, Solver, Sort,
    /// };
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    ///
    /// // Define Option<Int> = none | some(value: Int)
    /// let option_int = DatatypeSort {
    ///     name: "OptionInt".to_string(),
    ///     constructors: vec![
    ///         DatatypeConstructor { name: "none".to_string(), fields: vec![] },
    ///         DatatypeConstructor {
    ///             name: "some".to_string(),
    ///             fields: vec![DatatypeField { name: "value".to_string(), sort: Sort::Int }],
    ///         },
    ///     ],
    /// };
    /// solver.declare_datatype(&option_int);
    ///
    /// // Create none (nullary)
    /// let none = solver.datatype_constructor(&option_int, "none", &[]);
    ///
    /// // Create some(42) (unary with Int argument)
    /// let forty_two = solver.int_const(42);
    /// let some_42 = solver.datatype_constructor(&option_int, "some", &[forty_two]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The datatype has not been declared (call `declare_datatype` first).
    /// - The constructor is not declared (not registered in the symbol table).
    /// - The constructor does not construct the given datatype.
    /// - The number of arguments does not match the constructor's arity.
    /// - Any argument sort does not match the constructor's argument sorts.
    ///
    /// Use [`Self::try_datatype_constructor`] for a fallible version.
    pub fn datatype_constructor(&mut self, dt: &DatatypeSort, ctor: &str, args: &[Term]) -> Term {
        self.try_datatype_constructor(dt, ctor, args)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Build a datatype selector (field access) term.
    ///
    /// Selectors extract field values from datatype constructor applications.
    /// The selector name must match a field declared in the datatype definition.
    ///
    /// # Arguments
    ///
    /// * `selector` - The selector (field) name from the datatype definition.
    /// * `expr` - A term of the datatype sort to extract from.
    /// * `result_sort` - The sort of the field being accessed.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{
    ///     DatatypeConstructor, DatatypeField, DatatypeSort, Logic, SolveResult, Solver, Sort,
    /// };
    ///
    /// let mut solver = Solver::new(Logic::QfUflia);
    ///
    /// // Define Pair = pair(fst: Int, snd: Int)
    /// let pair_dt = DatatypeSort {
    ///     name: "Pair".to_string(),
    ///     constructors: vec![DatatypeConstructor {
    ///         name: "pair".to_string(),
    ///         fields: vec![
    ///             DatatypeField { name: "fst".to_string(), sort: Sort::Int },
    ///             DatatypeField { name: "snd".to_string(), sort: Sort::Int },
    ///         ],
    ///     }],
    /// };
    /// solver.declare_datatype(&pair_dt);
    ///
    /// // Create pair(1, 2)
    /// let one = solver.int_const(1);
    /// let two = solver.int_const(2);
    /// let p = solver.datatype_constructor(&pair_dt, "pair", &[one, two]);
    ///
    /// // Extract fst(p) - should equal 1
    /// let fst_p = solver.datatype_selector("fst", p, Sort::Int);
    /// let eq = solver.eq(fst_p, one);
    /// solver.assert_term(eq);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The selector is not declared (not registered in the symbol table).
    /// - The `result_sort` does not match the selector's declared return sort.
    /// - The `expr` sort does not match the selector's argument sort.
    ///
    /// Use [`Self::try_datatype_selector`] for a fallible version.
    pub fn datatype_selector(&mut self, selector: &str, expr: Term, result_sort: Sort) -> Term {
        self.try_datatype_selector(selector, expr, result_sort)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Build a datatype tester (is-Constructor) term.
    ///
    /// Testers check if a datatype value was constructed with a specific constructor.
    /// Returns a boolean term that is true iff the expression was built with that
    /// constructor.
    ///
    /// # Arguments
    ///
    /// * `ctor` - The constructor name to test for.
    /// * `expr` - A term of the datatype sort to test.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{
    ///     DatatypeConstructor, DatatypeField, DatatypeSort, Logic, SolveResult, Solver, Sort,
    /// };
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    ///
    /// // Define Option<Bool> = none | some(value: Bool)
    /// let option_bool = DatatypeSort {
    ///     name: "OptionBool".to_string(),
    ///     constructors: vec![
    ///         DatatypeConstructor { name: "none".to_string(), fields: vec![] },
    ///         DatatypeConstructor {
    ///             name: "some".to_string(),
    ///             fields: vec![DatatypeField { name: "value".to_string(), sort: Sort::Bool }],
    ///         },
    ///     ],
    /// };
    /// solver.declare_datatype(&option_bool);
    ///
    /// // Create some(true)
    /// let t = solver.bool_const(true);
    /// let some_true = solver.datatype_constructor(&option_bool, "some", &[t]);
    ///
    /// // Test is-some(some_true) - should be true
    /// let is_some = solver.datatype_tester("some", some_true);
    /// solver.assert_term(is_some);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The tester (is-ctor) is not declared in the symbol table.
    /// - The `expr` sort does not match the tester's argument sort.
    ///
    /// Use [`Self::try_datatype_tester`] for a fallible version.
    pub fn datatype_tester(&mut self, ctor: &str, expr: Term) -> Term {
        self.try_datatype_tester(ctor, expr)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to build a datatype constructor application.
    ///
    /// Fallible version of [`datatype_constructor`]. Returns an error instead
    /// of panicking on invalid input.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - The datatype has not been declared (call `declare_datatype` first)
    /// - The constructor is not declared (not registered in the symbol table)
    /// - The constructor does not construct the given datatype
    /// - The number of arguments does not match the constructor's arity
    ///
    /// Returns [`SolverError::SortMismatch`] if any argument sort does not match the
    /// corresponding constructor argument sort.
    ///
    /// [`datatype_constructor`]: Solver::datatype_constructor
    /// `declare_datatype`: Solver::declare_datatype
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_datatype_constructor(
        &mut self,
        dt: &DatatypeSort,
        ctor: &str,
        args: &[Term],
    ) -> Result<Term, SolverError> {
        let dt_sort = self.lower_live_sort(&Sort::Datatype(dt.clone()));
        let arg_ids: Vec<TermId> = args
            .iter()
            .map(|term| self.resolve_term("datatype_constructor", *term))
            .collect::<Result<_, _>>()?;
        let ctor_arg_sorts: Vec<Sort> = dt
            .constructors
            .iter()
            .find(|candidate| candidate.name == ctor)
            .ok_or_else(|| SolverError::InvalidArgument {
                operation: "datatype_constructor",
                message: format!("constructor '{ctor}' is not part of datatype '{}'", dt.name),
            })?
            .fields
            .iter()
            .map(|field| self.lower_live_sort(&field.sort))
            .collect();
        let (ctor_term, ctor_sort, ctor_identity) = {
            let ctx = self.executor.context();

            let is_live_datatype = matches!(&dt_sort, Sort::Uninterpreted(identity)
                if ctx.is_live_datatype_carrier(identity));
            if !is_live_datatype {
                return Err(SolverError::InvalidArgument {
                    operation: "datatype_constructor",
                    message: format!(
                        "datatype '{}' not declared. Call declare_datatype(...) before using datatype_constructor",
                        dt.name
                    ),
                });
            }

            let symbol_info = ctx
                .symbol_info_with_signature(ctor, &ctor_arg_sorts, &dt_sort)
                .ok_or_else(|| SolverError::InvalidArgument {
                    operation: "datatype_constructor",
                    message: format!(
                        "constructor '{}' not declared for datatype '{}'. Ensure the exact datatype has been declared with declare_datatype",
                        ctor, dt.name
                    ),
                })?;

            (
                symbol_info.term,
                symbol_info.sort.clone(),
                ctx.symbol_identity_name(ctor, symbol_info).to_string(),
            )
        };

        if ctor_sort != dt_sort {
            return Err(SolverError::InvalidArgument {
                operation: "datatype_constructor",
                message: format!(
                    "constructor '{}' does not construct datatype '{}': declared return sort is {:?}",
                    ctor, dt.name, ctor_sort
                ),
            });
        }

        if args.len() != ctor_arg_sorts.len() {
            return Err(SolverError::InvalidArgument {
                operation: "datatype_constructor",
                message: format!(
                    "constructor '{}' expects {} argument(s), got {}",
                    ctor,
                    ctor_arg_sorts.len(),
                    args.len()
                ),
            });
        }

        for (arg, expected_sort) in arg_ids.iter().zip(ctor_arg_sorts.iter()) {
            let arg_sort = self.terms().sort(*arg).clone();
            if &arg_sort != expected_sort {
                return Err(SolverError::SortMismatch {
                    operation: "datatype_constructor",
                    expected: "argument sorts matching constructor signature",
                    got: vec![arg_sort],
                });
            }
        }

        if args.is_empty() {
            if let Some(term) = ctor_term {
                Ok(self.wrap_term(term))
            } else {
                let term = self.terms_mut().mk_var(&ctor_identity, dt_sort);
                Ok(self.wrap_term(term))
            }
        } else {
            let term = self
                .terms_mut()
                .mk_app(Symbol::Named(ctor_identity), arg_ids, dt_sort);
            Ok(self.wrap_term(term))
        }
    }

    /// Report whether `name` is a registered NULLARY datatype constructor
    /// (an enum value, or any other 0-field constructor such as `nil`).
    ///
    /// A nullary constructor constant is a fully-interpreted, pairwise-distinct
    /// value — it is NEVER an unconstrained leaf. Internally it is stored as a
    /// `Var` at the datatype's (uninterpreted-encoded) sort, which makes it
    /// indistinguishable, by sort alone, from a genuine uninterpreted-sort
    /// constant. Callers that complete/default unconstrained leaves (the FFI
    /// `Z3_model_eval` snapshot's `model_completion` path) use this to leave a
    /// constructor constant in place instead of collapsing distinct enum values
    /// to one shared universe element, and to fold `=`/`distinct` over
    /// constructor constants by constructor-name identity.
    #[must_use]
    pub fn is_nullary_constructor(&self, name: &str) -> bool {
        let ctx = self.executor.context();
        ctx.symbols_iter()
            .filter(|(surface, _)| surface.as_str() == name)
            .any(|(surface, info)| {
                let identity = ctx.symbol_identity_name(surface, info);
                ctx.is_constructor(identity).is_some()
                    && ctx
                        .constructor_selectors(identity)
                        .is_none_or(|sels| sels.is_empty())
            })
    }

    /// Try to build a datatype selector (field access) term.
    ///
    /// Fallible version of [`datatype_selector`]. Returns an error instead
    /// of panicking on invalid input.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - The selector is not declared (not registered in the symbol table)
    /// - The selector is not a unary function
    /// - The result_sort does not match the selector's declared return sort
    ///
    /// [`datatype_selector`]: Solver::datatype_selector
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_datatype_selector(
        &mut self,
        selector: &str,
        expr: Term,
        result_sort: Sort,
    ) -> Result<Term, SolverError> {
        let expected_sort = self.lower_live_sort(&result_sort);
        let expr = self.resolve_term("datatype_selector", expr)?;
        let expr_sort = self.terms().sort(expr).clone();
        let (symbol_info, selector_identity) = {
            let ctx = self.executor.context();
            let info = if let Some(info) = ctx.symbol_info_with_signature(
                selector,
                std::slice::from_ref(&expr_sort),
                &expected_sort,
            ) {
                info
            } else {
                let candidates: Vec<_> = ctx
                    .symbols_iter()
                    .filter(|(surface, info)| {
                        surface.as_str() == selector
                            && info.declaration_kind()
                                == ay_frontend::DeclarationKind::DatatypeSelector
                    })
                    .map(|(_, info)| info)
                    .collect();
                if candidates
                    .iter()
                    .any(|info| info.arg_sorts == std::slice::from_ref(&expr_sort))
                {
                    return Err(SolverError::SortMismatch {
                        operation: "datatype_selector",
                        expected: "result_sort matching selector's return sort",
                        got: vec![expected_sort],
                    });
                }
                if candidates.iter().any(|info| info.sort == expected_sort) {
                    return Err(SolverError::SortMismatch {
                        operation: "datatype_selector",
                        expected: "expr sort matching selector's argument sort",
                        got: vec![expr_sort],
                    });
                }
                return Err(SolverError::InvalidArgument {
                    operation: "datatype_selector",
                    message: format!(
                        "selector '{selector}' is not declared with the requested argument and result sorts"
                    ),
                });
            };
            (
                info.clone(),
                ctx.symbol_identity_name(selector, info).to_string(),
            )
        };

        if symbol_info.arg_sorts.len() != 1 {
            return Err(SolverError::InvalidArgument {
                operation: "datatype_selector",
                message: format!(
                    "selector '{}' expects 1 argument, but is declared with {} argument(s)",
                    selector,
                    symbol_info.arg_sorts.len()
                ),
            });
        }

        let declared_sort = &symbol_info.sort;
        if *declared_sort != expected_sort {
            return Err(SolverError::SortMismatch {
                operation: "datatype_selector",
                expected: "result_sort matching selector's return sort",
                got: vec![expected_sort],
            });
        }

        if expr_sort != symbol_info.arg_sorts[0] {
            return Err(SolverError::SortMismatch {
                operation: "datatype_selector",
                expected: "expr sort matching selector's argument sort",
                got: vec![expr_sort],
            });
        }

        let term =
            self.terms_mut()
                .mk_app(Symbol::Named(selector_identity), vec![expr], expected_sort);
        Ok(self.wrap_term(term))
    }

    /// Try to build a datatype tester (is-Constructor) term.
    ///
    /// Fallible version of [`datatype_tester`]. Returns an error instead
    /// of panicking on invalid input.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - The tester (is-ctor) is not declared in the symbol table
    /// - The tester is not a unary Bool-returning function
    ///
    /// [`datatype_tester`]: Solver::datatype_tester
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_datatype_tester(&mut self, ctor: &str, expr: Term) -> Result<Term, SolverError> {
        let tester_name = format!("is-{ctor}");
        let expr = self.resolve_term("datatype_tester", expr)?;
        let expr_sort = self.terms().sort(expr).clone();
        let (symbol_info, tester_identity) = {
            let ctx = self.executor.context();
            let info = if let Some(info) = ctx.symbol_info_with_signature(
                &tester_name,
                std::slice::from_ref(&expr_sort),
                &Sort::Bool,
            ) {
                info
            } else if ctx.symbols_iter().any(|(surface, info)| {
                surface == &tester_name
                    && info.declaration_kind() == ay_frontend::DeclarationKind::DatatypeTester
            }) {
                return Err(SolverError::SortMismatch {
                    operation: "datatype_tester",
                    expected: "expr sort matching tester's argument sort",
                    got: vec![expr_sort],
                });
            } else {
                return Err(SolverError::InvalidArgument {
                    operation: "datatype_tester",
                    message: format!(
                        "tester '{tester_name}' is not declared for the supplied datatype sort"
                    ),
                });
            };
            (
                info.clone(),
                ctx.symbol_identity_name(&tester_name, info).to_string(),
            )
        };

        if symbol_info.arg_sorts.len() != 1 {
            return Err(SolverError::InvalidArgument {
                operation: "datatype_tester",
                message: format!(
                    "tester '{}' expects 1 argument, but is declared with {} argument(s)",
                    tester_name,
                    symbol_info.arg_sorts.len()
                ),
            });
        }

        if symbol_info.sort != Sort::Bool {
            return Err(SolverError::InvalidArgument {
                operation: "datatype_tester",
                message: format!(
                    "tester '{}' should return Bool, but returns {:?}",
                    tester_name, symbol_info.sort
                ),
            });
        }

        if expr_sort != symbol_info.arg_sorts[0] {
            return Err(SolverError::SortMismatch {
                operation: "datatype_tester",
                expected: "expr sort matching tester's argument sort",
                got: vec![expr_sort],
            });
        }

        let term = self
            .terms_mut()
            .mk_app(Symbol::Named(tester_identity), vec![expr], Sort::Bool);
        Ok(self.wrap_term(term))
    }
}
