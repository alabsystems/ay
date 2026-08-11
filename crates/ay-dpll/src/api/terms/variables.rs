// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native variable declarations.

use ay_core::Sort;
use ay_frontend::is_reserved_symbol;

use super::super::types::{NativeReplayEventKind, SolverError, Term};
use super::super::Solver;

// Public convenience wrappers intentionally panic on error. Each has a
// fallible `try_*` counterpart.
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
        let requested_core_sort = self.lower_live_sort(&sort);
        // Looking up the exact native identity through the reverse index keeps
        // repeated declaration O(1); scanning `var_names` (or every overload
        // of a surface name) would make large declaration sets quadratic.
        if let Some(&term_id) = self.var_terms_by_name.get(name) {
            match self.var_sorts.get(&term_id) {
                Some(existing_sort)
                    if existing_sort == &sort
                        && self.terms().sort(term_id) == &requested_core_sort =>
                {
                    return Ok(self.wrap_term(term_id));
                }
                // The verification-consumer `__upgraded` path intentionally replaces an
                // opaque placeholder with its full datatype definition. Both
                // use one core uninterpreted carrier, but this is a deliberately
                // NARROW surface upgrade: `as_term_sort` also collapses distinct
                // Char/Int, finite-domain, type-variable, nested-array, and
                // same-named-but-different-datatype sorts. Accepting every equal
                // core lowering would erase the bounds/schema metadata that the
                // native API must preserve.
                Some(Sort::Uninterpreted(existing_name))
                    if matches!(&sort, Sort::Datatype(datatype) if datatype.name == *existing_name)
                        && self.terms().sort(term_id) == &requested_core_sort =>
                {
                    self.var_sorts.insert(term_id, sort);
                    return Ok(self.wrap_term(term_id));
                }
                // An opaque spelling after the concrete definition is the same
                // placeholder relationship in reverse. Reuse the identity, but
                // NEVER downgrade the stored datatype schema.
                Some(Sort::Datatype(existing_datatype))
                    if matches!(&sort, Sort::Uninterpreted(name) if *name == existing_datatype.name)
                        && self.terms().sort(term_id) == &requested_core_sort =>
                {
                    return Ok(self.wrap_term(term_id));
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

        let term_sort = requested_core_sort;
        // Allocate the term and its frontend metadata as one operation. The
        // public/model/replay key remains `name`, while a map-target spelling
        // (or any reused core spelling) receives a private identity in BOTH the
        // term DAG and `SymbolInfo::internal_name`.
        let term_id = self
            .executor
            .register_native_global_constant(name.to_string(), term_sort.clone());
        self.var_names.insert(term_id, name.to_string());
        self.var_terms_by_name.insert(name.to_string(), term_id);
        self.var_sorts.insert(term_id, sort);
        self.record_native_replay_event(NativeReplayEventKind::DeclareConst {
            name: name.to_string(),
            term: term_id,
            sort: self.terms().sort(term_id).clone(),
        });
        Ok(self.wrap_term(term_id))
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
        let term_sort = self.lower_live_sort(&sort);
        // `identity_name` remains the model/replay key documented by this API,
        // while the frontend may allocate a still-more-private core spelling
        // when that identity collides with a canonical theory operator.
        // Allocation and registration are atomic, so TermData and SymbolInfo
        // cannot disagree about the core identity.
        let term_id = self
            .executor
            .register_native_global_constant(identity_name.to_string(), term_sort.clone());
        // Model extraction is keyed by declaration identity, not display
        // text: two C-API constants may intentionally share a printed name.
        self.var_names.insert(term_id, identity_name.to_string());
        self.var_terms_by_name
            .insert(identity_name.to_string(), term_id);
        self.var_sorts.insert(term_id, sort);
        self.record_native_replay_event(NativeReplayEventKind::DeclareConst {
            name: identity_name.to_string(),
            term: term_id,
            sort: self.terms().sort(term_id).clone(),
        });
        Ok(self.wrap_term(term_id))
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
        let term_sort = self.lower_live_sort(&sort);
        let id = self.terms_mut().mk_fresh_var(prefix, term_sort);
        Ok(self.wrap_term(id))
    }
}
