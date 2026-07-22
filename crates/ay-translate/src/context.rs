// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Translation context holding solver and variable mappings.
//!
//! Three-layer architecture:
//! - [`TranslationState`]: Owns variable/function caches (no solver dependency)
//! - [`TranslationSession`]: Borrows solver + state for a translation pass
//! - [`TranslationContext`]: Compatibility wrapper that owns both

use std::borrow::Borrow;
use std::hash::Hash;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_dpll::api::{FuncDecl, Logic, Solver, SolverError, Sort, Term, VerifiedSolveResult};

use crate::ops::expect_result;

/// Reusable translation state independent of solver lifetime.
///
/// Owns the variable cache, function declaration cache, and fresh name counter.
/// Can be paired with different solver instances across incremental sessions.
pub struct TranslationState<V: Eq + Hash> {
    vars: HashMap<V, Term>,
    declared_funcs: HashMap<String, FuncDecl>,
    fresh_counter: u32,
}

impl<V: Eq + Hash> TranslationState<V> {
    /// Create empty translation state.
    pub fn new() -> Self {
        Self {
            vars: HashMap::default(),
            declared_funcs: HashMap::default(),
            fresh_counter: 0,
        }
    }

    /// Get the number of declared variables.
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Check if a variable exists.
    pub fn has_var<Q>(&self, key: &Q) -> bool
    where
        V: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.vars.contains_key(key)
    }

    /// Get a variable if it exists.
    pub fn get_var<Q>(&self, key: &Q) -> Option<Term>
    where
        V: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.vars.get(key).copied()
    }

    /// Get the number of declared functions.
    pub fn func_count(&self) -> usize {
        self.declared_funcs.len()
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        self.declared_funcs.get(name)
    }
}

impl<V: Eq + Hash> Default for TranslationState<V> {
    fn default() -> Self {
        Self::new()
    }
}

/// Minimal capability surface shared by owning and borrowed translators.
pub trait TranslationHost<V: Eq + Hash> {
    /// Access the underlying solver.
    fn solver(&mut self) -> &mut Solver;

    /// Declare or retrieve a function by name.
    fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl;

    /// Cache a function declaration or definition by name.
    ///
    /// Custom hosts that do not keep a function cache may use the default
    /// no-op implementation. Hosts backed by [`TranslationState`] override it
    /// so later expression translation can resolve `FuncApp` nodes by name.
    fn cache_fun(&mut self, _name: String, _func: FuncDecl) {}

    /// Define a non-recursive function from already-translated parameter and
    /// body terms, then cache the resulting function handle.
    fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        let func = self
            .solver()
            .try_define_fun_body(name, params, range, body)?;
        self.cache_fun(name.to_string(), func.clone());
        Ok(func)
    }
}

/// Extended capability surface for recursive term translation.
///
/// Provides variable management operations needed by `TermTranslator`
/// implementations. Extends `TranslationHost<V>` with variable declaration,
/// lookup, and fresh variable generation.
pub trait TranslationTermHost<V: Eq + Hash>: TranslationHost<V> {
    /// Declare or retrieve a variable by key.
    fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term;

    /// Get a previously declared variable by key.
    fn get_var(&self, key: &V) -> Option<Term>;

    /// Create a fresh declared constant with a unique name.
    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term;

    /// Create a fresh bound variable (not tracked in the model).
    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term;
}

/// Borrowed translation session combining a solver reference with state.
///
/// This is the type that `execute_direct` and other borrowed-solver consumers
/// should use instead of owning a `TranslationContext`.
pub struct TranslationSession<'a, V: Eq + Hash> {
    solver: &'a mut Solver,
    state: &'a mut TranslationState<V>,
}

impl<'a, V: Eq + Hash> TranslationSession<'a, V> {
    /// Create a session from borrowed solver and state.
    pub fn new(solver: &'a mut Solver, state: &'a mut TranslationState<V>) -> Self {
        Self { solver, state }
    }

    /// Declare or retrieve a variable.
    pub fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        if let Some(&term) = self.state.vars.get(&key) {
            return term;
        }
        let term = self.solver.declare_const(name, sort);
        self.state.vars.insert(key, term);
        term
    }

    /// Check if a variable exists.
    pub fn has_var(&self, key: &V) -> bool {
        self.state.has_var(key)
    }

    /// Get a variable if it exists.
    pub fn get_var(&self, key: &V) -> Option<Term> {
        self.state.get_var(key)
    }

    /// Create a fresh declared constant with a unique name.
    pub fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        let name = format!("{}{}", prefix, self.state.fresh_counter);
        self.state.fresh_counter += 1;
        self.solver.declare_const(&name, sort)
    }

    /// Create a fresh bound variable (not tracked in the model).
    ///
    /// Uses the solver's `fresh_var` API for quantifier/let-bound variables
    /// that should not appear in model output.
    pub fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        let name = format!("_bv_{}{}", prefix, self.state.fresh_counter);
        self.state.fresh_counter += 1;
        self.solver.fresh_var(&name, sort)
    }

    /// Create a boolean constant.
    pub fn bool_const(&mut self, value: bool) -> Term {
        self.solver.bool_const(value)
    }

    /// Create an integer constant.
    pub fn int_const(&mut self, value: i64) -> Term {
        self.solver.int_const(value)
    }

    /// Create a bitvector constant.
    pub fn bv_const(&mut self, value: i64, width: u32) -> Term {
        expect_result(self.try_bv_const(value, width), "context.bv_const")
    }

    /// Try to create a bitvector constant.
    pub fn try_bv_const(&mut self, value: i64, width: u32) -> Result<Term, SolverError> {
        self.solver.try_bv_const(value, width)
    }

    /// Create a bitvector constant from an unsigned 64-bit value.
    pub fn bv_const_u64(&mut self, value: u64, width: u32) -> Term {
        expect_result(self.try_bv_const_u64(value, width), "context.bv_const_u64")
    }

    /// Try to create a bitvector constant from an unsigned 64-bit value.
    pub fn try_bv_const_u64(&mut self, value: u64, width: u32) -> Result<Term, SolverError> {
        self.solver.try_bv_const_u64(value, width)
    }

    /// Get the number of declared variables.
    pub fn var_count(&self) -> usize {
        self.state.var_count()
    }

    /// Declare or retrieve a function by name.
    ///
    /// Caches declarations so repeated calls with the same name return
    /// the same `FuncDecl` without re-declaring.
    pub fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        if let Some(func) = self.state.declared_funcs.get(name) {
            return func.clone();
        }
        let func = self.solver.try_declare_fun(name, domain, range);
        let func = expect_result(func, "context.declare_or_get_fun");
        self.state
            .declared_funcs
            .insert(name.to_string(), func.clone());
        func
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        self.state.get_func(name)
    }

    /// Assert a constraint.
    pub fn assert_term(&mut self, term: Term) {
        expect_result(self.try_assert_term(term), "context.assert_term");
    }

    /// Try to assert a constraint.
    pub fn try_assert_term(&mut self, term: Term) -> Result<(), SolverError> {
        self.solver.try_assert_term(term)
    }

    /// Check satisfiability.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        self.solver.check_sat()
    }

    /// Push a new assertion scope.
    pub fn push(&mut self) {
        expect_result(self.try_push(), "context.push");
    }

    /// Try to push a new assertion scope.
    pub fn try_push(&mut self) -> Result<(), SolverError> {
        self.solver.try_push()
    }

    /// Pop an assertion scope.
    pub fn pop(&mut self) {
        expect_result(self.try_pop(), "context.pop");
    }

    /// Try to pop an assertion scope.
    pub fn try_pop(&mut self) -> Result<(), SolverError> {
        self.solver.try_pop()
    }

    /// Access the underlying solver.
    pub fn solver(&mut self) -> &mut Solver {
        self.solver
    }
}

impl<V: Eq + Hash> TranslationHost<V> for TranslationSession<'_, V> {
    fn solver(&mut self) -> &mut Solver {
        self.solver
    }

    fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.declare_or_get_fun(name, domain, range)
    }

    fn cache_fun(&mut self, name: String, func: FuncDecl) {
        self.state.declared_funcs.insert(name, func);
    }
}

impl<V: Eq + Hash> TranslationTermHost<V> for TranslationSession<'_, V> {
    fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        self.get_or_declare(key, name, sort)
    }

    fn get_var(&self, key: &V) -> Option<Term> {
        self.get_var(key)
    }

    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_const(self, prefix, sort)
    }

    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_bound_var(self, prefix, sort)
    }
}

/// Owning translation context — compatibility wrapper.
///
/// Owns both a `Solver` and a `TranslationState<V>`. All existing callers
/// that used `TranslationContext<V>` continue to compile unchanged.
///
/// For borrowed-solver use cases (e.g., `execute_direct`), prefer
/// [`TranslationSession`] which borrows the solver instead of owning it.
pub struct TranslationContext<V: Eq + Hash> {
    solver: Solver,
    state: TranslationState<V>,
}

impl<V: Eq + Hash> TranslationContext<V> {
    /// Create a new translation context for the given logic.
    ///
    /// **Deprecated:** Prefer constructing a [`TranslationSession`] from a
    /// borrowed `Solver` and `TranslationState` instead.
    #[deprecated(
        since = "0.1.0",
        note = "Use TranslationSession with separate Solver + TranslationState instead"
    )]
    pub fn new(logic: Logic) -> Self {
        expect_result(Self::try_new_inner(logic), "context.new")
    }

    /// Try to create a new translation context for the given logic.
    ///
    /// **Deprecated:** Prefer constructing a [`TranslationSession`] from a
    /// borrowed `Solver` and `TranslationState` instead.
    #[deprecated(
        since = "0.1.0",
        note = "Use TranslationSession with separate Solver + TranslationState instead"
    )]
    pub fn try_new(logic: Logic) -> Result<Self, SolverError> {
        Self::try_new_inner(logic)
    }

    /// Internal constructor (not deprecated) used by the public constructors.
    fn try_new_inner(logic: Logic) -> Result<Self, SolverError> {
        Ok(Self {
            solver: Solver::try_new(logic)?,
            state: TranslationState::new(),
        })
    }

    /// Create a temporary session borrowing from this context.
    ///
    /// Useful when calling code that expects `&mut TranslationSession`.
    pub fn session(&mut self) -> TranslationSession<'_, V> {
        TranslationSession::new(&mut self.solver, &mut self.state)
    }

    /// Access the underlying state (e.g., for inspection or transfer).
    pub fn state(&self) -> &TranslationState<V> {
        &self.state
    }

    /// Access the underlying state mutably.
    pub fn state_mut(&mut self) -> &mut TranslationState<V> {
        &mut self.state
    }

    // --- Delegated methods (backwards compatibility) ---

    /// Declare or retrieve a variable.
    pub fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        self.session().get_or_declare(key, name, sort)
    }

    /// Check if a variable exists.
    pub fn has_var(&self, key: &V) -> bool {
        self.state.vars.contains_key(key)
    }

    /// Get a variable if it exists.
    pub fn get_var(&self, key: &V) -> Option<Term> {
        self.state.vars.get(key).copied()
    }

    /// Create a fresh declared constant with a unique name.
    pub fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        self.session().fresh_const(prefix, sort)
    }

    /// Create a fresh bound variable (not tracked in the model).
    pub fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        self.session().fresh_bound_var(prefix, sort)
    }

    /// Declare or retrieve a function by name.
    pub fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.session().declare_or_get_fun(name, domain, range)
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        self.state.declared_funcs.get(name)
    }

    /// Assert a constraint.
    pub fn assert_term(&mut self, term: Term) {
        expect_result(self.try_assert_term(term), "context.assert_term");
    }

    /// Try to assert a constraint.
    pub fn try_assert_term(&mut self, term: Term) -> Result<(), SolverError> {
        self.solver.try_assert_term(term)
    }

    /// Check satisfiability.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        self.solver.check_sat()
    }

    /// Access the underlying solver.
    pub fn solver(&mut self) -> &mut Solver {
        &mut self.solver
    }

    /// Create a boolean constant.
    pub fn bool_const(&mut self, value: bool) -> Term {
        self.solver.bool_const(value)
    }

    /// Create an integer constant.
    pub fn int_const(&mut self, value: i64) -> Term {
        self.solver.int_const(value)
    }

    /// Create a bitvector constant.
    pub fn bv_const(&mut self, value: i64, width: u32) -> Term {
        expect_result(self.try_bv_const(value, width), "context.bv_const")
    }

    /// Try to create a bitvector constant.
    pub fn try_bv_const(&mut self, value: i64, width: u32) -> Result<Term, SolverError> {
        self.solver.try_bv_const(value, width)
    }

    /// Create a bitvector constant from an unsigned 64-bit value.
    pub fn bv_const_u64(&mut self, value: u64, width: u32) -> Term {
        expect_result(self.try_bv_const_u64(value, width), "context.bv_const_u64")
    }

    /// Try to create a bitvector constant from an unsigned 64-bit value.
    pub fn try_bv_const_u64(&mut self, value: u64, width: u32) -> Result<Term, SolverError> {
        self.solver.try_bv_const_u64(value, width)
    }

    /// Push a new assertion scope.
    pub fn push(&mut self) {
        expect_result(self.try_push(), "context.push");
    }

    /// Try to push a new assertion scope.
    pub fn try_push(&mut self) -> Result<(), SolverError> {
        self.solver.try_push()
    }

    /// Pop an assertion scope.
    pub fn pop(&mut self) {
        expect_result(self.try_pop(), "context.pop");
    }

    /// Try to pop an assertion scope.
    pub fn try_pop(&mut self) -> Result<(), SolverError> {
        self.solver.try_pop()
    }

    /// Get the number of declared variables.
    pub fn var_count(&self) -> usize {
        self.state.var_count()
    }
}

impl<V: Eq + Hash> TranslationHost<V> for TranslationContext<V> {
    fn solver(&mut self) -> &mut Solver {
        &mut self.solver
    }

    fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.declare_or_get_fun(name, domain, range)
    }

    fn cache_fun(&mut self, name: String, func: FuncDecl) {
        self.state.declared_funcs.insert(name, func);
    }
}

impl<V: Eq + Hash> TranslationTermHost<V> for TranslationContext<V> {
    fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        self.get_or_declare(key, name, sort)
    }

    fn get_var(&self, key: &V) -> Option<Term> {
        self.get_var(key)
    }

    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_const(self, prefix, sort)
    }

    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_bound_var(self, prefix, sort)
    }
}

#[cfg(test)]
#[path = "context_tests.rs"]
mod tests;
