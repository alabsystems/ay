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
use ay_dpll::api::{
    FuncDecl, Logic, Solver, SolverCacheToken, SolverError, Sort, Term, VerifiedSolveResult,
};

use crate::ops::expect_result;

/// Reusable translation state independent of solver lifetime.
///
/// Owns the variable cache, function declaration cache, and fresh name counter.
/// Can be paired with different solver instances across incremental sessions.
/// Solver-local term and function handles are retained while sessions use the
/// same handle-arena generation and automatically invalidated when a different
/// solver is bound or the current solver is fully reset.
pub struct TranslationState<V: Eq + Hash> {
    vars: HashMap<V, CachedVar>,
    declared_funcs: HashMap<String, FuncDecl>,
    fresh_counter: u32,
    cache_token: Option<SolverCacheToken>,
}

struct CachedVar {
    term: Term,
    name: String,
    sort: Sort,
}

impl<V: Eq + Hash> TranslationState<V> {
    /// Create empty translation state.
    pub fn new() -> Self {
        Self {
            vars: HashMap::default(),
            declared_funcs: HashMap::default(),
            fresh_counter: 0,
            cache_token: None,
        }
    }

    /// Bind solver-local caches to `token`, invalidating handles from a
    /// different solver arena generation before they can be reused.
    fn bind_solver(&mut self, token: SolverCacheToken) {
        if self
            .cache_token
            .as_ref()
            .is_some_and(|current| !current.is_current() || current != &token)
        {
            self.vars.clear();
            self.declared_funcs.clear();
        }
        self.cache_token = Some(token);
    }

    fn cache_is_current(&self) -> bool {
        self.cache_token
            .as_ref()
            .is_some_and(SolverCacheToken::is_current)
    }

    fn cache_is_bound_to(&self, token: &SolverCacheToken) -> bool {
        self.cache_token
            .as_ref()
            .is_some_and(|current| current.is_current() && current == token)
    }

    /// Get the number of declared variables.
    pub fn var_count(&self) -> usize {
        if self.cache_is_current() {
            self.vars.len()
        } else {
            0
        }
    }

    /// Check if a variable exists.
    pub fn has_var<Q>(&self, key: &Q) -> bool
    where
        V: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.cache_is_current() && self.vars.contains_key(key)
    }

    /// Get a variable if it exists.
    pub fn get_var<Q>(&self, key: &Q) -> Option<Term>
    where
        V: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        if !self.cache_is_current() {
            return None;
        }
        self.vars.get(key).map(|cached| cached.term)
    }

    /// Get the number of declared functions.
    pub fn func_count(&self) -> usize {
        if self.cache_is_current() {
            self.declared_funcs.len()
        } else {
            0
        }
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        if !self.cache_is_current() {
            return None;
        }
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

    /// Fallible form of [`Self::declare_or_get_fun`].
    ///
    /// The default preserves compatibility with custom hosts whose declaration
    /// API is infallible. State-backed AY hosts override it to reject a cached
    /// name requested with a different signature.
    fn try_declare_or_get_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        Ok(self.declare_or_get_fun(name, domain, range))
    }

    /// Define a non-recursive function from already-translated parameter and
    /// body terms.
    ///
    /// State-backed AY hosts override this method to cache the handle. Keeping
    /// cache insertion out of the public trait surface prevents a handle made
    /// by another solver from being injected into [`TranslationState`].
    fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        self.solver().try_define_fun_body(name, params, range, body)
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

    /// Fallible form of [`Self::get_or_declare`].
    fn try_get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Result<Term, SolverError> {
        Ok(self.get_or_declare(key, name, sort))
    }

    /// Get a previously declared variable by key.
    fn get_var(&self, key: &V) -> Option<Term>;

    /// Create a fresh declared constant with a unique name.
    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term;

    /// Fallible form of [`Self::fresh_const`].
    fn try_fresh_const(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        Ok(self.fresh_const(prefix, sort))
    }

    /// Create a fresh bound variable (not tracked in the model).
    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term;

    /// Fallible form of [`Self::fresh_bound_var`].
    fn try_fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        Ok(self.fresh_bound_var(prefix, sort))
    }
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
        state.bind_solver(solver.cache_token());
        Self { solver, state }
    }

    fn bind_current_solver(&mut self) {
        self.state.bind_solver(self.solver.cache_token());
    }

    fn cache_is_bound_to_current_solver(&self) -> bool {
        self.state.cache_is_bound_to(&self.solver.cache_token())
    }

    /// Declare or retrieve a variable.
    pub fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        expect_result(
            self.try_get_or_declare(key, name, sort),
            "context.get_or_declare",
        )
    }

    /// Fallible variable declaration/cache lookup.
    ///
    /// A source key already cached at another sort is rejected rather than
    /// returning a mis-sorted term.
    pub fn try_get_or_declare(
        &mut self,
        key: V,
        name: &str,
        sort: Sort,
    ) -> Result<Term, SolverError> {
        self.bind_current_solver();
        if let Some(cached) = self.state.vars.get(&key) {
            if cached.name == name && cached.sort == sort {
                return Ok(cached.term);
            }
            return Err(SolverError::InvalidArgument {
                operation: "declare_const",
                message: format!(
                    "translation key is already cached as '{}' with sort {}, not '{name}' with sort {sort}",
                    cached.name, cached.sort
                ),
            });
        }
        let term = self.solver.try_declare_const(name, sort)?;
        self.state.vars.insert(
            key,
            CachedVar {
                term,
                name: name.to_string(),
                sort: self.solver.sort_of(term),
            },
        );
        Ok(term)
    }

    /// Check if a variable exists.
    pub fn has_var(&self, key: &V) -> bool {
        self.cache_is_bound_to_current_solver() && self.state.has_var(key)
    }

    /// Get a variable if it exists.
    pub fn get_var(&self, key: &V) -> Option<Term> {
        if !self.cache_is_bound_to_current_solver() {
            return None;
        }
        self.state.get_var(key)
    }

    /// Create a fresh declared constant with a unique name.
    pub fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        expect_result(self.try_fresh_const(prefix, sort), "context.fresh_const")
    }

    /// Fallible fresh constant creation.
    ///
    /// Existing solver declarations are skipped, including declarations made
    /// outside this translation state, so the returned term is genuinely new.
    pub fn try_fresh_const(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        self.bind_current_solver();
        if prefix.starts_with("__ay_") {
            return Err(SolverError::InvalidArgument {
                operation: "fresh_const",
                message: format!("fresh-constant prefix '{prefix}' enters a reserved namespace"),
            });
        }

        loop {
            let suffix = self.next_fresh_suffix("fresh_const")?;
            let name = format!("{prefix}{suffix}");
            if self.solver.is_symbol_name_occupied(&name) {
                continue;
            }
            // No mutation can interleave while this session holds `&mut
            // Solver`, so an error here is not a name race and must be exposed
            // rather than mistaken for another collision.
            return self.solver.try_declare_const(&name, sort);
        }
    }

    /// Create a fresh bound variable (not tracked in the model).
    ///
    /// Uses the solver's `fresh_var` API for quantifier/let-bound variables
    /// that should not appear in model output.
    pub fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        expect_result(
            self.try_fresh_bound_var(prefix, sort),
            "context.fresh_bound_var",
        )
    }

    /// Fallible fresh bound-variable creation.
    pub fn try_fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        self.bind_current_solver();
        let suffix = self.next_fresh_suffix("fresh_bound_var")?;
        let name = format!("_bv_{prefix}{suffix}");
        self.solver.try_fresh_var(&name, sort)
    }

    fn next_fresh_suffix(&mut self, operation: &'static str) -> Result<u32, SolverError> {
        let suffix = self.state.fresh_counter;
        self.state.fresh_counter =
            suffix
                .checked_add(1)
                .ok_or_else(|| SolverError::InvalidArgument {
                    operation,
                    message: "translation fresh-name counter exhausted".to_string(),
                })?;
        Ok(suffix)
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
        if self.cache_is_bound_to_current_solver() {
            self.state.var_count()
        } else {
            0
        }
    }

    /// Declare or retrieve a function by name.
    ///
    /// Caches declarations so repeated calls with the same name return
    /// the same `FuncDecl` without re-declaring.
    pub fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        expect_result(
            self.try_declare_or_get_fun(name, domain, range),
            "context.declare_or_get_fun",
        )
    }

    /// Fallible function declaration/cache lookup.
    ///
    /// A name already cached with another signature is rejected rather than
    /// returning a handle that disagrees with the caller's requested sorts.
    pub fn try_declare_or_get_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        self.bind_current_solver();
        if let Some(func) = self.state.declared_funcs.get(name) {
            if func.domain() == domain && func.range() == &range {
                return Ok(func.clone());
            }
            return Err(SolverError::InvalidArgument {
                operation: "declare_fun",
                message: format!("function name '{name}' is already cached with another signature"),
            });
        }
        let func = self.solver.try_declare_fun(name, domain, range)?;
        self.state
            .declared_funcs
            .insert(name.to_string(), func.clone());
        Ok(func)
    }

    /// Define and cache a non-recursive function in this solver.
    pub fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        self.bind_current_solver();
        let func = self.solver.try_define_fun_body(name, params, range, body)?;
        self.state
            .declared_funcs
            .insert(name.to_string(), func.clone());
        Ok(func)
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        if !self.cache_is_bound_to_current_solver() {
            return None;
        }
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

    fn try_declare_or_get_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        TranslationSession::try_declare_or_get_fun(self, name, domain, range)
    }

    fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        TranslationSession::try_define_fun_body(self, name, params, range, body)
    }
}

impl<V: Eq + Hash> TranslationTermHost<V> for TranslationSession<'_, V> {
    fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        TranslationSession::get_or_declare(self, key, name, sort)
    }

    fn try_get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationSession::try_get_or_declare(self, key, name, sort)
    }

    fn get_var(&self, key: &V) -> Option<Term> {
        self.get_var(key)
    }

    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_const(self, prefix, sort)
    }

    fn try_fresh_const(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationSession::try_fresh_const(self, prefix, sort)
    }

    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_bound_var(self, prefix, sort)
    }

    fn try_fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationSession::try_fresh_bound_var(self, prefix, sort)
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

    /// Fallible variable declaration/cache lookup.
    pub fn try_get_or_declare(
        &mut self,
        key: V,
        name: &str,
        sort: Sort,
    ) -> Result<Term, SolverError> {
        self.session().try_get_or_declare(key, name, sort)
    }

    /// Check if a variable exists.
    pub fn has_var(&self, key: &V) -> bool {
        self.state.cache_is_bound_to(&self.solver.cache_token()) && self.state.has_var(key)
    }

    /// Get a variable if it exists.
    pub fn get_var(&self, key: &V) -> Option<Term> {
        if !self.state.cache_is_bound_to(&self.solver.cache_token()) {
            return None;
        }
        self.state.get_var(key)
    }

    /// Create a fresh declared constant with a unique name.
    pub fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        self.session().fresh_const(prefix, sort)
    }

    /// Fallible fresh constant creation.
    pub fn try_fresh_const(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        self.session().try_fresh_const(prefix, sort)
    }

    /// Create a fresh bound variable (not tracked in the model).
    pub fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        self.session().fresh_bound_var(prefix, sort)
    }

    /// Fallible fresh bound-variable creation.
    pub fn try_fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        self.session().try_fresh_bound_var(prefix, sort)
    }

    /// Declare or retrieve a function by name.
    pub fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.session().declare_or_get_fun(name, domain, range)
    }

    /// Fallible function declaration/cache lookup.
    pub fn try_declare_or_get_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        self.session().try_declare_or_get_fun(name, domain, range)
    }

    /// Define and cache a non-recursive function in this solver.
    pub fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        self.session()
            .try_define_fun_body(name, params, range, body)
    }

    /// Get a previously declared function by name.
    pub fn get_func(&self, name: &str) -> Option<&FuncDecl> {
        if !self.state.cache_is_bound_to(&self.solver.cache_token()) {
            return None;
        }
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
        if self.state.cache_is_bound_to(&self.solver.cache_token()) {
            self.state.var_count()
        } else {
            0
        }
    }
}

impl<V: Eq + Hash> TranslationHost<V> for TranslationContext<V> {
    fn solver(&mut self) -> &mut Solver {
        &mut self.solver
    }

    fn declare_or_get_fun(&mut self, name: &str, domain: &[Sort], range: Sort) -> FuncDecl {
        self.declare_or_get_fun(name, domain, range)
    }

    fn try_declare_or_get_fun(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> Result<FuncDecl, SolverError> {
        TranslationContext::try_declare_or_get_fun(self, name, domain, range)
    }

    fn try_define_fun_body(
        &mut self,
        name: &str,
        params: &[(&str, Term)],
        range: Sort,
        body: Term,
    ) -> Result<FuncDecl, SolverError> {
        TranslationContext::try_define_fun_body(self, name, params, range, body)
    }
}

impl<V: Eq + Hash> TranslationTermHost<V> for TranslationContext<V> {
    fn get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Term {
        TranslationContext::get_or_declare(self, key, name, sort)
    }

    fn try_get_or_declare(&mut self, key: V, name: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationContext::try_get_or_declare(self, key, name, sort)
    }

    fn get_var(&self, key: &V) -> Option<Term> {
        self.get_var(key)
    }

    fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_const(self, prefix, sort)
    }

    fn try_fresh_const(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationContext::try_fresh_const(self, prefix, sort)
    }

    fn fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Term {
        Self::fresh_bound_var(self, prefix, sort)
    }

    fn try_fresh_bound_var(&mut self, prefix: &str, sort: Sort) -> Result<Term, SolverError> {
        TranslationContext::try_fresh_bound_var(self, prefix, sort)
    }
}

#[cfg(test)]
#[path = "context_tests.rs"]
mod tests;
