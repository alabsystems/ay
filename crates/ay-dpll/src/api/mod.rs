// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native Rust API for AY SMT Solver
//!
//! This module provides a programmatic interface for building and solving SMT
//! constraints directly in Rust, without parsing SMT-LIB text.
//!
//! # Example
//!
//! ```
//! use num_bigint::BigInt;
//! use ay_dpll::api::{Logic, ModelValue, SolveResult, Solver, Sort};
//!
//! let mut solver = Solver::try_new(Logic::QfLia).expect("valid logic");
//!
//! // Declare variables
//! let x = solver.declare_const("x", Sort::Int);
//! let y = solver.declare_const("y", Sort::Int);
//!
//! // Assert constraints: x > 0 and y = x + 1
//! let zero = solver.int_const(0);
//! let one = solver.int_const(1);
//! let x_gt_zero = solver.try_gt(x, zero).expect("int > int");
//! solver.try_assert_term(x_gt_zero).expect("boolean assertion");
//! let x_plus_one = solver.try_add(x, one).expect("int + int");
//! let y_eq_x_plus_one = solver.try_eq(y, x_plus_one).expect("matching sorts");
//! solver
//!     .try_assert_term(y_eq_x_plus_one)
//!     .expect("boolean assertion");
//!
//! // Check satisfiability with the atomic solve envelope
//! let details = solver.check_sat_with_details();
//! match details.accept_for_consumer() {
//!     Ok(SolveResult::Sat) => {
//!         let x_val = match solver.value(x) {
//!             Some(ModelValue::Int(value)) => value,
//!             _ => unreachable!("expected Int model value for x"),
//!         };
//!         let y_val = match solver.value(y) {
//!             Some(ModelValue::Int(value)) => value,
//!             _ => unreachable!("expected Int model value for y"),
//!         };
//!         assert!(x_val > BigInt::from(0));
//!         assert_eq!(y_val, x_val + BigInt::from(1));
//!     }
//!     Ok(SolveResult::Unsat(_)) => { /* unsatisfiable */ }
//!     Ok(SolveResult::Unknown) | Err(_) => {
//!         let _reason = details.unknown_reason;
//!     }
//!     Ok(_) => { /* future solve result variant */ }
//! }
//! ```

mod bitvectors;
mod compat_ext;
mod floating_point;
mod floating_point_conv;
mod fpa_introspect;
mod introspect;
mod model_parse;
mod model_parse_compound;
pub(crate) mod proofs;
mod rec_defs;
mod sequences;
pub(crate) mod solving;
mod string_bv_bridge;
mod strings;
mod terms;
pub mod types;

/// Maximum dense bit-vector width accepted by the native API and solve
/// boundary. Keep construction-time checks and the recursive pre-solve gate
/// on one envelope.
pub(crate) const MAX_API_BITVECTOR_WIDTH: u32 = 1 << 20;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

// Re-export FP/BV bridge classification constants (#8332)
pub use floating_point_conv::fp_class;
pub use fpa_introspect::{FpCategory, FpNumeral};
// Check-time recursive-definition expansion (Z3_add_rec_def semantics).
pub use rec_defs::{
    rec_def_name_conflates_with_builtin, RecExpandError, RecFunDef, MAX_FRONTIER_PER_ROUND,
};

// Re-export all public types for backwards compatibility
pub use introspect::TermKind;
pub use proofs::{
    FarkasCertificate, ProofAcceptanceError, ProofAcceptanceMode, StrictProofVerdict,
    UnsatProofArtifact,
};
pub use solving::{
    ApplyResult, Goal, ParsedPublicFormulaMetadata, ParsedPublicTermMetadata, ParsedSmtlib2Batch,
    ParsedSmtlib2Formula, PatchStrength, PatchSuggestion, SolverScope, Tactic, TacticFailure,
    TacticSolver,
};
pub use types::*;
// Re-export proof types used in public API signatures
pub use ay_proof::{PartialProofCheck, ProofCheckError, ProofQuality};
// Re-export the offline proof-bundle API (genuinely-external re-check): consumers
// can re-validate an exported `SerializableProofBundle` with no solver run.
pub use ay_proof::{
    re_check_bundle_strict, render_term_canonical, BundleReCheck, SerializableProofBundle,
    PROOF_BUNDLE_SCHEMA,
};
// Re-export Sort types from ay_core (#1437 - Sort type consolidation)
pub use ay_core::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort, TermId,
};
// Re-export deprecated term introspection types for backwards compatibility
#[allow(deprecated)]
pub use terms::AstKind;

use ay_core::kani_compat::DetHashMap as HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_core::TermStore;

use crate::{Executor, UnknownReason};

/// Configuration for constructing a [`Solver`] with pre-set options.
///
/// Use this to configure timeout, memory limits, and other solver parameters
/// at construction time rather than calling individual setter methods.
///
/// # Example
///
/// ```
/// use std::time::Duration;
/// use ay_dpll::api::{Logic, Solver, SolverConfig};
///
/// let config = SolverConfig::default()
///     .with_timeout(Duration::from_millis(5000))
///     .with_memory_limit(1024 * 1024 * 1024);
/// let mut solver = Solver::try_new_with_config(Logic::QfBv, config).unwrap();
/// // All check_sat calls will respect the 5s timeout
/// ```
#[derive(Debug, Clone, Default)]
#[must_use]
pub struct SolverConfig {
    /// Per-query timeout for check_sat calls.
    pub timeout: Option<Duration>,
    /// Process RSS memory limit in bytes.
    pub memory_limit: Option<usize>,
    /// Per-instance term memory limit in bytes.
    pub term_memory_limit: Option<usize>,
    /// Maximum learned clauses for SAT solver.
    pub learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver.
    pub clause_db_bytes_limit: Option<usize>,
}

impl SolverConfig {
    /// Set the per-query timeout for check_sat calls.
    ///
    /// Each `check_sat` call computes a deadline from `Instant::now() + timeout`
    /// and returns `Unknown` with reason `Timeout` if the deadline expires.
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set the process RSS memory limit in bytes.
    pub fn with_memory_limit(mut self, limit: usize) -> Self {
        self.memory_limit = Some(limit);
        self
    }

    /// Set the per-instance term memory limit in bytes.
    pub fn with_term_memory_limit(mut self, limit: usize) -> Self {
        self.term_memory_limit = Some(limit);
        self
    }

    /// Set the maximum learned clauses for the SAT solver.
    pub fn with_learned_clause_limit(mut self, limit: usize) -> Self {
        self.learned_clause_limit = Some(limit);
        self
    }

    /// Set the maximum clause DB size in bytes.
    pub fn with_clause_db_bytes_limit(mut self, limit: usize) -> Self {
        self.clause_db_bytes_limit = Some(limit);
        self
    }
}

/// A stored function definition for API-level define-fun (#8613).
///
/// When the function is applied via `try_apply`, the body is expanded by
/// substituting parameter term IDs with the application argument term IDs.
#[derive(Debug, Clone)]
struct DefinedFun {
    /// Parameter names and their TermIds (fresh variables)
    params: Vec<(String, TermId)>,
    /// The body term (built using the parameter variables)
    body: TermId,
    /// The function's return sort
    #[allow(dead_code)]
    return_sort: Sort,
    /// True when this definition was adopted from an asserted universal
    /// equality rather than introduced by the explicit define-fun API.
    /// Assertion-derived definitions must be removed by reset-assertions.
    assertion_derived: bool,
    /// Exact authority of the handle allowed to expand this body. Explicit
    /// native definitions get a fresh opaque incarnation; an assertion-adopted
    /// definition retains the frontend identity of the declared UF it refines.
    identity: FuncDeclIdentity,
}

/// One authenticated native uninterpreted-function declaration.
///
/// The public name remains the map key. `core_name` is the frontend-assigned
/// declaration identity used in the term DAG and can deliberately differ from
/// that key when the public spelling collides with an interpreted builtin.
#[derive(Debug, Clone)]
struct NativeFunctionRegistration {
    domain: Vec<Sort>,
    range: Sort,
    core_name: String,
    /// Exact frontend declaration and context incarnation. A reused core name
    /// and matching signature after reset must not authenticate an old handle.
    identity: FrontendFuncDeclIdentity,
}

/// Native Rust API for AY SMT solver
///
/// Provides a programmatic interface for building SMT constraints
/// and checking satisfiability without parsing SMT-LIB text.
pub struct Solver {
    /// Opaque generation identity for consumers caching solver-local handles.
    /// It remains stable while the term/declaration arena is preserved and is
    /// rotated by a full reset.
    cache_token: SolverCacheToken,
    /// Boxed: `Executor` is a ~56 KiB struct (the inline incremental BV/theory
    /// state alone holds three `SatSolver`s). Held inline it makes `Solver` —
    /// and every consumer struct embedding a `Solver` by value — a ~56 KiB
    /// object; unoptimized builds give each move its own stack slot, so
    /// consumer call chains accumulate megabytes of stack and overflow
    /// default 2 MiB threads (the 2026-07-18 deductive-checks stack overflow on
    /// libtest's default 2 MiB test threads). Boxing collapses every such
    /// slot to 8 bytes; all access auto-derefs and only the construction
    /// site (stack-guarded below) allocates.
    executor: Box<Executor>,
    /// Opaque incarnation of the native term-handle arena. Rotated only by a
    /// successful full reset; push/pop and reset-assertions preserve it.
    term_arena: TermArenaStamp,
    /// Variable names for model extraction
    var_names: HashMap<TermId, String>,
    /// Exact native declaration identity -> variable term.
    ///
    /// This reverse index makes idempotent declarations and adapter-identity
    /// collision checks constant-time even when a solver has many constants.
    var_terms_by_name: HashMap<String, TermId>,
    /// Variable sorts for model extraction
    var_sorts: HashMap<TermId, Sort>,
    /// Last assumptions from check_sat_assuming (TermId -> Term mapping)
    last_assumptions: Option<HashMap<TermId, Term>>,
    /// Interrupt flag for cancelling solve from another thread
    interrupt: Arc<AtomicBool>,
    /// Timeout duration for check_sat calls (None = no timeout)
    timeout: Option<Duration>,
    /// Memory limit in bytes for check_sat calls (None = no limit)
    memory_limit: Option<usize>,
    /// Maximum learned clauses for SAT solver (None = no limit)
    learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver (None = no limit)
    clause_db_bytes_limit: Option<usize>,
    /// Current push/pop scope depth (incremented by push, decremented by pop)
    scope_level: u32,
    /// Reason for last Unknown result
    last_unknown_reason: Option<UnknownReason>,
    /// Detail message from the last executor error (when reason is InternalError)
    last_executor_error: Option<String>,
    /// Typed payload for an artifact-export failure flattened by an infallible
    /// `check_sat*` compatibility entrypoint.
    last_artifact_export_failure: Option<String>,
    /// Per-instance term memory limit in bytes (None = no limit).
    /// Unlike `memory_limit` (process RSS), this caps term allocation for
    /// THIS solver only, preventing cross-instance budget interference (#6563).
    term_memory_limit: Option<usize>,
    /// Core evolution tracker for incremental UNSAT core diffing (#8154, #8306).
    /// Extracted into a standalone type so consumers can manage it independently
    /// of the solver's borrow state.
    core_tracker: CoreEvolutionTracker,
    /// Soft constraints for MaxSMT solving (#8300).
    /// Populated by `assert_soft()`, consumed by `check_sat_max()`.
    soft_constraints: Vec<maxsmt::SoftConstraint>,
    /// Test-only release-soundness hook: corrupt one executor-installed native
    /// soft after execution so the transaction authentication check is exercised.
    #[cfg(test)]
    corrupt_native_soft_transaction: bool,
    /// Test-only publication-lifetime hook: fire the native interrupt after the
    /// MaxSMT engine has returned but before objective accounting is admitted.
    #[cfg(test)]
    interrupt_native_maxsmt_after_execution: bool,
    /// Test-only publication-lifetime hook: exhaust the per-instance term
    /// budget after the MaxSMT engine returns, at the native accounting boundary.
    #[cfg(test)]
    exhaust_native_maxsmt_term_memory_after_execution: bool,
    /// Function definitions registered via `try_define_fun` (#8613).
    /// Maps function name to its definition (params, body, return sort).
    /// When `try_apply` encounters a defined function, it expands inline
    /// by substituting parameter terms rather than creating an uninterpreted
    /// application.
    defined_funs: HashMap<String, DefinedFun>,
    /// Exact native uninterpreted-function signatures, preserving API-level
    /// sort kinds (notably `TypeVar`) that the frontend lowers in its core
    /// symbol table. This authenticates public `FuncDecl` handles in O(1).
    native_fun_signatures: HashMap<String, NativeFunctionRegistration>,
    /// Native API replay trace for downstream reducers/debuggers.
    native_replay_events: Vec<NativeReplayEvent>,
}

/// Opaque identity for one generation of a [`Solver`]'s handle arena.
///
/// Term handles are meaningful only in the solver that created them. Adapter
/// crates that cache such handles can retain this token and invalidate their
/// cache when a different solver is attached or the solver is fully reset. The
/// marker allocation is kept alive by every clone, so identities cannot collide
/// through allocator address reuse after a generation ends.
#[doc(hidden)]
#[derive(Clone)]
pub struct SolverCacheToken(Arc<SolverCacheMarker>);

struct SolverCacheMarker {
    current: AtomicBool,
}

impl SolverCacheToken {
    fn new() -> Self {
        Self(Arc::new(SolverCacheMarker {
            current: AtomicBool::new(true),
        }))
    }

    fn invalidate(&self) {
        self.0.current.store(false, Ordering::Release);
    }

    /// Whether the solver still retains the handle arena represented by this
    /// token.
    ///
    /// A successful full reset invalidates every clone of the previous token,
    /// allowing adapter caches to reject stale handles even before they obtain
    /// the solver's replacement token.
    #[doc(hidden)]
    #[must_use]
    pub fn is_current(&self) -> bool {
        self.0.current.load(Ordering::Acquire)
    }
}

impl PartialEq for SolverCacheToken {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for SolverCacheToken {}

impl std::fmt::Debug for SolverCacheToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SolverCacheToken(..)")
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        // Cached handles cannot outlive their arena. Notify every retained
        // token clone before the executor and term store are destroyed.
        self.cache_token.invalidate();
    }
}

impl Solver {
    /// Create a new solver for the specified logic
    ///
    /// # Panics
    ///
    /// Panics if the logic is not supported. Use [`try_new`] for a fallible
    /// version that returns an error instead.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let _solver = Solver::new(Logic::QfLia);
    /// ```
    ///
    /// [`try_new`]: Solver::try_new
    /// # Panics
    ///
    /// Panics if the solver cannot be created for the given logic. Use
    /// [`try_new`](Solver::try_new) for a fallible alternative.
    #[must_use]
    #[allow(clippy::panic)]
    pub fn new(logic: Logic) -> Self {
        Self::try_new(logic)
            .unwrap_or_else(|e| panic!("Failed to create solver for logic {logic:?}: {e}"))
    }

    /// Try to create a new solver for the specified logic.
    ///
    /// Fallible version of [`new`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the logic is not supported.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic, SolverError};
    ///
    /// // Create solver with fallible constructor
    /// let solver = Solver::try_new(Logic::QfLia);
    /// assert!(solver.is_ok());
    /// ```
    ///
    /// [`new`]: Solver::new
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_new(logic: Logic) -> Result<Self, SolverError> {
        Self::try_new_with_config(logic, SolverConfig::default())
    }

    /// Create a new solver with the specified logic and configuration.
    ///
    /// This is the preferred constructor when you need to set timeout, memory
    /// limits, or other options at creation time.
    ///
    /// # Errors
    ///
    /// Returns an error if the logic is not supported.
    ///
    /// # Example
    ///
    /// ```
    /// use std::time::Duration;
    /// use ay_dpll::api::{Logic, Solver, SolverConfig};
    ///
    /// let config = SolverConfig::default()
    ///     .with_timeout(Duration::from_millis(5000));
    /// let mut solver = Solver::try_new_with_config(Logic::QfBv, config).unwrap();
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_new_with_config(logic: Logic, config: SolverConfig) -> Result<Self, SolverError> {
        // Guard against small embedder/test thread stacks (e.g. libtest's
        // default 2 MiB): construction moves the ~57 KB `Solver`/`Executor`
        // by value through several frames on top of `Executor::new` and the
        // `set-logic` dispatch, which in an embedder's opt-level-0 dev build
        // needs well over half a MiB of stack on its own (2026-07-18
        // deductive-checks overflow inside `Executor::execute` during
        // `Solver::try_new`). Grow once up front; the inner guards in
        // `Executor::new`/`Executor::execute` then find ample remaining
        // stack on the grown segment and do not re-grow.
        stacker::maybe_grow(
            crate::executor::EXECUTOR_STACK_RED_ZONE,
            crate::executor::EXECUTOR_STACK_SIZE,
            || Self::try_new_with_config_stack_guarded(logic, config),
        )
    }

    /// Body of [`Solver::try_new_with_config`] — only called through the
    /// stack guard above so the by-value construction frames land on the
    /// grown segment.
    fn try_new_with_config_stack_guarded(
        logic: Logic,
        config: SolverConfig,
    ) -> Result<Self, SolverError> {
        // Box while still on the grown segment: the ~56 KB `Executor` value
        // exists only in frames protected by the stack guard above, and what
        // escapes to the caller is a small `Solver` holding a heap pointer.
        let mut executor = Box::new(Executor::new());
        // Install the logic WITHOUT recording a command-stream `(set-logic ...)`.
        // Going through `Command::SetLogic` marks the logic as having been set
        // by the command stream, which then rejects the first `(set-logic ...)`
        // of any script this solver later parses — z3 accepts that, because for
        // it "already been set" is parser state and `SolverFor` is not part of
        // the stream.
        executor.set_initial_logic(logic.as_str())?;
        let native_replay_events = vec![NativeReplayEvent::new(
            0,
            NativeReplayEventKind::SetLogic {
                logic: logic.as_str().to_string(),
            },
            0,
        )];
        Ok(Self {
            cache_token: SolverCacheToken::new(),
            executor,
            term_arena: TermArenaStamp::fresh(),
            var_names: HashMap::default(),
            var_terms_by_name: HashMap::default(),
            var_sorts: HashMap::default(),
            last_assumptions: None,
            interrupt: Arc::new(AtomicBool::new(false)),
            timeout: config.timeout,
            memory_limit: config.memory_limit,
            learned_clause_limit: config.learned_clause_limit,
            clause_db_bytes_limit: config.clause_db_bytes_limit,
            scope_level: 0,
            last_unknown_reason: None,
            last_executor_error: None,
            last_artifact_export_failure: None,
            term_memory_limit: config.term_memory_limit,
            core_tracker: CoreEvolutionTracker::new(),
            soft_constraints: Vec::new(),
            #[cfg(test)]
            corrupt_native_soft_transaction: false,
            #[cfg(test)]
            interrupt_native_maxsmt_after_execution: false,
            #[cfg(test)]
            exhaust_native_maxsmt_term_memory_after_execution: false,
            defined_funs: HashMap::default(),
            native_fun_signatures: HashMap::default(),
            native_replay_events,
        })
    }

    /// Access the internal term store
    fn terms(&self) -> &TermStore {
        &self.executor.context().terms
    }

    /// Authenticate a public term capability before any term-store indexing or
    /// solver-state mutation.
    fn resolve_term(&self, operation: &'static str, term: Term) -> Result<TermId, SolverError> {
        let id = term.id();
        let Some(entry) = self.terms().entry_stamp(id) else {
            return Err(SolverError::InvalidTermHandle {
                operation,
                term: term.to_raw(),
            });
        };
        if !term.authenticates(self.term_arena, entry) {
            return Err(SolverError::InvalidTermHandle {
                operation,
                term: term.to_raw(),
            });
        }
        Ok(id)
    }

    fn resolve_terms(
        &self,
        operation: &'static str,
        terms: &[Term],
    ) -> Result<Vec<TermId>, SolverError> {
        terms
            .iter()
            .map(|term| self.resolve_term(operation, *term))
            .collect()
    }

    #[allow(clippy::panic)]
    fn require_term(&self, operation: &'static str, term: Term) -> TermId {
        self.resolve_term(operation, term)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    #[allow(clippy::panic)]
    fn require_terms(&self, operation: &'static str, terms: &[Term]) -> Vec<TermId> {
        self.resolve_terms(operation, terms)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Mint the sole authenticated public wrapper for a live internal term.
    #[allow(clippy::panic)]
    fn wrap_term(&self, id: TermId) -> Term {
        let entry = self
            .terms()
            .entry_stamp(id)
            .unwrap_or_else(|| panic!("attempted to publish non-live internal term {id}"));
        Term::authenticated(id, self.term_arena, entry)
    }

    /// Lower an API sort through this solver's live nominal-sort registry.
    ///
    /// `Sort::as_term_sort` is context-free and therefore cannot distinguish a
    /// datatype (or other named sort) redeclared with the same surface spelling
    /// after scope exit.  Every API boundary that creates or checks a term sort
    /// must use this contextual lowering so the engine sees the exact live
    /// carrier identity.  Undeclared uninterpreted sorts retain their ordinary
    /// context-free identity for backwards-compatible native construction.
    fn lower_live_sort(&self, sort: &Sort) -> Sort {
        match sort {
            Sort::Uninterpreted(name) => self
                .executor
                .context()
                .sort_definition(name)
                .cloned()
                .unwrap_or_else(|| sort.as_term_sort()),
            Sort::Datatype(datatype) => self
                .executor
                .context()
                .sort_definition(&datatype.name)
                .cloned()
                .unwrap_or_else(|| sort.as_term_sort()),
            Sort::Array(array) => Sort::array(
                self.lower_live_sort(&array.index_sort),
                self.lower_live_sort(&array.element_sort),
            ),
            Sort::Seq(element) => Sort::seq(self.lower_live_sort(element)),
            _ => sort.as_term_sort(),
        }
    }

    /// Return this solver's opaque handle-arena generation identity.
    ///
    /// Intended for adapter caches that hold solver-local [`Term`] or
    /// [`FuncDecl`] handles. A successful full [`Self::try_reset`] changes the
    /// token because all such handles become stale; reset-assertions does not.
    #[doc(hidden)]
    #[must_use]
    pub fn cache_token(&self) -> SolverCacheToken {
        self.cache_token.clone()
    }

    /// Whether `name` is already occupied by a declaration in this solver.
    ///
    /// This adapter-facing query lets fresh-name generators distinguish a
    /// collision from other [`SolverError::InvalidArgument`] failures without
    /// parsing error text.
    #[doc(hidden)]
    #[must_use]
    pub fn is_symbol_name_occupied(&self, name: &str) -> bool {
        self.var_terms_by_name.contains_key(name)
            || self.executor.context().has_symbol_binding(name)
    }

    /// Crate-internal accessor for the term store backing [`Self::last_proof`].
    ///
    /// Exposed within the crate (not part of the public API) so the semantic
    /// array proof checker's end-to-end tests can hand the prover's actual
    /// `Proof` together with the matching `TermStore` to
    /// [`crate::array_proof_check::check_array_proof`].
    #[cfg(test)]
    pub(crate) fn proof_term_store(&self) -> &TermStore {
        self.terms()
    }

    /// Access the internal term store mutably
    fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.executor.context_mut_internal().terms
    }

    /// Mark the native term arena as containing a user-shadowed `to_real`.
    ///
    /// This is a narrow friend hook for `ay-ffi`'s cross-context translation
    /// tests.  It is absent from ordinary `ay-dpll` builds; production native
    /// callers should create declarations through [`Self::try_declare_fun`],
    /// which maintains the latch automatically.
    #[cfg(feature = "z3-compat-internals")]
    #[doc(hidden)]
    pub fn z3_compat_mark_to_real_shadowed(&mut self) {
        self.terms_mut().mark_to_real_shadowed();
    }

    /// Whether the user-shadowed `to_real` latch is active.
    ///
    /// See [`Self::z3_compat_mark_to_real_shadowed`].
    #[cfg(feature = "z3-compat-internals")]
    #[doc(hidden)]
    #[must_use]
    pub fn z3_compat_to_real_is_shadowed(&self) -> bool {
        self.terms().to_real_is_shadowed()
    }

    fn resolved_term_sort(&self, operation: &'static str, term: Term) -> Result<Sort, SolverError> {
        let id = self.resolve_term(operation, term)?;
        Ok(self.terms().sort(id).clone())
    }

    fn expect_bitvec(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        match sort {
            Sort::BitVec(_) => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec",
                got: vec![other],
            }),
        }
    }

    fn expect_int(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        match sort {
            Sort::Int => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Int",
                got: vec![other],
            }),
        }
    }

    fn expect_real(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        match sort {
            Sort::Real => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Real",
                got: vec![other],
            }),
        }
    }

    fn expect_bitvec_width(&self, operation: &'static str, t: Term) -> Result<u32, SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        match sort {
            Sort::BitVec(bv) => Ok(bv.width),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec",
                got: vec![other],
            }),
        }
    }

    fn expect_bitvec_width2(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(u32, u32), SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        match (&a_sort, &b_sort) {
            (Sort::BitVec(a_bv), Sort::BitVec(b_bv)) => Ok((a_bv.width, b_bv.width)),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec, BitVec",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    fn expect_same_bitvec_width(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<u32, SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        match (&a_sort, &b_sort) {
            (Sort::BitVec(a_bv), Sort::BitVec(b_bv)) if a_bv.width == b_bv.width => Ok(a_bv.width),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec(w), BitVec(w)",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that a term has an arithmetic sort (Int or Real).
    fn expect_arith(&self, operation: &'static str, a: Term) -> Result<Sort, SolverError> {
        let sort = self.resolved_term_sort(operation, a)?;
        match &sort {
            Sort::Int | Sort::Real => Ok(sort),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Int or Real",
                got: vec![sort],
            }),
        }
    }

    /// Check that two terms have the same arithmetic sort (both Int or both Real).
    fn expect_same_arith_sort(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<Sort, SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        match (&a_sort, &b_sort) {
            (Sort::Int, Sort::Int) => Ok(Sort::Int),
            (Sort::Real, Sort::Real) => Ok(Sort::Real),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "same arithmetic sort (Int,Int) or (Real,Real)",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that two terms are both Int.
    fn expect_both_int(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        match (&a_sort, &b_sort) {
            (Sort::Int, Sort::Int) => Ok(()),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Int, Int",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that two terms are both Real.
    fn expect_both_real(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        match (&a_sort, &b_sort) {
            (Sort::Real, Sort::Real) => Ok(()),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Real, Real",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that a term has Bool sort.
    fn expect_bool(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        match sort {
            Sort::Bool => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Bool",
                got: vec![other],
            }),
        }
    }

    /// Check that two terms have the same sort (any sort, but matching).
    fn expect_same_sort(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.resolved_term_sort(operation, a)?;
        let b_sort = self.resolved_term_sort(operation, b)?;
        if a_sort == b_sort {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "same sort for both arguments",
                got: vec![a_sort, b_sort],
            })
        }
    }

    /// Check that a term has String sort.
    fn expect_string(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        if sort == Sort::String {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "String",
                got: vec![sort],
            })
        }
    }

    /// Check that a term has RegLan sort.
    fn expect_reglan(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.resolved_term_sort(operation, t)?;
        if sort == Sort::RegLan {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "RegLan",
                got: vec![sort],
            })
        }
    }
}
