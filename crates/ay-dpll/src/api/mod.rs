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
mod proofs;
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
    ApplyResult, Goal, PatchStrength, PatchSuggestion, SolverScope, Tactic, TacticFailure,
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
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use ay_core::TermStore;
use ay_frontend::Command;

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
}

/// Native Rust API for AY SMT solver
///
/// Provides a programmatic interface for building SMT constraints
/// and checking satisfiability without parsing SMT-LIB text.
pub struct Solver {
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
    /// Function definitions registered via `try_define_fun` (#8613).
    /// Maps function name to its definition (params, body, return sort).
    /// When `try_apply` encounters a defined function, it expands inline
    /// by substituting parameter terms rather than creating an uninterpreted
    /// application.
    defined_funs: HashMap<String, DefinedFun>,
    /// Exact native uninterpreted-function signatures, preserving API-level
    /// sort kinds (notably `TypeVar`) that the frontend lowers in its core
    /// symbol table. This authenticates public `FuncDecl` handles in O(1).
    native_fun_signatures: HashMap<String, (Vec<Sort>, Sort)>,
    /// Native API replay trace for downstream reducers/debuggers.
    native_replay_events: Vec<NativeReplayEvent>,
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
        // Set the logic and propagate errors
        executor.execute(&Command::SetLogic(logic.as_str().to_string()))?;
        let native_replay_events = vec![NativeReplayEvent::new(
            0,
            NativeReplayEventKind::SetLogic {
                logic: logic.as_str().to_string(),
            },
            0,
        )];
        Ok(Self {
            executor,
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
            defined_funs: HashMap::default(),
            native_fun_signatures: HashMap::default(),
            native_replay_events,
        })
    }

    /// Access the internal term store
    fn terms(&self) -> &TermStore {
        &self.executor.context().terms
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
        &mut self.executor.context_mut().terms
    }

    fn expect_bitvec(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let sort = self.terms().sort(a.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
        let sort = self.terms().sort(t.0).clone();
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
