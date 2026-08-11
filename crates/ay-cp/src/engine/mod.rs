// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CP-SAT engine: orchestrates solving with Lazy Clause Generation (LCG).
//!
//! The engine owns the SAT solver, integer trail, encoder, and propagators.
//! It implements `ay_sat::Extension` to integrate CP propagation into the
//! SAT solver's CDCL loop.
//!
//! Solve loop: SAT decision → Extension::asserted (update trail) →
//! Extension::propagate (run dirty propagators, tighten bounds) →
//! conflict → CDCL backtrack; on full assignment → Extension::check.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use ay_sat::Solver as SatSolver;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Constraint, Propagator};
use crate::search::{SearchState, SearchStrategy};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

mod compile;
mod encoding;
mod extension;
mod optimization;
pub use optimization::IncrementalEncodingError;
mod solve;
#[cfg(debug_assertions)]
mod validate;
pub use extension::CpExtension;

/// A lazily-checked `x - y != offset` constraint.
///
/// Instead of eagerly encoding O(d) SAT clauses, these are verified in
/// `Extension::check()` on complete assignments. If violated, a blocking
/// clause is generated: `¬[x >= vx] ∨ [x >= vx+1] ∨ ¬[y >= vy] ∨ [y >= vy+1]`.
#[derive(Clone, Debug)]
pub(crate) struct LazyNeq {
    pub x: IntVarId,
    pub y: IntVarId,
    pub offset: i64,
}

/// Domain overlap threshold for lazy neq routing.
/// PairwiseNeq with overlap > this use lazy checking instead of eager encoding.
const LAZY_NEQ_DOMAIN_THRESHOLD: i64 = 64;

/// Handle to a cancellable timer thread.
///
/// When the timer expires, it sets the interrupt `AtomicBool`. Calling
/// `cancel()` or dropping the handle wakes the thread early via `unpark`
/// and prevents it from firing. This avoids fire-and-forget timer threads
/// that accumulate during optimization probing (#6231).
struct TimerHandle {
    cancelled: Arc<AtomicBool>,
    handle: JoinHandle<()>,
}

impl TimerHandle {
    /// Spawn a timer thread that sets `flag` to `true` after `duration`.
    fn spawn(flag: Arc<AtomicBool>, duration: Duration) -> Self {
        let cancelled = Arc::new(AtomicBool::new(false));
        let cancel_flag = Arc::clone(&cancelled);
        let handle = std::thread::spawn(move || {
            std::thread::park_timeout(duration);
            if !cancel_flag.load(Ordering::Acquire) {
                flag.store(true, Ordering::Relaxed);
            }
        });
        Self { cancelled, handle }
    }

    /// Cancel the timer, preventing it from firing. Wakes the thread early.
    fn cancel(self) {
        // Signal cancellation (Drop impl handles the actual work).
        // Consuming `self` triggers `Drop::drop`.
        drop(self);
    }
}

impl Drop for TimerHandle {
    fn drop(&mut self) {
        self.cancelled.store(true, Ordering::Release);
        self.handle.thread().unpark();
        // Do not join — the timer thread will observe the cancel flag
        // and exit promptly. Joining here could block the destructor
        // if the thread is slow to wake from park_timeout.
    }
}

/// Result of CP-SAT solving.
#[derive(Debug)]
#[non_exhaustive]
pub enum CpSolveResult {
    /// Satisfiable with integer assignment: (var_id → value)
    Sat(Vec<(IntVarId, i64)>),
    /// Unsatisfiable
    Unsat,
    /// Unknown (timeout or resource limit)
    Unknown,
}

/// The main CP-SAT engine.
///
/// Build a model by adding variables and constraints, then call `solve()`.
///
/// # Example
///
/// ```rust,no_run
/// use ay_cp::{CpSatEngine, Domain};
///
/// let mut engine = CpSatEngine::new();
///
/// // Create variables
/// let x = engine.new_int_var(Domain::new(1, 10), Some("x"));
/// let y = engine.new_int_var(Domain::new(1, 10), Some("y"));
/// let z = engine.new_int_var(Domain::new(1, 10), Some("z"));
///
/// // Add constraints
/// engine.add_constraint(ay_cp::propagator::Constraint::AllDifferent(vec![x, y, z]));
///
/// // Solve
/// match engine.solve() {
///     ay_cp::engine::CpSolveResult::Sat(assignment) => {
///         assert!(!assignment.is_empty());
///     }
///     ay_cp::engine::CpSolveResult::Unsat => {}
///     ay_cp::engine::CpSolveResult::Unknown | _ => {}
/// }
/// ```
pub struct CpSatEngine {
    /// The underlying SAT solver
    sat: SatSolver,
    /// Integer trail (bound changes + undo)
    trail: IntegerTrail,
    /// Integer-to-SAT encoder
    encoder: IntegerEncoder,
    /// Compiled propagators
    propagators: Vec<Box<dyn Propagator>>,
    /// Pending constraints (not yet compiled)
    constraints: Vec<Constraint>,
    /// Variable names (for output)
    var_names: Vec<Option<String>>,
    /// Propagator dirty flags (indexed by propagator index)
    dirty: Vec<bool>,
    /// Search strategy for variable selection
    search_strategy: SearchStrategy,
    /// Value selection strategy for branching
    value_choice: crate::search::ValueChoice,
    /// Annotation-specified variable ordering for InputOrder
    search_vars: Vec<IntVarId>,
    /// Shared interrupt flag for cooperative timeout cancellation.
    /// When set to true, the SAT solver will return Unknown at the next
    /// decision-level check point (~every 1000 decisions).
    interrupt: Arc<AtomicBool>,
    /// Persisted search state (weights, activities) across solve calls.
    /// Populated after the first solve; reused on subsequent calls so that
    /// incremental optimization retains learned heuristic information.
    search_state: Option<SearchState>,
    /// Lazily-checked neq constraints (large domains, deferred to Extension::check).
    lazy_neqs: Vec<LazyNeq>,
    /// Snapshot of all constraints (before compilation) for post-solve validation.
    /// Only populated in debug builds to avoid allocation overhead in release.
    #[cfg(debug_assertions)]
    debug_constraints: Vec<Constraint>,
    /// Optional wall-clock deadline. When set, the engine starts the SAT
    /// interrupt timer only AFTER encoding completes, so that encoding time
    /// does not consume the solving budget (#5683).
    deadline: Option<Instant>,
    /// Optimization objective: (variable, minimize). When set, the CP
    /// extension uses `suggest_phase` to persistently guide the SAT solver's
    /// phase selection toward the optimal direction for the objective variable.
    objective: Option<(IntVarId, bool)>,
    /// Active timer thread handle. Uses `Mutex` for interior mutability so
    /// `set_timeout(&self)` can cancel previous timers without `&mut self`.
    /// Previous fire-and-forget timers accumulated threads and caused race
    /// conditions where stale timers set the interrupt during subsequent
    /// solves (#6231).
    timer: Mutex<Option<TimerHandle>>,
    /// A permanent incremental constraint proved the model inconsistent.
    ///
    /// This cannot be represented by a transient SAT empty-clause flag:
    /// incremental solve setup clears that flag between calls.
    permanently_inconsistent: bool,
    /// Number of registered domains whose sparse holes have been encoded.
    /// Hole clauses are deferred until after the global order-encoding
    /// capacity preflight, avoiding unbounded SAT allocation during variable
    /// registration.
    domain_holes_encoded: usize,
}

impl CpSatEngine {
    /// Create a new CP-SAT engine.
    ///
    /// Configures the underlying SAT solver for CP-specific restart policy:
    /// Luby-sequence restarts with base 250 (instead of Glucose EMA restarts).
    /// CP propagation-derived clauses often have high LBD, causing Glucose
    /// restarts to fire too aggressively. Luby restarts with a larger base
    /// allow more exploration between restarts, which is critical for
    /// constraint propagation to make progress.
    pub fn new() -> Self {
        let interrupt = Arc::new(AtomicBool::new(false));
        let mut sat = SatSolver::new(0);
        sat.set_interrupt(Arc::clone(&interrupt));
        // CP-SAT always uses incremental solving (optimization loop).
        // Enter incremental mode early to prevent destructive inprocessing
        // (BVE, BCE) on the first solve — this avoids the arena rebuild that
        // drops learned clauses on the second solve (#5608).
        sat.set_incremental_mode();
        // CP-specific restart policy: Luby restarts with base 250.
        // Glucose EMA restarts fire too aggressively on CP problems because
        // propagation-derived clauses have high LBD. Luby with a larger base
        // gives the solver more time to explore between restarts.
        sat.set_glucose_restarts(false);
        sat.set_restart_base(250);
        Self {
            sat,
            trail: IntegerTrail::new(),
            encoder: IntegerEncoder::new(),
            propagators: Vec::new(),
            constraints: Vec::new(),
            var_names: Vec::new(),
            dirty: Vec::new(),
            search_strategy: SearchStrategy::default(),
            value_choice: crate::search::ValueChoice::default(),
            search_vars: Vec::new(),
            interrupt,
            search_state: None,
            lazy_neqs: Vec::new(),
            #[cfg(debug_assertions)]
            debug_constraints: Vec::new(),
            deadline: None,
            objective: None,
            timer: Mutex::new(None),
            permanently_inconsistent: false,
            domain_holes_encoded: 0,
        }
    }

    /// Set a wall-clock deadline for solving (#5683).
    ///
    /// Unlike `set_timeout()`, this does not start a timer immediately.
    /// Instead, the timer is started inside `solve()` AFTER constraint
    /// compilation and order-encoding pre-allocation complete. This ensures
    /// that encoding time does not consume the solving budget.
    ///
    /// Call `clear_deadline()` between optimization iterations if needed,
    /// though typically the deadline remains the same throughout.
    pub fn set_deadline(&mut self, deadline: Instant) {
        self.deadline = Some(deadline);
    }

    /// Clear the deadline (e.g. when no timeout is desired).
    pub fn clear_deadline(&mut self) {
        self.deadline = None;
    }

    /// Set a timeout for the next `solve()` call.
    ///
    /// Spawns a cancellable background thread that sets the interrupt flag
    /// after `duration` has elapsed. The SAT solver checks this flag every
    /// ~1000 decisions and returns `Unknown` when set.
    ///
    /// Any previously-active timer is cancelled before the new one starts.
    /// This prevents stale timers from accumulating during optimization
    /// probing and eliminates the race condition where an old timer fires
    /// during a subsequent solve (#6231).
    pub fn set_timeout(&self, duration: Duration) {
        let new_timer = TimerHandle::spawn(Arc::clone(&self.interrupt), duration);
        let prev = self
            .timer
            .lock()
            .expect("invariant: timer mutex not poisoned")
            .replace(new_timer);
        if let Some(old) = prev {
            old.cancel();
        }
    }

    /// Clear the interrupt flag and cancel any active timer (#6231).
    ///
    /// Cancelling the timer prevents stale timer threads from setting
    /// the interrupt flag after it has been cleared.
    pub fn clear_interrupt(&self) {
        let prev = self
            .timer
            .lock()
            .expect("invariant: timer mutex not poisoned")
            .take();
        if let Some(old) = prev {
            old.cancel();
        }
        self.interrupt.store(false, Ordering::Relaxed);
    }

    /// Check whether the interrupt flag has been set.
    pub fn is_interrupted(&self) -> bool {
        self.interrupt.load(Ordering::Relaxed)
    }

    /// Set the search strategy for variable selection.
    ///
    /// Must be called before `solve()`. Default is `DomWDeg`.
    pub fn set_search_strategy(&mut self, strategy: SearchStrategy) {
        self.search_strategy = strategy;
    }

    /// Get the current search variable ordering.
    pub fn search_vars(&self) -> &[IntVarId] {
        &self.search_vars
    }

    /// Set the variable ordering for `InputOrder` search.
    pub fn set_search_vars(&mut self, vars: Vec<IntVarId>) {
        self.search_vars = vars;
    }

    /// Set the value selection strategy for branching.
    pub fn set_value_choice(&mut self, choice: crate::search::ValueChoice) {
        self.value_choice = choice;
    }

    /// Install an interrupt flag for cooperative cancellation and timeouts.
    ///
    /// The engine and underlying SAT solver retain the same handle, so later
    /// [`set_timeout`](Self::set_timeout) and deadline timers also signal the
    /// caller-provided flag. Any timer attached to the previous handle is
    /// cancelled before replacement.
    pub fn set_interrupt(&mut self, handle: Arc<AtomicBool>) {
        let prev = self
            .timer
            .lock()
            .expect("invariant: timer mutex not poisoned")
            .take();
        if let Some(old) = prev {
            old.cancel();
        }
        self.interrupt = Arc::clone(&handle);
        self.sat.set_interrupt(handle);
    }

    /// Add an integer variable with the given domain.
    pub fn new_int_var(&mut self, domain: crate::domain::Domain, name: Option<&str>) -> IntVarId {
        let lb = domain.lb();
        let ub = domain.ub();
        let trail_id = self.trail.register_domain(domain);
        let enc_id = self.encoder.register_var(lb, ub);
        debug_assert_eq!(trail_id, enc_id, "trail and encoder must agree on var ids");
        self.var_names.push(name.map(String::from));
        trail_id
    }

    /// Add a Boolean variable (domain {0, 1}).
    pub fn new_bool_var(&mut self, name: Option<&str>) -> IntVarId {
        self.new_int_var(crate::domain::Domain::new(0, 1), name)
    }

    /// Add a constraint to the model.
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Return the initial domain bounds (lb, ub) for a variable.
    pub fn var_bounds(&self, var: IntVarId) -> (i64, i64) {
        self.encoder.var_bounds(var)
    }

    /// Pre-compile constraints into SAT clauses and propagators.
    ///
    /// Call this **before** `set_timeout()` so that encoding overhead
    /// (AllDifferent pattern detection, constraint compilation, and
    /// order-encoding literal allocation) does not consume the solve budget.
    ///
    /// This is idempotent: calling it multiple times has no effect if no
    /// new constraints were added. `solve()` also calls these internally,
    /// so calling `pre_compile()` is optional — it only matters when you
    /// want compilation to happen outside the timed window.
    ///
    /// Returns `false` without compiling when dense order encoding would
    /// exceed its resource-safety limit. Use [`try_pre_compile`](Self::try_pre_compile)
    /// to retain the typed failure reason.
    pub fn pre_compile(&mut self) -> bool {
        self.try_pre_compile().is_ok()
    }

    /// Typed, fallible form of [`pre_compile`](Self::pre_compile).
    pub fn try_pre_compile(&mut self) -> Result<(), crate::encoder::OrderEncodingCapacityError> {
        if self.permanently_inconsistent {
            return Ok(());
        }
        // Run this before compilation because some constraint compilers inspect
        // or enumerate domains. Compilation can introduce auxiliary variables,
        // so re-check before allocating the dense encoding as well.
        self.prepare_domain_holes()?;
        self.detect_alldifferent();
        self.detect_shifted_alldifferent();
        #[cfg(debug_assertions)]
        self.debug_constraints
            .extend(self.constraints.iter().cloned());
        self.compile_constraints();
        self.prepare_domain_holes()?;
        self.encoder.try_pre_allocate_all(&mut self.sat)?;
        Ok(())
    }

    /// Capacity-check all domains, then encode sparse holes for variables not
    /// seen by an earlier preflight. The plan bounds total materialization
    /// before `missing_values()` or SAT clauses are allocated.
    fn prepare_domain_holes(&mut self) -> Result<(), crate::encoder::OrderEncodingCapacityError> {
        self.encoder.preallocation_plan()?;
        let registered = self.trail.num_vars();
        for index in self.domain_holes_encoded..registered {
            let var = IntVarId(index as u32);
            for value in self.trail.missing_values(var) {
                self.encoder.forbid_value(&mut self.sat, var, value);
            }
        }
        self.domain_holes_encoded = registered;
        Ok(())
    }

    /// Record a contradiction introduced by a permanent incremental
    /// constraint. All subsequent solve variants return UNSAT before encoding.
    pub(super) fn mark_permanently_inconsistent(&mut self) {
        self.permanently_inconsistent = true;
    }

    // solve, apply_root_propagation, solve_pure_sat, solve_with_cp_extension,
    // add_propagator, propagate_all, extract_assignment, solve_pure_sat_only,
    // debug_dump_unit_clauses, debug_clause_counts, clear_learned_clauses
    // extracted to solve.rs
}

impl Default for CpSatEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_incremental;
