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
    /// A known solution to check propagator clauses against (debug aid, see
    /// [`CpSatEngine::set_witness`]).
    witness: Option<Arc<extension::Witness>>,
    /// Process memory this engine may plan with (see
    /// [`CpSatEngine::set_memory_budget`]); taken when the first search
    /// starts.
    memory_budget: Option<usize>,
    /// The clause-database ceiling installed from `memory_budget`.
    clause_db_ceiling: Option<usize>,
}

/// Peak bytes one dense order literal costs (SAT variable, ordering clause and
/// its watches, the encoder's maps while it allocates). Measured with
/// `ay flatzinc solve` on one variable: 2,000,001 values 1,539 MB resident,
/// 8,000,001 values 6,013 MB (about 750 bytes each).
pub const ORDER_LITERAL_BYTES: usize = 800;

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
        // The engine writes no proof and no clause trace, so nothing reads the
        // SAT core's clause-ID table. That table is indexed by arena word (8
        // bytes per word, twice the arena), and propagator explanations are
        // long: on MiniZinc `orthorio/challenge_04` it held 2,148 MB of a
        // 2,927 MB clause database (726 MB arena) after 8 s.
        sat.set_clause_ids_disabled(true);
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
            witness: None,
            memory_budget: None,
            clause_db_ceiling: None,
        }
    }

    /// Bound the SAT core's clause database by a share of `process_bytes`,
    /// the memory this engine may use (`0`: no bound, the default).
    ///
    /// Every bound change a propagator makes is handed to the SAT core with
    /// its explanation clause, and those clauses stay until a reduction
    /// deletes them. Without a ceiling the database grows until the process
    /// is killed (MiniZinc `orthorio/challenge_04`: 16 GB in 37 s). The
    /// ceiling is installed when the first search starts, after compilation,
    /// so that its floor covers the compiled model.
    ///
    /// The same budget sizes the dense order encoding: up to half of it, at
    /// [`ORDER_LITERAL_BYTES`] each, and never fewer literals than the
    /// default [`MAX_PREALLOCATED_ORDER_LITERALS`](crate::encoder::MAX_PREALLOCATED_ORDER_LITERALS).
    /// Call it before the first compilation.
    pub fn set_memory_budget(&mut self, process_bytes: usize) {
        self.memory_budget = (process_bytes > 0).then_some(process_bytes);
        let default = crate::encoder::MAX_PREALLOCATED_ORDER_LITERALS;
        let scaled = (process_bytes / 2 / ORDER_LITERAL_BYTES) as u128;
        self.encoder.set_literal_limit(scaled.max(default));
    }

    /// The clause-database ceiling installed from
    /// [`set_memory_budget`](Self::set_memory_budget), once a search started.
    pub fn clause_db_ceiling(&self) -> Option<usize> {
        self.clause_db_ceiling
    }

    /// Test hook: install a clause-database byte limit on the SAT core
    /// directly, below the floor `set_memory_budget` keeps (the loaded
    /// formula plus 64 MB of headroom), so that tests on small models make
    /// the clause-DB limit reductions fire.
    #[cfg(test)]
    pub(crate) fn set_clause_db_limit_for_tests(&mut self, bytes: usize) {
        self.sat.set_max_clause_db_bytes(Some(bytes));
    }

    /// Debug aid: check every clause a propagator hands to the SAT core
    /// against a known solution of the model.
    ///
    /// Each propagation reason and conflict clause is learned for good, so
    /// it must hold in every solution. When `values` assigns all variables
    /// of such a clause and falsifies every literal, the engine reports the
    /// propagator and the clause on stderr: either that propagator's
    /// inference or explanation is unsound, or `values` is not a solution.
    /// Variables missing from `values` and not fixed in their root domain
    /// make a clause unknown: never reported, but counted (see
    /// [`CpSatEngine::witness_counts`]; the count is printed when a solve
    /// ends without a solution). Clauses the encoders add before search are
    /// checked too, when the witness is set before the first solve; the
    /// encoders give their auxiliary variables (`Diffn` separation
    /// indicators, `Circuit` positions) the values the witness determines.
    /// Checking changes no search decision.
    pub fn set_witness(&mut self, values: &[(IntVarId, i64)]) {
        let mut known = vec![None; self.encoder.num_vars()];
        for &(var, value) in values {
            if let Some(slot) = known.get_mut(var.index()) {
                *slot = Some(value);
            }
        }
        let names = (0..self.encoder.num_vars())
            .map(|i| {
                self.var_names
                    .get(i)
                    .and_then(Clone::clone)
                    .unwrap_or_else(|| format!("v{i}"))
            })
            .collect();
        self.witness = Some(Arc::new(extension::Witness::new(known, names)));
    }

    /// Clause counts of the witness check so far: `(checked, falsified,
    /// unknown)`, `None` without a witness.
    pub fn witness_counts(&self) -> Option<(usize, usize, usize)> {
        self.witness.as_ref().map(|w| w.counts())
    }

    /// The witness value of `var`, if a witness is set and determines it.
    pub(super) fn witness_value(&self, var: IntVarId) -> Option<i64> {
        self.witness.as_ref()?.value(&self.encoder, var)
    }

    /// Give an auxiliary variable an encoder created its witness value, so
    /// that clauses over it are checked instead of counted unknown.
    pub(super) fn witness_define(&mut self, var: IntVarId, value: Option<i64>, name: &str) {
        if let Some(witness) = self.witness.as_mut().and_then(Arc::get_mut) {
            witness.define(var, value, name.to_string());
        }
    }

    /// Add a clause of the model's encoding to the SAT core, checking it
    /// against the witness first when one is set.
    pub(super) fn add_model_clause(&mut self, origin: &str, clause: Vec<ay_sat::Literal>) {
        if let Some(witness) = &self.witness {
            witness.check_clause(&self.encoder, origin, "encoding", &clause);
        }
        self.sat.add_clause(clause);
    }

    /// Print the witness summary (when a solve ends without a solution).
    pub(super) fn report_witness(&self) {
        if let Some(witness) = &self.witness {
            eprintln!("{}", witness.summary());
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

    /// The smallest value in any of `vars`' current domains (0 for none).
    fn smallest_domain_value(&self, vars: &[IntVarId]) -> i64 {
        vars.iter()
            .map(|&v| self.encoder.var_bounds(v).0)
            .min()
            .unwrap_or(0)
    }

    /// A [`Constraint::Circuit`] numbered by the rule the variant followed
    /// before 2026-11-19: the nodes start at the smallest value in any
    /// successor's domain, read now. Prefer the variant with the array's
    /// index base (FlatZinc: the index set), whose meaning does not depend
    /// on the domains: a successor domain that cannot take the first node
    /// shifts this numbering.
    pub fn circuit_numbered_by_domains(&self, succ: Vec<IntVarId>) -> Constraint {
        let base = self.smallest_domain_value(&succ);
        Constraint::Circuit { succ, base }
    }

    /// A [`Constraint::Inverse`] numbered by the rule the variant followed
    /// before 2026-11-19: each array's values start at the smallest value in
    /// any of its domains, read now. Prefer the variant with explicit bases
    /// (see [`Self::circuit_numbered_by_domains`]).
    pub fn inverse_numbered_by_domains(&self, x: Vec<IntVarId>, y: Vec<IntVarId>) -> Constraint {
        let base_x = self.smallest_domain_value(&x);
        let base_y = self.smallest_domain_value(&y);
        Constraint::Inverse {
            x,
            y,
            base_x,
            base_y,
        }
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
mod tests_branching;
#[cfg(test)]
mod tests_brute_force;
#[cfg(test)]
mod tests_disjunctive;
#[cfg(test)]
mod tests_endpoints;
#[cfg(test)]
mod tests_incremental;
#[cfg(test)]
mod tests_memory;
#[cfg(test)]
mod tests_witness;
