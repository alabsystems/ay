// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Programmatic progress callback trait for AI consumers.
//!
//! The `SolveObserver` trait provides zero-cost callbacks for monitoring
//! SAT/SMT solver progress. When no observer is registered, all callback
//! sites compile to a single `Option::is_some()` check that the branch
//! predictor eliminates.
//!
//! Designed for AI orchestration tools (model-checker-consumer, deductive-checks, verification-consumer) that need
//! programmatic stall detection and timeout decisions instead of stderr
//! progress lines.
//!
//! # Example
//!
//! ```rust
//! use ay_sat::observer::{SolveObserver, ProgressStats};
//! use std::sync::atomic::{AtomicU64, Ordering};
//! use std::sync::Arc;
//!
//! struct ConflictCounter(Arc<AtomicU64>);
//!
//! impl SolveObserver for ConflictCounter {
//!     fn on_conflict(&mut self, _stats: &ProgressStats) {
//!         self.0.fetch_add(1, Ordering::Relaxed);
//!     }
//! }
//! ```

/// Snapshot of solver progress at the time of a callback.
///
/// All fields are cheap copies (u64/bool). The struct is `#[non_exhaustive]`
/// so new fields can be added without breaking downstream consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ProgressStats {
    /// Total number of conflicts so far.
    pub conflicts: u64,
    /// Total number of decisions so far.
    pub decisions: u64,
    /// Total number of unit propagations so far.
    pub propagations: u64,
    /// Total number of restarts so far.
    pub restarts: u64,
    /// Whether the solver is in stable mode (true) or focused mode (false).
    pub stable_mode: bool,
    /// Current decision level.
    pub decision_level: u32,
}

/// Identifies the inprocessing technique that just ran.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InprocessingTechnique {
    /// Vivification (clause strengthening via propagation).
    Vivify,
    /// Forward subsumption.
    Subsume,
    /// Bounded variable elimination.
    Bve,
    /// Blocked clause elimination.
    Bce,
    /// Failed-literal probing.
    Probe,
    /// Hyper-ternary resolution.
    Htr,
    /// Congruence closure.
    Congruence,
    /// SAT sweeping.
    Sweep,
    /// Backbone detection.
    Backbone,
    /// Transitive reduction.
    TransRed,
    /// SCC decomposition.
    Decompose,
    /// Gate extraction / factoring.
    Factor,
    /// Conditioning (root-satisfied clause GC).
    Condition,
    /// Covered clause elimination.
    Cce,
    /// Clause-weighted reorder.
    Reorder,
}

impl InprocessingTechnique {
    /// Map from the internal pass name strings used by the inprocessing
    /// pipeline to the public enum variant.
    #[must_use]
    pub fn from_pass_name(name: &str) -> Option<Self> {
        match name {
            "vivify" | "vivify_irred" => Some(Self::Vivify),
            "subsume" => Some(Self::Subsume),
            "bve" => Some(Self::Bve),
            "bce" => Some(Self::Bce),
            "cce" => Some(Self::Cce),
            "probe" | "intree" => Some(Self::Probe),
            "htr" => Some(Self::Htr),
            "congruence" => Some(Self::Congruence),
            "sweep" => Some(Self::Sweep),
            "backbone" => Some(Self::Backbone),
            "transred" => Some(Self::TransRed),
            "decompose" => Some(Self::Decompose),
            "factor" => Some(Self::Factor),
            "condition" => Some(Self::Condition),
            "reorder" => Some(Self::Reorder),
            _ => None,
        }
    }
}

/// Programmatic progress callback trait for SAT solver events.
///
/// All methods have default no-op implementations. Consumers override
/// only the events they care about.
///
/// # Zero-cost guarantee
///
/// When no observer is registered (`Option<Box<dyn SolveObserver>>` is `None`),
/// each call site is a single branch on the `Option` discriminant. The branch
/// predictor learns this quickly, making the overhead unmeasurable.
///
/// # Thread safety
///
/// The observer is `&mut self` (exclusive access). It is called from the
/// solver's single-threaded CDCL loop. If you need to share data with other
/// threads, use interior mutability (`Arc<AtomicU64>`, channels, etc.) inside
/// your observer implementation. Observers must be `Send` so solvers can be
/// moved into worker threads when used by downstream verification tools.
pub trait SolveObserver: Send {
    /// Called after every conflict (high frequency: thousands per second).
    ///
    /// Use this sparingly for stall detection. Implementations should be
    /// O(1) and avoid any I/O. For periodic reporting, check
    /// `stats.conflicts % N == 0` inside the callback.
    fn on_conflict(&mut self, _stats: &ProgressStats) {}

    /// Called after every restart.
    ///
    /// Lower frequency than conflicts. Good for tracking search phase changes
    /// and computing restart rates.
    fn on_restart(&mut self, _stats: &ProgressStats) {}

    /// Called periodically (approximately every 5 seconds wall-clock).
    ///
    /// This fires at the same cadence as the `--progress` stderr output.
    /// Suitable for UI updates and timeout decisions.
    fn on_progress(&mut self, _stats: &ProgressStats) {}

    /// Called after each inprocessing round completes.
    ///
    /// `simplifications` is the number of clause/variable reductions achieved
    /// in this round.
    fn on_inprocessing(&mut self, _technique: InprocessingTechnique, _simplifications: u64) {}

    /// Called after a clause is learned from conflict analysis.
    ///
    /// `clause_len` is the number of literals in the learned clause.
    /// `lbd` is the Literal Block Distance (glue level) — lower LBD indicates
    /// higher quality clauses. This fires at the same frequency as conflicts.
    fn on_learn(&mut self, _clause_len: u32, _lbd: u32) {}

    /// Called when a theory conflict is detected (DPLL(T) only).
    ///
    /// `theory` identifies which theory produced the conflict. This does not
    /// fire for pure SAT conflicts — only for conflicts originating from
    /// the theory solver layer (LIA, LRA, BV, EUF, etc.).
    fn on_theory_conflict(&mut self, _theory: TheoryId) {}
}

/// Identifies the theory that produced a conflict or propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TheoryId {
    /// Linear integer arithmetic.
    Lia,
    /// Linear real arithmetic.
    Lra,
    /// Bit-vectors.
    Bv,
    /// Equality and uninterpreted functions.
    Euf,
    /// Arrays.
    Arrays,
    /// Strings.
    Strings,
    /// Datatypes.
    Datatypes,
    /// Floating-point.
    Fp,
    /// Combined/Nelson-Oppen theory.
    Combined,
    /// Unknown or unclassified theory.
    Other,
}
