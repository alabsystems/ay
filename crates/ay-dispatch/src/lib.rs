// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared engine-dispatch primitives (Part of #8775).
//!
//! `ay-dispatch` is the home for logic that is currently duplicated between
//! `ay-chc`'s adaptive portfolio and `ay-sat`'s parallel portfolio:
//!
//! 1. Extracting *features* from a problem instance (classification input).
//! 2. Selecting an ordered list of *engines* to run based on those features.
//! 3. *Scheduling* those engines across a wall-clock budget.
//! 4. Updating online-learning state (multiplicative-weights / EXP3 bandits)
//!    from per-engine solve outcomes.
//!
//! This crate is deliberately domain-agnostic: it does not know what a CHC or
//! CNF problem looks like, nor what "PDR" or "VsidsLuby" are. Each downstream
//! portfolio implements the small set of traits below for its own
//! feature/engine types, then composes the shared schedulers and bandits on
//! top.
//!
//! # Example
//!
//! ```no_run
//! use std::time::Duration;
//! use ay_dispatch::{
//!     EngineId, ProblemClassifier, ProblemFeatures, EngineSelector,
//!     PortfolioSchedule, FixedOrderSchedule,
//! };
//!
//! # #[derive(Debug, Clone)]
//! # struct MyFeatures { num_vars: usize }
//! # impl ProblemFeatures for MyFeatures {}
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
//! # enum MyEngine { A, B, C }
//! # impl EngineId for MyEngine {}
//! # struct Classifier;
//! # impl ProblemClassifier for Classifier {
//! #     type Features = MyFeatures;
//! #     fn classify(&self, _input: &[u8]) -> MyFeatures { MyFeatures { num_vars: 0 } }
//! # }
//! # struct Selector;
//! # impl EngineSelector for Selector {
//! #     type Features = MyFeatures;
//! #     type Engine = MyEngine;
//! #     fn select(&self, _features: &MyFeatures) -> Vec<MyEngine> {
//! #         vec![MyEngine::A, MyEngine::B]
//! #     }
//! # }
//! let features = Classifier.classify(b"(set-logic QF_LIA)");
//! let engines = Selector.select(&features);
//! let schedule = FixedOrderSchedule::equal_share(engines, Duration::from_secs(30));
//! for (engine, budget) in schedule.next_engines(Duration::ZERO, Duration::from_secs(30)) {
//!     // run `engine` with at most `budget` time
//!     # let _ = (engine, budget);
//! }
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::fmt::Debug;
use std::hash::Hash;
use std::time::Duration;

pub mod bandit;

pub use bandit::{Exp3, MultiplicativeWeights};

// ---------------------------------------------------------------------------
// Core traits
// ---------------------------------------------------------------------------

/// Marker trait for instance-feature vectors.
///
/// Implementors are the output of [`ProblemClassifier::classify`] and the
/// input to [`EngineSelector::select`]. Feature vectors must be cheap to
/// clone so they can be logged, stored alongside decisions, and reused across
/// multiple selectors.
///
/// This trait is intentionally empty: the dispatch crate never inspects
/// feature contents, it only forwards them between classifier and selector.
pub trait ProblemFeatures: Debug + Clone + Send + Sync + 'static {}

/// Marker trait for engine identifiers.
///
/// Implementors are small, copyable tokens such as `EngineType::Pdr` in
/// `ay-chc` or `Strategy::VsidsLuby` in `ay-sat`. The trait bound set is
/// chosen so engine ids can be used as map keys (bandit weights, budget
/// policies) and safely shared between threads.
pub trait EngineId: Debug + Clone + Copy + PartialEq + Eq + Hash + Send + Sync + 'static {}

/// Extract a feature vector from a raw problem encoding.
///
/// The input is the caller's choice of raw bytes (SMT-LIB source, DIMACS,
/// serialised IR). Implementors are expected to run in `O(|input|)` so
/// classification does not dominate the overall solve budget.
pub trait ProblemClassifier {
    /// Feature vector produced by this classifier.
    type Features: ProblemFeatures;

    /// Run feature extraction on `input`.
    fn classify(&self, input: &[u8]) -> Self::Features;
}

/// Pick an ordered list of engines to try for a given feature vector.
///
/// The returned vector is in *priority order* (first engine is attempted
/// first). Selectors should not allocate time budgets themselves — that is
/// the scheduler's job — and should not make assumptions about how many
/// engines will actually run.
pub trait EngineSelector {
    /// Feature-vector type accepted by this selector.
    type Features: ProblemFeatures;
    /// Engine id type produced by this selector.
    type Engine: EngineId;

    /// Return engines in priority order.
    fn select(&self, features: &Self::Features) -> Vec<Self::Engine>;
}

/// Allocate per-engine time budgets across a wall-clock window.
///
/// A schedule is queried once per "dispatch tick" — typically once at the
/// start of a solve attempt, and then again whenever an engine returns
/// without a definitive answer. The caller passes in the elapsed time since
/// the portfolio started and the total remaining budget; the schedule
/// returns zero-or-more `(engine, budget)` pairs to run next.
///
/// Returning an empty vector means "nothing more to try"; returning a single
/// pair means "run this engine next for up to `budget`"; returning several
/// pairs means "launch these engines in parallel for up to the given
/// budgets".
pub trait PortfolioSchedule<E: EngineId> {
    /// Compute the next batch of engine launches.
    ///
    /// * `elapsed` - total wall-clock elapsed since the portfolio started.
    /// * `remaining` - total remaining budget, `Duration::ZERO` = unlimited.
    fn next_engines(&self, elapsed: Duration, remaining: Duration) -> Vec<(E, Duration)>;
}

// ---------------------------------------------------------------------------
// Feedback / reward hooks
// ---------------------------------------------------------------------------

/// Outcome of a single engine run, suitable for feeding back into a bandit.
///
/// The shared crate does not prescribe a reward function; downstream
/// portfolios construct rewards from their own telemetry (solve success,
/// elapsed time, lemma quality). This struct only carries the inputs the
/// generic bandits need.
#[derive(Debug, Clone, Copy)]
pub struct EngineFeedback<E: EngineId> {
    /// Which engine produced this outcome.
    pub engine: E,
    /// Wall-clock time consumed by this engine.
    pub elapsed: Duration,
    /// Reward in `[0.0, 1.0]`. 1.0 = best possible outcome (e.g., solved the
    /// instance quickly), 0.0 = no useful progress. Callers clamp as needed.
    pub reward: f64,
}

// ---------------------------------------------------------------------------
// Fixed-order schedule (simple equal-share / weighted reference impl)
// ---------------------------------------------------------------------------

/// Fixed-order schedule that hands out engines sequentially.
///
/// Used as a reference implementation of [`PortfolioSchedule`] and as a sane
/// default when the caller has no bandit state yet. Two construction modes:
///
/// * [`FixedOrderSchedule::equal_share`] splits the total budget evenly
///   across the given engines.
/// * [`FixedOrderSchedule::weighted`] takes an explicit `(engine, weight)`
///   list and distributes the total budget proportionally (weights are
///   normalised internally; all-zero weights fall back to equal share).
#[derive(Debug, Clone)]
pub struct FixedOrderSchedule<E: EngineId> {
    entries: Vec<(E, Duration)>,
}

impl<E: EngineId> FixedOrderSchedule<E> {
    /// Build a schedule that gives every engine the same slice of `total`.
    ///
    /// If `engines` is empty the schedule is empty. If `total` is zero every
    /// engine gets `Duration::ZERO` (which downstream schedulers interpret as
    /// "run without an internal deadline").
    #[must_use]
    pub fn equal_share(engines: Vec<E>, total: Duration) -> Self {
        if engines.is_empty() {
            return Self {
                entries: Vec::new(),
            };
        }
        let per = if total.is_zero() {
            Duration::ZERO
        } else {
            total / u32::try_from(engines.len()).unwrap_or(u32::MAX)
        };
        let entries = engines.into_iter().map(|e| (e, per)).collect();
        Self { entries }
    }

    /// Build a schedule from explicit `(engine, weight)` pairs.
    ///
    /// Weights are normalised to `1.0`. Negative weights are clamped to zero.
    /// If all weights are zero the allocation falls back to equal share.
    #[must_use]
    pub fn weighted(weights: Vec<(E, f64)>, total: Duration) -> Self {
        if weights.is_empty() {
            return Self {
                entries: Vec::new(),
            };
        }
        let clamped: Vec<(E, f64)> = weights
            .into_iter()
            .map(|(e, w)| (e, if w.is_finite() && w > 0.0 { w } else { 0.0 }))
            .collect();
        let sum: f64 = clamped.iter().map(|(_, w)| w).sum();
        if sum <= 0.0 || total.is_zero() {
            let engines: Vec<E> = clamped.into_iter().map(|(e, _)| e).collect();
            return Self::equal_share(engines, total);
        }
        let total_secs = total.as_secs_f64();
        let entries = clamped
            .into_iter()
            .map(|(e, w)| (e, Duration::from_secs_f64(total_secs * (w / sum))))
            .collect();
        Self { entries }
    }

    /// Access the raw `(engine, budget)` entries in priority order.
    #[must_use]
    pub fn entries(&self) -> &[(E, Duration)] {
        &self.entries
    }
}

impl<E: EngineId> PortfolioSchedule<E> for FixedOrderSchedule<E> {
    fn next_engines(&self, _elapsed: Duration, _remaining: Duration) -> Vec<(E, Duration)> {
        self.entries.clone()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum E {
        A,
        B,
        C,
    }

    impl EngineId for E {}

    #[test]
    fn equal_share_splits_evenly() {
        let s = FixedOrderSchedule::equal_share(vec![E::A, E::B, E::C], Duration::from_secs(30));
        let entries = s.next_engines(Duration::ZERO, Duration::from_secs(30));
        assert_eq!(entries.len(), 3);
        for (_, d) in &entries {
            assert_eq!(*d, Duration::from_secs(10));
        }
    }

    #[test]
    fn equal_share_zero_total_returns_zero_budgets() {
        let s = FixedOrderSchedule::equal_share(vec![E::A, E::B], Duration::ZERO);
        let entries = s.next_engines(Duration::ZERO, Duration::ZERO);
        assert_eq!(entries.len(), 2);
        for (_, d) in &entries {
            assert!(d.is_zero());
        }
    }

    #[test]
    fn weighted_respects_weights() {
        let s =
            FixedOrderSchedule::weighted(vec![(E::A, 1.0), (E::B, 3.0)], Duration::from_secs(40));
        let entries = s.next_engines(Duration::ZERO, Duration::from_secs(40));
        assert_eq!(entries.len(), 2);
        // 25% / 75% split.
        assert!(entries[0].1 >= Duration::from_secs(9));
        assert!(entries[0].1 <= Duration::from_secs(11));
        assert!(entries[1].1 >= Duration::from_secs(29));
        assert!(entries[1].1 <= Duration::from_secs(31));
    }

    #[test]
    fn weighted_all_zero_falls_back_to_equal_share() {
        let s =
            FixedOrderSchedule::weighted(vec![(E::A, 0.0), (E::B, 0.0)], Duration::from_secs(20));
        let entries = s.next_engines(Duration::ZERO, Duration::from_secs(20));
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].1, Duration::from_secs(10));
        assert_eq!(entries[1].1, Duration::from_secs(10));
    }
}
