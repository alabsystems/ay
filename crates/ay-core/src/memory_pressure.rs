// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-cutting memory-pressure observer.
//!
//! Ports the Z3 `memory::above_high_watermark` idea
//! (`reference/z3/src/util/memory_manager.cpp:127-137`) and the CaDiCaL
//! `lim.reduce` ladder (`reference/cadical/src/reduce.cpp:88-163`) onto
//! AY's portfolio/engine model.
//!
//! Design reference: the development design notes §2.
//!
//! # Philosophy
//!
//! Memory pressure is a **cross-cutting signal**, not an eviction policy.
//! This module owns only the signal (RSS, budget, band). Individual
//! subsystems (TermStore compaction, PDR lemma GC, MustSummaries LRU,
//! ProofManager live-id bitmap) read the band and choose their own
//! reclamation intensity.
//!
//! The observer never evicts, caps, compacts, or disables anything. It
//! never returns a hard failure. Its one guarantee is: on the **Red** band,
//! callers can choose to gracefully abort with `Outcome::RedAbort`, which
//! carries enough data to construct a `SolveResult::Unknown` equivalent.
//!
//! # Bands
//!
//! Mirrors CaDiCaL's four-level ladder with hysteresis to prevent flapping:
//!
//! | Band   | Enter at (rss/budget) | Exit toward Green at |
//! |--------|-----------------------|----------------------|
//! | Green  | `< 0.50`              | —                    |
//! | Yellow | `≥ 0.50`              | `< 0.45`             |
//! | Orange | `≥ 0.70`              | `< 0.65`             |
//! | Red    | `≥ 0.85`              | `< 0.80`             |
//!
//! Exit thresholds are 5 percentage points below the entry thresholds — the
//! same geometric hysteresis pattern as CaDiCaL's `inc.flush *= flushfactor`
//! (`reduce.cpp:262-264`).
//!
//! # Budget
//!
//! `budget()` returns the effective cap in bytes:
//!
//! ```text
//! budget = min(process_rlimit, system_available * 0.75)
//! ```
//!
//! See `ay_sys::effective_available_bytes` for the source of truth. When no
//! OS memory data is available at all, budget is `usize::MAX` and the
//! observer stays Green indefinitely.
//!
//! # Usage
//!
//! ```no_run
//! use ay_core::memory_pressure::{MemoryPressure, Band};
//!
//! let mut pressure = MemoryPressure::new();
//! pressure.sample();
//! match pressure.current_band() {
//!     Band::Green | Band::Yellow => { /* keep going */ }
//!     Band::Orange => { /* force reclamation */ }
//!     Band::Red => {
//!         // Return SolveResult::Unknown(UnknownReason::MemoryPressure { ... })
//!         // — never crash.
//!     }
//!     _ => { /* future memory-pressure bands: degrade conservatively */ }
//! }
//! ```
//!
//! This module is observation-only: no subsystem is wired in yet. Callers
//! opt in explicitly.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

// ============================================================================
// Band
// ============================================================================

/// Coarse memory-pressure classification.
///
/// Ordered from lowest to highest pressure so consumers can compare
/// (`band >= Band::Orange`) when scaling reclamation intensity.
///
/// Marked `#[non_exhaustive]` so future additions (e.g., an OS-signalled
/// `Critical` band from macOS `vm_pressure_notification`) do not break
/// downstream match statements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Band {
    /// Normal operation. No forced reclamation.
    Green,
    /// Soft reclamation. Run scheduled GC now instead of deferring.
    Yellow,
    /// Hard reclamation. Evict LRU, compact arenas aggressively.
    Orange,
    /// Emergency. Caller should checkpoint proof and return `Unknown`.
    Red,
}

impl Band {
    /// Human-readable lowercase name (`"green"`, `"yellow"`, ...). Stable
    /// across versions — suitable for `--stats-json` / `--progress` output.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Green => "green",
            Self::Yellow => "yellow",
            Self::Orange => "orange",
            Self::Red => "red",
        }
    }

    /// Is this the emergency band?
    #[inline]
    #[must_use]
    pub const fn is_red(self) -> bool {
        matches!(self, Self::Red)
    }
}

// ============================================================================
// Thresholds
// ============================================================================

/// Pressure thresholds in basis points (1 bp = 0.01%) to avoid floating-point
/// non-determinism. Entry thresholds match the design doc §2.2.
#[derive(Debug, Clone, Copy)]
pub struct BandThresholds {
    /// Enter Yellow when `rss*10000/budget >= yellow_enter_bp`. Default 5000 (50%).
    pub yellow_enter_bp: u32,
    /// Enter Orange when fraction_bp >= orange_enter_bp. Default 7000 (70%).
    pub orange_enter_bp: u32,
    /// Enter Red when fraction_bp >= red_enter_bp. Default 8500 (85%).
    pub red_enter_bp: u32,
    /// Exit hysteresis: on each transition down, the threshold is lower by
    /// `hysteresis_bp` basis points. Default 500 (5%).
    pub hysteresis_bp: u32,
}

impl Default for BandThresholds {
    fn default() -> Self {
        Self {
            yellow_enter_bp: 5000,
            orange_enter_bp: 7000,
            red_enter_bp: 8500,
            hysteresis_bp: 500,
        }
    }
}

impl BandThresholds {
    /// Classify a basis-points fraction into a band, using hysteresis
    /// relative to the previous band. The exit threshold toward a lower
    /// band is `enter_bp - hysteresis_bp`.
    #[inline]
    fn classify(self, fraction_bp: u32, previous: Band) -> Band {
        let hyst = self.hysteresis_bp;
        // Compute exit thresholds (where we step DOWN from the current band).
        let red_exit = self.red_enter_bp.saturating_sub(hyst);
        let orange_exit = self.orange_enter_bp.saturating_sub(hyst);
        let yellow_exit = self.yellow_enter_bp.saturating_sub(hyst);

        match previous {
            Band::Red => {
                if fraction_bp >= red_exit {
                    Band::Red
                } else if fraction_bp >= self.orange_enter_bp {
                    // Still hot enough to be Orange.
                    Band::Orange
                } else if fraction_bp >= self.yellow_enter_bp {
                    Band::Yellow
                } else {
                    Band::Green
                }
            }
            Band::Orange => {
                if fraction_bp >= self.red_enter_bp {
                    Band::Red
                } else if fraction_bp >= orange_exit {
                    Band::Orange
                } else if fraction_bp >= self.yellow_enter_bp {
                    Band::Yellow
                } else {
                    Band::Green
                }
            }
            Band::Yellow => {
                if fraction_bp >= self.red_enter_bp {
                    Band::Red
                } else if fraction_bp >= self.orange_enter_bp {
                    Band::Orange
                } else if fraction_bp >= yellow_exit {
                    Band::Yellow
                } else {
                    Band::Green
                }
            }
            Band::Green => {
                // From Green we always use entry thresholds (no hysteresis
                // in the upward direction — overshoot should engage GC
                // promptly).
                if fraction_bp >= self.red_enter_bp {
                    Band::Red
                } else if fraction_bp >= self.orange_enter_bp {
                    Band::Orange
                } else if fraction_bp >= self.yellow_enter_bp {
                    Band::Yellow
                } else {
                    Band::Green
                }
            }
        }
    }
}

// ============================================================================
// RSS and budget readers (mockable for tests)
// ============================================================================

/// Abstracted source of memory figures. Production wiring uses
/// [`SystemSource`]; tests use [`MockSource`].
pub trait MemorySource: Send + Sync {
    /// Current resident set size of this process in bytes. Returns 0 when
    /// measurement is unavailable (observer treats as "no pressure data").
    fn rss_bytes(&self) -> usize;

    /// Effective budget: `min(rlimit, system_available * 0.75)`. Returns
    /// `usize::MAX` when no figure is available (observer stays Green).
    fn budget_bytes(&self) -> usize;
}

/// Production memory source, delegating to `ay_sys`.
#[derive(Debug, Default, Clone, Copy)]
pub struct SystemSource;

impl MemorySource for SystemSource {
    #[inline]
    fn rss_bytes(&self) -> usize {
        // Use the larger of the OS peak RSS and the exact live-heap-bytes
        // counter maintained by `ay_sys::CountingAllocator` (installed by the
        // `ay` binary). Live bytes reflect a bulk allocation the instant it
        // lands, before `getrusage` peak RSS catches up — so feeding the max
        // into the band classifier makes the Red band (→ graceful `Unknown`)
        // fire on the burst that would otherwise OOM the machine. When no
        // counting allocator is installed (library consumers), live bytes are
        // 0 and this is exactly `current_rss_bytes()`.
        ay_sys::current_rss_bytes().max(ay_sys::current_live_bytes())
    }

    #[inline]
    fn budget_bytes(&self) -> usize {
        let b = ay_sys::effective_available_bytes();
        if b == 0 {
            usize::MAX
        } else {
            b
        }
    }
}

/// Test-only memory source with externally settable RSS and budget.
///
/// Exposed unconditionally (not `#[cfg(test)]`) because downstream crates
/// want to test their own pressure-aware code without pulling in `ay-sys`.
#[derive(Debug, Default)]
pub struct MockSource {
    rss: AtomicUsize,
    budget: AtomicUsize,
}

impl MockSource {
    /// Create a new mock with the given RSS and budget.
    #[must_use]
    pub fn new(rss_bytes: usize, budget_bytes: usize) -> Self {
        Self {
            rss: AtomicUsize::new(rss_bytes),
            budget: AtomicUsize::new(budget_bytes),
        }
    }

    /// Update the mocked RSS (used by tests to drive band transitions).
    pub fn set_rss(&self, bytes: usize) {
        self.rss.store(bytes, Ordering::SeqCst);
    }

    /// Update the mocked budget.
    pub fn set_budget(&self, bytes: usize) {
        self.budget.store(bytes, Ordering::SeqCst);
    }
}

impl MemorySource for MockSource {
    fn rss_bytes(&self) -> usize {
        self.rss.load(Ordering::Relaxed)
    }
    fn budget_bytes(&self) -> usize {
        let b = self.budget.load(Ordering::Relaxed);
        if b == 0 {
            usize::MAX
        } else {
            b
        }
    }
}

// ============================================================================
// Observer trait
// ============================================================================

/// Hook implemented by reclamation schedulers that want band-change
/// callbacks rather than polling `current_band()` every tick.
///
/// Implementations must be non-blocking — they run on the control thread
/// inside `MemoryPressure::sample()`.
pub trait PressureObserver {
    /// Called when a `sample()` call transitions between bands.
    fn on_band_change(&mut self, old: Band, new: Band);
}

// ============================================================================
// MemoryPressure
// ============================================================================

/// Cross-cutting memory-pressure observer.
///
/// One instance per engine (not per thread). Poll via [`Self::sample`] on a
/// natural cadence (e.g., CDCL restart boundary, PDR frame extension, CHC
/// iteration) and read [`Self::current_band`] to scale reclamation.
///
/// **Not wired in yet.** Consumers opt in per-subsystem in follow-up
/// sub-tasks of epic #8599. See the design doc §3 for per-subsystem plans.
pub struct MemoryPressure {
    source: Box<dyn MemorySource>,
    thresholds: BandThresholds,
    /// Last observed band (for hysteresis and change detection).
    current: Band,
    /// Cached RSS from the last `sample()` call, atomic for observer reads.
    last_rss: AtomicUsize,
    /// Cached budget from the last `sample()` call.
    last_budget: AtomicUsize,
    /// Number of samples taken (telemetry).
    sample_count: AtomicU64,
    /// Number of Red-band samples (telemetry).
    red_samples: AtomicU64,
}

impl std::fmt::Debug for MemoryPressure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryPressure")
            .field("current_band", &self.current)
            .field("thresholds", &self.thresholds)
            .field("last_rss", &self.last_rss.load(Ordering::Relaxed))
            .field("last_budget", &self.last_budget.load(Ordering::Relaxed))
            .field("sample_count", &self.sample_count.load(Ordering::Relaxed))
            .field("red_samples", &self.red_samples.load(Ordering::Relaxed))
            .finish_non_exhaustive()
    }
}

impl Default for MemoryPressure {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryPressure {
    /// Construct with the production [`SystemSource`] and default thresholds.
    #[must_use]
    pub fn new() -> Self {
        Self::with_source(Box::new(SystemSource))
    }

    /// Construct with a caller-supplied source (used by tests).
    #[must_use]
    pub fn with_source(source: Box<dyn MemorySource>) -> Self {
        Self {
            source,
            thresholds: BandThresholds::default(),
            current: Band::Green,
            last_rss: AtomicUsize::new(0),
            last_budget: AtomicUsize::new(0),
            sample_count: AtomicU64::new(0),
            red_samples: AtomicU64::new(0),
        }
    }

    /// Construct with custom thresholds (tests and advanced tuning).
    #[must_use]
    pub fn with_thresholds(source: Box<dyn MemorySource>, thresholds: BandThresholds) -> Self {
        let mut mp = Self::with_source(source);
        mp.thresholds = thresholds;
        mp
    }

    /// Read current RSS from the source. Cheap (one syscall via ay-sys).
    #[must_use]
    pub fn read_rss(&self) -> usize {
        self.source.rss_bytes()
    }

    /// Effective budget: `min(rlimit, system_available * 0.75)` in bytes.
    ///
    /// Returns `usize::MAX` when no OS figure is available.
    #[must_use]
    pub fn budget(&self) -> usize {
        self.source.budget_bytes()
    }

    /// Current band, as of the most recent [`Self::sample`] call.
    #[inline]
    #[must_use]
    pub fn current_band(&self) -> Band {
        self.current
    }

    /// Most recently sampled RSS (0 before first `sample()`).
    #[inline]
    #[must_use]
    pub fn last_rss(&self) -> usize {
        self.last_rss.load(Ordering::Relaxed)
    }

    /// Most recently sampled budget (0 before first `sample()`).
    #[inline]
    #[must_use]
    pub fn last_budget(&self) -> usize {
        self.last_budget.load(Ordering::Relaxed)
    }

    /// Number of samples since construction.
    #[inline]
    #[must_use]
    pub fn sample_count(&self) -> u64 {
        self.sample_count.load(Ordering::Relaxed)
    }

    /// Number of Red-band samples since construction.
    #[inline]
    #[must_use]
    pub fn red_samples(&self) -> u64 {
        self.red_samples.load(Ordering::Relaxed)
    }

    /// Take a fresh reading, update the cached band, and return it.
    ///
    /// Notifies `observer` on transitions; pass `&mut ()` for polling-only
    /// callers (the unit impl is a no-op).
    pub fn sample_with(&mut self, observer: &mut dyn PressureObserver) -> Band {
        let rss = self.source.rss_bytes();
        let budget = self.source.budget_bytes();
        self.last_rss.store(rss, Ordering::Relaxed);
        self.last_budget.store(budget, Ordering::Relaxed);
        self.sample_count.fetch_add(1, Ordering::Relaxed);

        let new_band = classify_raw(rss, budget, self.thresholds, self.current);
        if new_band.is_red() {
            self.red_samples.fetch_add(1, Ordering::Relaxed);
        }
        if new_band != self.current {
            let old = self.current;
            self.current = new_band;
            observer.on_band_change(old, new_band);
        }
        new_band
    }

    /// Polling variant — no observer notified. Equivalent to
    /// `self.sample_with(&mut NoopObserver)`.
    pub fn sample(&mut self) -> Band {
        self.sample_with(&mut NoopObserver)
    }

    /// Build the graceful-abort payload for the Red band. Caller packages
    /// this into their crate's `SolveResult::Unknown` equivalent.
    ///
    /// `ay-core` does not depend on `SolveResult`, so the contract here is
    /// just the data tuple. See [`UnknownReason::MemoryPressure`].
    #[must_use]
    pub fn red_abort_reason(&self) -> UnknownReason {
        UnknownReason::MemoryPressure {
            rss_bytes: self.last_rss() as u64,
            budget_bytes: self.last_budget() as u64,
        }
    }
}

/// Observer that ignores all band changes. Used by `sample()`.
struct NoopObserver;
impl PressureObserver for NoopObserver {
    fn on_band_change(&mut self, _old: Band, _new: Band) {}
}

/// Convenience impl so callers can pass `&mut ()` instead of wrapping a
/// struct when they just want polling.
impl PressureObserver for () {
    fn on_band_change(&mut self, _old: Band, _new: Band) {}
}

// ============================================================================
// Classification primitive (pure function — easy to unit-test)
// ============================================================================

/// Compute the band for a given `(rss, budget, thresholds, previous_band)`.
///
/// Exposed for tests. Callers should prefer [`MemoryPressure::sample`] in
/// production.
///
/// When `budget == 0` or `budget == usize::MAX` with zero RSS, the band is
/// Green (no signal = no pressure).
#[must_use]
pub fn classify_raw(
    rss_bytes: usize,
    budget_bytes: usize,
    thresholds: BandThresholds,
    previous: Band,
) -> Band {
    if budget_bytes == 0 || budget_bytes == usize::MAX || rss_bytes == 0 {
        // Stay in `previous` if we had a meaningful previous band; Green
        // otherwise. We specifically do NOT drop Red->Green purely because
        // we lost the signal — that would hide real pressure. Callers with
        // active pressure see it persist until the signal returns.
        return match previous {
            Band::Red | Band::Orange => previous,
            _ => Band::Green,
        };
    }

    // fraction_bp = rss * 10_000 / budget, saturating on overflow.
    // Using u128 intermediate avoids usize overflow at ~18 exabytes on 64-bit.
    let rss_u = rss_bytes as u128;
    let budget_u = budget_bytes as u128;
    let fraction_bp = rss_u
        .saturating_mul(10_000)
        .checked_div(budget_u)
        .unwrap_or(0);
    // Clamp to u32 for classify().
    let fraction_bp_u32 = u32::try_from(fraction_bp).unwrap_or(u32::MAX);
    thresholds.classify(fraction_bp_u32, previous)
}

// ============================================================================
// UnknownReason — cross-cutting enum for "solver returned Unknown because X"
// ============================================================================

/// Reason a solver returned `SolveResult::Unknown` (or equivalent).
///
/// This module defines only the `MemoryPressure` variant. Other variants
/// may be added as other subsystems gain graceful-abort contracts.
///
/// Downstream crates (`ay-sat`, `ay-dpll`, `ay-chc`) adapt this into their
/// own `SolveResult::Unknown(...)` variants; see design doc §4.4 for the
/// `MemoryPressure` contract specifically.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnknownReason {
    /// Red band fired — the engine aborted rather than crash. Both fields
    /// are in bytes; `budget_bytes == u64::MAX` means "no budget figure
    /// was available but the engine aborted for another pressure reason".
    MemoryPressure {
        /// Last-sampled RSS at abort time.
        rss_bytes: u64,
        /// Effective budget at abort time.
        budget_bytes: u64,
    },
}

impl UnknownReason {
    /// Human-readable short name, stable across versions.
    #[must_use]
    pub const fn kind_str(&self) -> &'static str {
        match self {
            Self::MemoryPressure { .. } => "memory_pressure",
        }
    }
}

impl std::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryPressure {
                rss_bytes,
                budget_bytes,
            } => {
                write!(
                    f,
                    "memory pressure (rss={rss_bytes} bytes, budget={budget_bytes} bytes)"
                )
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
#[path = "memory_pressure_tests.rs"]
mod tests;
