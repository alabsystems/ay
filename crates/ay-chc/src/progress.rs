// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC engine-level progress reporting (#8155 task 7c).
//!
//! Provides `ChcProgressSink` trait for structured progress callbacks and
//! [`ChcProgressSnapshot`] for a thread-safe progress state that engines
//! update and observers query.
//!
//! The progress model is pull-based: engines update an `Arc<ChcProgressSnapshot>`
//! at natural checkpoints (after each PDR iteration, after BMC unrolling, etc.),
//! and the progress thread reads the latest state on its 5-second cadence.
//! This avoids requiring engines to know about observers and keeps the
//! coupling minimal.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;

/// Snapshot of CHC solver progress, updated by engines and read by observers.
///
/// All fields use atomics or `Mutex` for lock-free reads from the progress
/// thread. Engines call `update_*` methods; the progress thread calls
/// `snapshot()` to get a consistent read.
pub struct ChcProgressSnapshot {
    /// Name of the currently active engine (e.g., "PDR", "BMC", "Kind").
    engine_name: Mutex<String>,
    /// Current PDR frame depth (0 if engine does not use frames).
    frame_count: AtomicU64,
    /// Total lemmas learned across all frames.
    lemma_count: AtomicU64,
    /// Number of predicates that have converged (fixpoint reached).
    predicates_converged: AtomicU64,
    /// Total number of predicates in the problem.
    predicates_total: AtomicU64,
    /// Whether the portfolio has switched engines at least once.
    engine_switched: AtomicBool,
    /// Index of the active engine in the portfolio (0-based).
    active_engine_idx: AtomicU64,
}

/// A read-only snapshot of CHC progress for formatting/reporting.
#[derive(Debug, Clone)]
pub struct ChcProgressReport {
    /// Name of the currently active engine.
    pub engine_name: String,
    /// Current PDR frame depth.
    pub frame_count: u64,
    /// Total lemmas learned.
    pub lemma_count: u64,
    /// Number of converged predicates.
    pub predicates_converged: u64,
    /// Total predicates.
    pub predicates_total: u64,
    /// Whether the portfolio has switched engines.
    pub engine_switched: bool,
    /// Index of the active engine.
    pub active_engine_idx: u64,
}

impl std::fmt::Debug for ChcProgressSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let engine_name = self
            .engine_name
            .lock()
            .map(|name| name.clone())
            .unwrap_or_else(|_| String::from("<poisoned>"));
        f.debug_struct("ChcProgressSnapshot")
            .field("engine_name", &engine_name)
            .field("frame_count", &self.frame_count.load(Ordering::Relaxed))
            .field("lemma_count", &self.lemma_count.load(Ordering::Relaxed))
            .field(
                "predicates_converged",
                &self.predicates_converged.load(Ordering::Relaxed),
            )
            .field(
                "predicates_total",
                &self.predicates_total.load(Ordering::Relaxed),
            )
            .field(
                "engine_switched",
                &self.engine_switched.load(Ordering::Relaxed),
            )
            .field(
                "active_engine_idx",
                &self.active_engine_idx.load(Ordering::Relaxed),
            )
            .finish()
    }
}

impl ChcProgressSnapshot {
    /// Create a new progress snapshot with initial problem metadata.
    pub fn new(predicates_total: u64) -> Self {
        Self {
            engine_name: Mutex::new(String::from("initializing")),
            frame_count: AtomicU64::new(0),
            lemma_count: AtomicU64::new(0),
            predicates_converged: AtomicU64::new(0),
            predicates_total: AtomicU64::new(predicates_total),
            engine_switched: AtomicBool::new(false),
            active_engine_idx: AtomicU64::new(0),
        }
    }

    /// Update the active engine name and index.
    pub fn set_active_engine(&self, name: &str, idx: usize) {
        if let Ok(mut guard) = self.engine_name.lock() {
            let prev = guard.clone();
            guard.clear();
            guard.push_str(name);
            // Mark engine switch if name changed from a non-init value.
            if prev != "initializing" && prev != name {
                self.engine_switched.store(true, Ordering::Relaxed);
            }
        }
        self.active_engine_idx.store(idx as u64, Ordering::Relaxed);
    }

    /// Update frame and lemma counts (called by PDR engines).
    pub fn update_pdr_progress(&self, frames: u64, lemmas: u64) {
        self.frame_count.store(frames, Ordering::Relaxed);
        self.lemma_count.store(lemmas, Ordering::Relaxed);
    }

    /// Update predicate convergence count.
    pub fn update_convergence(&self, converged: u64) {
        self.predicates_converged
            .store(converged, Ordering::Relaxed);
    }

    /// Read a consistent snapshot for reporting.
    pub fn snapshot(&self) -> ChcProgressReport {
        let engine_name = self
            .engine_name
            .lock()
            .map(|g| g.clone())
            .unwrap_or_else(|_| String::from("unknown"));
        ChcProgressReport {
            engine_name,
            frame_count: self.frame_count.load(Ordering::Relaxed),
            lemma_count: self.lemma_count.load(Ordering::Relaxed),
            predicates_converged: self.predicates_converged.load(Ordering::Relaxed),
            predicates_total: self.predicates_total.load(Ordering::Relaxed),
            engine_switched: self.engine_switched.load(Ordering::Relaxed),
            active_engine_idx: self.active_engine_idx.load(Ordering::Relaxed),
        }
    }
}

impl ChcProgressReport {
    /// Format as a human-readable progress line in DIMACS comment style.
    ///
    /// Example outputs:
    /// - `c [5.0s] PDR: frame=12, lemmas=847, predicates=3/3 converged`
    /// - `c [10.0s] BMC: unrolling depth=frame_count`
    /// - `c [15.0s] Portfolio: switched to Kind (engine 2)`
    pub fn format_line(&self, elapsed_secs: f64) -> String {
        let pred_info = if self.predicates_total > 0 {
            format!(
                ", predicates={}/{}",
                self.predicates_converged, self.predicates_total
            )
        } else {
            String::new()
        };

        let rss_str = format_rss_field();
        if self.engine_switched {
            format!(
                "c [{elapsed_secs:.1}s] {}: frame={}, lemmas={}{pred_info} (switched) {rss_str}",
                self.engine_name, self.frame_count, self.lemma_count,
            )
        } else {
            format!(
                "c [{elapsed_secs:.1}s] {}: frame={}, lemmas={}{pred_info} {rss_str}",
                self.engine_name, self.frame_count, self.lemma_count,
            )
        }
    }
}

/// Format the RSS field for progress line output (#8641).
///
/// Returns `rss=<N>MB` normally. When a process memory limit is configured
/// and current RSS exceeds 80% of it, returns `rss=<USED>/<LIMIT>(<PCT>%)`
/// with human-friendly GB units.
fn format_rss_field() -> String {
    let rss_bytes = ay_sys::current_rss_bytes();
    let limit = ay_sys::get_process_memory_limit();
    if limit > 0 {
        let pct = (rss_bytes as u64 * 100) / limit as u64;
        if pct > 80 {
            return format!(
                "rss={:.1}GB/{:.1}GB({}%)",
                rss_bytes as f64 / (1024.0 * 1024.0 * 1024.0),
                limit as f64 / (1024.0 * 1024.0 * 1024.0),
                pct,
            );
        }
    }
    let rss_mb = rss_bytes / (1024 * 1024);
    format!("rss={rss_mb}MB")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_progress_snapshot_initial_state() {
        let snap = ChcProgressSnapshot::new(5);
        let report = snap.snapshot();
        assert_eq!(report.engine_name, "initializing");
        assert_eq!(report.frame_count, 0);
        assert_eq!(report.lemma_count, 0);
        assert_eq!(report.predicates_total, 5);
        assert!(!report.engine_switched);
    }

    #[test]
    fn test_progress_snapshot_pdr_update() {
        let snap = ChcProgressSnapshot::new(3);
        snap.set_active_engine("PDR", 0);
        snap.update_pdr_progress(12, 847);
        snap.update_convergence(2);

        let report = snap.snapshot();
        assert_eq!(report.engine_name, "PDR");
        assert_eq!(report.frame_count, 12);
        assert_eq!(report.lemma_count, 847);
        assert_eq!(report.predicates_converged, 2);
        assert_eq!(report.predicates_total, 3);
    }

    #[test]
    fn test_progress_snapshot_engine_switch() {
        let snap = ChcProgressSnapshot::new(1);
        snap.set_active_engine("PDR", 0);
        assert!(!snap.snapshot().engine_switched);

        snap.set_active_engine("Kind", 2);
        assert!(snap.snapshot().engine_switched);
        assert_eq!(snap.snapshot().engine_name, "Kind");
        assert_eq!(snap.snapshot().active_engine_idx, 2);
    }

    #[test]
    fn test_progress_report_format() {
        let report = ChcProgressReport {
            engine_name: "PDR".to_string(),
            frame_count: 12,
            lemma_count: 847,
            predicates_converged: 3,
            predicates_total: 3,
            engine_switched: false,
            active_engine_idx: 0,
        };
        let line = report.format_line(5.0);
        assert!(line.contains("PDR"));
        assert!(line.contains("frame=12"));
        assert!(line.contains("lemmas=847"));
        assert!(line.contains("predicates=3/3"));
        assert!(!line.contains("switched"));
        assert!(
            line.contains("rss="),
            "Progress line must contain rss= (#8641)"
        );
    }

    #[test]
    fn test_progress_report_format_with_switch() {
        let report = ChcProgressReport {
            engine_name: "Kind".to_string(),
            frame_count: 0,
            lemma_count: 0,
            predicates_converged: 0,
            predicates_total: 2,
            engine_switched: true,
            active_engine_idx: 2,
        };
        let line = report.format_line(15.0);
        assert!(line.contains("switched"));
        assert!(line.contains("Kind"));
    }

    #[test]
    fn test_progress_snapshot_thread_safe() {
        let snap = Arc::new(ChcProgressSnapshot::new(2));
        let snap2 = snap.clone();

        let handle = std::thread::spawn(move || {
            snap2.set_active_engine("PDR", 0);
            snap2.update_pdr_progress(5, 100);
        });
        handle.join().expect("thread join");

        let report = snap.snapshot();
        assert_eq!(report.engine_name, "PDR");
        assert_eq!(report.frame_count, 5);
    }
}
