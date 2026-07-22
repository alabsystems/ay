// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Convergence monitor enhancements for graduated stagnation response (#7906).
//!
//! This module extends the base `ConvergenceMonitor` (defined in `mod.rs`) with:
//! 1. **Graduated response levels** (Warn -> Throttle -> Abort) instead of binary detection
//! 2. **Convergence health** (Healthy -> Slowing -> Stagnating -> Stuck) combining
//!    stagnation response with lemma quality signals
//! 3. **Lemma quality tracking**: push ratio, clause size trend, duplicate rate,
//!    and generalization success/failure ratio
//! 4. **Adaptive thresholds** that scale with problem size
//!
//! The base struct in `mod.rs` retains the core fields. This module adds the
//! extension types (`StagnationResponse`, `ConvergenceHealth`, `ProblemSizeHint`,
//! `LemmaQualityMetrics`) and the extended `impl` block with graduated methods.

use crate::ChcProblem;

use super::ConvergenceMonitor;

/// Graduated response level from stagnation detection (#7906).
///
/// Instead of binary stagnation (stalled or not), the monitor classifies the
/// severity so the main loop can take proportional action:
/// - `Warn`: log diagnostics, no behavioral change yet
/// - `Throttle`: escalate/de-escalate generalization strategy
/// - `Abort`: all escalation levels exhausted, return Unknown
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StagnationResponse {
    /// No stagnation detected; solver is making progress.
    None,
    /// First stagnant window detected. Log diagnostics but continue with
    /// current strategy to allow transient plateaus.
    Warn,
    /// Multiple stagnant windows. Escalate or de-escalate generalization
    /// strategy to attempt a different approach.
    Throttle,
    /// All escalation levels exhausted and still stagnating. The main loop
    /// should return Unknown.
    Abort,
}

/// Combined convergence health level (#7906).
///
/// Provides a unified view of solver health by combining the stagnation
/// response level with lemma quality signals. The main loop can use this
/// for proportional strategy adaptation:
/// - `Healthy`: solver is making progress; continue normally
/// - `Slowing`: early warning; lemma quality declining or first stagnant window
/// - `Stagnating`: persistent stagnation; escalate generalization strategy
/// - `Stuck`: all recovery attempts exhausted; return Unknown
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConvergenceHealth {
    /// Making progress. Lemma quality is adequate and no stagnation detected.
    Healthy,
    /// Early warning. One or more of: first stagnant window, declining lemma
    /// quality (one low-quality window), or low generalization success rate.
    Slowing,
    /// Persistent stagnation. Multiple stagnant windows or sustained low
    /// lemma quality. Escalation of generalization strategy is warranted.
    Stagnating,
    /// Terminal. All escalation exhausted and still not making progress.
    /// The solver should return Unknown.
    Stuck,
}

/// Problem size features used to adapt convergence thresholds (#7906).
///
/// Larger problems naturally need more iterations and longer wall-clock
/// windows before stagnation is declared. These hints are computed once
/// at construction from the `ChcProblem` and remain constant.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProblemSizeHint {
    /// Number of Horn clauses in the problem.
    pub num_clauses: usize,
    /// Number of predicates in the problem.
    pub num_predicates: usize,
    /// Total variable arity across all predicates (sum of arg_sorts.len()).
    pub total_predicate_arity: usize,
}

impl ProblemSizeHint {
    /// Compute size hint from a CHC problem.
    pub(crate) fn from_problem(problem: &ChcProblem) -> Self {
        let total_predicate_arity: usize =
            problem.predicates().iter().map(|p| p.arg_sorts.len()).sum();
        Self {
            num_clauses: problem.clauses().len(),
            num_predicates: problem.predicates().len(),
            total_predicate_arity,
        }
    }

    /// Multiplier for adaptive thresholds based on problem size.
    ///
    /// Returns a factor >= 1.0 that scales window sizes and stall timeouts.
    /// Small problems (< 5 clauses, < 3 predicates) use the base thresholds.
    /// Larger problems get proportionally more patience.
    ///
    /// The formula: 1.0 + 0.5 * log2(1 + complexity_score)
    /// where complexity_score = clauses * max(1, predicates) * max(1, arity / predicates).
    /// This grows sub-linearly so a 100-clause problem gets ~3x patience, not 100x.
    pub(crate) fn adaptive_multiplier(&self) -> f64 {
        let preds = self.num_predicates.max(1) as f64;
        let avg_arity = if self.num_predicates > 0 {
            (self.total_predicate_arity as f64 / preds).max(1.0)
        } else {
            1.0
        };
        let complexity = self.num_clauses.max(1) as f64 * preds * avg_arity;
        1.0 + 0.5 * (1.0 + complexity).log2()
    }

    /// Default hint for tests and backward-compatible usage.
    #[allow(dead_code)] // retained for future tests/back-compat
    pub(crate) fn default_hint() -> Self {
        Self {
            num_clauses: 3,
            num_predicates: 1,
            total_predicate_arity: 1,
        }
    }
}

/// Lemma quality metrics tracked per convergence window (#7906).
///
/// These metrics extend the base push-ratio tracking in `ConvergenceMonitor`
/// with clause-size trend, duplicate detection, and generalization
/// success/failure tracking. The per-window counters reset each window via
/// `reset_window()`.
#[derive(Debug, Clone)]
pub(crate) struct LemmaQualityMetrics {
    /// Total lemmas learned in the current window.
    pub window_learned_lemmas: usize,
    /// Total lemmas pushed to higher frames in the current window.
    pub window_pushed_lemmas: usize,
    /// Sum of clause sizes (number of literals) for lemmas learned in the
    /// current window. Divided by `window_learned_lemmas` to get average.
    pub window_clause_size_sum: usize,
    /// Average clause size from the previous window. Used to detect growing
    /// trend (current avg > previous avg indicates overgeneralization).
    pub prev_window_avg_clause_size: f64,
    /// Number of duplicate lemmas detected in the current window (lemmas
    /// that were already present in the target frame).
    pub window_duplicate_lemmas: usize,
    /// Number of consecutive windows where average clause size increased.
    pub consecutive_growing_clause_size_windows: usize,
    /// Number of consecutive quality-tracking windows where the combined
    /// quality signal was below threshold.
    pub consecutive_low_quality_windows: usize,
    /// Number of successful lemma generalization attempts in the current window.
    /// A generalization is "successful" when it produces a strictly more general
    /// lemma than the input (at least one literal dropped or weakened).
    pub window_generalization_successes: usize,
    /// Number of failed lemma generalization attempts in the current window.
    /// A generalization "fails" when the generalizer returns the original
    /// lemma unchanged (no literal could be dropped while maintaining inductiveness).
    pub window_generalization_failures: usize,
}

// LemmaQualityMetrics is wired into the PDR main loop: `check_quality` and
// `reset_all` are driven by the graduated stagnation / convergence-health
// handling in `solve/main_loop.rs`. The per-event recorder helpers
// (`note_*`) and read-only accessors (`current_*`) are exercised by tests but
// not yet fed from the live solve loop, so the allow is retained to cover
// those until the per-event instrumentation lands.
#[allow(dead_code)]
impl LemmaQualityMetrics {
    /// Minimum lemmas in a quality window before evaluating metrics.
    /// Below this count, the sample is too small to judge quality.
    const MIN_QUALITY_SAMPLE: usize = 5;

    /// Push ratio threshold below which lemma quality is considered "low".
    /// If fewer than 20% of learned lemmas are pushed, generalization may be
    /// producing overly general (non-inductive at higher frames) lemmas.
    const LOW_QUALITY_PUSH_RATIO: f64 = 0.20;

    /// Consecutive low-quality windows required to trigger de-escalation.
    const LOW_QUALITY_WINDOWS_FOR_DEESCALATION: usize = 2;

    /// Duplicate rate threshold (fraction of learned lemmas that are duplicates).
    /// Above 50% suggests the solver is re-deriving the same lemmas.
    const HIGH_DUPLICATE_RATE: f64 = 0.50;

    /// Consecutive windows of growing average clause size before it contributes
    /// to a quality warning signal.
    const GROWING_CLAUSE_SIZE_WINDOWS: usize = 3;

    /// Generalization success rate below which quality is considered degraded.
    /// If fewer than 30% of generalization attempts succeed, the generalizer
    /// pipeline is struggling with the current lemma shapes.
    const LOW_GENERALIZATION_SUCCESS_RATE: f64 = 0.30;

    /// Minimum generalization attempts in a window before evaluating the
    /// success rate. Below this count, the sample is too small.
    const MIN_GENERALIZATION_SAMPLE: usize = 3;

    pub(crate) fn new() -> Self {
        Self {
            window_learned_lemmas: 0,
            window_pushed_lemmas: 0,
            window_clause_size_sum: 0,
            prev_window_avg_clause_size: 0.0,
            window_duplicate_lemmas: 0,
            consecutive_growing_clause_size_windows: 0,
            consecutive_low_quality_windows: 0,
            window_generalization_successes: 0,
            window_generalization_failures: 0,
        }
    }

    /// Record a newly learned lemma for quality tracking.
    pub(crate) fn note_lemma_learned(&mut self) {
        self.window_learned_lemmas += 1;
    }

    /// Record a newly learned lemma with its clause size (number of literals).
    pub(crate) fn note_lemma_learned_with_size(&mut self, clause_size: usize) {
        self.window_learned_lemmas += 1;
        self.window_clause_size_sum += clause_size;
    }

    /// Record a duplicate lemma (one already in the target frame).
    pub(crate) fn note_duplicate_lemma(&mut self) {
        self.window_duplicate_lemmas += 1;
    }

    /// Record a lemma that was successfully pushed to a higher frame.
    pub(crate) fn note_lemma_pushed(&mut self) {
        self.window_pushed_lemmas += 1;
    }

    /// Record a successful generalization attempt (lemma was generalized).
    pub(crate) fn note_generalization_success(&mut self) {
        self.window_generalization_successes += 1;
    }

    /// Record a failed generalization attempt (lemma unchanged).
    pub(crate) fn note_generalization_failure(&mut self) {
        self.window_generalization_failures += 1;
    }

    /// Record a generalization attempt with its outcome.
    pub(crate) fn note_generalization_attempt(&mut self, success: bool) {
        if success {
            self.window_generalization_successes += 1;
        } else {
            self.window_generalization_failures += 1;
        }
    }

    /// Total generalization attempts in this window.
    pub(crate) fn window_generalization_attempts(&self) -> usize {
        self.window_generalization_successes + self.window_generalization_failures
    }

    /// Current generalization success rate in this window (0.0 to 1.0).
    /// Returns 1.0 if no attempts have been made (avoid penalizing empty windows).
    pub(crate) fn current_generalization_success_rate(&self) -> f64 {
        let total = self.window_generalization_attempts();
        if total == 0 {
            return 1.0;
        }
        self.window_generalization_successes as f64 / total as f64
    }

    /// Current duplicate rate in this window (0.0 to 1.0).
    pub(crate) fn current_duplicate_rate(&self) -> f64 {
        if self.window_learned_lemmas == 0 {
            return 0.0;
        }
        self.window_duplicate_lemmas as f64 / self.window_learned_lemmas as f64
    }

    /// Current average clause size in this window.
    pub(crate) fn current_avg_clause_size(&self) -> f64 {
        if self.window_learned_lemmas == 0 {
            return 0.0;
        }
        self.window_clause_size_sum as f64 / self.window_learned_lemmas as f64
    }

    /// Evaluate lemma quality at the end of a convergence window.
    ///
    /// Returns `true` when lemma quality has been consistently low for
    /// `LOW_QUALITY_WINDOWS_FOR_DEESCALATION` consecutive windows, suggesting
    /// the current generalization strategy is overgeneralizing.
    ///
    /// Quality assessment combines three signals:
    /// 1. Push ratio: fraction of learned lemmas pushed to higher frames
    /// 2. Clause size trend: growing average clause size across windows
    /// 3. Duplicate rate: high duplicate rate indicates re-derivation
    pub(crate) fn check_quality(&mut self) -> bool {
        if self.window_learned_lemmas < Self::MIN_QUALITY_SAMPLE {
            self.reset_window();
            return false;
        }

        let push_ratio = self.window_pushed_lemmas as f64 / self.window_learned_lemmas as f64;
        let avg_clause_size = self.current_avg_clause_size();
        let duplicate_rate = self.current_duplicate_rate();

        // Track clause size trend
        if self.prev_window_avg_clause_size > 0.0
            && avg_clause_size > self.prev_window_avg_clause_size
        {
            self.consecutive_growing_clause_size_windows += 1;
        } else {
            self.consecutive_growing_clause_size_windows = 0;
        }
        self.prev_window_avg_clause_size = avg_clause_size;

        // Check generalization success rate
        let low_generalization = self.window_generalization_attempts()
            >= Self::MIN_GENERALIZATION_SAMPLE
            && self.current_generalization_success_rate() < Self::LOW_GENERALIZATION_SUCCESS_RATE;

        // Combined quality signal: low push ratio OR low generalization success
        // OR (growing clause sizes AND high duplicates)
        let low_push = push_ratio < Self::LOW_QUALITY_PUSH_RATIO;
        let quality_degradation = self.consecutive_growing_clause_size_windows
            >= Self::GROWING_CLAUSE_SIZE_WINDOWS
            && duplicate_rate > Self::HIGH_DUPLICATE_RATE;

        if low_push || quality_degradation || low_generalization {
            self.consecutive_low_quality_windows += 1;
        } else {
            self.consecutive_low_quality_windows = 0;
        }

        self.reset_window();
        self.consecutive_low_quality_windows >= Self::LOW_QUALITY_WINDOWS_FOR_DEESCALATION
    }

    /// Reset per-window counters (called at each window boundary).
    pub(crate) fn reset_window(&mut self) {
        self.window_pushed_lemmas = 0;
        self.window_learned_lemmas = 0;
        self.window_clause_size_sum = 0;
        self.window_duplicate_lemmas = 0;
        self.window_generalization_successes = 0;
        self.window_generalization_failures = 0;
    }

    /// Full reset including cross-window state (after escalation/de-escalation).
    pub(crate) fn reset_all(&mut self) {
        self.reset_window();
        self.consecutive_low_quality_windows = 0;
        self.consecutive_growing_clause_size_windows = 0;
        self.prev_window_avg_clause_size = 0.0;
    }
}

// =============================================================================
// Extended ConvergenceMonitor methods (#7906)
// =============================================================================

impl ConvergenceMonitor {
    /// Legacy binary stagnation check retained for tests and callers that only
    /// need the final bailout decision. New solver code should prefer
    /// `check_stagnation_graduated` so it can react proportionally before abort.
    #[allow(dead_code)]
    pub(super) fn check_stagnation(
        &mut self,
        current_iteration: usize,
        current_lemma_count: usize,
        current_frame_count: usize,
        has_solve_timeout: bool,
    ) -> bool {
        if !has_solve_timeout {
            return false;
        }

        if current_iteration >= Self::WINDOW_SIZE {
            let secs_since_frame = self.last_frame_advance.elapsed().as_secs();
            if secs_since_frame >= Self::FRAME_STALL_SECS {
                let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
                let iter_delta = current_iteration.saturating_sub(self.window_start_iteration);
                if iter_delta > 0 && lemma_delta == 0 {
                    return true;
                }
            }
        }

        let iters_in_window = current_iteration.saturating_sub(self.window_start_iteration);
        if iters_in_window < Self::WINDOW_SIZE {
            return false;
        }

        let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
        let frame_delta = current_frame_count.saturating_sub(self.window_frame_count);
        let is_stagnant =
            lemma_delta == 0 && frame_delta == 0 && self.window_productive_strengthens == 0;

        if is_stagnant {
            self.consecutive_stagnant_windows += 1;
        } else {
            self.consecutive_stagnant_windows = 0;
        }

        self.window_lemma_count = current_lemma_count;
        self.window_start_iteration = current_iteration;
        self.window_frame_count = current_frame_count;
        self.window_productive_strengthens = 0;
        self.window_total_strengthens = 0;

        self.consecutive_stagnant_windows >= Self::MAX_STAGNANT_WINDOWS
    }

    /// Adaptive window size scaled by problem complexity.
    pub(crate) fn adaptive_window_size(&self, problem_size: &ProblemSizeHint) -> usize {
        let scaled = Self::WINDOW_SIZE as f64 * problem_size.adaptive_multiplier();
        (scaled as usize).max(Self::WINDOW_SIZE)
    }

    /// Adaptive max stagnant windows scaled by problem complexity.
    pub(crate) fn adaptive_max_stagnant_windows(&self, problem_size: &ProblemSizeHint) -> usize {
        let scaled = Self::MAX_STAGNANT_WINDOWS as f64 * problem_size.adaptive_multiplier();
        (scaled as usize).max(Self::MAX_STAGNANT_WINDOWS)
    }

    /// Adaptive frame stall timeout in seconds, scaled by problem complexity.
    pub(crate) fn adaptive_frame_stall_secs(&self, problem_size: &ProblemSizeHint) -> u64 {
        let scaled = Self::FRAME_STALL_SECS as f64 * problem_size.adaptive_multiplier();
        (scaled as u64).max(Self::FRAME_STALL_SECS)
    }

    /// Graduated stagnation check returning a response level (#7906).
    ///
    /// Returns a `StagnationResponse` that indicates the severity of detected
    /// stagnation. The main loop can use this to take proportional action:
    /// - `None`: continue normally
    /// - `Warn`: log diagnostics only (first stagnant window)
    /// - `Throttle`: escalate or de-escalate generalization strategy
    /// - `Abort`: all escalation exhausted, return Unknown
    ///
    /// Thresholds are adapted based on problem size via `ProblemSizeHint`.
    pub(crate) fn check_stagnation_graduated(
        &mut self,
        current_iteration: usize,
        current_lemma_count: usize,
        current_frame_count: usize,
        has_solve_timeout: bool,
        problem_size: &ProblemSizeHint,
    ) -> StagnationResponse {
        // Only activate when running under a budget (portfolio/solve_timeout).
        if !has_solve_timeout {
            return StagnationResponse::None;
        }

        let adaptive_window = self.adaptive_window_size(problem_size);
        let adaptive_stall_secs = self.adaptive_frame_stall_secs(problem_size);
        let adaptive_max_windows = self.adaptive_max_stagnant_windows(problem_size);

        // Check frame stall: no frame advancement in adaptive_stall_secs
        // while we've done at least adaptive_window iterations total.
        if current_iteration >= adaptive_window {
            let secs_since_frame = self.last_frame_advance.elapsed().as_secs();
            if secs_since_frame >= adaptive_stall_secs {
                let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
                let iter_delta = current_iteration.saturating_sub(self.window_start_iteration);
                if iter_delta > 0 && lemma_delta == 0 {
                    // Frame stall with no lemma velocity: immediate Abort.
                    return StagnationResponse::Abort;
                }
            }
        }

        // Check window-based stagnation: every adaptive_window iterations
        let iters_in_window = current_iteration.saturating_sub(self.window_start_iteration);
        if iters_in_window < adaptive_window {
            return StagnationResponse::None;
        }

        // Window complete -- evaluate progress
        let lemma_delta = current_lemma_count.saturating_sub(self.window_lemma_count);
        let frame_delta = current_frame_count.saturating_sub(self.window_frame_count);

        let is_stagnant =
            lemma_delta == 0 && frame_delta == 0 && self.window_productive_strengthens == 0;

        if is_stagnant {
            self.consecutive_stagnant_windows += 1;
        } else {
            self.consecutive_stagnant_windows = 0;
        }

        // Reset window
        self.window_lemma_count = current_lemma_count;
        self.window_start_iteration = current_iteration;
        self.window_frame_count = current_frame_count;
        self.window_productive_strengthens = 0;
        self.window_total_strengthens = 0;

        // Graduated response based on consecutive stagnant windows
        if self.consecutive_stagnant_windows >= adaptive_max_windows {
            StagnationResponse::Abort
        } else if self.consecutive_stagnant_windows >= 2 {
            StagnationResponse::Throttle
        } else if self.consecutive_stagnant_windows == 1 {
            StagnationResponse::Warn
        } else {
            StagnationResponse::None
        }
    }

    /// Assess overall convergence health by combining stagnation response
    /// with lemma quality signals (#7906).
    ///
    /// This produces a unified `ConvergenceHealth` that the main loop can
    /// use for proportional strategy adaptation. The mapping:
    ///
    /// | Stagnation | Quality  | Health      |
    /// |------------|----------|-------------|
    /// | None       | Good     | Healthy     |
    /// | None       | Low (1w) | Slowing     |
    /// | Warn       | any      | Slowing     |
    /// | Throttle   | any      | Stagnating  |
    /// | Abort      | any      | Stuck       |
    /// | None       | Low (2w) | Stagnating  |
    ///
    /// `lemma_quality` provides the quality signal: `consecutive_low_quality_windows`
    /// indicates how many consecutive windows had poor push ratio, high
    /// duplicate rate, growing clause sizes, or low generalization success rate.
    pub(crate) fn assess_health(
        &self,
        stagnation: StagnationResponse,
        lemma_quality: &LemmaQualityMetrics,
    ) -> ConvergenceHealth {
        match stagnation {
            StagnationResponse::Abort => ConvergenceHealth::Stuck,
            StagnationResponse::Throttle => ConvergenceHealth::Stagnating,
            StagnationResponse::Warn => ConvergenceHealth::Slowing,
            StagnationResponse::None => {
                // No stagnation detected by iteration/frame metrics.
                // Use lemma quality to detect early warning signs.
                if lemma_quality.consecutive_low_quality_windows
                    >= LemmaQualityMetrics::LOW_QUALITY_WINDOWS_FOR_DEESCALATION
                {
                    // Sustained low quality without stagnation: the solver
                    // is learning lemmas but they are not useful.
                    ConvergenceHealth::Stagnating
                } else if lemma_quality.consecutive_low_quality_windows >= 1 {
                    // One low-quality window: early warning.
                    ConvergenceHealth::Slowing
                } else {
                    ConvergenceHealth::Healthy
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // ProblemSizeHint tests
    // =========================================================================

    #[test]
    fn test_problem_size_hint_default_multiplier_near_one() {
        let hint = ProblemSizeHint::default_hint();
        let m = hint.adaptive_multiplier();
        // Default: 3 clauses, 1 predicate, 1 arity
        // complexity = 3 * 1 * 1 = 3
        // multiplier = 1.0 + 0.5 * log2(4) = 1.0 + 0.5 * 2 = 2.0
        assert!(m >= 1.0, "Multiplier should be >= 1.0, got {m}");
        assert!(
            m <= 3.0,
            "Small problem multiplier should be <= 3.0, got {m}"
        );
    }

    #[test]
    fn test_problem_size_hint_large_problem_higher_multiplier() {
        let small = ProblemSizeHint {
            num_clauses: 3,
            num_predicates: 1,
            total_predicate_arity: 1,
        };
        let large = ProblemSizeHint {
            num_clauses: 50,
            num_predicates: 10,
            total_predicate_arity: 30,
        };
        assert!(
            large.adaptive_multiplier() > small.adaptive_multiplier(),
            "Larger problem should have higher multiplier: small={}, large={}",
            small.adaptive_multiplier(),
            large.adaptive_multiplier()
        );
    }

    #[test]
    fn test_problem_size_hint_multiplier_grows_sublinearly() {
        let p10 = ProblemSizeHint {
            num_clauses: 10,
            num_predicates: 3,
            total_predicate_arity: 6,
        };
        let p100 = ProblemSizeHint {
            num_clauses: 100,
            num_predicates: 30,
            total_predicate_arity: 60,
        };
        let m10 = p10.adaptive_multiplier();
        let m100 = p100.adaptive_multiplier();
        // 10x clauses and 10x predicates should NOT give 10x multiplier
        assert!(
            m100 < m10 * 5.0,
            "Multiplier should grow sub-linearly: m10={m10}, m100={m100}"
        );
    }

    #[test]
    fn test_problem_size_hint_zero_predicates() {
        // Edge case: no predicates (degenerate problem)
        let hint = ProblemSizeHint {
            num_clauses: 5,
            num_predicates: 0,
            total_predicate_arity: 0,
        };
        let m = hint.adaptive_multiplier();
        assert!(
            m >= 1.0,
            "Multiplier should be >= 1.0 even with 0 predicates"
        );
        assert!(m.is_finite(), "Multiplier should be finite");
    }

    // =========================================================================
    // LemmaQualityMetrics tests
    // =========================================================================

    #[test]
    fn test_lemma_quality_high_push_ratio_no_trigger() {
        let mut metrics = LemmaQualityMetrics::new();
        // 10 learned, 5 pushed (50% ratio > 20% threshold)
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        assert!(
            !metrics.check_quality(),
            "High push ratio should not trigger de-escalation"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
    }

    #[test]
    fn test_lemma_quality_low_push_single_window_no_trigger() {
        let mut metrics = LemmaQualityMetrics::new();
        // 10 learned, 1 pushed (10% ratio < 20% threshold)
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        metrics.note_lemma_pushed();
        assert!(
            !metrics.check_quality(),
            "Single low-quality window should not trigger"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 1);
    }

    #[test]
    fn test_lemma_quality_two_low_windows_triggers() {
        let mut metrics = LemmaQualityMetrics::new();

        // First low-quality window
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        metrics.note_lemma_pushed(); // 10% ratio
        assert!(!metrics.check_quality());

        // Second low-quality window
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        // No pushes (0% ratio)
        assert!(
            metrics.check_quality(),
            "Two consecutive low-quality windows should trigger de-escalation"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 2);
    }

    #[test]
    fn test_lemma_quality_resets_on_good_window() {
        let mut metrics = LemmaQualityMetrics::new();

        // One low-quality window
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        metrics.check_quality();
        assert_eq!(metrics.consecutive_low_quality_windows, 1);

        // One high-quality window (80% push ratio)
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..8 {
            metrics.note_lemma_pushed();
        }
        metrics.check_quality();
        assert_eq!(
            metrics.consecutive_low_quality_windows, 0,
            "Good window should reset consecutive counter"
        );
    }

    #[test]
    fn test_lemma_quality_small_sample_no_trigger() {
        let mut metrics = LemmaQualityMetrics::new();
        // Only 3 lemmas learned (below MIN_QUALITY_SAMPLE = 5)
        for _ in 0..3 {
            metrics.note_lemma_learned();
        }
        assert!(
            !metrics.check_quality(),
            "Too few samples should not trigger de-escalation"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
    }

    #[test]
    fn test_lemma_quality_clause_size_tracking() {
        let mut metrics = LemmaQualityMetrics::new();

        // Window 1: average clause size = 3
        for _ in 0..5 {
            metrics.note_lemma_learned_with_size(3);
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed(); // high push ratio
        }
        metrics.check_quality();
        assert!(
            (metrics.prev_window_avg_clause_size - 3.0).abs() < 0.01,
            "Previous avg clause size should be 3.0, got {}",
            metrics.prev_window_avg_clause_size
        );

        // Window 2: average clause size = 5 (growing)
        for _ in 0..5 {
            metrics.note_lemma_learned_with_size(5);
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        metrics.check_quality();
        assert_eq!(
            metrics.consecutive_growing_clause_size_windows, 1,
            "Growing clause size should be detected"
        );
    }

    #[test]
    fn test_lemma_quality_duplicate_rate() {
        let mut metrics = LemmaQualityMetrics::new();
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..6 {
            metrics.note_duplicate_lemma();
        }
        assert!(
            metrics.current_duplicate_rate() > 0.50,
            "Duplicate rate should be > 50%: {}",
            metrics.current_duplicate_rate()
        );
    }

    #[test]
    fn test_lemma_quality_degradation_via_clause_size_and_duplicates() {
        let mut metrics = LemmaQualityMetrics::new();

        // Build up 3 windows of growing clause sizes with high duplicates
        // but good push ratio -- should not trigger on push ratio alone.
        for window in 0..4 {
            let clause_size = 3 + window;
            for _ in 0..10 {
                metrics.note_lemma_learned_with_size(clause_size);
                metrics.note_duplicate_lemma(); // 100% duplicate rate
            }
            for _ in 0..5 {
                metrics.note_lemma_pushed(); // 50% push ratio (good)
            }
            let triggered = metrics.check_quality();
            if window < 3 {
                // Need GROWING_CLAUSE_SIZE_WINDOWS (3) + LOW_QUALITY_WINDOWS_FOR_DEESCALATION (2)
                // to trigger. The clause size grows from window 1 onward (window 0 has no previous).
                // So growing windows: 0 after window 0, 1 after window 1, 2 after window 2.
                // quality_degradation only fires at >= 3 growing windows (after window 3).
            }
            if window >= 3 {
                // By window 3 we should have at least GROWING_CLAUSE_SIZE_WINDOWS = 3 consecutive
                // growing clause sizes (windows 1, 2, 3) and HIGH_DUPLICATE_RATE satisfied.
                // But we also need LOW_QUALITY_WINDOWS_FOR_DEESCALATION = 2 consecutive windows.
                // First quality_degradation fires at window 3 (growing>=3), setting
                // consecutive_low_quality_windows to 1. The second fires next window.
                // So 4 windows with growing sizes + high duplicates + push ratio OK:
                // triggered at window index 4.
                let _ = triggered;
            }
        }

        // One more window to reach LOW_QUALITY_WINDOWS_FOR_DEESCALATION
        for _ in 0..10 {
            metrics.note_lemma_learned_with_size(7);
            metrics.note_duplicate_lemma();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        assert!(
            metrics.check_quality(),
            "Quality degradation should trigger after sustained growing clause sizes + high duplicates"
        );
    }

    #[test]
    fn test_lemma_quality_reset_all() {
        let mut metrics = LemmaQualityMetrics::new();

        // Build some state
        for _ in 0..10 {
            metrics.note_lemma_learned_with_size(5);
            metrics.note_duplicate_lemma();
        }
        metrics.note_generalization_success();
        metrics.note_generalization_failure();
        metrics.check_quality();
        assert_eq!(metrics.consecutive_low_quality_windows, 1);

        // Full reset
        metrics.reset_all();
        assert_eq!(metrics.window_learned_lemmas, 0);
        assert_eq!(metrics.window_pushed_lemmas, 0);
        assert_eq!(metrics.window_clause_size_sum, 0);
        assert_eq!(metrics.window_duplicate_lemmas, 0);
        assert_eq!(metrics.window_generalization_successes, 0);
        assert_eq!(metrics.window_generalization_failures, 0);
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
        assert_eq!(metrics.consecutive_growing_clause_size_windows, 0);
        assert!((metrics.prev_window_avg_clause_size - 0.0).abs() < 0.01);
    }

    // =========================================================================
    // StagnationResponse / graduated detection tests
    // =========================================================================

    #[test]
    fn test_graduated_no_stagnation_without_budget() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        for iter in 1..=200 {
            let resp = monitor.check_stagnation_graduated(iter, 0, 2, false, &hint);
            assert_eq!(
                resp,
                StagnationResponse::None,
                "Should never detect stagnation without budget"
            );
        }
    }

    #[test]
    fn test_graduated_progress_returns_none() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        for iter in 1..=20 {
            monitor.note_strengthen(true);
            let resp = monitor.check_stagnation_graduated(iter, iter, 2 + iter / 5, true, &hint);
            assert_eq!(
                resp,
                StagnationResponse::None,
                "Should not detect stagnation while making progress (iter {iter})"
            );
        }
    }

    #[test]
    fn test_graduated_warn_after_first_stagnant_window() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        let window = monitor.adaptive_window_size(&hint);

        // First window: progress
        for iter in 1..=window {
            monitor.note_strengthen(true);
            monitor.check_stagnation_graduated(iter, iter, 2, true, &hint);
        }

        // Second window: stagnation (frozen lemmas and frames)
        let frozen_lemmas = window;
        let frozen_frames = 2;
        let mut saw_warn = false;
        for iter in (window + 1)..=(2 * window) {
            let resp =
                monitor.check_stagnation_graduated(iter, frozen_lemmas, frozen_frames, true, &hint);
            if resp == StagnationResponse::Warn {
                saw_warn = true;
            }
        }
        assert!(
            saw_warn,
            "Should have seen Warn after first stagnant window"
        );
    }

    #[test]
    fn test_graduated_throttle_after_two_stagnant_windows() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        let window = monitor.adaptive_window_size(&hint);

        // First window: progress
        for iter in 1..=window {
            monitor.note_strengthen(true);
            monitor.check_stagnation_graduated(iter, iter, 2, true, &hint);
        }

        // Second + third windows: stagnation
        let frozen_lemmas = window;
        let frozen_frames = 2;
        let mut saw_throttle = false;
        for iter in (window + 1)..=(3 * window) {
            let resp =
                monitor.check_stagnation_graduated(iter, frozen_lemmas, frozen_frames, true, &hint);
            if resp == StagnationResponse::Throttle {
                saw_throttle = true;
            }
        }
        assert!(
            saw_throttle,
            "Should have seen Throttle after 2 stagnant windows"
        );
    }

    #[test]
    fn test_graduated_abort_after_max_stagnant_windows() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        let window = monitor.adaptive_window_size(&hint);
        let max_windows = monitor.adaptive_max_stagnant_windows(&hint);

        // First window: progress
        for iter in 1..=window {
            monitor.note_strengthen(true);
            monitor.check_stagnation_graduated(iter, iter, 2, true, &hint);
        }

        // Enough stagnant windows to hit Abort
        let frozen_lemmas = window;
        let frozen_frames = 2;
        let mut saw_abort = false;
        for iter in (window + 1)..=(window * (max_windows + 2)) {
            let resp =
                monitor.check_stagnation_graduated(iter, frozen_lemmas, frozen_frames, true, &hint);
            if resp == StagnationResponse::Abort {
                saw_abort = true;
                break;
            }
        }
        assert!(
            saw_abort,
            "Should have seen Abort after {max_windows} stagnant windows"
        );
    }

    #[test]
    fn test_graduated_resets_on_progress() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        let window = monitor.adaptive_window_size(&hint);

        // First window: progress
        for iter in 1..=window {
            monitor.note_strengthen(true);
            monitor.check_stagnation_graduated(iter, iter, 2, true, &hint);
        }

        // Second window: stagnation
        let frozen_lemmas = window;
        for iter in (window + 1)..=(2 * window) {
            monitor.check_stagnation_graduated(iter, frozen_lemmas, 2, true, &hint);
        }
        assert_eq!(monitor.consecutive_stagnant_windows, 1);

        // Third window: progress again (new lemmas)
        for iter in (2 * window + 1)..=(3 * window) {
            monitor.note_strengthen(true);
            monitor.check_stagnation_graduated(
                iter,
                frozen_lemmas + (iter - 2 * window),
                2,
                true,
                &hint,
            );
        }
        assert_eq!(
            monitor.consecutive_stagnant_windows, 0,
            "Progress should reset stagnation counter"
        );
    }

    #[test]
    fn test_adaptive_thresholds_scale_with_problem_size() {
        let monitor = ConvergenceMonitor::new();
        let small = ProblemSizeHint::default_hint();
        let large = ProblemSizeHint {
            num_clauses: 100,
            num_predicates: 20,
            total_predicate_arity: 60,
        };

        assert!(
            monitor.adaptive_window_size(&large) > monitor.adaptive_window_size(&small),
            "Larger problem should have larger window"
        );
        assert!(
            monitor.adaptive_max_stagnant_windows(&large)
                > monitor.adaptive_max_stagnant_windows(&small),
            "Larger problem should tolerate more stagnant windows"
        );
        assert!(
            monitor.adaptive_frame_stall_secs(&large) > monitor.adaptive_frame_stall_secs(&small),
            "Larger problem should have longer frame stall timeout"
        );
    }

    #[test]
    fn test_graduated_stagnation_eventually_throttles() {
        let mut monitor = ConvergenceMonitor::new();
        let hint = ProblemSizeHint::default_hint();
        let window = monitor.adaptive_window_size(&hint);

        // Progress window
        for iter in 1..=window {
            monitor.note_strengthen(true);
            let response = monitor.check_stagnation_graduated(iter, iter, 2, true, &hint);
            assert_eq!(response, StagnationResponse::None);
        }

        // Stagnation windows
        let frozen_lemmas = window;
        let mut graduated_triggered = false;
        for iter in (window + 1)..=(window * 5) {
            let resp = monitor.check_stagnation_graduated(iter, frozen_lemmas, 2, true, &hint);
            if matches!(
                resp,
                StagnationResponse::Throttle | StagnationResponse::Abort
            ) {
                graduated_triggered = true;
                break;
            }
        }
        assert!(
            graduated_triggered,
            "graduated monitor should throttle after repeated stagnant windows"
        );
    }

    // =========================================================================
    // Generalization success/failure tracking tests
    // =========================================================================

    #[test]
    fn test_generalization_success_rate_empty() {
        let metrics = LemmaQualityMetrics::new();
        assert!(
            (metrics.current_generalization_success_rate() - 1.0).abs() < 0.01,
            "Empty window should report 100% success rate"
        );
        assert_eq!(metrics.window_generalization_attempts(), 0);
    }

    #[test]
    fn test_generalization_success_rate_tracking() {
        let mut metrics = LemmaQualityMetrics::new();

        // 3 successes, 7 failures = 30% success rate
        for _ in 0..3 {
            metrics.note_generalization_success();
        }
        for _ in 0..7 {
            metrics.note_generalization_failure();
        }
        assert_eq!(metrics.window_generalization_attempts(), 10);
        assert!(
            (metrics.current_generalization_success_rate() - 0.30).abs() < 0.01,
            "Success rate should be 30%, got {}",
            metrics.current_generalization_success_rate()
        );
    }

    #[test]
    fn test_generalization_attempt_convenience_method() {
        let mut metrics = LemmaQualityMetrics::new();

        metrics.note_generalization_attempt(true);
        metrics.note_generalization_attempt(true);
        metrics.note_generalization_attempt(false);

        assert_eq!(metrics.window_generalization_successes, 2);
        assert_eq!(metrics.window_generalization_failures, 1);
        assert_eq!(metrics.window_generalization_attempts(), 3);
        assert!(
            (metrics.current_generalization_success_rate() - 2.0 / 3.0).abs() < 0.01,
            "Success rate should be ~66.7%"
        );
    }

    #[test]
    fn test_generalization_counters_reset_on_window() {
        let mut metrics = LemmaQualityMetrics::new();
        metrics.note_generalization_success();
        metrics.note_generalization_failure();
        assert_eq!(metrics.window_generalization_attempts(), 2);

        metrics.reset_window();
        assert_eq!(metrics.window_generalization_successes, 0);
        assert_eq!(metrics.window_generalization_failures, 0);
        assert_eq!(metrics.window_generalization_attempts(), 0);
    }

    #[test]
    fn test_low_generalization_success_triggers_quality_check() {
        let mut metrics = LemmaQualityMetrics::new();

        // Window 1: enough lemmas + enough generalization attempts with low success.
        // 10 learned, 5 pushed (good push ratio 50%), but 1/5 generalization success (20% < 30%).
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        metrics.note_generalization_success();
        for _ in 0..4 {
            metrics.note_generalization_failure();
        }
        assert!(
            !metrics.check_quality(),
            "Single low-generalization window should not trigger"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 1);

        // Window 2: same pattern
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        metrics.note_generalization_success();
        for _ in 0..4 {
            metrics.note_generalization_failure();
        }
        assert!(
            metrics.check_quality(),
            "Two consecutive low-generalization windows should trigger de-escalation"
        );
    }

    #[test]
    fn test_high_generalization_success_no_trigger() {
        let mut metrics = LemmaQualityMetrics::new();

        // Good push ratio AND good generalization success rate
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        for _ in 0..4 {
            metrics.note_generalization_success();
        }
        metrics.note_generalization_failure();
        assert!(
            !metrics.check_quality(),
            "High generalization success rate should not trigger"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
    }

    #[test]
    fn test_generalization_below_min_sample_ignored() {
        let mut metrics = LemmaQualityMetrics::new();

        // Good push ratio, but only 2 generalization attempts (below MIN_GENERALIZATION_SAMPLE=3)
        // with 0% success rate -- should not count as low generalization.
        for _ in 0..10 {
            metrics.note_lemma_learned();
        }
        for _ in 0..5 {
            metrics.note_lemma_pushed();
        }
        metrics.note_generalization_failure();
        metrics.note_generalization_failure();
        assert!(
            !metrics.check_quality(),
            "Below-threshold generalization sample should not affect quality"
        );
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
    }

    // =========================================================================
    // ConvergenceHealth / assess_health tests
    // =========================================================================

    #[test]
    fn test_health_healthy_when_no_stagnation_good_quality() {
        let monitor = ConvergenceMonitor::new();
        let metrics = LemmaQualityMetrics::new();
        let health = monitor.assess_health(StagnationResponse::None, &metrics);
        assert_eq!(health, ConvergenceHealth::Healthy);
    }

    #[test]
    fn test_health_slowing_on_warn() {
        let monitor = ConvergenceMonitor::new();
        let metrics = LemmaQualityMetrics::new();
        let health = monitor.assess_health(StagnationResponse::Warn, &metrics);
        assert_eq!(health, ConvergenceHealth::Slowing);
    }

    #[test]
    fn test_health_slowing_on_one_low_quality_window() {
        let monitor = ConvergenceMonitor::new();
        let mut metrics = LemmaQualityMetrics::new();
        metrics.consecutive_low_quality_windows = 1;
        let health = monitor.assess_health(StagnationResponse::None, &metrics);
        assert_eq!(health, ConvergenceHealth::Slowing);
    }

    #[test]
    fn test_health_stagnating_on_throttle() {
        let monitor = ConvergenceMonitor::new();
        let metrics = LemmaQualityMetrics::new();
        let health = monitor.assess_health(StagnationResponse::Throttle, &metrics);
        assert_eq!(health, ConvergenceHealth::Stagnating);
    }

    #[test]
    fn test_health_stagnating_on_sustained_low_quality() {
        let monitor = ConvergenceMonitor::new();
        let mut metrics = LemmaQualityMetrics::new();
        // LOW_QUALITY_WINDOWS_FOR_DEESCALATION = 2
        metrics.consecutive_low_quality_windows = 2;
        let health = monitor.assess_health(StagnationResponse::None, &metrics);
        assert_eq!(
            health,
            ConvergenceHealth::Stagnating,
            "Sustained low quality without stagnation should still be Stagnating"
        );
    }

    #[test]
    fn test_health_stuck_on_abort() {
        let monitor = ConvergenceMonitor::new();
        let metrics = LemmaQualityMetrics::new();
        let health = monitor.assess_health(StagnationResponse::Abort, &metrics);
        assert_eq!(health, ConvergenceHealth::Stuck);
    }

    #[test]
    fn test_health_abort_overrides_good_quality() {
        let monitor = ConvergenceMonitor::new();
        // Even with perfect quality metrics, Abort means Stuck.
        let metrics = LemmaQualityMetrics::new();
        assert_eq!(metrics.consecutive_low_quality_windows, 0);
        let health = monitor.assess_health(StagnationResponse::Abort, &metrics);
        assert_eq!(health, ConvergenceHealth::Stuck);
    }

    #[test]
    fn test_health_throttle_with_low_quality_still_stagnating() {
        let monitor = ConvergenceMonitor::new();
        let mut metrics = LemmaQualityMetrics::new();
        metrics.consecutive_low_quality_windows = 3;
        // Throttle + low quality = Stagnating (not Stuck, because Throttle is not terminal)
        let health = monitor.assess_health(StagnationResponse::Throttle, &metrics);
        assert_eq!(health, ConvergenceHealth::Stagnating);
    }

    #[test]
    fn test_health_full_lifecycle() {
        // Simulate a solver going through all health states.
        let monitor = ConvergenceMonitor::new();

        // Phase 1: Healthy (no issues)
        let metrics = LemmaQualityMetrics::new();
        assert_eq!(
            monitor.assess_health(StagnationResponse::None, &metrics),
            ConvergenceHealth::Healthy
        );

        // Phase 2: Slowing (one bad quality window)
        let mut metrics = LemmaQualityMetrics::new();
        metrics.consecutive_low_quality_windows = 1;
        assert_eq!(
            monitor.assess_health(StagnationResponse::None, &metrics),
            ConvergenceHealth::Slowing
        );

        // Phase 3: Stagnating (multiple bad windows or Throttle)
        assert_eq!(
            monitor.assess_health(StagnationResponse::Throttle, &metrics),
            ConvergenceHealth::Stagnating
        );

        // Phase 4: Stuck (Abort)
        assert_eq!(
            monitor.assess_health(StagnationResponse::Abort, &metrics),
            ConvergenceHealth::Stuck
        );
    }
}
