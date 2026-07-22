// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failure analysis for CHC solving attempts.
//!
//! When a CHC solver returns Unknown, the failed attempt contains valuable
//! information that can guide subsequent attempts:
//!
//! - **Weak lemmas**: Lemmas that were almost inductive but needed more strength
//! - **Blocking frontier**: The stuck region in the state space
//! - **CEX depth**: How deep counterexamples got (may indicate real bugs)
//! - **SMT pressure**: Whether the solver is struggling with large formulas
//!
//! This module provides `FailureAnalysis` to extract these insights and
//! `FailureGuide` to suggest improved configurations for retry attempts.
//!
//! # Usage (crate-internal)
//!
//! ```rust,compile_fail
//! // This module is pub(crate) — these types are internal to ay-chc.
//! use ay_chc::PdrConfig;
//! use ay_chc::failure_analysis::{FailureAnalysis, FailureGuide, SolverStats};
//!
//! let stats = SolverStats { iterations: 100, smt_unknowns: 30, ..Default::default() };
//! let analysis = FailureAnalysis::from_stats(&stats);
//! let guide = FailureGuide::from_analysis(&analysis);
//!
//! let config = PdrConfig::default();
//! let _retry_config = guide.apply_to_config(config);
//! ```
//!
//! # Design Reference
//!
//! Part of #1870 - Failure-guided learning for retry attempts.

use crate::pdr::PdrConfig;
use crate::PredicateId;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Classification of why a solving attempt failed
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FailureMode {
    /// Lemmas learned were too weak - kept getting blocked repeatedly
    WeakLemmas,
    /// Counterexample depth kept growing without convergence
    DeepCounterexample,
    /// Oscillation detected - same states revisited multiple times
    Oscillation,
    /// Progress on one predicate broke invariants for another
    PredicateCoupling,
    /// SMT queries taking too long or timing out
    SmtTimeout,
    /// Resource limits hit without clear other cause
    ResourceExhausted,
    /// Convergence monitor detected stagnation (no lemma velocity, no frame progress).
    ConvergenceStagnation,
}

impl std::fmt::Display for FailureMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WeakLemmas => write!(f, "weak_lemmas"),
            Self::DeepCounterexample => write!(f, "deep_cex"),
            Self::Oscillation => write!(f, "oscillation"),
            Self::PredicateCoupling => write!(f, "predicate_coupling"),
            Self::SmtTimeout => write!(f, "smt_timeout"),
            Self::ResourceExhausted => write!(f, "resource_exhausted"),
            Self::ConvergenceStagnation => write!(f, "convergence_stagnation"),
        }
    }
}

/// Statistics collected during a PDR solve attempt
///
/// This is designed to be extracted from PdrSolver state without exposing
/// internal implementation details.
#[derive(Debug, Clone, Default)]
pub(crate) struct SolverStats {
    /// Total iterations performed
    pub iterations: usize,
    /// Number of lemmas learned
    pub lemmas_learned: usize,
    /// Maximum frame depth reached
    pub max_frame: usize,
    /// Number of restarts performed
    pub restart_count: usize,
    /// Number of consecutive unlearnable failures
    pub consecutive_unlearnable: usize,
    /// Number of SMT unknown results
    pub smt_unknowns: usize,
    /// Per-predicate lemma counts
    pub lemmas_per_predicate: FxHashMap<PredicateId, usize>,
    /// Maximum counterexample depth explored
    pub max_cex_depth: usize,
    /// Whether any predicate coupling was detected
    pub has_predicate_coupling: bool,

    // ImplicationCache statistics (#2126, #2262)
    /// Number of implication cache hits (exact result reused)
    pub implication_cache_hits: usize,
    /// Number of model rejections (fast rejection via cached countermodel)
    pub implication_model_rejections: usize,
    /// Number of solver calls recorded by the implication cache
    pub implication_solver_calls: usize,
    /// CHC native helper compile attempts.
    pub chc_native_code_helper_compile_attempts: usize,
    /// CHC native helper successful compilations.
    pub chc_native_code_helper_compile_successes: usize,
    /// CHC native helper failed or unsupported compilations.
    pub chc_native_code_helper_compile_failures: usize,
    /// CHC native helper evaluation attempts.
    pub chc_native_code_helper_evaluations: usize,
    /// CHC native helper deopts to conservative evaluation.
    pub chc_native_code_helper_deopts: usize,
    /// CHC native helper fallbacks to the interpreter path.
    pub chc_native_code_helper_fallbacks: usize,
    /// CHC native helper fallbacks caused by missing model bindings.
    pub chc_native_code_helper_missing_var_fallbacks: usize,
    /// CHC native helper true results checked by the interpreter oracle.
    pub chc_native_code_helper_interpreter_confirmations: usize,
    /// CHC native helper true results accepted by the trusted grammar.
    pub chc_native_code_helper_trusted_true_results: usize,
    /// CHC native helper applications that accepted a native true result.
    pub chc_native_code_helper_applications: usize,
    /// Profile-only TLA transition-cluster metadata applications.
    pub chc_tla_transition_cluster_applications: usize,
    /// Distinct symbolic array-scalarization projected cells.
    pub symbolic_scalarization_projected_cells: usize,
    /// Original predicate array args with more than one distinct symbolic projected cell.
    pub symbolic_scalarization_multi_cell_args: usize,
    /// Number of SAT predecessor queries where cube extraction failed
    pub sat_no_cube_events: usize,
    /// Entry-inductiveness conservative-failure counters by reason key.
    ///
    /// Keys come from `EntryInductiveFailureReason::as_str()`.
    pub entry_inductive_failure_counts: FxHashMap<String, usize>,

    // Convergence monitoring data
    /// Wall-clock seconds elapsed during solving.
    pub elapsed_secs: f64,
    /// Wall-clock seconds since the last frame advancement.
    pub secs_since_frame_advance: f64,
    /// Number of consecutive stagnant windows detected by the convergence monitor.
    pub consecutive_stagnant_windows: usize,
    /// Whether the solver terminated due to convergence stagnation detection.
    pub terminated_by_stagnation: bool,
}

impl SolverStats {
    /// Total lemma count.
    ///
    /// # Contracts
    ///
    /// ENSURES: Returns `self.lemmas_learned`.
    pub(crate) fn total_lemmas(&self) -> usize {
        self.lemmas_learned
    }

    /// Lemma rate per iteration.
    ///
    /// # Contracts
    ///
    /// ENSURES: If `self.iterations == 0`, returns `0.0`.
    /// ENSURES: If `self.iterations > 0`, returns `self.lemmas_learned / self.iterations`.
    pub(crate) fn lemma_rate(&self) -> f64 {
        if self.iterations == 0 {
            0.0
        } else {
            self.lemmas_learned as f64 / self.iterations as f64
        }
    }
}

/// Analysis of a failed solving attempt
#[derive(Debug, Clone)]
pub(crate) struct FailureAnalysis {
    /// Primary failure mode detected
    pub mode: FailureMode,
    /// Predicate that was "stuck" (if identifiable)
    pub stuck_predicate: Option<PredicateId>,
    /// Maximum counterexample depth reached
    pub max_cex_depth: usize,
    /// Confidence score (0.0 to 1.0) in the failure mode classification
    pub confidence: f64,
    /// Detailed diagnostic message
    pub diagnostic: String,
}

impl FailureAnalysis {
    /// Create analysis from solver statistics.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `stats` contains valid solver statistics (non-negative counts).
    ///
    /// ENSURES: Returns a `FailureAnalysis` with:
    ///          1. `mode` reflects the most likely failure reason based on `stats`
    ///          2. `confidence` is in range `[0.0, 1.0]`
    ///          3. `stuck_predicate` is set if one predicate has >50% of lemmas
    ///          4. `max_cex_depth` equals `stats.max_cex_depth`
    pub(crate) fn from_stats(stats: &SolverStats) -> Self {
        let entry_inductive_failures: usize = stats.entry_inductive_failure_counts.values().sum();
        let mut analysis = Self {
            mode: FailureMode::ResourceExhausted,
            stuck_predicate: None,
            max_cex_depth: stats.max_cex_depth,
            confidence: 0.5,
            diagnostic: String::new(),
        };

        // Classify failure mode based on statistics
        // Check convergence stagnation first (highest confidence when flagged)
        if stats.terminated_by_stagnation {
            analysis.mode = FailureMode::ConvergenceStagnation;
            analysis.confidence = 0.95;
            analysis.diagnostic = format!(
                "Convergence stagnation: {}s elapsed, {}s since frame advance, \
                 {} stagnant windows",
                stats.elapsed_secs as u64,
                stats.secs_since_frame_advance as u64,
                stats.consecutive_stagnant_windows,
            );
        // Guard against division by zero: require at least some iterations
        } else if stats.iterations > 0 && stats.smt_unknowns > stats.iterations / 4 {
            // More than 25% SMT unknowns suggests SMT pressure
            analysis.mode = FailureMode::SmtTimeout;
            analysis.confidence = (stats.smt_unknowns as f64 / stats.iterations as f64).min(1.0);
            analysis.diagnostic = format!(
                "High SMT timeout rate: {}/{} queries unknown",
                stats.smt_unknowns, stats.iterations
            );
        } else if stats.consecutive_unlearnable > 10 {
            // Many consecutive failures to learn suggests weak lemmas or stuck state
            analysis.mode = FailureMode::WeakLemmas;
            analysis.confidence = (stats.consecutive_unlearnable as f64 / 20.0).min(1.0);
            analysis.diagnostic = format!(
                "Unable to learn new lemmas: {} consecutive failures",
                stats.consecutive_unlearnable
            );
        } else if stats.max_cex_depth > stats.max_frame * 2 {
            // CEX depth much larger than frames suggests deep counterexamples
            analysis.mode = FailureMode::DeepCounterexample;
            analysis.confidence = 0.7;
            analysis.diagnostic = format!(
                "Deep counterexample exploration: depth {} vs {} frames",
                stats.max_cex_depth, stats.max_frame
            );
        } else if stats.restart_count > 5 && stats.lemma_rate() < 0.1 {
            // Many restarts with few lemmas suggests oscillation
            analysis.mode = FailureMode::Oscillation;
            analysis.confidence = 0.6;
            analysis.diagnostic = format!(
                "Potential oscillation: {} restarts, {:.2} lemmas/iter",
                stats.restart_count,
                stats.lemma_rate()
            );
        } else if stats.has_predicate_coupling {
            analysis.mode = FailureMode::PredicateCoupling;
            analysis.confidence = 0.8;
            analysis.diagnostic = "Inter-predicate coupling detected".to_string();
        }
        if entry_inductive_failures > 0 {
            let suffix = format!("entry-inductiveness failures={entry_inductive_failures}");
            if analysis.diagnostic.is_empty() {
                analysis.diagnostic = suffix;
            } else {
                analysis.diagnostic.push_str("; ");
                analysis.diagnostic.push_str(&suffix);
            }
        }

        // Identify stuck predicate
        if let Some((&pred, &count)) = stats.lemmas_per_predicate.iter().max_by_key(|(_, &c)| c) {
            // Predicate with most lemmas is likely where we're stuck
            if count > stats.total_lemmas() / 2 {
                analysis.stuck_predicate = Some(pred);
            }
        }

        analysis
    }
}

/// Guided configuration adjustments based on failure analysis
#[derive(Debug, Clone)]
pub(crate) struct FailureGuide {
    /// Suggested changes to PDR configuration
    pub adjustments: Vec<ConfigAdjustment>,
    /// Whether to try a different engine instead of PDR
    pub try_alternative_engine: Option<AlternativeEngine>,
}

/// Specific configuration adjustment recommendation
#[derive(Debug, Clone)]
pub(crate) enum ConfigAdjustment {
    /// Increase generalization aggressiveness
    StrongerGeneralization,
    /// Increase max frames to allow more exploration
    IncreaseMaxFrames(usize),
    /// Add more iterations budget
    IncreaseIterations(usize),
    /// Enable or tune specific feature
    EnableFeature(String),
    /// Disable feature that may be causing issues
    DisableFeature(String),
}

/// Alternative engine recommendation
#[derive(Debug, Clone)]
pub(crate) enum AlternativeEngine {
    /// Try BMC to confirm/refute counterexample
    Bmc { suggested_depth: usize },
}

impl FailureGuide {
    /// Generate guidance from failure analysis.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `analysis` is a valid FailureAnalysis from `FailureAnalysis::from_stats`.
    ///
    /// ENSURES: Returns a `FailureGuide` with:
    ///          1. `adjustments` contains config changes appropriate for `analysis.mode`
    ///          2. `try_alternative_engine` is set if mode suggests a different engine
    ///          3. `confidence` equals `analysis.confidence`
    pub(crate) fn from_analysis(analysis: &FailureAnalysis) -> Self {
        let mut guide = Self {
            adjustments: Vec::new(),
            try_alternative_engine: None,
        };

        match analysis.mode {
            FailureMode::WeakLemmas => {
                guide
                    .adjustments
                    .push(ConfigAdjustment::StrongerGeneralization);
                guide
                    .adjustments
                    .push(ConfigAdjustment::EnableFeature("use_farkas".to_string()));
            }
            FailureMode::DeepCounterexample => {
                // Verify with BMC whether the CEX is real
                guide.try_alternative_engine = Some(AlternativeEngine::Bmc {
                    suggested_depth: analysis.max_cex_depth + 10,
                });
            }
            FailureMode::Oscillation => {
                guide
                    .adjustments
                    .push(ConfigAdjustment::EnableFeature("use_restarts".to_string()));
                guide
                    .adjustments
                    .push(ConfigAdjustment::IncreaseIterations(2000));
            }
            FailureMode::PredicateCoupling => {
                // Multi-predicate coupling - try decomposition or joint reasoning
                guide.adjustments.push(ConfigAdjustment::EnableFeature(
                    "use_convex_closure".to_string(),
                ));
            }
            FailureMode::SmtTimeout => {
                // Reduce SMT pressure
                guide.adjustments.push(ConfigAdjustment::DisableFeature(
                    "use_convex_closure".to_string(),
                ));
                guide
                    .adjustments
                    .push(ConfigAdjustment::IncreaseMaxFrames(100));
            }
            FailureMode::ResourceExhausted => {
                // Generic: try more resources
                guide
                    .adjustments
                    .push(ConfigAdjustment::IncreaseMaxFrames(200));
                guide
                    .adjustments
                    .push(ConfigAdjustment::IncreaseIterations(10000));
            }
            FailureMode::ConvergenceStagnation => {
                // PDR was stagnating — try a different approach entirely.
                // Enable stronger generalization for the retry to escape the
                // local minimum that caused stagnation.
                guide
                    .adjustments
                    .push(ConfigAdjustment::StrongerGeneralization);
                // Also suggest BMC to check if the system is actually unsafe
                // (stagnation may indicate the problem is UNSAT but PDR's
                // lemma generalization cannot express the invariant).
                guide.try_alternative_engine = Some(AlternativeEngine::Bmc {
                    suggested_depth: analysis.max_cex_depth.max(20) + 10,
                });
            }
        }

        guide
    }

    /// Apply guidance to create a new PDR configuration.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `config` is a valid PdrConfig.
    ///
    /// ENSURES: Returns a new PdrConfig with:
    ///          1. Each adjustment in `self.adjustments` applied
    ///          2. `max_frames` and `max_iterations` are >= their original values
    ///          3. Feature toggles reflect all EnableFeature/DisableFeature adjustments
    pub(crate) fn apply_to_config(&self, mut config: PdrConfig) -> PdrConfig {
        for adjustment in &self.adjustments {
            match adjustment {
                ConfigAdjustment::StrongerGeneralization => {
                    // Enable more aggressive generalization features, but respect
                    // max_escalation_level cap (#7930). When PDR escalation is
                    // capped (e.g., DT problems), these features are unproductive.
                    if config.max_escalation_level > 0 {
                        config.use_farkas_combination = true;
                        config.use_relational_equality = true;
                        config.use_range_weakening = true;
                    }
                }
                ConfigAdjustment::IncreaseMaxFrames(frames) => {
                    config.max_frames = config.max_frames.max(*frames);
                }
                ConfigAdjustment::IncreaseIterations(iters) => {
                    config.max_iterations = config.max_iterations.max(*iters);
                }
                ConfigAdjustment::EnableFeature(feature) => match feature.as_str() {
                    "use_farkas" => config.use_farkas_combination = true,
                    "use_interpolation" => config.use_interpolation = true,
                    "use_convex_closure" => config.use_convex_closure = true,
                    "use_restarts" => config.use_restarts = true,
                    _ => {}
                },
                ConfigAdjustment::DisableFeature(feature) => match feature.as_str() {
                    "use_convex_closure" => config.use_convex_closure = false,
                    "use_interpolation" => config.use_interpolation = false,
                    _ => {}
                },
            }
        }
        config
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "failure_analysis_tests.rs"]
mod tests;
