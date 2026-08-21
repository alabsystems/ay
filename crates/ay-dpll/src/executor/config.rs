// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `executor` to preserve constant paths and visibility.

/// Bounded E-matching passes per check-sat to allow instantiation chaining.
///
/// Each round builds a fresh TermIndex, so terms created by instantiation in
/// round N become matchable in round N+1. A chain of depth D (where axiom A's
/// output triggers axiom B, whose output triggers axiom C, etc.) requires D
/// rounds.
///
/// Budget 16 covers typical axiom chains in verification-consumer's 21-axiom Seq encoding
/// (#3994) plus deeper iterator/permutation clusters whose instantiation chains
/// exceed the original budget of 8 (the chain output of round N only becomes
/// matchable in round N+1, so an axiom family of depth D needs D rounds).
/// Generation-based cost filtering (eager/lazy thresholds) prevents
/// self-triggering patterns from consuming the budget, and the solve deadline
/// floor keeps each chain terminating even when the round budget is raised.
const MAX_EMATCHING_ROUNDS: usize = 16;

/// Hard ceiling on the configurable E-matching round limit.
///
/// Callers (e.g. verification-consumer proof obligations) may raise the per-solver round
/// limit via [`Executor::set_ematching_round_limit`] up to this bound to allow
/// very deep quantifier chains. The solve deadline still bounds wall-clock
/// time, so a high ceiling cannot cause a non-terminating solve.
const MAX_EMATCHING_ROUND_CEILING: usize = 128;

/// Maximum interleaved E-matching refinement rounds after initial SAT solve.
///
/// After the initial E-matching preprocessing + SAT solve, the interleaved loop
/// re-runs E-matching with the fresh EUF model from the solve. New congruence
/// equalities discovered during solving can trigger new pattern matches that
/// weren't available during preprocessing. Each round: E-match → add instances
/// → re-solve → repeat until fixpoint or budget (#5927).
///
/// Budget 4 is conservative — enough for typical multi-step quantifier chains
/// (e.g., verification-consumer's `f(g(a)) = b` patterns that need 2-3 rounds) without
/// excessive overhead on already-converged formulas.
const MAX_INTERLEAVED_EMATCHING_ROUNDS: usize = 4;

/// Parsed-assertion sentinel for constraints authored through the native API.
///
/// Native assertions have no SMT-LIB surface term to re-elaborate during proof
/// reconstruction.  Both anonymous and named assertions must therefore carry
/// the same sentinel: the optional name is unsat-core metadata, not syntax.
pub(crate) const NATIVE_API_ASSERTION_PLACEHOLDER: &str = "__ay_api_assertion__";
