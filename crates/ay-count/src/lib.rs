#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! # ay-count — exact model counting for the Model Counting Competition
//! A competition-grade exact counter covering every MC-2026 track:
//! | track | type | value domain |
//! |-------|------|--------------|
//! | 1 / 1F | `mc` | arbitrary-precision naturals |
//! | 2B | `wmc` | exact rationals (zero/negative weights supported) |
//! | 3 | `pmc` | arbitrary-precision naturals |
//! | 4 | `wmc`/`pmc`/`pwmc` | rationals |
//! | 5B | `amc-complex` | complex rationals |
//! The engine is an exhaustive DPLL with dynamic component decomposition and
//! component caching (sharpSAT/GANAK architecture), generic over the value
//! semiring; projected instances existentially check projection-free
//! components with the `ay-sat` CDCL solver. All arithmetic is exact.
//! ## Fail-closed contract
//! Any condition the counter cannot handle exactly (oracle `Unknown`,
//! malformed input) surfaces as an error or an `UNKNOWN` outcome — never a
//! best-effort count. A returned count is always exact.

pub mod cache;
pub mod engine;
mod options;
pub mod output;
pub mod parse;
pub mod prep;
pub mod prep_eg;
pub mod td;
mod threaded;
pub mod value;
pub mod xor;

pub use options::{SolveOptions, SolveOptionsError};
pub use threaded::solve_instance_big_stack;

use engine::{CountAbort, Engine, EngineConfig};
use num_rational::BigRational;
use output::{ExactValue, SolveOutcome};
use parse::{Instance, ProblemType};
use value::{GaussInt, WeightTable};

/// Scale per-literal rational weights to integer numerators over per-var
/// denominators; returns the scaled table and the global denominator
/// `prod(d_v)`. Every model's weight product carries each var's denominator
/// exactly once (each var is assigned one polarity, or free contributing
/// `w+w̄` — same denominator), so `integer count / global denominator` is
/// exactly the weighted count. Unweighted vars have d_v = 1.
fn scale_weights_to_integers(
    weights: &[BigRational],
) -> (Vec<num_bigint::BigInt>, num_bigint::BigInt) {
    use num_integer::Integer;
    let one = num_bigint::BigInt::from(1);
    let mut global_den = one.clone();
    let mut scaled = Vec::with_capacity(weights.len());
    for pair in weights.chunks(2) {
        let d = pair[0].denom().lcm(pair[1].denom());
        scaled.push(pair[0].numer() * (&d / pair[0].denom()));
        scaled.push(pair[1].numer() * (&d / pair[1].denom()));
        global_den *= &d;
    }
    (scaled, global_den)
}

/// Complex analogue: one denominator per variable covering all four parts.
fn scale_complex_weights_to_integers(
    weights: &[(BigRational, BigRational)],
) -> (Vec<GaussInt>, num_bigint::BigInt) {
    use num_integer::Integer;
    let mut global_den = num_bigint::BigInt::from(1);
    let mut scaled = Vec::with_capacity(weights.len());
    for pair in weights.chunks(2) {
        let (pre, pim) = &pair[0];
        let (nre, nim) = &pair[1];
        let d = pre
            .denom()
            .lcm(pim.denom())
            .lcm(&nre.denom().lcm(nim.denom()));
        scaled.push(GaussInt::new(
            pre.numer() * (&d / pre.denom()),
            pim.numer() * (&d / pim.denom()),
        ));
        scaled.push(GaussInt::new(
            nre.numer() * (&d / nre.denom()),
            nim.numer() * (&d / nim.denom()),
        ));
        global_den *= &d;
    }
    (scaled, global_den)
}

/// Run the counting engine with the two-phase TD strategy: phase 1 solves
/// without TD scores under a short deadline; if it expires, compute the tree
/// decomposition (full budget) and re-solve without a deadline. Easy
/// instances never pay the TD cost; hard ones amortize it.
fn count_with_phases<W: value::CountValue>(
    num_vars: usize,
    clauses: &[Vec<i32>],
    weights: WeightTable<W>,
    show: Option<&[u32]>,
    options: &SolveOptions,
    warnings: &mut Vec<String>,
) -> (Engine<W>, Result<W, CountAbort>) {
    let phase1_budget = std::time::Duration::try_from_secs_f64(options.phase1_secs).ok();
    let td_budget = std::time::Duration::try_from_secs_f64(options.td_budget_secs).ok();
    // TD-first for small primal graphs: FlowCutter converges in ~a second
    // there and the guided branching is worth orders of magnitude, so
    // skipping phase 1 is strictly better (loss analysis: 100-2300x decision
    // reductions on small low-width instances).
    let approx_edges: usize = clauses
        .iter()
        .filter(|c| c.len() <= 100) // mirrors td_scores' long-clause skip
        .map(|c| c.len() * (c.len().saturating_sub(1)) / 2)
        .sum();
    // Lower bound: tiny graphs solve in milliseconds inside phase 1 —
    // spawning FlowCutter there is a pure ~1s tax (and phase-1 expiry still
    // routes them to TD if they turn out hard).
    let td_first = num_vars <= 20_000 && (1_000..=50_000).contains(&approx_edges);
    if ay_core::misc_cli_flags().count_debug {
        eprintln!("c o [debug] scheduling: approx_edges={approx_edges} td_first={td_first}");
    }
    let phase1_deadline = phase1_budget
        .filter(|budget| !budget.is_zero())
        .and_then(|budget| std::time::Instant::now().checked_add(budget));
    let two_phase =
        td_budget.is_some_and(|budget| !budget.is_zero()) && phase1_deadline.is_some() && !td_first;
    if two_phase {
        let mut phase1: Engine<W> = Engine::new(
            num_vars,
            clauses,
            weights.clone(),
            show,
            EngineConfig {
                cache_budget_bytes: options.cache_budget_bytes,
                deadline: phase1_deadline,
            },
        );
        match phase1.count() {
            Err(CountAbort::Deadline) => {
                warnings.push(format!(
                    "phase 1 ({}s, no TD) expired; computing tree decomposition",
                    options.phase1_secs
                ));
                if ay_core::misc_cli_flags().count_debug {
                    eprintln!(
                        "c o [debug] phase1 expired after {}s (decisions={} conflicts={} cache_stores={})",
                        options.phase1_secs,
                        phase1.stats.decisions,
                        phase1.stats.conflicts,
                        phase1.stats.cache_stores
                    );
                }
            }
            result => return (phase1, result),
        }
    }
    // Phase 2 (or single-phase): optional TD scores, no deadline.
    let td_scores = if let Some(td_budget) = td_budget.filter(|budget| !budget.is_zero()) {
        match td::find_flow_cutter(options.flow_cutter.as_deref()) {
            Some(fc) => {
                let scores = td::td_scores(num_vars, clauses, td_budget, options.decow, &fc);
                match &scores {
                    Some(s) => {
                        warnings.push("TD scores active".to_string());
                        if ay_core::misc_cli_flags().count_debug {
                            let max = s.iter().copied().fold(0.0f64, f64::max);
                            eprintln!("c o [debug] TD scores active, max_score={max:.1}");
                        }
                    }
                    None => {
                        warnings
                            .push("TD skipped (graph guard or decomposition failure)".to_string());
                        if ay_core::misc_cli_flags().count_debug {
                            eprintln!("c o [debug] TD skipped");
                        }
                    }
                }
                scores
            }
            None => {
                warnings.push("TD skipped (no flow_cutter binary found)".to_string());
                None
            }
        }
    } else {
        None
    };
    let mut engine: Engine<W> = Engine::new(
        num_vars,
        clauses,
        weights,
        show,
        EngineConfig {
            cache_budget_bytes: options.cache_budget_bytes,
            deadline: None,
        },
    );
    if let Some(scores) = td_scores {
        engine.set_td_scores(scores);
    }
    let result = engine.count();
    (engine, result)
}

include!("weight_preparation.rs");

fn solve_unweighted(
    instance: &Instance,
    clauses: &[Vec<i32>],
    options: &SolveOptions,
    mut warnings: Vec<String>,
) -> SolveOutcome {
    // Pure-XOR shortcut (unprojected only): GF(2) elimination gives
    // the exact count without search.
    let unprojected = instance
        .show
        .as_ref()
        .is_none_or(|show| show.len() == instance.num_vars);
    if unprojected {
        if let Some(count) = xor::pure_xor_count(instance.num_vars, clauses) {
            warnings.push("pure-XOR system: counted by GF(2) elimination".into());
            let satisfiable = !num_traits::Zero::is_zero(&count);
            return SolveOutcome {
                ptype: instance.ptype,
                satisfiable: Some(satisfiable),
                value: Some(ExactValue::Nat(count)),
                warnings,
                stats: None,
            };
        }
    }
    // Independent support (unweighted, unprojected): if every var outside S
    // is Padoa-defined by S, projected models extend uniquely, so pmc(F, S) =
    // #F. Branching restricted to S with SAT-checked remainders is dramatically
    // cheaper on gate-heavy instances (ganak's signature preprocessing).
    let indep_show: Option<Vec<u32>> = if unprojected {
        let started = std::time::Instant::now();
        let support = prep_eg::independent_support(
            instance.num_vars,
            clauses,
            std::time::Duration::from_secs(5),
            100,
        );
        if ay_core::misc_cli_flags().count_debug {
            eprintln!(
                "c o [debug] indep support: {:?} vars in {:.2}s",
                support.as_ref().map(Vec::len),
                started.elapsed().as_secs_f64()
            );
        }
        support
    } else {
        None
    };
    let effective_show: Option<&[u32]> = match &indep_show {
        Some(show) => {
            warnings.push(format!(
                "independent support: {} of {} occurring vars",
                show.len(),
                instance.num_vars
            ));
            Some(show.as_slice())
        }
        None => instance.show.as_deref(),
    };
    let (engine, result) = count_with_phases::<num_bigint::BigUint>(
        instance.num_vars,
        clauses,
        WeightTable::unweighted(),
        effective_show,
        options,
        &mut warnings,
    );
    match result {
        Ok(count) => {
            let satisfiable = !num_traits::Zero::is_zero(&count);
            SolveOutcome {
                ptype: instance.ptype,
                satisfiable: Some(satisfiable),
                value: Some(ExactValue::Nat(count)),
                warnings,
                stats: options.stats.then(|| engine.stats.clone()),
            }
        }
        Err(abort) => unknown_outcome(instance.ptype, warnings, abort),
    }
}

fn solve_real_weighted(
    instance: &Instance,
    clauses: &[Vec<i32>],
    options: &SolveOptions,
    mut warnings: Vec<String>,
    weights: &[BigRational],
) -> SolveOutcome {
    // Every model's weight product carries each variable's denominator exactly
    // once. Count integer numerators, then divide by their product once.
    let (scaled, global_den) = scale_weights_to_integers(weights);
    let (mut engine, result) = count_with_phases::<num_bigint::BigInt>(
        instance.num_vars,
        clauses,
        WeightTable::weighted(scaled),
        instance.show.as_deref(),
        options,
        &mut warnings,
    );
    match result {
        Ok(int_count) => {
            let count = BigRational::new(int_count, global_den);
            let satisfiable = if num_traits::Zero::is_zero(&count) {
                // Zero weighted count does not imply UNSAT (zero weights).
                engine.formula_is_sat().ok()
            } else {
                Some(true)
            };
            SolveOutcome {
                ptype: instance.ptype,
                satisfiable,
                value: Some(ExactValue::Rat(count)),
                warnings,
                stats: options.stats.then(|| engine.stats.clone()),
            }
        }
        Err(abort) => unknown_outcome(instance.ptype, warnings, abort),
    }
}

fn solve_complex_weighted(
    instance: &Instance,
    clauses: &[Vec<i32>],
    options: &SolveOptions,
    mut warnings: Vec<String>,
    weights: &[(BigRational, BigRational)],
) -> SolveOutcome {
    // Use the same integer-scaling technique over Gaussian integers.
    let (scaled, global_den) = scale_complex_weights_to_integers(weights);
    let (mut engine, result) = count_with_phases::<GaussInt>(
        instance.num_vars,
        clauses,
        WeightTable::weighted(scaled),
        instance.show.as_deref(),
        options,
        &mut warnings,
    );
    match result {
        Ok(count) => {
            let is_zero = value::CountValue::is_zero(&count);
            let re = BigRational::new(count.re, global_den.clone());
            let im = BigRational::new(count.im, global_den);
            let satisfiable = if is_zero {
                engine.formula_is_sat().ok()
            } else {
                Some(true)
            };
            SolveOutcome {
                ptype: instance.ptype,
                satisfiable,
                value: Some(ExactValue::Complex(re, im)),
                warnings,
                stats: options.stats.then(|| engine.stats.clone()),
            }
        }
        Err(abort) => unknown_outcome(instance.ptype, warnings, abort),
    }
}

/// Solve a parsed instance, producing a renderable outcome.
///
/// This runs on the calling thread; the recursion depth is bounded by the
/// variable count, so callers should provide a large stack (see
/// [`solve_instance_big_stack`]).
/// Invalid options, inconsistent public [`Instance`] fields, and malformed
/// weight declarations produce an `UNKNOWN` outcome with no value.
pub fn solve_instance(instance: &Instance, options: &SolveOptions) -> SolveOutcome {
    let mut warnings = instance.warnings.clone();
    if let Err(error) = options.validate() {
        return no_value_outcome(instance.ptype, warnings, error.to_string());
    }
    if let Err(error) = instance.validate() {
        return format_error_outcome(instance.ptype, warnings, error);
    }
    let prepared_weights = match prepare_weights(instance, &mut warnings) {
        Ok(prepared) => prepared,
        Err(error) => return format_error_outcome(instance.ptype, warnings, error),
    };
    // Count-safe preprocessing (equivalence-preserving: same models over the
    // same variables, so sound for every track).
    let weighted = matches!(
        instance.ptype,
        ProblemType::Wmc | ProblemType::Pwmc | ProblemType::AmcComplex
    );
    let projected = instance
        .show
        .as_ref()
        .is_some_and(|s| s.len() < instance.num_vars);
    let prepped = prep::preprocess(
        instance.num_vars,
        &instance.clauses,
        prep::PrepOptions {
            weighted,
            projected,
        },
    );
    if prepped.unsat {
        let value = match instance.ptype {
            ProblemType::Mc | ProblemType::Pmc => ExactValue::Nat(num_traits::Zero::zero()),
            ProblemType::Wmc | ProblemType::Pwmc => ExactValue::Rat(num_traits::Zero::zero()),
            ProblemType::AmcComplex => {
                ExactValue::Complex(num_traits::Zero::zero(), num_traits::Zero::zero())
            }
        };
        return SolveOutcome {
            ptype: instance.ptype,
            satisfiable: Some(false),
            value: Some(value),
            warnings,
            stats: None,
        };
    }
    if ay_core::misc_cli_flags().count_debug {
        eprintln!(
            "c o [debug] prep: fixed={} vivified={} merged={} pinned={} clauses={} model_preserving={}",
            prepped.fixed_count,
            prepped.vivified_lits,
            prepped.merged_literals,
            prepped.pinned_defined.len(),
            prepped.clauses.len(),
            prepped.model_preserving,
        );
    }
    let clauses = &prepped.clauses;

    match prepared_weights {
        PreparedWeights::Unweighted => solve_unweighted(instance, clauses, options, warnings),
        PreparedWeights::Real(weights) => {
            solve_real_weighted(instance, clauses, options, warnings, &weights)
        }
        PreparedWeights::Complex(weights) => {
            solve_complex_weighted(instance, clauses, options, warnings, &weights)
        }
    }
}

fn unknown_outcome(
    ptype: ProblemType,
    mut warnings: Vec<String>,
    abort: CountAbort,
) -> SolveOutcome {
    warnings.push(format!("count aborted: {abort:?}"));
    SolveOutcome {
        ptype,
        satisfiable: None,
        value: None,
        warnings,
        stats: None,
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
