#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! # ay-count — exact model counting for the Model Counting Competition
//!
//! A competition-grade exact counter covering every MC-2026 track:
//!
//! | track | type | value domain |
//! |-------|------|--------------|
//! | 1 / 1F | `mc` | arbitrary-precision naturals |
//! | 2B | `wmc` | exact rationals (zero/negative weights supported) |
//! | 3 | `pmc` | arbitrary-precision naturals |
//! | 4 | `wmc`/`pmc`/`pwmc` | rationals |
//! | 5B | `amc-complex` | complex rationals |
//!
//! The engine is an exhaustive DPLL with dynamic component decomposition and
//! component caching (sharpSAT/GANAK architecture), generic over the value
//! semiring; projected instances existentially check projection-free
//! components with the `ay-sat` CDCL solver. All arithmetic is exact.
//!
//! ## Fail-closed contract
//!
//! Any condition the counter cannot handle exactly (oracle `Unknown`,
//! malformed input) surfaces as an error or an `UNKNOWN` outcome — never a
//! best-effort count. A returned count is always exact.

pub mod cache;
pub mod engine;
pub mod output;
pub mod parse;
pub mod prep;
pub mod prep_eg;
pub mod td;
pub mod value;
pub mod xor;

use engine::{CountAbort, Engine, EngineConfig};
use num_rational::BigRational;
use output::{ExactValue, SolveOutcome};
use parse::{Instance, ProblemType};
use value::{GaussInt, WeightTable};

/// Options for a solve run.
pub struct SolveOptions {
    /// Component-cache budget in bytes.
    pub cache_budget_bytes: usize,
    /// Attach engine statistics to the outcome.
    pub stats: bool,
    /// Tree-decomposition time budget in seconds (0 disables TD scoring).
    pub td_budget_secs: f64,
    /// Phase-1 budget: solve WITHOUT TD scores for this long first; only on
    /// expiry compute the tree decomposition and re-solve (easy instances
    /// never pay the TD cost). 0 = single-phase.
    pub phase1_secs: f64,
    /// TD score weight (`decow`; competition value 100).
    pub decow: f64,
    /// Explicit FlowCutter binary path (else `AY_FLOWCUTTER` env / exe dir /
    /// PATH).
    pub flow_cutter: Option<std::path::PathBuf>,
}

impl Default for SolveOptions {
    fn default() -> Self {
        Self {
            cache_budget_bytes: EngineConfig::default().cache_budget_bytes,
            stats: false,
            td_budget_secs: 0.0,
            phase1_secs: 10.0,
            decow: 100.0,
            flow_cutter: None,
        }
    }
}

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
    if std::env::var_os("AY_COUNT_DEBUG").is_some() {
        eprintln!("c o [debug] scheduling: approx_edges={approx_edges} td_first={td_first}");
    }
    let two_phase = options.td_budget_secs > 0.0 && options.phase1_secs > 0.0 && !td_first;
    if two_phase {
        let mut phase1: Engine<W> = Engine::new(
            num_vars,
            clauses,
            weights.clone(),
            show,
            EngineConfig {
                cache_budget_bytes: options.cache_budget_bytes,
                deadline: Some(
                    std::time::Instant::now()
                        + std::time::Duration::from_secs_f64(options.phase1_secs),
                ),
            },
        );
        match phase1.count() {
            Err(CountAbort::Deadline) => {
                warnings.push(format!(
                    "phase 1 ({}s, no TD) expired; computing tree decomposition",
                    options.phase1_secs
                ));
                if std::env::var_os("AY_COUNT_DEBUG").is_some() {
                    eprintln!(
                        "c o [debug] phase1 expired after {}s (decisions={} conflicts={} cache_stores={})",
                        options.phase1_secs, phase1.stats.decisions,
                        phase1.stats.conflicts, phase1.stats.cache_stores
                    );
                }
            }
            result => return (phase1, result),
        }
    }
    // Phase 2 (or single-phase): optional TD scores, no deadline.
    let td_scores = if options.td_budget_secs > 0.0 {
        match td::find_flow_cutter(options.flow_cutter.as_deref()) {
            Some(fc) => {
                let scores = td::td_scores(
                    num_vars,
                    clauses,
                    std::time::Duration::from_secs_f64(options.td_budget_secs),
                    options.decow,
                    &fc,
                );
                match &scores {
                    Some(s) => {
                        warnings.push("TD scores active".to_string());
                        if std::env::var_os("AY_COUNT_DEBUG").is_some() {
                            let max = s.iter().copied().fold(0.0f64, f64::max);
                            eprintln!("c o [debug] TD scores active, max_score={max:.1}");
                        }
                    }
                    None => {
                        warnings
                            .push("TD skipped (graph guard or decomposition failure)".to_string());
                        if std::env::var_os("AY_COUNT_DEBUG").is_some() {
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

/// Solve a parsed instance, producing a renderable outcome.
///
/// This runs on the calling thread; the recursion depth is bounded by the
/// variable count, so callers should provide a large stack (see
/// [`solve_instance_big_stack`]).
pub fn solve_instance(instance: &Instance, options: &SolveOptions) -> SolveOutcome {
    let mut warnings = instance.warnings.clone();
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
    if std::env::var_os("AY_COUNT_DEBUG").is_some() {
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

    match instance.ptype {
        ProblemType::Mc | ProblemType::Pmc => {
            // Pure-XOR shortcut (unprojected only): GF(2) elimination gives
            // the exact count without search.
            let unprojected = instance
                .show
                .as_ref()
                .is_none_or(|s| s.len() == instance.num_vars);
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
            // Independent support (unweighted, unprojected): if every var
            // outside S is Padoa-defined by S, projected models extend
            // uniquely, so pmc(F, S) = #F — and branching restricted to S
            // with SAT-checked remainders is dramatically cheaper on
            // gate-heavy instances (ganak's signature preprocessing).
            let indep_show: Option<Vec<u32>> = if unprojected {
                let t0 = std::time::Instant::now();
                let s = prep_eg::independent_support(
                    instance.num_vars,
                    clauses,
                    std::time::Duration::from_secs(5),
                    100,
                );
                if std::env::var_os("AY_COUNT_DEBUG").is_some() {
                    eprintln!(
                        "c o [debug] indep support: {:?} vars in {:.2}s",
                        s.as_ref().map(Vec::len),
                        t0.elapsed().as_secs_f64()
                    );
                }
                s
            } else {
                None
            };
            let effective_show: Option<&[u32]> = match &indep_show {
                Some(s) => {
                    warnings.push(format!(
                        "independent support: {} of {} occurring vars",
                        s.len(),
                        instance.num_vars
                    ));
                    Some(s.as_slice())
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
        ProblemType::Wmc | ProblemType::Pwmc => {
            let projected_mask = instance.show.as_ref().map(|show| {
                let mut mask = vec![false; instance.num_vars];
                for &v in show {
                    mask[v as usize - 1] = true;
                }
                mask
            });
            let resolved = match parse::resolve_real_weights(
                instance.num_vars,
                &instance.weights,
                projected_mask.as_deref(),
            ) {
                Ok(r) => r,
                Err(e) => {
                    warnings.push(format!("format error: {e}"));
                    return SolveOutcome {
                        ptype: instance.ptype,
                        satisfiable: None,
                        value: None,
                        warnings,
                        stats: None,
                    };
                }
            };
            warnings.extend(resolved.warnings);
            // Integer-scaled weighted counting: scale each variable's weight
            // pair to integer numerators over a per-var denominator; count
            // in signed BigInt (no per-operation gcd), divide once at the
            // end. Sound: every model's weight product carries each var's
            // denominator exactly once (assigned or free), so the integer
            // total equals count * prod(d_v).
            let (scaled, global_den) = scale_weights_to_integers(&resolved.weights);
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
                    let count = BigRational::new(int_count, global_den.clone());
                    let satisfiable = if num_traits::Zero::is_zero(&count) {
                        // Zero weighted count does not imply UNSAT (zero
                        // weights); decide the s line with a SAT check.
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
        ProblemType::AmcComplex => {
            let resolved =
                match parse::resolve_complex_weights(instance.num_vars, &instance.weights) {
                    Ok(r) => r,
                    Err(e) => {
                        warnings.push(format!("format error: {e}"));
                        return SolveOutcome {
                            ptype: instance.ptype,
                            satisfiable: None,
                            value: None,
                            warnings,
                            stats: None,
                        };
                    }
                };
            warnings.extend(resolved.warnings);
            // Same integer-scaling trick over Gaussian integers.
            let (scaled, global_den) = scale_complex_weights_to_integers(&resolved.weights);
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

/// Solve on a dedicated thread with a large stack (the counting recursion is
/// as deep as the variable count in the worst case).
pub fn solve_instance_big_stack(instance: Instance, options: SolveOptions) -> SolveOutcome {
    const STACK_BYTES: usize = 1 << 30;
    std::thread::Builder::new()
        .name("ay-count".into())
        .stack_size(STACK_BYTES)
        .spawn(move || solve_instance(&instance, &options))
        .expect("spawn counting thread")
        .join()
        .expect("counting thread panicked")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_text(text: &str) -> SolveOutcome {
        let instance = parse::parse_instance(text).expect("parses");
        solve_instance(&instance, &SolveOptions::default())
    }

    #[test]
    fn end_to_end_spec_example_1() {
        let text = "p cnf 6 4\nc t mc\n-1 -2\n0\n2 3 -4 0\n4 5 0\n4 6 0\n";
        let outcome = solve_text(text);
        assert_eq!(outcome.satisfiable, Some(true));
        assert_eq!(
            outcome.value,
            Some(ExactValue::Nat(num_bigint::BigUint::from(22u32)))
        );
        let rendered = output::render(&outcome);
        assert!(rendered.contains("c s exact arb int 22"));
    }

    #[test]
    fn end_to_end_spec_example_2_weighted() {
        let text = "p cnf 6 4\nc t wmc\n\
            c p weight 1 0.4 0\nc p weight 2 0.5 0\nc p weight 3 0.4 0\n\
            c p weight 4 0.3 0\nc p weight 5 0.5 0\nc p weight 6 0.7 0\n\
            -1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
        let outcome = solve_text(text);
        // Complements default to 1-w with warnings. Cross-check against an
        // independent brute-force computation (the spec's own example text
        // is inconsistent between 0.345 and 0.346, so compute the truth).
        assert_eq!(outcome.satisfiable, Some(true));
        let clauses = vec![vec![-1, -2], vec![2, 3, -4], vec![4, 5], vec![4, 6]];
        let expected = brute_force_weighted(
            6,
            &clauses,
            &[
                ("0.4", "0.6"),
                ("0.5", "0.5"),
                ("0.4", "0.6"),
                ("0.3", "0.7"),
                ("0.5", "0.5"),
                ("0.7", "0.3"),
            ],
        );
        match &outcome.value {
            Some(ExactValue::Rat(r)) => {
                assert_eq!(*r, expected, "weighted count mismatch: {r}");
            }
            other => panic!("expected rational, got {other:?}"),
        }
    }

    /// Brute-force real weighted count; weights[(v-1)] = (w(v), w(-v)).
    fn brute_force_weighted(
        num_vars: usize,
        clauses: &[Vec<i32>],
        weights: &[(&str, &str)],
    ) -> BigRational {
        use num_traits::{One, Zero};
        let w: Vec<(BigRational, BigRational)> = weights
            .iter()
            .map(|(p, n)| {
                (
                    parse::parse_rational(p).unwrap(),
                    parse::parse_rational(n).unwrap(),
                )
            })
            .collect();
        let mut total = BigRational::zero();
        for m in 0..(1u64 << num_vars) {
            let sat = clauses.iter().all(|cl| {
                cl.iter().any(|&l| {
                    let v = l.unsigned_abs() as usize - 1;
                    let bit = (m >> v) & 1 == 1;
                    if l > 0 {
                        bit
                    } else {
                        !bit
                    }
                })
            });
            if !sat {
                continue;
            }
            let mut prod = BigRational::one();
            for v in 0..num_vars {
                let bit = (m >> v) & 1 == 1;
                prod *= if bit { &w[v].0 } else { &w[v].1 };
            }
            total += prod;
        }
        total
    }

    #[test]
    fn end_to_end_spec_example_4_projected() {
        let text = "p cnf 6 4 2\nc t pmc\nc p show 1 2 0\n-1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
        let outcome = solve_text(text);
        assert_eq!(outcome.satisfiable, Some(true));
        assert_eq!(
            outcome.value,
            Some(ExactValue::Nat(num_bigint::BigUint::from(3u32)))
        );
    }

    #[test]
    fn end_to_end_spec_example_5_complex() {
        let text = "p cnf 3 2\nc t amc-complex\n\
            c p weight 1 0.4+0.2i 0\nc p weight -1 0.6+0.6i 0\n\
            c p weight 2 0.5+0.5i 0\nc p weight -2 0.5+0.5i 0\n\
            c p weight 3 0.3+0.7i 0\nc p weight -3 0.7+0.3i 0\n\
            1 -2 0\n-1 3 0\n";
        let outcome = solve_text(text);
        assert_eq!(outcome.satisfiable, Some(true));
        // Spec example: result 0.55 - 1.1i... the spec prints
        // `c s exact double float 0.55-1.1i`. Verify against an independent
        // brute-force complex computation.
        let (re, im) = brute_force_complex(
            3,
            &[vec![1, -2], vec![-1, 3]],
            &[
                ("0.4", "0.2"),
                ("0.6", "0.6"),
                ("0.5", "0.5"),
                ("0.5", "0.5"),
                ("0.3", "0.7"),
                ("0.7", "0.3"),
            ],
        );
        match &outcome.value {
            Some(ExactValue::Complex(gre, gim)) => {
                assert_eq!(*gre, re);
                assert_eq!(*gim, im);
            }
            other => panic!("expected complex, got {other:?}"),
        }
    }

    /// Brute-force complex weighted count for tests. Weight list is
    /// [(re,im) for lit codes 1,-1,2,-2,...] as decimal strings.
    fn brute_force_complex(
        num_vars: usize,
        clauses: &[Vec<i32>],
        weights: &[(&str, &str)],
    ) -> (BigRational, BigRational) {
        use num_traits::{One, Zero};
        let w: Vec<(BigRational, BigRational)> = weights
            .iter()
            .map(|(re, im)| {
                (
                    parse::parse_rational(re).unwrap(),
                    parse::parse_rational(im).unwrap(),
                )
            })
            .collect();
        let mut total_re = BigRational::zero();
        let mut total_im = BigRational::zero();
        for m in 0..(1u64 << num_vars) {
            let sat = clauses.iter().all(|cl| {
                cl.iter().any(|&l| {
                    let v = l.unsigned_abs() as usize - 1;
                    let bit = (m >> v) & 1 == 1;
                    if l > 0 {
                        bit
                    } else {
                        !bit
                    }
                })
            });
            if !sat {
                continue;
            }
            let mut prod_re = BigRational::one();
            let mut prod_im = BigRational::zero();
            for v in 0..num_vars {
                let bit = (m >> v) & 1 == 1;
                let (wre, wim) = &w[v * 2 + usize::from(!bit)];
                let new_re = &prod_re * wre - &prod_im * wim;
                let new_im = &prod_re * wim + &prod_im * wre;
                prod_re = new_re;
                prod_im = new_im;
            }
            total_re += prod_re;
            total_im += prod_im;
        }
        (total_re, total_im)
    }

    #[test]
    fn unsat_instance_reports_unsatisfiable() {
        let text = "p cnf 1 2\nc t mc\n1 0\n-1 0\n";
        let outcome = solve_text(text);
        assert_eq!(outcome.satisfiable, Some(false));
        assert_eq!(
            outcome.value,
            Some(ExactValue::Nat(num_bigint::BigUint::from(0u32)))
        );
    }

    #[test]
    fn pmc_with_no_show_line_is_sat_decision() {
        // Spec: "if no variables are stated the problem is simply to decide
        // satisfiability" — count over the empty projection is 1 if SAT.
        let text = "p cnf 2 1\nc t pmc\nc p show 0\n1 2 0\n";
        let outcome = solve_text(text);
        assert_eq!(outcome.satisfiable, Some(true));
        assert_eq!(
            outcome.value,
            Some(ExactValue::Nat(num_bigint::BigUint::from(1u32)))
        );
    }
}
