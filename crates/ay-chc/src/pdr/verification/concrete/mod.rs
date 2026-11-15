// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Concrete transition checking for PDR model verification.
//!
//! Provides exhaustive enumeration and Monte Carlo sampling to detect false-UNSAT
//! results from the SMT solver. When the SMT solver says a transition query is
//! UNSAT (invariant holds), these functions evaluate the formula on concrete
//! integer/bitvector assignments as a defense-in-depth check.
//!
//! Extracted from `model.rs` as part of the structural split (#5970).

use super::*;

mod budget;
mod helpers;
mod window;
pub(super) use budget::{ConcreteAnswer, ConcreteBudget};
// Only tests build a stop by hand; a verifier's comes from
// `PdrSolver::concrete_budget`.
#[cfg(test)]
pub(super) use budget::ConcreteStop;
use helpers::*;
use window::*;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod empty_domain_tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod window_tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod budget_tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod stop_tests;

/// Range descriptor for concrete enumeration: Int or BV variable.
pub(super) enum ConcreteCheckRange {
    Int {
        name: String,
        lo: i64,
        hi: i64,
    },
    BitVec {
        name: String,
        width: u32,
        count: u128,
    },
}

impl ConcreteCheckRange {
    /// True when the range holds no value: an `Int` range whose bounds cross,
    /// or a `BitVec` range of no values.
    pub(super) fn is_empty(&self) -> bool {
        match self {
            ConcreteCheckRange::Int { lo, hi, .. } => lo > hi,
            ConcreteCheckRange::BitVec { count, .. } => *count == 0,
        }
    }
}

/// Simple deterministic xorshift64 PRNG for Monte Carlo sampling.
/// No external dependency needed — reproducible from seed.
pub(super) struct Xorshift64(u64);

impl Xorshift64 {
    pub(super) fn new(seed: u64) -> Self {
        // Ensure non-zero seed (xorshift requires it)
        Self(if seed == 0 { 0x517cc1b727220a95 } else { seed })
    }

    pub(super) fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// Generate a random i64 in [lo, hi] inclusive.
    pub(super) fn next_range(&mut self, lo: i64, hi: i64) -> i64 {
        if lo >= hi {
            return lo;
        }
        let range_i128 = i128::from(hi) - i128::from(lo) + 1;
        if range_i128 > i128::from(u64::MAX) {
            // Full i64 range: just return a random i64 directly.
            self.next() as i64
        } else {
            let range = range_i128 as u64;
            // offset is in [0, range-1] which is at most u64::MAX-1.
            // When range > i64::MAX as u64, offset can exceed i64::MAX,
            // so use i128 arithmetic for the addition.
            let offset = self.next() % range;
            (i128::from(lo) + i128::from(offset)) as i64
        }
    }
}

/// Concrete transition check: exhaustive or Monte Carlo sampling (#5381, #5539).
///
/// Collects Int and small BV (≤8-bit) variables from the query, extracts bounds
/// from the body, gives each Int variable at most 201 values inside its bounds
/// ([`int_check_window`]), and evaluates the formula on concrete assignments:
///
/// 1. **Exhaustive** (≤10000 combos): tests all assignments in bounded range.
/// 2. **Monte Carlo** (>10000 combos): boundary-seeded random sampling, 10000 samples
///    Probabilistic: >99.99% detection for satisfying regions ≥0.1% of domain.
///    See `monte_carlo_transition_check` doc for formal analysis.
///
/// FIX #5539: Previously bailed out on >4 variables, leaving most CHC-COMP
/// LIA benchmarks (6-20+ variables) completely unchecked.
///
/// This form runs to completion, and only tests call it. The verifiers call
/// [`ConcreteBudget::check`], which searches the same domain under their time
/// accounting and stops when their solve does.
#[cfg(test)]
pub(super) fn transition_check(
    body: &ChcExpr,
    _head: &ChcExpr,
    query: &ChcExpr,
) -> Option<FxHashMap<String, SmtValue>> {
    let stop = ConcreteStop::none();
    CheckDomain::new(body, query)?.search(&mut Probe::new(query, None, stop.resolve()))
}

/// What one concrete check enumerates.
pub(super) struct CheckDomain {
    ranges: Vec<ConcreteCheckRange>,
    bounds: FxHashMap<String, (i64, i64)>,
    /// An Int range lies wholly beyond ±100 and is searched on its anchored
    /// window. Before 2026-11-01 the centred window emptied it, so the check
    /// evaluated nothing on this domain and answered `None` at once.
    pub(super) anchored: bool,
}

impl CheckDomain {
    /// The domain `query` is searched on, or `None` when there is nothing to
    /// evaluate: no Int or small BV variable, or a range that holds no value.
    pub(super) fn new(body: &ChcExpr, query: &ChcExpr) -> Option<Self> {
        // Collect Int and small BV variables from the query
        let all_vars = query.vars();
        let vars: Vec<ChcVar> = all_vars
            .iter()
            .filter(|v| match &v.sort {
                ChcSort::Int => true,
                ChcSort::BitVec(w) => *w <= 8,
                _ => false,
            })
            .cloned()
            .collect();

        if vars.is_empty() {
            return None;
        }

        // Extract bounds from body conjuncts (for Int vars)
        let bounds = extract_int_bounds_from_conjuncts(body);
        let (ranges, anchored) = check_ranges(&vars, &all_vars, &bounds);

        // A domain with an empty range holds no assignment, so the exhaustive
        // enumeration's answer is `None` without evaluating anything; answer
        // it here. An Int range is empty when its extracted bounds cross
        // (`x >= 150 /\ x <= 100` gives `150..=100`), which no value
        // satisfies, or, for a name another variable's lookup can read, when
        // the centred clamp misses its bounds (`x >= 150`). Such a domain's
        // product below is 0, which chose the exhaustive branch, and the
        // enumeration finds the empty range only at its own depth: with `k`
        // ranges before it, it walks every assignment of those (up to 201^k)
        // and evaluates nothing, and so polls nothing (the probe is polled
        // before each evaluation), and a PDR worker sat in it for hours
        // (Trust's verification of ay-sat, 2026-10-31). With every range
        // non-empty, the exhaustive branch evaluates exactly `total` (at most
        // 10000) assignments, polling the probe before each.
        if ranges.iter().any(ConcreteCheckRange::is_empty) {
            return None;
        }
        Some(Self {
            ranges,
            bounds,
            anchored,
        })
    }

    /// Evaluate the probe's query on this domain's assignments until one makes
    /// it true, the assignments run out, or the probe stops.
    fn search(&self, probe: &mut Probe<'_>) -> Option<FxHashMap<String, SmtValue>> {
        // Estimate total combinations (overflow-safe via saturating arithmetic)
        let total: u64 = self
            .ranges
            .iter()
            .map(|r| match r {
                ConcreteCheckRange::Int { lo, hi, .. } => {
                    (i128::from(*hi) - i128::from(*lo) + 1).max(0) as u64
                }
                ConcreteCheckRange::BitVec { count, .. } => {
                    u64::try_from(*count).unwrap_or(u64::MAX)
                }
            })
            .fold(1u64, u64::saturating_mul);

        if total <= 10000 {
            // Small enough for exhaustive enumeration
            let mut assignment: FxHashMap<String, SmtValue> = FxHashMap::default();
            enumerate_and_check_generic(&self.ranges, 0, &mut assignment, probe)
        } else {
            // Monte Carlo random sampling for large variable sets (#5539)
            monte_carlo_transition_check(&self.ranges, &self.bounds, probe)
        }
    }
}

/// Monte Carlo random sampling for concrete transition checking (#5539).
///
/// Samples up to max_samples (adaptive: 10k/5k/2k by var count) in two phases:
/// 1. **Boundary combinations** (up to 1,000): tests boundary values per variable
///    (lo, hi, 0, ±1, ±2, ±10, extracted bounds ±1). High detection rate for
///    bugs near constraint boundaries (common in linear integer arithmetic).
/// 2. **Uniform random sampling** (remaining budget): draws from each variable's
///    range independently.
///
/// ## Probabilistic Soundness Guarantee
///
/// For uniform random sampling over a domain of size D, if a satisfying region
/// has fraction p = S/D of the domain, then with k independent samples:
///
///   P(detect) = 1 - (1-p)^k
///
/// With k = 10,000 samples (worst case, all random):
/// - p ≥ 1/100 (1% of domain): P(detect) > 1 - e^(-100) ≈ 1.0
/// - p ≥ 1/1000 (0.1%):         P(detect) > 1 - e^(-10) ≈ 0.99995
/// - p ≥ 1/10000 (0.01%):        P(detect) > 1 - e^(-1) ≈ 0.632
///
/// For CHC transition formulas, a true counterexample to an invariant typically
/// occupies a non-negligible fraction of the bounded domain (especially with
/// bounds extraction narrowing ranges). The boundary-seeded phase further
/// improves detection for edge cases near constraint boundaries.
///
/// **Limitation**: Point-satisfiable formulas (e.g., exactly one assignment in
/// a domain of 10^12) have negligible detection probability. These require the
/// SMT solver to be correct — the concrete check is a defense-in-depth layer,
/// not a complete verifier.
///
/// Uses a deterministic xorshift64 PRNG seeded from the query structure
/// for reproducibility with formula-dependent variation.
fn monte_carlo_transition_check(
    ranges: &[ConcreteCheckRange],
    bounds: &FxHashMap<String, (i64, i64)>,
    probe: &mut Probe<'_>,
) -> Option<FxHashMap<String, SmtValue>> {
    let query = probe.query();
    // #5653: Adaptive sample count based on variable count.
    // High-variable-count formulas have huge search spaces where random
    // sampling is unlikely to find point counterexamples anyway. Reducing
    // samples for these cases avoids rejecting models that are "close enough"
    // while PDR cannot find better ones within the timeout.
    let max_samples: usize = match ranges.len() {
        0..=2 => 10000,
        3..=4 => 5000,
        _ => 2000,
    };

    // Seed from formula structure, not just variable/bound counts (#5539).
    // This ensures different formulas with the same number of variables
    // get different random samples.
    let query_hash = hash_expr_structure(query);
    let seed = query_hash
        .wrapping_mul(0x9e3779b97f4a7c15)
        .wrapping_add(ranges.len() as u64)
        .wrapping_mul(0x517cc1b727220a95)
        .wrapping_add(bounds.len() as u64);
    let mut rng = Xorshift64::new(seed);

    // Extract integer constants from the query formula to use as
    // additional boundary candidates (#5539). Constants appearing in
    // the formula (coefficients, thresholds) are often critical values
    // for satisfying or falsifying the formula.
    let formula_constants = extract_int_constants(query);

    // Collect boundary values per variable for initial targeted sampling
    let boundary_values: Vec<Vec<SmtValue>> = ranges
        .iter()
        .map(|r| match r {
            ConcreteCheckRange::Int { lo, hi, name } => {
                let mut vals: Vec<i64> = Vec::with_capacity(16);
                vals.push(*lo);
                vals.push(*hi);
                for &v in &[0i64, 1, -1, 2, -2, 10, -10] {
                    if v >= *lo && v <= *hi && !vals.contains(&v) {
                        vals.push(v);
                    }
                }
                if let Some((bl, bu)) = bounds.get(name) {
                    // Use saturating arithmetic to avoid overflow when
                    // bounds are i64::MIN or i64::MAX (#5926).
                    for &v in &[*bl, *bu, bl.saturating_sub(1), bu.saturating_add(1)] {
                        if v >= *lo && v <= *hi && !vals.contains(&v) {
                            vals.push(v);
                        }
                    }
                }
                // Add formula constants and their neighbors as boundary candidates.
                // Cap at 8 extra constants to avoid explosion.
                let mut added = 0;
                for &c in &formula_constants {
                    if added >= 8 {
                        break;
                    }
                    for &v in &[c, c.saturating_sub(1), c.saturating_add(1)] {
                        if v >= *lo && v <= *hi && !vals.contains(&v) {
                            vals.push(v);
                            added += 1;
                        }
                    }
                }
                vals.into_iter()
                    .map(|v| SmtValue::Int(i128::from(v)))
                    .collect()
            }
            ConcreteCheckRange::BitVec { width, count, .. } => {
                let mut vals = Vec::with_capacity(4);
                vals.push(SmtValue::bitvec_from_biguint(
                    num_bigint::BigUint::from(0u8),
                    *width,
                ));
                if *count > 1 {
                    vals.push(SmtValue::bitvec_from_biguint(
                        num_bigint::BigUint::from(1u8),
                        *width,
                    ));
                }
                if *count > 2 {
                    vals.push(SmtValue::bitvec_from_biguint(
                        num_bigint::BigUint::from(*count - 1),
                        *width,
                    ));
                }
                vals
            }
        })
        .collect();

    let mut assignment: FxHashMap<String, SmtValue> = FxHashMap::default();
    let mut samples_checked: usize = 0;

    // Phase 1: Boundary combinations (capped at half the budget)
    let boundary_limit = 1000.min(max_samples / 2);
    let result = sample_boundary_combinations(
        ranges,
        &boundary_values,
        &mut assignment,
        probe,
        boundary_limit,
        &mut samples_checked,
    );
    if result.is_some() {
        return result;
    }

    // Phase 2: Random sampling for remaining budget
    while samples_checked < max_samples && !probe.stopped() {
        assignment.clear();
        for r in ranges {
            let (name, val) = match r {
                ConcreteCheckRange::Int { name, lo, hi } => (
                    name.clone(),
                    SmtValue::Int(i128::from(rng.next_range(*lo, *hi))),
                ),
                ConcreteCheckRange::BitVec {
                    name, width, count, ..
                } => {
                    let v = u128::from(rng.next()) % count;
                    (
                        name.clone(),
                        SmtValue::bitvec_from_biguint(num_bigint::BigUint::from(v), *width),
                    )
                }
            };
            assignment.insert(name, val);
        }
        samples_checked += 1;

        if probe.holds(&assignment) {
            return Some(assignment);
        }
    }

    None
}
