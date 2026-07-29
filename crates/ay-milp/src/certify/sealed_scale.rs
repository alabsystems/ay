// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MEASUREMENT SCAFFOLD (not a shipped API): the exact-arithmetic weak-dual
//! row builder, timed against the `BigRational` implementation it replaced.
//!
//! Two things live here, and only the first is a measurement:
//!
//! 1. a **characterization** of [`super::weak_dual_row_proposal`] and
//!    [`crate::cert::combine_bounded`] at a caller-chosen sparse shape, run
//!    on demand through the `sealed_scale_rational_weak_row` example:
//!
//!    ```text
//!    cargo run --release -p ay-milp --example sealed_scale_rational_weak_row
//!    ```
//!
//! 2. a **differential oracle**. Every round asserts that the production
//!    `FastRational` lane and the `BigRational` reference produce the
//!    bit-identical proof object and the bit-identical recombination, and that
//!    the proposal independently verifies against the model. A timing run that
//!    diverges panics instead of reporting a speedup — a faster answer that is
//!    a different answer is not a speedup.
//!
//! Because (2) is real coverage, it is not left to the on-demand example:
//! `SealedScaleShape::SMOKE` runs the identical routine at ~1/160 scale under
//! `cargo test`, so the fast-vs-`BigRational` contract over the promoted-slot
//! and rational side-store paths is checked on every run of the suite.
//!
//! Nothing here participates in a verdict. The only item re-exported from the
//! crate root is [`diag_sealed_scale_rational_weak_row`], which takes no
//! arguments, builds its own synthetic model, and returns text: no
//! `CertifiedRow`, `Model`, or `Outcome` can escape through it, so no caller
//! can obtain evidence from this module.

use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::time::{Duration, Instant};

use ay_lra::rational::Rational as FastRational;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{certified_weak_dual_row_big_reference_proposal, weak_dual_row_proposal};
use crate::cert::{
    combine_bounded_big_reference, combine_bounded_fast_for_benchmark, CertifiedRow,
};
use crate::model::{Col, Model};

/// Rows whose lower bound is served from the exact side store rather than the
/// `f64` proxy, plus the count of rows whose first coefficient is.
const SIDE_STORE_BOUNDS: usize = 8;
const SIDE_STORE_COEFFS: usize = 8;

/// Column stride within a row. Coprimality with the column count is what makes
/// each row duplicate-free; [`SealedScaleShape::validate`] enforces it.
const COL_STRIDE: usize = 67;
/// Row-to-row offset of the sparsity pattern.
const ROW_STRIDE: usize = 131;

/// The sparse shape one characterization run should synthesize.
///
/// The shape is representative; the synthetic adjacency, coefficient
/// distribution, and one-hot objective are not a replay of any confidential
/// network.
#[derive(Clone, Copy)]
struct SealedScaleShape {
    /// Structural columns.
    cols: usize,
    /// Rows, each carrying `nnz / rows` (or one more) coefficients.
    rows: usize,
    /// Total row nonzeros, spread as evenly as the row count allows.
    nnz: usize,
    /// Timed rounds per implementation. Alternating order and medians reduce
    /// (but cannot eliminate) shared-host frequency and scheduling noise.
    rounds: usize,
}

impl SealedScaleShape {
    /// The sealed VNN-COMP instance's exact sparse dimensions: 7593 columns,
    /// 4846 rows, 502260 nonzeros.
    const SEALED: Self = Self {
        cols: 7_593,
        rows: 4_846,
        nnz: 502_260,
        rounds: 5,
    };

    /// ~1/160 of [`Self::SEALED`] at comparable row density, small enough to
    /// run the differential oracle inside `cargo test`.
    #[cfg(test)]
    const SMOKE: Self = Self {
        cols: 149,
        rows: 61,
        nnz: 3_100,
        rounds: 2,
    };

    /// Coefficients in row `r`.
    fn degree(self, r: usize) -> usize {
        self.nnz / self.rows + usize::from(r < self.nnz % self.rows)
    }

    /// Reject shapes the generator cannot honor. A shape that silently
    /// produced duplicate columns in a row, or too few rows to populate the
    /// side store, would measure and check something other than what it names.
    fn validate(self) {
        assert!(
            self.rows > 0 && self.cols > 0 && self.rounds > 0,
            "empty shape"
        );
        assert!(
            self.rows >= SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS,
            "shape needs at least {} rows to populate the exact side store",
            SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS
        );
        assert!(
            self.nnz >= self.rows,
            "every row must carry at least one coefficient"
        );
        // Duplicate-free rows: k·COL_STRIDE must be distinct modulo `cols` for
        // every k below the largest degree.
        assert_eq!(
            num_integer::gcd(COL_STRIDE, self.cols),
            1,
            "column stride {COL_STRIDE} must be coprime with the column count"
        );
        assert!(
            self.degree(0) <= self.cols,
            "row degree cannot exceed the column count"
        );
    }
}

/// One characterization run's medians and the identity of what it measured.
struct SealedScaleReport {
    shape: SealedScaleShape,
    multipliers: usize,
    /// Slots the production lane still holds as `BigRational` at the end of
    /// the recombination — the promotion the forced-big side-store inputs buy.
    final_big_slots: usize,
    row_hash: u64,
    combination_hash: u64,
    builder_fast_median: Duration,
    builder_big_median: Duration,
    combination_fast_median: Duration,
    combination_big_median: Duration,
    combined_fast_median: Duration,
    combined_big_median: Duration,
}

impl fmt::Display for SealedScaleReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let millis = |duration: Duration| duration.as_secs_f64() * 1_000.0;
        let speedup = |old: Duration, new: Duration| old.as_secs_f64() / new.as_secs_f64();
        write!(
            f,
            "sealed_scale_rational_weak_row \
             cols={} rows={} nnz={} rounds={} \
             objective_nnz=1 multipliers={} side_store_entries={} forced_big_inputs=2 \
             builder_fast_median_ms={:.3} builder_big_median_ms={:.3} \
             builder_speedup={:.3}x \
             combination_fast_median_ms={:.3} combination_big_median_ms={:.3} \
             combination_speedup={:.3}x \
             combined_fast_median_ms={:.3} combined_big_median_ms={:.3} \
             combined_speedup={:.3}x final_big_slots={} \
             row_hash={:016x} combination_hash={:016x}",
            self.shape.cols,
            self.shape.rows,
            self.shape.nnz,
            self.shape.rounds,
            self.multipliers,
            SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS,
            millis(self.builder_fast_median),
            millis(self.builder_big_median),
            speedup(self.builder_big_median, self.builder_fast_median),
            millis(self.combination_fast_median),
            millis(self.combination_big_median),
            speedup(self.combination_big_median, self.combination_fast_median),
            millis(self.combined_fast_median),
            millis(self.combined_big_median),
            speedup(self.combined_big_median, self.combined_fast_median),
            self.final_big_slots,
            self.row_hash,
            self.combination_hash,
        )
    }
}

/// Characterize the exact-rational weak-dual lane at the sealed instance's
/// dimensions and return the report line.
///
/// This is a measurement scaffold, not a shipped API: it is `#[doc(hidden)]` at
/// the crate root and hands back text only.
pub fn diag_sealed_scale_rational_weak_row() -> String {
    characterize(SealedScaleShape::SEALED).to_string()
}

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

fn sealed_mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn timed<T>(f: impl FnOnce() -> T) -> (Duration, T) {
    let start = Instant::now();
    let value = f();
    (start.elapsed(), value)
}

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

fn certified_row_hash(row: &CertifiedRow) -> u64 {
    let mut hasher = DefaultHasher::new();
    row.coeffs.hash(&mut hasher);
    row.lb.hash(&mut hasher);
    row.multipliers.len().hash(&mut hasher);
    for multiplier in &row.multipliers {
        multiplier.fact.hash(&mut hasher);
        multiplier.coeff.hash(&mut hasher);
    }
    hasher.finish()
}

fn combination_hash(coeffs: &[BigRational], constant: &BigRational) -> u64 {
    let mut hasher = DefaultHasher::new();
    coeffs.hash(&mut hasher);
    constant.hash(&mut hasher);
    hasher.finish()
}

/// Build the synthetic model, its snapped duals, and its exact side store.
///
/// Deterministic in `shape` alone: the same shape yields the same model on
/// every host and every run, which is what makes the report's `row_hash` a
/// usable regression handle.
fn synthesize(shape: SealedScaleShape) -> (Model, Vec<f64>) {
    let mut model = Model::new();
    let cols: Vec<Col> = (0..shape.cols)
        .map(|j| {
            let lb = -7.0 - (j % 3) as f64;
            let ub = 11.0 + (j % 5) as f64;
            model.add_col(lb, ub)
        })
        .collect();
    let mut duals = Vec::with_capacity(shape.rows);
    let mut actual_nnz = 0usize;

    for r in 0..shape.rows {
        let degree = shape.degree(r);
        let mut coeffs = Vec::with_capacity(degree);
        for k in 0..degree {
            // COL_STRIDE is coprime with the column count, so every row is
            // duplicate-free (checked by `SealedScaleShape::validate`).
            let col = cols[(r * ROW_STRIDE + k * COL_STRIDE) % shape.cols];
            let bits = sealed_mix(((r as u64) << 32) | k as u64);
            let numerator = ((bits >> 8) % 2_047 + 1) as f64;
            let denominator = (1_u64 << (8 + (bits as u32 % 5))) as f64;
            let sign = if bits & 1 == 0 { 1.0 } else { -1.0 };
            coeffs.push((col, sign * numerator / denominator));
        }
        actual_nnz += coeffs.len();

        let row = model.add_row(-3.0, 4.0, &coeffs);
        if r < SIDE_STORE_BOUNDS {
            let exact_lb = if r == 0 {
                let numerator = -((BigInt::from(1_u8) << 115_usize) + BigInt::from(17_u8));
                let denominator = (BigInt::from(1_u8) << 75_usize) + BigInt::from(3_u8);
                BigRational::new(numerator, denominator)
            } else {
                rat(-((2 * r + 1) as i64), 3)
            };
            model.record_inexact_row_bound(row, true, exact_lb);
        }
        if (SIDE_STORE_BOUNDS..SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS).contains(&r) {
            let exact_coeff = if r == SIDE_STORE_BOUNDS {
                let numerator = (BigInt::from(1_u8) << 113_usize) + BigInt::from(29_u8);
                let denominator = (BigInt::from(1_u8) << 73_usize) + BigInt::from(5_u8);
                BigRational::new(numerator, denominator)
            } else {
                rat((2 * r + 1) as i64, 3)
            };
            let overridden_col = coeffs[0].0;
            model.record_inexact_row_coeff(row, overridden_col.0, exact_coeff);
        }

        let bits = sealed_mix(0xd1b5_4a32_d192_ed03 ^ r as u64);
        let numerator = ((bits >> 12) % ((1_u64 << 29) - 1) + 1) as f64;
        let sign = if r < SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS || bits & 1 == 0 {
            1.0
        } else {
            -1.0
        };
        duals.push(sign * numerator / (1_u64 << 30) as f64);
    }
    assert_eq!(actual_nnz, shape.nnz, "generator missed the requested nnz");
    (model, duals)
}

/// One-process characterization at `shape`'s sparse dimensions, doubling as a
/// fail-closed differential oracle over the two exact-arithmetic phases.
///
/// This deliberately excludes model construction and solver setup: both
/// implementations see the same warm, immutable model, objective, snapped
/// duals, multiplier list, and rational side-store.
///
/// # Panics
///
/// If the production `FastRational` lane and the `BigRational` reference
/// disagree on the proposal, on the recombination, or on the promoted-slot
/// count, or if a proposal fails to verify against the model. Divergence is a
/// soundness-relevant defect, so it fails loudly rather than being reported as
/// a timing number.
fn characterize(shape: SealedScaleShape) -> SealedScaleReport {
    shape.validate();
    let (model, duals) = synthesize(shape);

    let mut q = vec![0.0; shape.cols];
    q[shape.cols - 1] = 1.0;

    // Untimed warm-up also establishes the shared proof and Combination
    // input before collecting any samples.
    let fast_warm =
        weak_dual_row_proposal(&model, &q, &duals, None).expect("finite box must build");
    let big_warm = certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
        .expect("BigRational oracle must build");
    assert_eq!(fast_warm, big_warm);
    fast_warm
        .verify(&model)
        .expect("warm proposal must independently verify");
    let multipliers = fast_warm.multipliers.clone();

    combine_bounded_big_reference(&multipliers, &model, None)
        .expect("BigRational Combination warm-up must succeed");
    let (fast_coeffs, fast_constant) =
        combine_bounded_fast_for_benchmark(&multipliers, &model, None)
            .expect("production Combination must succeed");
    let (big_coeffs, big_constant) = combine_bounded_big_reference(&multipliers, &model, None)
        .expect("BigRational Combination oracle must succeed");
    assert_eq!(
        fast_coeffs
            .iter()
            .map(FastRational::to_big)
            .collect::<Vec<_>>(),
        big_coeffs
    );
    assert_eq!(fast_constant.to_big(), big_constant);
    let expected_row_hash = certified_row_hash(&fast_warm);
    let expected_combination_hash = combination_hash(&big_coeffs, &big_constant);

    let mut builder_fast = Vec::with_capacity(shape.rounds);
    let mut builder_big = Vec::with_capacity(shape.rounds);
    let mut combination_fast = Vec::with_capacity(shape.rounds);
    let mut combination_big = Vec::with_capacity(shape.rounds);
    let mut final_big_slots = None;

    for round in 0..shape.rounds {
        let (fast_time, fast_row, big_time, big_row) = if round % 2 == 0 {
            let (fast_time, fast_row) = timed(|| {
                weak_dual_row_proposal(&model, &q, &duals, None)
                    .expect("production proposal must build")
            });
            let (big_time, big_row) = timed(|| {
                certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
                    .expect("BigRational proposal must build")
            });
            (fast_time, fast_row, big_time, big_row)
        } else {
            let (big_time, big_row) = timed(|| {
                certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
                    .expect("BigRational proposal must build")
            });
            let (fast_time, fast_row) = timed(|| {
                weak_dual_row_proposal(&model, &q, &duals, None)
                    .expect("production proposal must build")
            });
            (fast_time, fast_row, big_time, big_row)
        };
        assert_eq!(fast_row, big_row);
        assert_eq!(certified_row_hash(&fast_row), expected_row_hash);
        assert_eq!(certified_row_hash(&big_row), expected_row_hash);
        builder_fast.push(fast_time);
        builder_big.push(big_time);
        drop(fast_row);
        drop(big_row);

        let (fast_time, fast_combination, big_time, big_combination) = if round % 2 == 0 {
            let (fast_time, fast_combination) = timed(|| {
                combine_bounded_fast_for_benchmark(&multipliers, &model, None)
                    .expect("production Combination must succeed")
            });
            let (big_time, big_combination) = timed(|| {
                combine_bounded_big_reference(&multipliers, &model, None)
                    .expect("BigRational Combination oracle must succeed")
            });
            (fast_time, fast_combination, big_time, big_combination)
        } else {
            let (big_time, big_combination) = timed(|| {
                combine_bounded_big_reference(&multipliers, &model, None)
                    .expect("BigRational Combination oracle must succeed")
            });
            let (fast_time, fast_combination) = timed(|| {
                combine_bounded_fast_for_benchmark(&multipliers, &model, None)
                    .expect("production Combination must succeed")
            });
            (fast_time, fast_combination, big_time, big_combination)
        };

        // Conversion and final storage-state inspection are deliberately
        // outside the Combination timer.
        let (fast_coeffs, fast_constant) = fast_combination;
        let round_big_slots = fast_coeffs.iter().filter(|value| !value.is_small()).count()
            + usize::from(!fast_constant.is_small());
        assert_eq!(
            *final_big_slots.get_or_insert(round_big_slots),
            round_big_slots
        );
        let fast_big_coeffs = fast_coeffs
            .iter()
            .map(FastRational::to_big)
            .collect::<Vec<_>>();
        let fast_big_constant = fast_constant.to_big();
        let (big_coeffs, big_constant) = big_combination;
        assert_eq!(fast_big_coeffs, big_coeffs);
        assert_eq!(fast_big_constant, big_constant);
        assert_eq!(
            combination_hash(&fast_big_coeffs, &fast_big_constant),
            expected_combination_hash
        );
        assert_eq!(
            combination_hash(&big_coeffs, &big_constant),
            expected_combination_hash
        );
        combination_fast.push(fast_time);
        combination_big.push(big_time);
    }

    let combined_fast = builder_fast
        .iter()
        .zip(&combination_fast)
        .map(|(builder, combination)| *builder + *combination)
        .collect::<Vec<_>>();
    let combined_big = builder_big
        .iter()
        .zip(&combination_big)
        .map(|(builder, combination)| *builder + *combination)
        .collect::<Vec<_>>();

    SealedScaleReport {
        shape,
        multipliers: multipliers.len(),
        final_big_slots: final_big_slots.expect("at least one round"),
        row_hash: expected_row_hash,
        combination_hash: expected_combination_hash,
        builder_fast_median: median(builder_fast),
        builder_big_median: median(builder_big),
        combination_fast_median: median(combination_fast),
        combination_big_median: median(combination_big),
        combined_fast_median: median(combined_fast),
        combined_big_median: median(combined_big),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The fast-vs-`BigRational` differential contract, at a scale `cargo test`
    /// can afford. Every equality that matters is asserted inside
    /// [`characterize`]; this pins the shape it actually exercised so a
    /// degenerate model (no multipliers, nothing promoted to `BigRational`)
    /// cannot make the oracle pass vacuously.
    #[test]
    fn small_scale_rational_weak_row_matches_big_reference() {
        let shape = SealedScaleShape::SMOKE;
        let report = characterize(shape);

        assert_eq!(
            report.multipliers,
            shape.rows + shape.cols,
            "every row and every structural column should price into the proof"
        );
        assert!(
            report.final_big_slots >= 1,
            "the forced side-store inputs must leave at least one promoted slot"
        );
        // The routine is deterministic in its shape alone, so a second run
        // must reproduce both fingerprints bit for bit.
        let repeat = characterize(shape);
        assert_eq!(report.row_hash, repeat.row_hash);
        assert_eq!(report.combination_hash, repeat.combination_hash);
    }

    /// The sealed shape is the one the example reports on; a typo that made it
    /// unsynthesizable would otherwise only surface on a manual run.
    #[test]
    fn sealed_shape_is_synthesizable() {
        SealedScaleShape::SEALED.validate();
    }
}
