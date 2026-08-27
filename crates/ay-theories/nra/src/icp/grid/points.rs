// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Up to `want` dyadic points spread across the interior of `iv`, at the
/// coarsest dyadic spacing that fits that many points.
///
/// Candidates are proposals only: callers verify a complete model exactly.
/// Index arithmetic keeps this O(`want`) even when a finite interval is very
/// wide; materialising every dyadic multiple would be O(interval width).
pub(in super::super) fn interval_scale_points(iv: &Interval, want: usize) -> Vec<BigRational> {
    let (Endpoint::Finite(lo, _), Endpoint::Finite(hi, _)) = (&iv.lo, &iv.hi) else {
        return Vec::new();
    };
    if want == 0 || hi <= lo {
        return Vec::new();
    }

    let width = hi - lo;
    let need = BigRational::from_integer(BigInt::from(want as u64 + 1)) / &width;
    let mut scale_bits = 0usize;
    let mut scale = BigRational::one();
    let two = BigRational::from_integer(BigInt::from(2));
    while scale < need {
        if scale_bits == GRID_SCALE_MAX_BITS {
            return Vec::new();
        }
        scale *= &two;
        scale_bits += 1;
    }

    let first = (lo * &scale).floor().to_integer() + BigInt::one();
    let last = (hi * &scale).ceil().to_integer() - BigInt::one();
    if last < first {
        return Vec::new();
    }
    let denominator = BigInt::one() << scale_bits;
    let count = (&last - &first) + BigInt::one();
    let requested = BigInt::from(want as u64);
    let point = |numerator: &BigInt| BigRational::new(numerator.clone(), denominator.clone());

    if count <= requested {
        let mut points = Vec::new();
        let mut numerator = first.clone();
        while numerator <= last {
            let candidate = point(&numerator);
            if interval_contains(iv, &candidate) {
                points.push(candidate);
            }
            numerator += BigInt::one();
        }
        return points;
    }

    let last_index = &count - BigInt::one();
    let divisor = BigInt::from((want.saturating_sub(1)).max(1) as u64);
    let mut points = Vec::with_capacity(want);
    for i in 0..want {
        let index = (BigInt::from(i as u64) * &last_index) / &divisor;
        let candidate = point(&(&first + index));
        if interval_contains(iv, &candidate) && !points.contains(&candidate) {
            points.push(candidate);
        }
    }
    points
}

/// Candidate values for one coordinate, preserving the established ordering:
/// interval-derived points, fixed dyadics, then interval-scale dyadics.
pub(in super::super) fn coordinate_candidates(
    iv: &Interval,
    grid: &[BigRational],
) -> Vec<BigRational> {
    let mut candidates = Vec::with_capacity(grid.len() + GRID_MIN_BRANCH);
    for candidate in [nice_point_in_open(iv), interval_midpoint(iv)]
        .into_iter()
        .flatten()
    {
        if interval_contains(iv, &candidate) && !candidates.contains(&candidate) {
            candidates.push(candidate);
        }
    }
    for candidate in grid {
        if interval_contains(iv, candidate) && !candidates.contains(candidate) {
            candidates.push(candidate.clone());
        }
    }
    if candidates.len() < GRID_MIN_BRANCH {
        for candidate in interval_scale_points(iv, GRID_MIN_BRANCH - candidates.len()) {
            if !candidates.contains(&candidate) {
                candidates.push(candidate);
            }
        }
    }
    candidates
}

/// Small dyadic values `k / 2^level` with magnitude at most
/// [`GRID_ABS_CAP`], cumulative across levels and ordered by magnitude.
pub(in super::super) fn dyadic_grid(level: usize) -> &'static [BigRational] {
    static GRIDS: std::sync::OnceLock<Vec<Vec<BigRational>>> = std::sync::OnceLock::new();
    &GRIDS.get_or_init(|| {
        let mut grids = Vec::new();
        let mut accumulated = Vec::new();
        for level in 0..=GRID_MAX_LEVEL {
            let denominator = BigInt::one() << level;
            let cap = (GRID_ABS_CAP as i64) << level;
            let mut fresh = Vec::new();
            for numerator in -cap..=cap {
                let value = BigRational::new(BigInt::from(numerator), denominator.clone());
                if !accumulated.contains(&value) && !fresh.contains(&value) {
                    fresh.push(value);
                }
            }
            fresh.sort_by(|a, b| {
                let (abs_a, abs_b) = (a.abs(), b.abs());
                abs_a.cmp(&abs_b).then_with(|| b.cmp(a))
            });
            accumulated.extend(fresh);
            grids.push(accumulated.clone());
        }
        grids
    })[level.min(GRID_MAX_LEVEL)]
}
