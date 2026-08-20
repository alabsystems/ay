// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Split atom creation and oscillation tracking for theory split loops.
//!
//! Extracted from `mod.rs` for code health (#5970). Contains the sort-aware
//! branch-and-bound atom creation helpers and per-variable oscillation
//! detection used by the incremental split pipeline macros.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TermStore};

/// Per-variable oscillation tracking state for split loops (#1836).
///
/// Maps each variable to `(last_split_value, monotonic_direction_count)`.
/// When the direction counter reaches `±UNBOUNDED_THRESHOLD`, the variable
/// is considered to be in unbounded oscillation and the split loop should
/// bail to `Unknown`.
pub(in crate::executor) type SplitOscillationMap =
    HashMap<TermId, (num_rational::BigRational, i32)>;

/// Check whether a split variable is in unbounded oscillation (#1836).
///
/// Updates `tracking` with the new split value and returns `true` if the
/// monotonic direction counter has reached `±UNBOUNDED_THRESHOLD`.
///
/// The algorithm: each consecutive same-direction move increments the counter;
/// a direction reversal resets it. When `|count| >= threshold`, the variable
/// is oscillating unboundedly and the solver should return `Unknown`.
///
/// This deduplicates the identical 15-line pattern that appeared in the
/// legacy string split-loop path and the incremental split-loop pipeline.
pub(in crate::executor) fn check_split_oscillation(
    tracking: &mut SplitOscillationMap,
    variable: TermId,
    value: &num_rational::BigRational,
) -> bool {
    use super::super::UNBOUNDED_THRESHOLD;

    if let Some((last_val, count)) = tracking.get_mut(&variable) {
        let new_count = if *value > *last_val {
            if *count > 0 {
                *count + 1
            } else {
                1
            }
        } else if *value < *last_val {
            if *count < 0 {
                *count - 1
            } else {
                -1
            }
        } else {
            0
        };
        *last_val = value.clone();
        *count = new_count;
        new_count.abs() >= UNBOUNDED_THRESHOLD
    } else {
        tracking.insert(variable, (value.clone(), 0));
        false
    }
}

/// Result of creating disequality split atoms from a [`DisequalitySplitRequest`].
///
/// The 3-way branch depends on the sort of the variable and whether the excluded
/// value is integer or fractional. This deduplicates the identical pattern that
/// appeared in the split-loop pipeline macros.
pub(in crate::executor) enum DisequalitySplitAtoms {
    /// Non-numeric variable (not Int or Real) — skip this split.
    Skip,
    /// Int variable with fractional excluded value → branch-and-bound.
    /// Produces `(x <= floor(c), x >= ceil(c))` with no disequality context.
    IntFractional { le: TermId, ge: TermId },
    /// Int variable with integer excluded value → non-strict inequality split.
    /// Produces `(x <= c-1, x >= c+1)` conditioned on the disequality term.
    IntExact {
        le: TermId,
        ge: TermId,
        disequality_term: Option<TermId>,
        is_distinct: bool,
    },
    /// Real variable → strict inequality split.
    /// Produces `(x < c, x > c)` conditioned on the disequality term.
    Real {
        lt: TermId,
        gt: TermId,
        disequality_term: Option<TermId>,
        is_distinct: bool,
    },
}

/// Create split atoms from a [`DisequalitySplitRequest`].
///
/// Handles the sort-aware 3-way branch (#1836, #5569):
/// - Int variable + fractional value → branch-and-bound (floor/ceil)
/// - Int variable + integer value → non-strict inequality (c-1, c+1)
/// - Real variable → strict inequality (lt, gt)
/// - Non-numeric variable → [`DisequalitySplitAtoms::Skip`]
pub(in crate::executor) fn create_disequality_split_atoms(
    terms: &mut TermStore,
    split: &ay_core::DisequalitySplitRequest,
) -> DisequalitySplitAtoms {
    use ay_core::Sort;

    let var_sort = terms.sort(split.variable).clone();
    let is_int_val = split.excluded_value.is_integer();

    // Guard: skip non-numeric variables (#5569)
    if var_sort != Sort::Int && var_sort != Sort::Real {
        return DisequalitySplitAtoms::Skip;
    }

    if var_sort == Sort::Int && !is_int_val {
        // Int variable with fractional excluded value → branch-and-bound
        let floor_val = split.excluded_value.floor().to_integer();
        let ceil_val = split.excluded_value.ceil().to_integer();
        let floor_term = terms.mk_int(floor_val);
        let ceil_term = terms.mk_int(ceil_val);
        let le = terms.mk_le(split.variable, floor_term);
        let ge = terms.mk_ge(split.variable, ceil_term);
        DisequalitySplitAtoms::IntFractional { le, ge }
    } else if var_sort == Sort::Int {
        // Int variable, integer excluded value → non-strict inequality
        let excluded = split.excluded_value.to_integer();
        let le_bound = terms.mk_int(&excluded - num_bigint::BigInt::from(1));
        let ge_bound = terms.mk_int(&excluded + num_bigint::BigInt::from(1));
        let le = terms.mk_le(split.variable, le_bound);
        let ge = terms.mk_ge(split.variable, ge_bound);
        // (#ground-conflict-decomp, guard restoration) A request with NO
        // disequality term historically emitted the guard-less 2-literal
        // branch clause `x<=c-1 ∨ x>=c+1` — sound only in the requesting
        // context, NOT standalone-valid, so no theory authority was ever
        // recorded and the proof surfaced it as an uncertifiable Generic
        // clause. Synthesize the guard `¬(= x c)` so the emitted clause is
        // the guarded 3-literal integer-split TAUTOLOGY the typed
        // `ArithDisequalitySplit` validator independently re-derives. The
        // weaker clause can never manufacture a wrong verdict; a `x=c`
        // assignment is refuted by the theory's ordinary conflict path.
        let disequality_term = split.disequality_term.or_else(|| {
            if !crate::quant_unit_authority::ground_conflict_decomp_enabled() {
                return None;
            }
            let excluded_term = terms.mk_int(excluded.clone());
            let equality = terms.mk_eq(split.variable, excluded_term);
            Some(terms.mk_not(equality))
        });
        DisequalitySplitAtoms::IntExact {
            le,
            ge,
            disequality_term,
            is_distinct: split.is_distinct,
        }
    } else {
        // Real variable → strict inequalities
        let excluded_term = terms.mk_rational(split.excluded_value.clone());
        let lt = terms.mk_lt(split.variable, excluded_term);
        let gt = terms.mk_gt(split.variable, excluded_term);
        DisequalitySplitAtoms::Real {
            lt,
            gt,
            disequality_term: split.disequality_term,
            is_distinct: split.is_distinct,
        }
    }
}

/// Create sort-aware branch-and-bound split atoms from a [`SplitRequest`].
///
/// Returns `(le_atom, ge_atom, prefer_ceil)` where:
/// - `le_atom` = `variable <= floor` (using `mk_int` for Int, `mk_rational` for Real)
/// - `ge_atom` = `variable >= ceil`  (using `mk_int` for Int, `mk_rational` for Real)
/// - `prefer_ceil` = `Some(true)` if the fractional part > 0.5 (closer to ceil)
///
/// This deduplicates the sort-aware constant creation pattern (#6212) that was
/// repeated across the legacy pipeline code before the incremental split.
pub(in crate::executor) fn create_int_split_atoms(
    terms: &mut TermStore,
    split: &ay_core::SplitRequest,
) -> (TermId, TermId, Option<bool>) {
    use ay_core::Sort;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // Sort-aware constant creation: Int splits use mk_int,
    // Real splits (LIRA cross-sort) use mk_rational (#6212).
    let var_sort = terms.sort(split.variable).clone();
    let floor_term = if var_sort == Sort::Real {
        terms.mk_rational(BigRational::from(split.floor.clone()))
    } else {
        terms.mk_int(split.floor.clone())
    };
    let ceil_term = if var_sort == Sort::Real {
        terms.mk_rational(BigRational::from(split.ceil.clone()))
    } else {
        terms.mk_int(split.ceil.clone())
    };
    let le = terms.mk_le(split.variable, floor_term);
    let ge = terms.mk_ge(split.variable, ceil_term);

    // Compute prefer_ceil: closer integer first
    let frac = &split.value - BigRational::from(split.floor.clone());
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let prefer_ceil = Some(frac > half);

    (le, ge, prefer_ceil)
}
