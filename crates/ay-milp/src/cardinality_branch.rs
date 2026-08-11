// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact structural recognition and pure split construction for at-most-one
//! row branching.
//!
//! A unit AMO row
//!
//! ```text
//!     sum(j in C) x_j <= 1,       x_j binary
//! ```
//!
//! licenses the disjoint multiway partition
//!
//! ```text
//!     all x_j = 0,
//!     x_k = 1 and all x_j = 0 for j != k,       for every still-open k in C.
//! ```
//!
//! Every Boolean point satisfying the AMO row belongs to exactly one child.
//! Floating-point LP values choose only the row and child order; the branching
//! license itself is checked against the model's exact-rational side store.

use num_rational::BigRational;
use num_traits::One;

use crate::model::{Col, ColKind, Model, Row};

// Branch construction is linear in support membership and each child stores a
// fix for one side. Keep this structural detector bounded independently of the
// input size; declining an oversized support changes only advice, never the
// underlying MILP result.
const UNIT_AMO_MAX_ROWS: usize = 4_096;
const UNIT_AMO_MAX_MEMBERS: usize = 256;
const UNIT_AMO_MAX_MEMBERSHIPS: usize = 1 << 20;

// A multiway branch retains one node per still-open support member plus the
// all-zero child.  Keep both the frontier fan-out and the per-node row scan
// independently bounded.  Declining a wider/later row changes only branching
// advice; the ordinary complete branch-and-bound path remains available.
const AMO_MULTIWAY_MAX_WIDTH: usize = 32;
const AMO_MULTIWAY_MAX_CANDIDATES: usize = 64;

/// One model row that exactly certifies a unit at-most-one support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UnitAmoRow {
    pub(crate) row: usize,
    pub(crate) support: Vec<usize>,
}

/// A disjoint multiway branch over one exact AMO row.
///
/// `open` contains every support member not already fixed to zero.  The
/// children with a one are visited in `one_order` order, followed by the
/// all-zero child.  Each child fixes every member of `open`, so `open` is also
/// the complete exact-propagation seed set for every child.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AmoMultiwaySplit {
    pub(crate) row: usize,
    pub(crate) open: Vec<usize>,
    pub(crate) one_order: Vec<usize>,
}

/// Find rows whose true arithmetic is exactly `sum x_j <= 1` on binary
/// columns.  Other rows and other columns in the model are irrelevant.
///
/// In particular, this deliberately does not require a set-partitioning
/// equality, dominance among the model's equality rows, or that every integer
/// column elsewhere in the model be binary.  Those are performance-shape
/// predicates, not part of the AMO license.
pub(crate) fn unit_amo_rows(model: &Model) -> Vec<UnitAmoRow> {
    let one = BigRational::one();
    let mut rows = Vec::new();
    let mut memberships = 0usize;

    for row_index in 0..model.num_rows() {
        if rows.len() >= UNIT_AMO_MAX_ROWS {
            break;
        }
        let row = Row(row_index as u32);
        let (coeffs, _lb, ub) = model.row(row);
        if coeffs.len() < 2
            || coeffs.len() > UNIT_AMO_MAX_MEMBERS
            || coeffs.len() > UNIT_AMO_MAX_MEMBERSHIPS.saturating_sub(memberships)
            || model
                .row_ub_exact(row_index, ub)
                .is_none_or(|true_ub| true_ub != one)
        {
            continue;
        }

        let mut support = Vec::with_capacity(coeffs.len());
        let mut licensed = true;
        for &(column, stored_coefficient) in coeffs {
            if model.col_kind(Col(column)) != ColKind::Binary
                || model.row_coeff_exact(row_index, column, stored_coefficient) != one
            {
                licensed = false;
                break;
            }
            support.push(column as usize);
        }
        if licensed {
            memberships += support.len();
            rows.push(UnitAmoRow {
                row: row_index,
                support,
            });
        }
    }

    rows
}

/// Select one live exact unit-AMO row and construct its disjoint multiway
/// branch.  Only the first [`AMO_MULTIWAY_MAX_CANDIDATES`] bounded-width rows
/// are inspected, and a row wider than [`AMO_MULTIWAY_MAX_WIDTH`] is declined,
/// so the branch's node and memory fan-out are fixed independently of model
/// size.
///
/// A support member with `upper <= 0.5` is already zero and omitted.  A member
/// with `lower >= 0.5` decides the row, so that row is not branchable.  At least
/// two members must remain possible and at least one must be fractional in the
/// LP point; otherwise this structural arm has nothing useful to add to the
/// ordinary single-column brancher.  LP values are advice only: rows are ranked
/// by total fractional mass and active children by descending member value,
/// with row/column indices providing deterministic ties.
pub(crate) fn amo_multiway_split(
    rows: &[UnitAmoRow],
    values: &[f64],
    lower: &[f64],
    upper: &[f64],
) -> Option<AmoMultiwaySplit> {
    let vector_len = values.len().min(lower.len()).min(upper.len());
    let mut best: Option<(f64, usize, Vec<usize>)> = None;

    for row in rows.iter().take(AMO_MULTIWAY_MAX_CANDIDATES) {
        if row.support.len() > AMO_MULTIWAY_MAX_WIDTH {
            continue;
        }
        if row.support.iter().any(|&column| column >= vector_len) {
            continue;
        }

        let mut open = Vec::with_capacity(row.support.len());
        let mut decided = false;
        let mut fractional_mass = 0.0f64;
        let mut has_fractional = false;
        for &column in &row.support {
            if lower[column] >= 0.5 {
                decided = true;
                break;
            }
            if upper[column] <= 0.5 {
                continue;
            }
            open.push(column);
            let value = advisory_unit_value(values[column]);
            let mass = value.min(1.0 - value);
            fractional_mass += mass;
            has_fractional |= mass > 1e-6;
        }
        open.sort_unstable();
        if decided
            || open.len() < 2
            || open.windows(2).any(|pair| pair[0] == pair[1])
            || !has_fractional
        {
            continue;
        }

        let replace = best.as_ref().is_none_or(|(best_mass, best_row, _)| {
            fractional_mass
                .total_cmp(best_mass)
                .then_with(|| best_row.cmp(&row.row))
                .is_gt()
        });
        if replace {
            best = Some((fractional_mass, row.row, open));
        }
    }

    let (_, row, open) = best?;
    let mut one_order = open.clone();
    one_order.sort_by(|&left, &right| {
        advisory_unit_value(values[right])
            .total_cmp(&advisory_unit_value(values[left]))
            .then_with(|| left.cmp(&right))
    });
    Some(AmoMultiwaySplit {
        row,
        open,
        one_order,
    })
}

fn advisory_unit_value(value: f64) -> f64 {
    if value.is_finite() {
        value.clamp(0.0, 1.0)
    } else {
        0.0
    }
}

#[cfg(test)]
mod tests {
    use num_rational::BigRational;

    use super::{amo_multiway_split, unit_amo_rows, UnitAmoRow};
    use crate::model::Model;

    #[test]
    fn recognizer_requires_the_true_exact_unit_amo_shape() {
        let mut model = Model::new();
        let a = model.add_binary_col();
        let b = model.add_binary_col();
        let continuous = model.add_col(0.0, 1.0);
        let general_integer = model.add_int_col(0.0, 2.0);

        let good = model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 2.0, &[(a, 1.0), (b, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 2.0), (b, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (continuous, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (general_integer, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0)]);

        assert_eq!(
            unit_amo_rows(&model),
            vec![UnitAmoRow {
                row: good.index(),
                support: vec![a.index(), b.index()],
            }]
        );
    }

    #[test]
    fn recognizer_consults_exact_coefficient_and_bound_overrides() {
        let mut model = Model::new();
        let a = model.add_binary_col();
        let b = model.add_binary_col();

        let bad_coefficient = model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
        model.record_inexact_row_coeff(bad_coefficient, b.0, BigRational::from_integer(2.into()));

        let bad_bound = model.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
        model.record_inexact_row_bound(bad_bound, false, BigRational::from_integer(2.into()));

        assert!(unit_amo_rows(&model).is_empty());
    }

    #[test]
    fn multiway_children_are_pairwise_disjoint_and_cover_every_amo_assignment() {
        let rows = [UnitAmoRow {
            row: 7,
            support: vec![0, 1, 2, 3],
        }];
        let values = [0.4, 0.3, 0.2, 0.1];
        let lower = [0.0; 4];
        let upper = [1.0; 4];
        let split =
            amo_multiway_split(&rows, &values, &lower, &upper).expect("four open members split");

        assert_eq!(split.row, 7);
        assert_eq!(split.open, vec![0, 1, 2, 3]);
        assert_eq!(split.one_order, vec![0, 1, 2, 3]);
        for assignment in 0u8..(1 << split.open.len()) {
            if assignment.count_ones() > 1 {
                continue;
            }
            let matches = std::iter::once(None)
                .chain(split.one_order.iter().copied().map(Some))
                .filter(|&one| child_contains(&split, one, assignment))
                .count();
            assert_eq!(
                matches, 1,
                "AMO assignment {assignment:04b} must occur in exactly one child"
            );
        }
    }

    #[test]
    fn row_and_child_order_follow_fractional_mass_deterministically() {
        let rows = [
            UnitAmoRow {
                row: 11,
                support: vec![0, 1],
            },
            UnitAmoRow {
                row: 3,
                support: vec![2, 3, 4],
            },
        ];
        let values = [0.1, 0.1, 0.45, 0.4, 0.15];
        let lower = [0.0; 5];
        let upper = [1.0; 5];
        let split = amo_multiway_split(&rows, &values, &lower, &upper).expect("live row");
        assert_eq!(split.row, 3, "larger fractional mass must select the row");
        assert_eq!(split.one_order, vec![2, 3, 4]);
    }

    #[test]
    fn decided_wide_and_nonfractional_rows_fail_closed() {
        let support = vec![0, 1, 2, 3];
        let rows = [UnitAmoRow {
            row: 0,
            support: support.clone(),
        }];
        let values = [0.25; 4];
        let lower = [0.0; 4];
        let upper = [1.0; 4];
        let mut decided_lower = lower;
        decided_lower[2] = 1.0;
        assert!(amo_multiway_split(&rows, &values, &decided_lower, &upper).is_none());

        let integral_values = [0.0; 4];
        assert!(amo_multiway_split(&rows, &integral_values, &lower, &upper).is_none());

        let wide = [UnitAmoRow {
            row: 0,
            support: (0..=super::AMO_MULTIWAY_MAX_WIDTH).collect(),
        }];
        let wide_values = vec![0.25; super::AMO_MULTIWAY_MAX_WIDTH + 1];
        let wide_lower = vec![0.0; wide_values.len()];
        let wide_upper = vec![1.0; wide_values.len()];
        assert!(amo_multiway_split(&wide, &wide_values, &wide_lower, &wide_upper).is_none());
    }

    #[test]
    fn per_node_candidate_scan_is_bounded() {
        let mut rows: Vec<UnitAmoRow> = (0..super::AMO_MULTIWAY_MAX_CANDIDATES)
            .map(|row| UnitAmoRow {
                row,
                support: vec![0, 1],
            })
            .collect();
        rows.push(UnitAmoRow {
            row: 999,
            support: vec![2, 3],
        });
        let values = [0.01, 0.01, 0.5, 0.5];
        let lower = [0.0; 4];
        let upper = [1.0; 4];
        let split = amo_multiway_split(&rows, &values, &lower, &upper).expect("early live rows");
        assert_eq!(
            split.row, 0,
            "a higher-mass row beyond the hard candidate cap must not be inspected"
        );
    }

    fn child_contains(split: &super::AmoMultiwaySplit, one: Option<usize>, assignment: u8) -> bool {
        split.open.iter().all(|&column| {
            let actual = assignment & (1 << column) != 0;
            actual == (one == Some(column))
        })
    }
}
