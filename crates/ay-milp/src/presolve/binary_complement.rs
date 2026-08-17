// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact substitution of binary equivalence/complement equations.
//!
//! A two-variable binary equality can describe a bijection without leaving any
//! search behind:
//!
//! ```text
//!     a*x - a*y = 0   <=>   y = x
//!     a*x + a*y = a   <=>   y = 1 - x
//! ```
//!
//! Collapsing a connected component of those equations to one representative
//! removes one integer search dimension per non-representative column.  This is
//! the standard binary substitution presolve used for complement variables.  It
//! matters particularly for disjunctive scheduling encodings, which commonly
//! declare both order variables `x[i,j]` and `x[j,i]` and tie them with
//! `x[i,j] + x[j,i] = 1`.  After substitution, the two opposite big-M rows for
//! each pair are the lower and upper sides of one linear form; exact parallel
//! row consolidation emits that one range instead of carrying both rows.
//!
//! All classification, folding, and postsolve data are exact rationals.  The
//! reduced float model is emitted only when every changed coefficient and row
//! bound is exactly representable as `f64`; otherwise the whole reduction
//! declines and the caller receives its original model untouched.

use std::collections::{BTreeMap, VecDeque};

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::model::{Col, ColKind, Model, Row};

/// Recover one eliminated binary from the component representative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BinaryComplementRecovery {
    pub(crate) col: usize,
    pub(crate) representative: usize,
    /// `true` means `x[col] = 1 - x[representative]`; `false` means equality.
    pub(crate) complement: bool,
}

/// Which oriented side of an original row is exactly one reduced row side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinaryComplementSide {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BinaryComplementFactOrigin {
    pub(crate) row: usize,
    pub(crate) side: BinaryComplementSide,
}

/// The exact caller fact behind each finite side of one reduced row.  Opposite
/// parallel rows can therefore become one range row without losing evidence:
/// its lower side can name one caller row and its upper side another.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BinaryComplementRowOrigin {
    pub(crate) lower: Option<BinaryComplementFactOrigin>,
    pub(crate) upper: Option<BinaryComplementFactOrigin>,
}

/// Exact point/evidence postsolve for [`substitute_binary_complements`].
pub(crate) struct BinaryComplementPostsolve {
    pub(crate) n_orig: usize,
    /// Original column -> reduced column for survivors; eliminated columns are
    /// `None` and are recovered through [`Self::recover`].
    pub(crate) map: Vec<Option<Col>>,
    pub(crate) recover: Vec<BinaryComplementRecovery>,
    /// One independent defining equality per eliminated binary.  Certificate
    /// lifting re-reads these rows from the caller's model and solves for their
    /// exact multipliers.
    pub(crate) defining_rows: Vec<usize>,
    /// Reduced row -> original row, in reduced emission order.
    pub(crate) row_origin: Vec<BinaryComplementRowOrigin>,
    /// Objective constant folded out by `x = 1 - representative` substitutions.
    pub(crate) const_delta: BigRational,
}

impl BinaryComplementPostsolve {
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    /// Widen a reduced exact point to the caller's literal column frame.
    pub(crate) fn widen(&self, reduced: &[BigRational]) -> Vec<BigRational> {
        let mut full = vec![BigRational::zero(); self.n_orig];
        for (orig, slot) in self.map.iter().enumerate() {
            if let Some(reduced_col) = slot {
                if let Some(value) = reduced.get(reduced_col.index()) {
                    full[orig] = value.clone();
                }
            }
        }
        for recovery in &self.recover {
            let value = full[recovery.representative].clone();
            full[recovery.col] = if recovery.complement {
                BigRational::one() - value
            } else {
                value
            };
        }
        full
    }
}

#[derive(Debug, Clone, Copy)]
struct Edge {
    other: usize,
    complement: bool,
    row: usize,
}

struct FoldedRowGroup {
    coeffs: Vec<(usize, BigRational)>,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
    lower_origin: Option<BinaryComplementFactOrigin>,
    upper_origin: Option<BinaryComplementFactOrigin>,
}

/// Classify an exact two-binary equality as equivalence or complement.
fn binary_relation(model: &Model, row_index: usize) -> Option<(usize, usize, bool)> {
    let row = Row(u32::try_from(row_index).ok()?);
    let (coeffs, lb, ub) = model.row(row);
    if coeffs.len() != 2 || !lb.is_finite() || !ub.is_finite() {
        return None;
    }
    let rhs = model.row_lb_exact(row_index, lb)?;
    if model.row_ub_exact(row_index, ub)? != rhs {
        return None;
    }
    let (x, ax) = coeffs[0];
    let (y, ay) = coeffs[1];
    if x == y {
        return None;
    }
    for column in [x, y] {
        let col = Col(column);
        if model.col_kind(col) != ColKind::Binary || model.col_bounds(col) != (0.0, 1.0) {
            return None;
        }
    }
    let ax = model.row_coeff_exact(row_index, x, ax);
    let ay = model.row_coeff_exact(row_index, y, ay);
    if ax.is_zero() || ay.is_zero() {
        return None;
    }

    // ax*x + ay*y = rhs admits exactly (0,0),(1,1).
    if rhs.is_zero() && ax == -&ay {
        return Some((x as usize, y as usize, false));
    }
    // ax*x + ax*y = ax admits exactly (0,1),(1,0).
    if ax == ay && rhs == ax {
        return Some((x as usize, y as usize, true));
    }
    None
}

/// Collapse connected components of binary equivalence/complement equations.
///
/// Returns `None` when the model does not contain such a component, when its
/// relation graph is inconsistent (the ordinary solver then proves the original
/// model infeasible), or when any exact fold cannot be represented by the
/// reduced `f64` advice matrix.  No model-name or row-name information is used.
pub(crate) fn substitute_binary_complements(
    model: &Model,
) -> Option<(Model, BinaryComplementPostsolve)> {
    if model.has_inexact_coeffs() || model.margin_row().is_some() {
        return None;
    }

    let n = model.num_cols();
    let nr = model.num_rows();
    let mut graph = vec![Vec::<Edge>::new(); n];
    let mut candidate_row = vec![false; nr];
    let mut candidate_rows = 0usize;
    for row in 0..nr {
        let Some((x, y, complement)) = binary_relation(model, row) else {
            continue;
        };
        graph[x].push(Edge {
            other: y,
            complement,
            row,
        });
        graph[y].push(Edge {
            other: x,
            complement,
            row,
        });
        candidate_row[row] = true;
        candidate_rows += 1;
    }
    if candidate_rows == 0 {
        return None;
    }

    // `relation[j] = (representative, parity)`, with parity 1 meaning
    // `x_j = 1 - x_representative`.  Starting vertices in ascending order makes
    // the representative the smallest original column in each component.
    let mut relation: Vec<Option<(usize, bool)>> = vec![None; n];
    let mut defining_rows = Vec::new();
    for start in 0..n {
        if graph[start].is_empty() || relation[start].is_some() {
            continue;
        }
        relation[start] = Some((start, false));
        let mut queue = VecDeque::from([start]);
        while let Some(current) = queue.pop_front() {
            let (_, current_parity) = relation[current]?;
            for edge in &graph[current] {
                let expected = current_parity ^ edge.complement;
                match relation[edge.other] {
                    None => {
                        relation[edge.other] = Some((start, expected));
                        defining_rows.push(edge.row);
                        queue.push_back(edge.other);
                    }
                    Some((representative, parity))
                        if representative == start && parity == expected => {}
                    // An odd complement cycle proves the caller infeasible, but
                    // this reducer is an equivalence transformer, not a proof
                    // emitter.  Decline and let the ordinary exact lane prove it.
                    _ => return None,
                }
            }
        }
    }

    let eliminated = relation
        .iter()
        .enumerate()
        .filter(|&(j, relation)| relation.is_some_and(|(representative, _)| representative != j))
        .count();
    if eliminated == 0 || defining_rows.len() != eliminated {
        return None;
    }

    let representative_of = |j: usize| relation[j].map_or(j, |(representative, _)| representative);
    let complement_of = |j: usize| relation[j].is_some_and(|(_, complement)| complement);

    // Surviving columns retain original order and literal boxes.  In each
    // component only its representative survives, still as an ordinary binary;
    // this is what lets tree splits map 1:1 to the caller's representative.
    let mut reduced = Model::new();
    reduced.inherit_ft_adoption_solve_latch(model);
    let mut map = vec![None; n];
    for j in 0..n {
        if representative_of(j) != j {
            continue;
        }
        let original = Col(j as u32);
        let (lb, ub) = model.col_bounds(original);
        let new_col = match model.col_kind(original) {
            ColKind::Continuous => reduced.add_col(lb, ub),
            ColKind::Binary => reduced.add_binary_col(),
            ColKind::Integer => reduced.add_int_col(lb, ub),
        };
        // `add_binary_col` deliberately installs [0,1]; copying makes this
        // construction robust if Model later gains a more specific binary box.
        reduced.cols[new_col.index()].lb = lb;
        reduced.cols[new_col.index()].ub = ub;
        map[j] = Some(new_col);
    }

    // Fold rows first, then consolidate exact duplicates/opposites into one
    // range.  In a disjunctive pair the two original lower bounds become the
    // lower and upper side of the same form after `y = 1-x`; retaining them as
    // two rows would leave half of structural LP presolve undone.
    let mut row_origin = Vec::with_capacity(nr.saturating_sub(candidate_rows));
    let mut group_of: BTreeMap<Vec<(usize, BigRational)>, usize> = BTreeMap::new();
    let mut groups: Vec<FoldedRowGroup> = Vec::new();
    let mut nonconstant_rows = 0usize;
    for row_index in 0..nr {
        // Every classified relation is an identity after the component map.
        if candidate_row[row_index] {
            continue;
        }
        let row = Row(row_index as u32);
        let (coeffs, lb, ub) = model.row(row);
        let mut folded: BTreeMap<usize, BigRational> = BTreeMap::new();
        let mut constant = BigRational::zero();
        for &(column, a_float) in coeffs {
            let j = column as usize;
            let a = model.row_coeff_exact(row_index, column, a_float);
            let representative = representative_of(j);
            let target = map.get(representative).copied().flatten()?.index();
            if complement_of(j) {
                constant += &a;
                *folded.entry(target).or_insert_with(BigRational::zero) -= a;
            } else {
                *folded.entry(target).or_insert_with(BigRational::zero) += a;
            }
        }
        folded.retain(|_, coefficient| !coefficient.is_zero());
        let new_lb = model
            .row_lb_exact(row_index, lb)
            .map(|value| value - &constant);
        let new_ub = model
            .row_ub_exact(row_index, ub)
            .map(|value| value - &constant);
        // A constant row that became 0 within its range is redundant.  An
        // impossible constant row is retained empty so the reduced exact lane
        // can produce ordinary caller-liftable infeasibility evidence.
        if folded.is_empty() {
            let lower_ok = new_lb
                .as_ref()
                .is_none_or(|bound| bound <= &BigRational::zero());
            let upper_ok = new_ub
                .as_ref()
                .is_none_or(|bound| &BigRational::zero() <= bound);
            if lower_ok && upper_ok {
                continue;
            }
            let emitted_lb = new_lb
                .as_ref()
                .map_or(Some(f64::NEG_INFINITY), super::as_exact_f64)?;
            let emitted_ub = new_ub
                .as_ref()
                .map_or(Some(f64::INFINITY), super::as_exact_f64)?;
            reduced.add_row(emitted_lb, emitted_ub, &[]);
            row_origin.push(BinaryComplementRowOrigin {
                lower: new_lb.is_some().then_some(BinaryComplementFactOrigin {
                    row: row_index,
                    side: BinaryComplementSide::Lower,
                }),
                upper: new_ub.is_some().then_some(BinaryComplementFactOrigin {
                    row: row_index,
                    side: BinaryComplementSide::Upper,
                }),
            });
            continue;
        }

        nonconstant_rows += 1;
        let flip = folded
            .first_key_value()
            .is_some_and(|(_, coefficient)| coefficient.is_negative());
        let canonical = folded
            .into_iter()
            .map(|(column, coefficient)| (column, if flip { -coefficient } else { coefficient }))
            .collect::<Vec<_>>();
        let original_lower = BinaryComplementFactOrigin {
            row: row_index,
            side: BinaryComplementSide::Lower,
        };
        let original_upper = BinaryComplementFactOrigin {
            row: row_index,
            side: BinaryComplementSide::Upper,
        };
        let (canonical_lower, canonical_upper, lower_origin, upper_origin) = if flip {
            (
                new_ub.clone().map(|bound| -bound),
                new_lb.clone().map(|bound| -bound),
                new_ub.is_some().then_some(original_upper),
                new_lb.is_some().then_some(original_lower),
            )
        } else {
            (
                new_lb.clone(),
                new_ub.clone(),
                new_lb.is_some().then_some(original_lower),
                new_ub.is_some().then_some(original_upper),
            )
        };

        if let Some(&index) = group_of.get(&canonical) {
            let group = groups.get_mut(index)?;
            if canonical_lower.as_ref().is_some_and(|candidate| {
                group
                    .lower
                    .as_ref()
                    .is_none_or(|current| candidate > current)
            }) {
                group.lower = canonical_lower;
                group.lower_origin = lower_origin;
            }
            if canonical_upper.as_ref().is_some_and(|candidate| {
                group
                    .upper
                    .as_ref()
                    .is_none_or(|current| candidate < current)
            }) {
                group.upper = canonical_upper;
                group.upper_origin = upper_origin;
            }
        } else {
            let index = groups.len();
            group_of.insert(canonical.clone(), index);
            groups.push(FoldedRowGroup {
                coeffs: canonical,
                lower: canonical_lower,
                upper: canonical_upper,
                lower_origin,
                upper_origin,
            });
        }
    }

    let parallel_rows_removed = nonconstant_rows.saturating_sub(groups.len());
    for group in groups {
        let emitted_lb = group
            .lower
            .as_ref()
            .map_or(Some(f64::NEG_INFINITY), super::as_exact_f64)?;
        let emitted_ub = group
            .upper
            .as_ref()
            .map_or(Some(f64::INFINITY), super::as_exact_f64)?;
        let emitted = group
            .coeffs
            .iter()
            .map(|(column, coefficient)| {
                Some((Col(*column as u32), super::as_exact_f64(coefficient)?))
            })
            .collect::<Option<Vec<_>>>()?;
        reduced.add_row(emitted_lb, emitted_ub, &emitted);
        row_origin.push(BinaryComplementRowOrigin {
            lower: group.lower_origin,
            upper: group.upper_origin,
        });
    }

    let mut objective = vec![BigRational::zero(); reduced.num_cols()];
    let mut const_delta = BigRational::zero();
    for j in 0..n {
        let original = Col(j as u32);
        let c_float = model.obj_coeff(original);
        let c = model.obj_coeff_exact_at(j as u32, c_float);
        if c.is_zero() {
            continue;
        }
        let representative = representative_of(j);
        let target = map.get(representative).copied().flatten()?.index();
        if complement_of(j) {
            const_delta += &c;
            objective[target] -= c;
        } else {
            objective[target] += c;
        }
    }
    if model.has_objective() {
        let mut emitted = Vec::new();
        for (j, coefficient) in objective.iter().enumerate() {
            if !coefficient.is_zero() {
                emitted.push((Col(j as u32), super::as_exact_f64(coefficient)?));
            }
        }
        reduced.set_objective(&emitted, model.sense());
        reduced.set_objective_offset(model.objective_offset());
    }

    let recover = relation
        .iter()
        .enumerate()
        .filter_map(|(col, relation)| {
            let (representative, complement) = (*relation)?;
            (representative != col).then_some(BinaryComplementRecovery {
                col,
                representative,
                complement,
            })
        })
        .collect::<Vec<_>>();

    if trace_enabled() {
        eprintln!(
            "--trace binary-complement-sub: eliminated {eliminated} binary cols, \
             {candidate_rows} equality rows, {parallel_rows_removed} parallel rows; \
             model {}r/{}c -> {}r/{}c",
            nr,
            n,
            reduced.num_rows(),
            reduced.num_cols(),
        );
    }

    Some((
        reduced,
        BinaryComplementPostsolve {
            n_orig: n,
            map,
            recover,
            defining_rows,
            row_origin,
            const_delta,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Sense;

    #[test]
    fn complement_pair_folds_rows_objective_and_widens_exactly() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let t = model.add_int_col(0.0, 10.0);
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]); // duplicate relation
        model.add_row(3.0, f64::INFINITY, &[(y, 4.0), (t, 1.0)]);
        model.set_objective(&[(x, 3.0), (y, 5.0), (t, 2.0)], Sense::Minimize);

        let (reduced, post) = substitute_binary_complements(&model).expect("relation fires");
        assert_eq!(reduced.num_cols(), 2);
        assert_eq!(reduced.num_rows(), 1);
        assert_eq!(post.recover.len(), 1);
        assert_eq!(post.const_delta, BigRational::from_integer(5.into()));

        // Surviving order is x,t.  4*(1-x)+t >= 3 becomes 4*x-t <= 1
        // after canonical sign normalization;
        // 3*x+5*(1-x)+2*t becomes -2*x+2*t plus constant 5.
        assert_eq!(
            reduced.row(Row(0)),
            (&[(0, 4.0), (1, -1.0)][..], f64::NEG_INFINITY, 1.0)
        );
        assert_eq!(reduced.obj_coeff(Col(0)), -2.0);
        assert_eq!(reduced.obj_coeff(Col(1)), 2.0);

        let point = post.widen(&[BigRational::one(), BigRational::from_integer(7.into())]);
        assert_eq!(
            point,
            vec![
                BigRational::one(),
                BigRational::zero(),
                BigRational::from_integer(7.into())
            ]
        );
        assert!(model.check_point(&point).is_ok());
        assert_eq!(
            model.objective_value_at(&point),
            reduced.objective_value_at(&[BigRational::one(), BigRational::from_integer(7.into())])
                + post.const_delta()
        );
    }

    #[test]
    fn equivalence_and_complement_chains_collapse_to_one_binary() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]); // y = 1-x
        model.add_row(0.0, 0.0, &[(y, 3.0), (z, -3.0)]); // z = y

        let (reduced, post) = substitute_binary_complements(&model).expect("chain fires");
        assert_eq!(reduced.num_cols(), 1);
        assert_eq!(reduced.num_rows(), 0);
        assert_eq!(post.defining_rows.len(), 2);
        assert_eq!(
            post.widen(&[BigRational::zero()]),
            vec![BigRational::zero(), BigRational::one(), BigRational::one()]
        );
        assert_eq!(
            post.widen(&[BigRational::one()]),
            vec![BigRational::one(), BigRational::zero(), BigRational::zero()]
        );
    }

    #[test]
    fn opposite_disjunctive_rows_become_one_exact_range() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let first = model.add_int_col(0.0, 20.0);
        let second = model.add_int_col(0.0, 20.0);
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        model.add_row(
            2.0,
            f64::INFINITY,
            &[(x, 10.0), (first, 1.0), (second, -1.0)],
        );
        model.add_row(
            3.0,
            f64::INFINITY,
            &[(y, 10.0), (first, -1.0), (second, 1.0)],
        );

        let (reduced, post) = substitute_binary_complements(&model).expect("relation fires");
        assert_eq!(reduced.num_cols(), 3);
        assert_eq!(reduced.num_rows(), 1);
        assert_eq!(
            reduced.row(Row(0)),
            (&[(0, 10.0), (1, 1.0), (2, -1.0)][..], 2.0, 7.0)
        );
        let origin = post.row_origin[0];
        assert_eq!(origin.lower.expect("lower source").row, 1);
        assert_eq!(origin.upper.expect("upper source").row, 2);
        assert_eq!(
            origin.upper.expect("upper source").side,
            BinaryComplementSide::Lower,
            "the reduced upper side is the opposite original row's lower fact"
        );
    }

    #[test]
    fn inconsistent_relation_cycle_declines_instead_of_claiming_infeasibility() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]); // x = y
        model.add_row(0.0, 0.0, &[(y, 1.0), (z, -1.0)]); // y = z
        model.add_row(1.0, 1.0, &[(z, 1.0), (x, 1.0)]); // z = 1-x
        assert!(substitute_binary_complements(&model).is_none());
    }

    #[test]
    fn nearby_two_binary_equalities_are_not_misclassified() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(1.0, 1.0, &[(x, 2.0), (y, 1.0)]);
        assert!(substitute_binary_complements(&model).is_none());
    }

    #[test]
    fn deterministic_exhaustive_models_preserve_feasibility_and_objective() {
        // Tiny exhaustive differential over affine chains plus arbitrary
        // integer rows.  This checks both directions of the correspondence,
        // including cancellations and constant shifts, without consulting a
        // solver or sharing its implementation.
        for seed in 0u64..64 {
            let mut state = seed.wrapping_add(1);
            let mut next = || {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                state
            };
            let mut model = Model::new();
            let binary = (0..5).map(|_| model.add_binary_col()).collect::<Vec<_>>();
            let integer = model.add_int_col(0.0, 2.0);
            for j in 1..binary.len() {
                if next() & 1 == 0 {
                    model.add_row(0.0, 0.0, &[(binary[j - 1], 1.0), (binary[j], -1.0)]);
                } else {
                    model.add_row(1.0, 1.0, &[(binary[j - 1], 1.0), (binary[j], 1.0)]);
                }
            }
            for _ in 0..4 {
                let mut terms = Vec::new();
                for &column in &binary {
                    let coefficient = (next() % 7) as i64 - 3;
                    if coefficient != 0 {
                        terms.push((column, coefficient as f64));
                    }
                }
                let coefficient = (next() % 7) as i64 - 3;
                if coefficient != 0 {
                    terms.push((integer, coefficient as f64));
                }
                let a = (next() % 11) as i64 - 5;
                let b = (next() % 11) as i64 - 5;
                let (lower, upper) = if next() & 1 == 0 {
                    (a.min(b) as f64, a.max(b) as f64)
                } else if next() & 1 == 0 {
                    (f64::NEG_INFINITY, a as f64)
                } else {
                    (a as f64, f64::INFINITY)
                };
                model.add_row(lower, upper, &terms);
            }
            let mut objective = Vec::new();
            for &column in &binary {
                objective.push((column, (next() % 9) as f64 - 4.0));
            }
            objective.push((integer, (next() % 9) as f64 - 4.0));
            model.set_objective(&objective, Sense::Minimize);

            let (reduced, post) = substitute_binary_complements(&model).expect("chain fires");
            assert_eq!(reduced.num_cols(), 2, "seed {seed}");
            for representative in 0..=1i64 {
                for integer_value in 0..=2i64 {
                    let reduced_point = vec![
                        BigRational::from_integer(representative.into()),
                        BigRational::from_integer(integer_value.into()),
                    ];
                    let original_point = post.widen(&reduced_point);
                    assert_eq!(
                        reduced.check_point(&reduced_point).is_ok(),
                        model.check_point(&original_point).is_ok(),
                        "backward feasibility seed={seed} rep={representative} int={integer_value}"
                    );
                    assert_eq!(
                        model.objective_value_at(&original_point),
                        reduced.objective_value_at(&reduced_point) + post.const_delta(),
                        "objective seed={seed} rep={representative} int={integer_value}"
                    );
                }
            }

            for bits in 0u64..32 {
                for integer_value in 0..=2i64 {
                    let mut original_point = (0..5)
                        .map(|j| BigRational::from_integer(((bits >> j) & 1).into()))
                        .collect::<Vec<_>>();
                    original_point.push(BigRational::from_integer(integer_value.into()));
                    if model.check_point(&original_point).is_err() {
                        continue;
                    }
                    let reduced_point = vec![original_point[0].clone(), original_point[5].clone()];
                    assert!(
                        reduced.check_point(&reduced_point).is_ok(),
                        "forward feasibility seed={seed} bits={bits} int={integer_value}"
                    );
                    assert_eq!(post.widen(&reduced_point), original_point);
                }
            }
        }
    }
}

/// Cached trace predicate; see the live-read ratchet in `tests/env_ledger.rs`.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
