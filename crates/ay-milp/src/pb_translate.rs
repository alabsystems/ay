// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact translation plans for the MILP-to-PB route.
//!
//! This module deliberately contains no PB-solver dependency.  It is the exact
//! semantic boundary between [`Model`] and the public `ay-pb-core` types: every
//! [`PbInequality`] mechanically becomes one `PbConstraint { rel: Ge, .. }`, and
//! [`PbObjectivePlan::terms`] mechanically become a `PbObjective`.  Keeping the
//! boundary narrow lets `ay-milp` depend on the cycle-free solver core while
//! the `ay-pb` facade retains its reverse PB-to-MILP portfolio arm, without
//! duplicating an encoder or solver here.
//!
//! The direct lane handles pure-Boolean models.  A fail-closed sibling first
//! eliminates continuous objective singletons and radix-encodes bounded general
//! integers; an exact interval pass may close an otherwise-open integer side
//! when the original rows mathematically imply the missing bound.  This is the
//! fixed-charge/network-cost shape used by `qnet1`.
//! Both lanes expose the same exact postsolve map, so the adapter independently
//! checks every lifted point against the original model.
//!
//! All decisions are made from the model's authoritative exact-rational side
//! stores.  A row `a*x >= b` is integralized by a positive common denominator
//! `d`: because `d*a*x` is integral for every Boolean assignment, the exact
//! equivalent is `d*a*x >= ceil(d*b)`.  An upper side uses the same identity on
//! `-a*x >= -b`.  This accepts arbitrary exact rational bounds without a
//! tolerance and generally produces smaller integers than clearing the bound's
//! denominator too.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::model::{exact, ColKind, Model, Sense};

mod bounded;
mod implicit_bounds;

/// One exact pseudo-Boolean inequality, using zero-based model column indices.
///
/// The eventual `ay-pb` adapter adds one to each variable index and emits a
/// single positive literal per term.  Coefficients may be negative.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbInequality {
    pub(crate) terms: Vec<(u32, i128)>,
    pub(crate) rhs: i128,
}

/// Reversible map between the integer PB objective and the model objective.
///
/// If `direction` is `+1` for minimization and `-1` for maximization, the PB
/// objective is
///
/// ```text
/// pb = direction * denominator * (model_value - offset).
/// ```
///
/// The denominator is positive.  Thus minimizing `pb` preserves the caller's
/// optimization direction exactly, and [`Self::model_value`] reverses the map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbObjectiveMap {
    denominator: BigInt,
    direction: i8,
    offset: BigRational,
}

impl PbObjectiveMap {
    /// Recover the exact model objective from a PB solver's claimed value.
    pub(crate) fn model_value(&self, pb_value: i128) -> BigRational {
        debug_assert!(self.direction == 1 || self.direction == -1);
        debug_assert!(self.denominator > BigInt::zero());
        let signed = BigInt::from(pb_value) * BigInt::from(self.direction);
        self.offset.clone() + BigRational::new(signed, self.denominator.clone())
    }

    /// Recover the integer PB objective represented by an exact model value.
    ///
    /// This is the inverse of [`Self::model_value`].  A value outside the
    /// translated objective lattice (or outside `i128`) is rejected rather
    /// than rounded.  Certificate construction uses this to express the
    /// strict-better objective face as the exact PB row `pb <= value - 1`.
    pub(crate) fn pb_value(&self, model_value: &BigRational) -> Option<i128> {
        debug_assert!(self.direction == 1 || self.direction == -1);
        debug_assert!(self.denominator > BigInt::zero());
        let scaled = (model_value - &self.offset)
            * BigRational::from_integer(self.denominator.clone())
            * BigRational::from_integer(BigInt::from(self.direction));
        scaled
            .is_integer()
            .then(|| scaled.to_integer().to_i128())
            .flatten()
    }

    #[cfg(test)]
    fn denominator(&self) -> &BigInt {
        &self.denominator
    }

    #[cfg(test)]
    fn direction(&self) -> i8 {
        self.direction
    }

    #[cfg(test)]
    fn offset(&self) -> &BigRational {
        &self.offset
    }
}

/// Integer objective handed to the PB optimizer, plus its exact value map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbObjectivePlan {
    pub(crate) terms: Vec<(u32, i128)>,
    pub(crate) map: PbObjectiveMap,
}

/// One original model column as an exact affine form in PB variables.
///
/// The bounded-integer lane uses radix bits (`x = lo + sum(2^k * bit_k)`) and the
/// singleton eliminator composes those forms into the removed continuous
/// columns.  Terms are canonical (sorted, duplicate-free, nonzero).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PbAffine {
    pub(super) constant: BigRational,
    pub(super) terms: Vec<(u32, BigRational)>,
}

impl PbAffine {
    fn value_at(&self, assignment: &[bool]) -> Option<BigRational> {
        let mut value = self.constant.clone();
        for &(variable, ref coefficient) in &self.terms {
            if assignment.get(variable as usize).copied()? {
                value += coefficient;
            }
        }
        Some(value)
    }
}

impl PbObjectivePlan {
    /// Evaluate the integer PB objective without overflow.
    pub(crate) fn value_at(&self, assignment: &[bool]) -> Option<i128> {
        if self
            .terms
            .iter()
            .any(|&(column, _)| column as usize >= assignment.len())
        {
            return None;
        }
        self.terms.iter().try_fold(0i128, |sum, &(column, weight)| {
            if assignment[column as usize] {
                sum.checked_add(weight)
            } else {
                Some(sum)
            }
        })
    }
}

/// Complete exact PB projection.  `objective == None` preserves a feasibility
/// model; `Some` also covers an explicitly-set constant objective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbRoutePlan {
    pub(crate) num_vars: u32,
    pub(crate) num_constraints: u32,
    pub(crate) constraints: Vec<PbInequality>,
    pub(crate) objective: Option<PbObjectivePlan>,
    /// `None` is the identity map used by the direct pure-Boolean lane.
    /// `Some` is indexed by ORIGINAL model column and may reconstruct removed
    /// continuous columns as exact affine forms of the PB assignment.
    column_lifts: Option<Vec<PbAffine>>,
    pub(crate) eliminated_continuous: usize,
    pub(crate) encoded_general_integers: usize,
}

impl PbRoutePlan {
    /// Lift a total Boolean assignment to exact model-column order.
    pub(crate) fn lift(&self, assignment: &[bool]) -> Option<Vec<BigRational>> {
        if assignment.len() < self.num_vars as usize {
            return None;
        }
        if let Some(lifts) = &self.column_lifts {
            return lifts
                .iter()
                .map(|expression| expression.value_at(assignment))
                .collect();
        }
        Some(
            assignment[..self.num_vars as usize]
                .iter()
                .map(|&value| BigRational::from_integer(BigInt::from(u8::from(value))))
                .collect(),
        )
    }

    /// Exact independent check of the normalized PB rows.
    ///
    /// The production route still re-checks the lifted point with
    /// `Model::check_point`; this helper protects the adapter boundary and is
    /// useful for property tests.
    pub(crate) fn satisfies(&self, assignment: &[bool]) -> bool {
        assignment.len() >= self.num_vars as usize
            && self.constraints.iter().all(|row| {
                let lhs = row
                    .terms
                    .iter()
                    .fold(BigInt::zero(), |mut sum, &(column, a)| {
                        if assignment[column as usize] {
                            sum += a;
                        }
                        sum
                    });
                lhs >= BigInt::from(row.rhs)
            })
    }

    /// Lift a zero-based source-model column permutation into the core's
    /// one-based Boolean variable space.
    ///
    /// A bounded integer may own several radix bits, so a single model-column
    /// swap can expand into several Boolean transpositions. Bits are paired by
    /// their exact affine weight, never by an assumed allocation stride. A
    /// malformed source permutation, unequal affine constants/weights, shared
    /// bit ownership, or integer overflow declines the whole optional map.
    /// Fixed zero-bit columns may be permuted but contribute no moved support.
    pub(crate) fn lift_model_column_permutation_to_pb(
        &self,
        permutation: &BTreeMap<u32, u32>,
    ) -> Option<BTreeMap<u32, u32>> {
        let domain: BTreeSet<u32> = permutation.keys().copied().collect();
        let image: BTreeSet<u32> = permutation.values().copied().collect();
        if domain.is_empty() || domain != image || image.len() != permutation.len() {
            return None;
        }

        let source_columns = self
            .column_lifts
            .as_ref()
            .map_or(self.num_vars as usize, Vec::len);
        if domain
            .iter()
            .any(|&column| column as usize >= source_columns)
        {
            return None;
        }

        let mut lifted = BTreeMap::new();
        if let Some(column_lifts) = &self.column_lifts {
            for (&source, &target) in permutation {
                let source_lift = column_lifts.get(source as usize)?;
                let target_lift = column_lifts.get(target as usize)?;
                if source_lift.constant != target_lift.constant
                    || source_lift.terms.len() != target_lift.terms.len()
                {
                    return None;
                }

                let mut target_by_weight = BTreeMap::new();
                for &(variable, ref weight) in &target_lift.terms {
                    if variable >= self.num_vars
                        || target_by_weight.insert(weight.clone(), variable).is_some()
                    {
                        return None;
                    }
                }
                for &(source_variable, ref weight) in &source_lift.terms {
                    if source_variable >= self.num_vars {
                        return None;
                    }
                    let target_variable = *target_by_weight.get(weight)?;
                    let source_variable = source_variable.checked_add(1)?;
                    let target_variable = target_variable.checked_add(1)?;
                    if source_variable == target_variable {
                        continue;
                    }
                    if lifted
                        .insert(source_variable, target_variable)
                        .is_some_and(|previous| previous != target_variable)
                    {
                        return None;
                    }
                }
            }
        } else {
            for (&source, &target) in permutation {
                let source = source.checked_add(1)?;
                let target = target.checked_add(1)?;
                if source == target {
                    continue;
                }
                if lifted
                    .insert(source, target)
                    .is_some_and(|previous| previous != target)
                {
                    return None;
                }
            }
        }

        let lifted_domain: BTreeSet<u32> = lifted.keys().copied().collect();
        let lifted_image: BTreeSet<u32> = lifted.values().copied().collect();
        (!lifted.is_empty() && lifted_domain == lifted_image && lifted_image.len() == lifted.len())
            .then_some(lifted)
    }

    /// Lift a complete ordered partition of model columns into one-based PB
    /// variable blocks.
    ///
    /// Every source block must have the same nonzero model-column width and
    /// together the blocks must cover every source model column exactly once.
    /// For a bounded-radix plan, columns at the same coordinate must have the
    /// same exact affine constant and the same multiset of exact bit weights.
    /// Equal-weight bits are ordered by their zero-based PB variable only to
    /// make the resulting coordinate order deterministic. A fixed coordinate
    /// contributes no PB variables, but is accepted only when it is fixed in
    /// every block with the same constant.
    ///
    /// The result is returned only when it is itself a complete partition of
    /// all PB variables: every PB variable must occur exactly once. Thus a
    /// missing/duplicated model column, shared affine bit, partial family, or
    /// malformed lift declines the complete optional route.
    pub(crate) fn lift_model_column_blocks_to_pb(
        &self,
        blocks: &[Vec<u32>],
    ) -> Option<Vec<Vec<u32>>> {
        let width = blocks.first()?.len();
        if blocks.len() < 2 || width == 0 || blocks.iter().any(|block| block.len() != width) {
            return None;
        }

        let source_columns = self
            .column_lifts
            .as_ref()
            .map_or(self.num_vars as usize, Vec::len);
        let mut covered_columns = BTreeSet::new();
        for block in blocks {
            for &column in block {
                if column as usize >= source_columns || !covered_columns.insert(column) {
                    return None;
                }
            }
        }
        if covered_columns.len() != source_columns
            || !covered_columns
                .iter()
                .copied()
                .eq(0..u32::try_from(source_columns).ok()?)
        {
            return None;
        }

        let mut lifted = vec![Vec::new(); blocks.len()];
        let mut covered_variables = BTreeSet::new();
        if let Some(column_lifts) = &self.column_lifts {
            for coordinate in 0..width {
                let mut expected_constant = None;
                let mut expected_weights = None;
                for (block_index, block) in blocks.iter().enumerate() {
                    let expression = column_lifts.get(block[coordinate] as usize)?;
                    if expected_constant
                        .as_ref()
                        .is_some_and(|constant| constant != &expression.constant)
                    {
                        return None;
                    }
                    expected_constant.get_or_insert_with(|| expression.constant.clone());

                    let mut terms = expression.terms.clone();
                    if terms.iter().any(|&(variable, ref weight)| {
                        variable >= self.num_vars || weight.is_zero()
                    }) {
                        return None;
                    }
                    terms.sort_by(
                        |(left_variable, left_weight), (right_variable, right_weight)| {
                            left_weight
                                .cmp(right_weight)
                                .then_with(|| left_variable.cmp(right_variable))
                        },
                    );
                    let weights = terms
                        .iter()
                        .map(|(_, weight)| weight.clone())
                        .collect::<Vec<_>>();
                    if expected_weights
                        .as_ref()
                        .is_some_and(|expected| expected != &weights)
                    {
                        return None;
                    }
                    expected_weights.get_or_insert(weights);

                    for (variable, _) in terms {
                        if !covered_variables.insert(variable) {
                            return None;
                        }
                        lifted[block_index].push(variable.checked_add(1)?);
                    }
                }
            }
        } else {
            for (block_index, block) in blocks.iter().enumerate() {
                for &column in block {
                    if column >= self.num_vars || !covered_variables.insert(column) {
                        return None;
                    }
                    lifted[block_index].push(column.checked_add(1)?);
                }
            }
        }

        let expected_variables = self.num_vars as usize;
        if expected_variables == 0
            || covered_variables.len() != expected_variables
            || !covered_variables.iter().copied().eq(0..self.num_vars)
            || lifted.iter().any(Vec::is_empty)
            || lifted.windows(2).any(|pair| pair[0].len() != pair[1].len())
        {
            return None;
        }
        Some(lifted)
    }
}

/// Typed, fail-closed reason the PB route does not own a model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PbTranslateDecline {
    Deadline,
    TooManyColumns,
    TooManyConstraints,
    NonBooleanColumn { column: usize },
    NonBooleanDomain { column: usize },
    IntegerEncodingTooWide { column: usize },
    ImpliedBoundsResourceLimit,
    ContinuousNotSingleton { column: usize },
    SingletonRowNotEquality { column: usize, row: usize },
    SingletonRowHasContinuousPeer { column: usize, row: usize },
    RowCoefficientOverflow { row: usize },
    RowBoundOverflow { row: usize },
    RowNormalizationOverflow { row: usize },
    ObjectiveCoefficientOverflow,
    ObjectiveRangeOverflow,
}

/// Build an exact PB projection or decline without changing the model.
///
/// The established pure-Boolean translator gets first refusal, preserving its
/// byte-for-byte plan on that class.  Only a structural/domain decline enters
/// the bounded-integer + objective-singleton lane; arithmetic overflow and
/// deadlines remain terminal declines rather than silently selecting a more
/// permissive translation.
pub(crate) fn translate(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<PbRoutePlan, PbTranslateDecline> {
    match translate_boolean(model, deadline) {
        Ok(plan) => Ok(plan),
        Err(PbTranslateDecline::NonBooleanColumn { .. })
        | Err(PbTranslateDecline::NonBooleanDomain { .. }) => bounded::translate(model, deadline),
        Err(reason) => Err(reason),
    }
}

/// The original pure-Boolean projection.  Kept separate so the broader route
/// cannot perturb existing Boolean plans or their tests.
fn translate_boolean(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<PbRoutePlan, PbTranslateDecline> {
    if deadline_reached(deadline) {
        return Err(PbTranslateDecline::Deadline);
    }
    // The public PB type uses `u32`, but the core's literal representation is
    // bounded by signed DIMACS indices.  Decline before any adapter allocates
    // or converts an out-of-range variable.
    if model.cols.len() > i32::MAX as usize {
        return Err(PbTranslateDecline::TooManyColumns);
    }
    let num_vars =
        u32::try_from(model.cols.len()).map_err(|_| PbTranslateDecline::TooManyColumns)?;
    let mut constraints = Vec::with_capacity(model.rows.len().saturating_mul(2));

    // PB variables are intrinsically Boolean.  Explicit model bounds still
    // matter: represent fixed/empty integral domains as exact PB rows, and
    // decline if an integer admitted by the model lies outside {0, 1}.
    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        if !matches!(spec.kind, ColKind::Binary | ColKind::Integer) {
            return Err(PbTranslateDecline::NonBooleanColumn { column });
        }
        let Some(lb) = exact(spec.lb) else {
            return Err(PbTranslateDecline::NonBooleanDomain { column });
        };
        let Some(ub) = exact(spec.ub) else {
            return Err(PbTranslateDecline::NonBooleanDomain { column });
        };
        let lo = lb.numer().div_ceil(lb.denom());
        let hi = ub.numer().div_floor(ub.denom());
        if lo > hi {
            constraints.push(PbInequality {
                terms: Vec::new(),
                rhs: 1,
            });
        } else if lo < BigInt::zero() || hi > BigInt::one() {
            return Err(PbTranslateDecline::NonBooleanDomain { column });
        } else if lo == BigInt::one() {
            constraints.push(PbInequality {
                terms: vec![(column as u32, 1)],
                rhs: 1,
            });
        } else if hi == BigInt::zero() {
            constraints.push(PbInequality {
                terms: vec![(column as u32, -1)],
                rhs: 0,
            });
        }
    }

    for (row_index, row) in model.rows.iter().enumerate() {
        if row_index & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        let mut exact_terms = Vec::with_capacity(row.coeffs.len());
        for (term_index, &(column, advice)) in row.coeffs.iter().enumerate() {
            if term_index & 0x3ff == 0 && deadline_reached(deadline) {
                return Err(PbTranslateDecline::Deadline);
            }
            let coefficient = model.row_coeff_exact(row_index, column, advice);
            if !coefficient.is_zero() {
                exact_terms.push((column, coefficient));
            }
        }
        let (terms, denominator) = integralize_terms(&exact_terms, deadline)?
            .ok_or(PbTranslateDecline::RowCoefficientOverflow { row: row_index })?;

        if let Some(lb) = model.row_lb_exact(row_index, row.lb) {
            let rhs = scaled_ceil(&lb, &denominator)
                .and_then(|value| value.to_i128())
                .ok_or(PbTranslateDecline::RowBoundOverflow { row: row_index })?;
            let inequality = reduce_row_gcd(PbInequality {
                terms: terms.clone(),
                rhs,
            })
            .ok_or(PbTranslateDecline::RowNormalizationOverflow { row: row_index })?;
            if !pb_core_row_range_fits(&inequality) {
                return Err(PbTranslateDecline::RowNormalizationOverflow { row: row_index });
            }
            constraints.push(inequality);
        }
        if let Some(ub) = model.row_ub_exact(row_index, row.ub) {
            let rhs = scaled_ceil(&-ub, &denominator)
                .and_then(|value| value.to_i128())
                .ok_or(PbTranslateDecline::RowBoundOverflow { row: row_index })?;
            let negated = terms
                .iter()
                .map(|&(column, coefficient)| coefficient.checked_neg().map(|a| (column, a)))
                .collect::<Option<Vec<_>>>()
                .ok_or(PbTranslateDecline::RowCoefficientOverflow { row: row_index })?;
            let inequality = reduce_row_gcd(PbInequality {
                terms: negated,
                rhs,
            })
            .ok_or(PbTranslateDecline::RowNormalizationOverflow { row: row_index })?;
            if !pb_core_row_range_fits(&inequality) {
                return Err(PbTranslateDecline::RowNormalizationOverflow { row: row_index });
            }
            constraints.push(inequality);
        }
    }

    let objective = model
        .has_objective
        .then(|| translate_objective(model, deadline))
        .transpose()?;
    let num_constraints =
        u32::try_from(constraints.len()).map_err(|_| PbTranslateDecline::TooManyConstraints)?;

    Ok(PbRoutePlan {
        num_vars,
        num_constraints,
        constraints,
        objective,
        column_lifts: None,
        eliminated_continuous: 0,
        encoded_general_integers: 0,
    })
}

fn translate_objective(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<PbObjectivePlan, PbTranslateDecline> {
    let mut exact_terms = Vec::with_capacity(model.cols.len());
    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        let coefficient = model.obj_coeff_exact_at(column as u32, spec.obj);
        if !coefficient.is_zero() {
            exact_terms.push((column as u32, coefficient));
        }
    }
    let (mut terms, denominator) = integralize_terms(&exact_terms, deadline)?
        .ok_or(PbTranslateDecline::ObjectiveCoefficientOverflow)?;
    let direction = match model.sense {
        Sense::Minimize => 1,
        Sense::Maximize => {
            for (_, coefficient) in &mut terms {
                *coefficient = coefficient
                    .checked_neg()
                    .ok_or(PbTranslateDecline::ObjectiveCoefficientOverflow)?;
            }
            -1
        }
    };

    // Every exact ay-pb-core optimization adapter represents the complete
    // objective range in i128. Enforce that at admission so solver selection
    // remains independent of an arithmetic overflow in one particular arm.
    let mut minimum = 0i128;
    let mut maximum = 0i128;
    for &(_, coefficient) in &terms {
        if coefficient == i128::MIN {
            return Err(PbTranslateDecline::ObjectiveCoefficientOverflow);
        }
        if coefficient < 0 {
            minimum = minimum
                .checked_add(coefficient)
                .ok_or(PbTranslateDecline::ObjectiveRangeOverflow)?;
        } else {
            maximum = maximum
                .checked_add(coefficient)
                .ok_or(PbTranslateDecline::ObjectiveRangeOverflow)?;
        }
    }

    Ok(PbObjectivePlan {
        terms,
        map: PbObjectiveMap {
            denominator,
            direction,
            offset: model.obj_offset_exact(),
        },
    })
}

/// Clear only the coefficient denominators.  Returns integer terms and the
/// positive multiplier used.  Zero coefficients are omitted.
fn integralize_terms(
    terms: &[(u32, BigRational)],
    deadline: Option<Instant>,
) -> Result<Option<(Vec<(u32, i128)>, BigInt)>, PbTranslateDecline> {
    let mut denominator = BigInt::one();
    for (index, (_, coefficient)) in terms.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        denominator = denominator.lcm(coefficient.denom());
    }
    let mut integer_terms = Vec::with_capacity(terms.len());
    for (index, &(column, ref coefficient)) in terms.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        if coefficient.is_zero() {
            continue;
        }
        let multiplier = &denominator / coefficient.denom();
        let Some(integer) = (coefficient.numer() * multiplier)
            .to_i128()
            // ay-pb normalizes a negative coefficient by negating it.
            // `i128::MIN` has no positive counterpart and must never reach
            // that path.
            .filter(|&integer| integer != i128::MIN)
        else {
            return Ok(None);
        };
        integer_terms.push((column, integer));
    }
    Ok(Some((integer_terms, denominator)))
}

fn deadline_reached(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

/// The PB core's normalized row representation rewrites each negative `a*x` into
/// `(-a)*~x` and raises the rhs by `-a`, then maintains sums of all positive
/// weights in `i128`.  Preflight those exact operations so none of its
/// saturating defensive arithmetic is semantically reachable from this route.
fn pb_core_row_range_fits(row: &PbInequality) -> bool {
    let mut normalized_rhs = row.rhs;
    let mut total_weight = 0i128;
    for &(_, coefficient) in &row.terms {
        let Some(weight) = coefficient.checked_abs() else {
            return false;
        };
        let Some(next_total) = total_weight.checked_add(weight) else {
            return false;
        };
        total_weight = next_total;
        if coefficient < 0 {
            let Some(next_rhs) = normalized_rhs.checked_add(weight) else {
                return false;
            };
            normalized_rhs = next_rhs;
        }
    }
    true
}

/// Certificate-only sibling access for constructing the exact strict-objective
/// cutoff after ordinary model translation.
pub(crate) fn pb_core_row_range_fits_for_certificate(row: &PbInequality) -> bool {
    pb_core_row_range_fits(row)
}

/// Divide a PB row by the GCD of its integer coefficients.  Since the left
/// side is a multiple of `g` on every Boolean assignment,
/// `sum(a*x) >= rhs` is exactly equivalent to
/// `sum((a/g)*x) >= ceil(rhs/g)`.  This is the standard PB GCD
/// strengthening and keeps common MPS scaling factors out of the solver.
fn reduce_row_gcd(mut row: PbInequality) -> Option<PbInequality> {
    let gcd = row
        .terms
        .iter()
        .map(|&(_, coefficient)| coefficient.abs())
        .fold(0i128, |acc, coefficient| acc.gcd(&coefficient));
    if gcd <= 1 {
        return Some(row);
    }
    for (_, coefficient) in &mut row.terms {
        *coefficient /= gcd;
    }
    row.rhs = BigInt::from(row.rhs)
        .div_ceil(&BigInt::from(gcd))
        .to_i128()?;
    Some(row)
}

/// `ceil(value * denominator)`; `None` is reserved for an impossible zero or
/// negative denominator invariant violation.
fn scaled_ceil(value: &BigRational, denominator: &BigInt) -> Option<BigInt> {
    if denominator <= &BigInt::zero() {
        return None;
    }
    let scaled_numerator = value.numer() * denominator;
    Some(scaled_numerator.div_ceil(value.denom()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Col, Model};

    fn br(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn bits(values: usize) -> impl Iterator<Item = Vec<bool>> {
        (0usize..(1usize << values))
            .map(move |mask| (0..values).map(|bit| mask & (1usize << bit) != 0).collect())
    }

    fn model_accepts(model: &Model, assignment: &[bool]) -> bool {
        let point: Vec<BigRational> = assignment
            .iter()
            .map(|&value| BigRational::from_integer(BigInt::from(u8::from(value))))
            .collect();
        model.check_point(&point).is_ok()
    }

    #[test]
    fn fractional_range_uses_exact_ceil_and_floor_semantics() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(0.75, 1.30, &[(x, 0.5), (y, 1.25)]);

        let plan = translate(&model, None).expect("pure binary rational row");
        assert_eq!(
            plan.constraints,
            vec![
                PbInequality {
                    terms: vec![(0, 2), (1, 5)],
                    rhs: 3,
                },
                PbInequality {
                    terms: vec![(0, -2), (1, -5)],
                    // ceil(-4 * 1.30) = ceil(-5.2) = -5.
                    rhs: -5,
                },
            ]
        );
        for assignment in bits(2) {
            assert_eq!(
                plan.satisfies(&assignment),
                model_accepts(&model, &assignment),
                "assignment={assignment:?}"
            );
        }
    }

    #[test]
    fn true_rational_side_store_controls_rows_and_objective_mapping() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let row = model.add_row(0.0, f64::INFINITY, &[(x, 1.0 / 3.0), (y, 0.5)]);
        model.record_inexact_row_coeff(row, x.0, br(1, 3));
        model.record_inexact_row_bound(row, true, br(2, 3));

        model.set_objective(&[(x, 1.0 / 3.0), (y, -0.5)], Sense::Maximize);
        model.record_inexact_obj_coeff(x.0, br(1, 3));
        model.set_objective_offset(0.2);
        model.record_inexact_obj_offset(br(1, 5));

        let plan = translate(&model, None).expect("exact side-store model");
        assert_eq!(
            plan.constraints,
            vec![PbInequality {
                terms: vec![(0, 2), (1, 3)],
                rhs: 4,
            }]
        );
        let objective = plan.objective.as_ref().expect("explicit objective");
        // max (1/3 x - 1/2 y) -> min (-2x + 3y), denominator 6.
        assert_eq!(objective.terms, vec![(0, -2), (1, 3)]);
        assert_eq!(objective.map.denominator(), &BigInt::from(6));
        assert_eq!(objective.map.direction(), -1);
        assert_eq!(objective.map.offset(), &br(1, 5));
        for assignment in bits(2) {
            let pb_value = objective
                .value_at(&assignment)
                .expect("two-column assignment");
            let point = plan.lift(&assignment).expect("total lift");
            assert_eq!(
                objective.map.model_value(pb_value),
                model.objective_value_at(&point),
                "assignment={assignment:?}"
            );
            assert_eq!(
                objective.map.pb_value(&model.objective_value_at(&point)),
                Some(pb_value),
                "inverse objective map, assignment={assignment:?}"
            );
        }
        assert_eq!(objective.map.pb_value(&br(1, 7)), None);
    }

    #[test]
    fn fixed_fractional_and_empty_integral_domains_are_exact() {
        let mut model = Model::new();
        let zero = model.add_int_col(-0.2, 0.8);
        let one = model.add_int_col(0.2, 1.8);
        let empty = model.add_int_col(0.2, 0.8);
        assert_eq!((zero, one, empty), (Col(0), Col(1), Col(2)));

        let plan = translate(&model, None).expect("domains are subsets of Boolean");
        assert_eq!(
            plan.constraints,
            vec![
                PbInequality {
                    terms: vec![(0, -1)],
                    rhs: 0,
                },
                PbInequality {
                    terms: vec![(1, 1)],
                    rhs: 1,
                },
                PbInequality {
                    terms: Vec::new(),
                    rhs: 1,
                },
            ]
        );
        assert!(bits(3).all(|assignment| !plan.satisfies(&assignment)));
    }

    #[test]
    fn explicit_constant_objective_keeps_offset_and_implicit_feasibility_does_not_optimize() {
        let mut feasibility = Model::new();
        feasibility.add_binary_col();
        assert!(translate(&feasibility, None)
            .expect("feasibility")
            .objective
            .is_none());

        let mut constant = feasibility;
        constant.set_objective_offset(7.25);
        let objective = translate(&constant, None)
            .expect("constant objective")
            .objective
            .expect("explicit objective remains optimization");
        assert!(objective.terms.is_empty());
        assert_eq!(objective.map.denominator(), &BigInt::one());
        assert_eq!(objective.map.model_value(0), br(29, 4));
    }

    #[test]
    fn maximizing_minimizing_and_offset_mapping_are_reversible() {
        for sense in [Sense::Minimize, Sense::Maximize] {
            let mut model = Model::new();
            let x = model.add_binary_col();
            let y = model.add_binary_col();
            model.set_objective(&[(x, 0.5), (y, -0.75)], sense);
            model.set_objective_offset(0.625);

            let plan = translate(&model, None).expect("dyadic objective");
            let objective = plan.objective.as_ref().expect("objective plan");
            let expected = if sense == Sense::Minimize {
                vec![(0, 2), (1, -3)]
            } else {
                vec![(0, -2), (1, 3)]
            };
            assert_eq!(objective.terms, expected);
            for assignment in bits(2) {
                let pb_value = objective.value_at(&assignment).expect("complete model");
                let point = plan.lift(&assignment).expect("lift");
                assert_eq!(
                    objective.map.model_value(pb_value),
                    model.objective_value_at(&point),
                    "sense={sense:?}, assignment={assignment:?}"
                );
            }
        }
    }

    #[test]
    fn objective_range_overflow_declines_before_solver_dispatch() {
        let mut model = Model::new();
        let a = model.add_binary_col();
        let b = model.add_binary_col();
        model.set_objective(
            &[(a, i128::MAX as f64), (b, i128::MAX as f64)],
            Sense::Minimize,
        );
        // The f64 advice above is rounded.  Install exact values so each term
        // fits i128 but their positive range does not.
        model.record_inexact_obj_coeff(a.0, BigRational::from_integer(BigInt::from(i128::MAX)));
        model.record_inexact_obj_coeff(b.0, BigRational::from_integer(BigInt::from(i128::MAX)));
        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::ObjectiveRangeOverflow)
        );
    }

    #[test]
    fn row_normalization_overflow_declines_before_solver_dispatch() {
        let mut model = Model::new();
        let a = model.add_binary_col();
        let b = model.add_binary_col();
        let row = model.add_row(
            1.0,
            f64::INFINITY,
            &[(a, i128::MAX as f64), (b, i128::MAX as f64)],
        );
        model.record_inexact_row_coeff(
            row,
            a.0,
            BigRational::from_integer(BigInt::from(i128::MAX)),
        );
        model.record_inexact_row_coeff(
            row,
            b.0,
            BigRational::from_integer(BigInt::from(i128::MAX - 1)),
        );
        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::RowNormalizationOverflow { row: 0 })
        );
    }

    #[test]
    fn common_row_scale_is_removed_with_exact_rhs_strengthening() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(3.0, f64::INFINITY, &[(x, 2.0), (y, 4.0)]);
        let plan = translate(&model, None).expect("scaled PB row");
        assert_eq!(
            plan.constraints,
            vec![PbInequality {
                terms: vec![(0, 1), (1, 2)],
                rhs: 2,
            }]
        );
        for assignment in bits(2) {
            assert_eq!(
                plan.satisfies(&assignment),
                model_accepts(&model, &assignment)
            );
        }
    }

    #[test]
    fn bounded_general_integer_uses_exact_radix_fallback() {
        let mut model = Model::new();
        model.add_int_col(0.0, 2.0);

        let plan = translate(&model, None).expect("finite general-integer projection");
        assert_eq!(plan.num_vars, 2);
        assert_eq!(plan.encoded_general_integers, 1);
        assert_eq!(plan.eliminated_continuous, 0);
        for assignment in bits(2) {
            let accepted = plan.satisfies(&assignment);
            let point = plan.lift(&assignment).expect("radix postsolve");
            assert_eq!(accepted, model.check_point(&point).is_ok());
        }
    }

    #[test]
    fn model_column_swap_expands_through_exact_radix_weights() {
        let mut model = Model::new();
        model.add_int_col(0.0, 2.0);
        model.add_int_col(0.0, 2.0);
        let plan = translate(&model, None).expect("two bounded integer columns");
        assert_eq!(plan.num_vars, 4);

        let source = BTreeMap::from([(0, 1), (1, 0)]);
        let lifted = plan
            .lift_model_column_permutation_to_pb(&source)
            .expect("equal radix domains lift to a Boolean permutation");
        assert_eq!(lifted, BTreeMap::from([(1, 3), (2, 4), (3, 1), (4, 2)]));
    }

    #[test]
    fn model_column_swap_declines_mismatched_radix_domains() {
        let mut model = Model::new();
        model.add_int_col(0.0, 1.0);
        model.add_int_col(0.0, 2.0);
        let plan = translate(&model, None).expect("bounded integer columns");
        let source = BTreeMap::from([(0, 1), (1, 0)]);
        assert!(plan.lift_model_column_permutation_to_pb(&source).is_none());
    }

    #[test]
    fn complete_ordered_binary_blocks_lift_to_one_based_pb_partition() {
        let mut model = Model::new();
        for _ in 0..6 {
            model.add_binary_col();
        }
        let plan = translate(&model, None).expect("six Boolean columns");
        let blocks = vec![vec![0, 2, 4], vec![1, 3, 5]];
        assert_eq!(
            plan.lift_model_column_blocks_to_pb(&blocks),
            Some(vec![vec![1, 3, 5], vec![2, 4, 6]])
        );
    }

    #[test]
    fn ordered_blocks_expand_radix_coordinates_and_skip_uniform_fixed_coordinates() {
        let mut model = Model::new();
        for _ in 0..2 {
            model.add_int_col(2.0, 2.0);
            model.add_int_col(0.0, 2.0);
            model.add_binary_col();
        }
        let plan = translate(&model, None).expect("two fixed/radix/Boolean blocks");
        assert_eq!(plan.num_vars, 6);
        assert_eq!(
            plan.lift_model_column_blocks_to_pb(&[vec![0, 1, 2], vec![3, 4, 5]]),
            Some(vec![vec![1, 2, 3], vec![4, 5, 6]])
        );
    }

    #[test]
    fn ordered_blocks_preserve_equal_weight_multiplicity_deterministically() {
        let plan = PbRoutePlan {
            num_vars: 4,
            num_constraints: 0,
            constraints: Vec::new(),
            objective: None,
            column_lifts: Some(vec![
                PbAffine {
                    constant: br(0, 1),
                    terms: vec![(0, br(1, 1)), (1, br(1, 1))],
                },
                PbAffine {
                    constant: br(0, 1),
                    terms: vec![(2, br(1, 1)), (3, br(1, 1))],
                },
            ]),
            eliminated_continuous: 0,
            encoded_general_integers: 0,
        };
        assert_eq!(
            plan.lift_model_column_blocks_to_pb(&[vec![0], vec![1]]),
            Some(vec![vec![1, 2], vec![3, 4]])
        );

        // Decline even though both visible block coordinates still match: PB
        // variable five has no model-column owner in this malformed plan.
        let mut missing_variable = plan;
        missing_variable.num_vars = 5;
        assert!(missing_variable
            .lift_model_column_blocks_to_pb(&[vec![0], vec![1]])
            .is_none());
    }

    #[test]
    fn ordered_blocks_decline_partial_duplicate_or_unequal_model_partitions() {
        let mut model = Model::new();
        for _ in 0..4 {
            model.add_binary_col();
        }
        let plan = translate(&model, None).expect("four Boolean columns");
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0], vec![1]])
            .is_none());
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0, 1], vec![2, 2]])
            .is_none());
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0, 1], vec![2]])
            .is_none());
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0, 1, 2, 3]])
            .is_none());
    }

    #[test]
    fn ordered_radix_blocks_decline_constant_weight_and_fixed_shape_mismatches() {
        let mut constant_mismatch = Model::new();
        constant_mismatch.add_int_col(0.0, 2.0);
        constant_mismatch.add_int_col(1.0, 3.0);
        let plan = translate(&constant_mismatch, None).expect("equal-width shifted integers");
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0], vec![1]])
            .is_none());

        let mut weight_mismatch = Model::new();
        weight_mismatch.add_int_col(0.0, 1.0);
        weight_mismatch.add_int_col(0.0, 2.0);
        let plan = translate(&weight_mismatch, None).expect("different radix widths");
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0], vec![1]])
            .is_none());

        let mut fixed_mismatch = Model::new();
        fixed_mismatch.add_int_col(2.0, 2.0);
        fixed_mismatch.add_binary_col();
        fixed_mismatch.add_binary_col();
        fixed_mismatch.add_int_col(2.0, 2.0);
        let plan = translate(&fixed_mismatch, None).expect("fixed-coordinate mismatch");
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0, 1], vec![2, 3]])
            .is_none());
    }

    #[test]
    fn ordered_blocks_decline_shared_pb_variable_ownership() {
        let mut model = Model::new();
        let bit = model.add_binary_col();
        let alias = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(alias, 1.0), (bit, -1.0)]);
        let plan = translate(&model, None).expect("exact singleton alias");
        assert_eq!(plan.num_vars, 1);
        assert!(plan
            .lift_model_column_blocks_to_pb(&[vec![0], vec![1]])
            .is_none());
    }

    #[test]
    fn expired_deadline_declines_before_translation() {
        let model = Model::new();
        assert_eq!(
            translate(&model, Some(Instant::now())),
            Err(PbTranslateDecline::Deadline)
        );
    }

    #[test]
    fn exhaustive_small_rows_match_original_exact_model() {
        let coefficients = [-1.5, -0.5, 0.25, 1.0, 1.75];
        let bounds = [-1.25, -0.25, 0.5, 1.25, 2.5];
        for &a in &coefficients {
            for &b in &coefficients {
                for &lb in &bounds {
                    for &ub in bounds.iter().filter(|&&ub| ub >= lb) {
                        let mut model = Model::new();
                        let x = model.add_binary_col();
                        let y = model.add_binary_col();
                        model.add_row(lb, ub, &[(x, a), (y, b)]);
                        let plan = translate(&model, None).expect("small dyadic row");
                        for assignment in bits(2) {
                            assert_eq!(
                                plan.satisfies(&assignment),
                                model_accepts(&model, &assignment),
                                "a={a}, b={b}, lb={lb}, ub={ub}, assignment={assignment:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}
