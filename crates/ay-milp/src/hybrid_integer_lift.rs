// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact bounded-integer lift for the binary-master hybrid PB/LP route.
//!
//! [`hybrid_pb_lp`](crate::hybrid_pb_lp) deliberately accepts only Boolean
//! master columns.  This module gives a finite general-integer master the same
//! semantics through a checked radix bijection:
//!
//! ```text
//! x = ceil(lb) + b0 + 2*b1 + 4*b2 + ...
//! ```
//!
//! and, when necessary, one exact row excluding unused high codes.  Every
//! original row and the objective is substituted in exact rational arithmetic.
//! The rebuilt model retains an `f64` advice matrix for the numerical LP, but
//! any rounded value is recorded in the model's authoritative exact side
//! store.  A nonzero coefficient without a finite, nonzero advice value makes
//! the route decline.
//!
//! The construction is fail-closed.  It accepts only explicitly finite
//! integral domains, caps radix and matrix growth, independently reads every
//! rebuilt row/objective back through the exact side store, and revalidates the
//! whole equivalence before treating transformed-model infeasibility as an
//! original-model verdict.  Feasible/optimal points are lifted and checked
//! against both models.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

#[cfg(test)]
use crate::hybrid_pb_lp::HybridPbLpDecision;
use crate::hybrid_pb_lp::{
    verify_hybrid_pb_lp_infeasibility_certificate_interruptible, CertifiedHybridPbLpDecision,
    HybridPbLpInfeasibilityCertificate,
};
use crate::model::{exact, Col, ColKind, Model, Row};

/// One source domain cannot expand into an effectively unbounded PB master.
/// The later total-column and total-term envelopes are independent backstops.
const MAX_RADIX_BITS_PER_COLUMN: usize = 126;
const MAX_TRANSFORMED_COLUMNS: usize = 250_000;
const MAX_TRANSFORMED_ROWS: usize = 250_000;
const MAX_TRANSFORMED_TERMS: usize = 4_000_000;
const MAX_EXACT_VALUE_BITS: u64 = 16_384;
const MAX_HYBRID_INTEGER_LIFT_CERTIFICATE_JSON_BYTES: u64 = 64 << 20;

pub(crate) const HYBRID_INTEGER_LIFT_INFEASIBILITY_CERTIFICATE_FORMAT: &str =
    "ay.hybrid-integer-lift-infeasible.v1";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HybridIntegerLiftDecline {
    Deadline,
    InvalidModel,
    NoIntegralMaster,
    NoContinuousRecourse,
    OpenIntegerDomain { column: usize },
    BinaryDomain { column: usize },
    RadixTooWide { column: usize },
    TooManyColumns,
    TooManyRows,
    TooManyTerms,
    ExactValueTooLarge,
    CoefficientAdvice,
    BoundAdvice,
    ObjectiveAdvice,
    EquivalenceCheck,
}

/// Proof-retaining result from the exact bounded-integer lift.
pub(crate) enum CertifiedHybridIntegerLiftDecision {
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    Infeasible(HybridIntegerLiftInfeasibilityCertificate),
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

/// The integer-lift wrapper stores no transformed model or trusted mapping.
/// Replay deterministically rebuilds and revalidates the exact radix
/// bijection from the original model, then checks the nested hybrid proof
/// against that rebuilt model.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HybridIntegerLiftInfeasibilityCertificate {
    pub(crate) format: String,
    pub(crate) transformed: HybridPbLpInfeasibilityCertificate,
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum HybridIntegerLiftCertificateCodecError {
    #[error("hybrid integer-lift certificate exceeds the {limit}-byte encoded limit")]
    Oversized { limit: u64 },
    #[error("malformed hybrid integer-lift certificate: {0}")]
    Malformed(#[source] serde_json::Error),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub(crate) enum HybridIntegerLiftCertificateVerificationError {
    #[error("hybrid integer-lift certificate verification was interrupted")]
    Interrupted,
    #[error("original model is not an admissible exact bounded-integer lift")]
    UnsupportedModel,
    #[error("hybrid integer-lift certificate has the wrong format")]
    InvalidFormat,
    #[error("rebuilt transformed model rejected the nested hybrid certificate")]
    NestedCertificateRejected,
    #[error("hybrid integer-lift certificate cannot be represented by the bounded codec")]
    SerializationLimit,
}

/// Try the integer-lifted hybrid route.  `None` is a structural/resource
/// decline or an exact postsolve failure, never a partial verdict.
#[cfg(test)]
pub(crate) fn try_solve(original: &Model, deadline: Option<Instant>) -> Option<HybridPbLpDecision> {
    try_solve_interruptible(original, deadline, || false)
}

#[cfg(test)]
pub(crate) fn try_solve_interruptible<F>(
    original: &Model,
    deadline: Option<Instant>,
    should_stop: F,
) -> Option<HybridPbLpDecision>
where
    F: FnMut() -> bool,
{
    try_solve_certified_interruptible(original, deadline, should_stop)
        .map(drop_integer_lift_certificate)
}

pub(crate) fn try_solve_certified(
    original: &Model,
    deadline: Option<Instant>,
) -> Option<CertifiedHybridIntegerLiftDecision> {
    try_solve_certified_interruptible(original, deadline, || false)
}

pub(crate) fn try_solve_certified_interruptible<F>(
    original: &Model,
    deadline: Option<Instant>,
    mut should_stop: F,
) -> Option<CertifiedHybridIntegerLiftDecision>
where
    F: FnMut() -> bool,
{
    let lift = ValidatedLift::build(original, deadline, &mut should_stop).ok()?;
    if stopped(deadline, &mut should_stop) {
        return None;
    }
    let decision = crate::hybrid_pb_lp::try_solve_certified_interruptible(
        &lift.transformed,
        deadline,
        &mut should_stop,
    )?;
    if stopped(deadline, &mut should_stop) {
        return None;
    }

    match decision {
        CertifiedHybridPbLpDecision::Feasible {
            model_values,
            incumbent_only,
        } => {
            let lifted = lift.checked_lift_point(original, &model_values)?;
            if stopped(deadline, &mut should_stop) {
                return None;
            }
            Some(CertifiedHybridIntegerLiftDecision::Feasible {
                model_values: lifted,
                incumbent_only,
            })
        }
        CertifiedHybridPbLpDecision::Optimal {
            value,
            model_values,
        } => {
            let lifted = lift.checked_lift_point(original, &model_values)?;
            if stopped(deadline, &mut should_stop) {
                return None;
            }
            if lift.transformed.objective_value_at(&model_values) != value
                || original.objective_value_at(&lifted) != value
            {
                return None;
            }
            Some(CertifiedHybridIntegerLiftDecision::Optimal {
                value,
                model_values: lifted,
            })
        }
        CertifiedHybridPbLpDecision::Infeasible(transformed) => {
            // This is the load-bearing implication.  Re-read the completed
            // transformed model through the exact side store after the solve;
            // only a still-valid radix bijection licenses promotion.
            lift.revalidate(original, deadline, &mut should_stop).ok()?;
            if stopped(deadline, &mut should_stop) {
                return None;
            }
            let certificate = HybridIntegerLiftInfeasibilityCertificate {
                format: HYBRID_INTEGER_LIFT_INFEASIBILITY_CERTIFICATE_FORMAT.to_owned(),
                transformed,
            };
            verify_hybrid_integer_lift_infeasibility_certificate_interruptible(
                original,
                &certificate,
                deadline,
                &mut should_stop,
            )
            .ok()?;
            encode_hybrid_integer_lift_infeasibility_certificate_json(&certificate).ok()?;
            Some(CertifiedHybridIntegerLiftDecision::Infeasible(certificate))
        }
    }
}

#[cfg(test)]
fn drop_integer_lift_certificate(
    decision: CertifiedHybridIntegerLiftDecision,
) -> HybridPbLpDecision {
    match decision {
        CertifiedHybridIntegerLiftDecision::Feasible { .. } => HybridPbLpDecision::Feasible,
        CertifiedHybridIntegerLiftDecision::Infeasible(_) => HybridPbLpDecision::Infeasible,
        CertifiedHybridIntegerLiftDecision::Optimal {
            value,
            model_values,
        } => HybridPbLpDecision::Optimal {
            value,
            model_values,
        },
    }
}

pub(crate) fn verify_hybrid_integer_lift_infeasibility_certificate(
    original: &Model,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Result<(), HybridIntegerLiftCertificateVerificationError> {
    verify_hybrid_integer_lift_infeasibility_certificate_interruptible(
        original,
        certificate,
        None,
        &mut || false,
    )
}

pub(crate) fn verify_hybrid_integer_lift_infeasibility_certificate_interruptible<F>(
    original: &Model,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<(), HybridIntegerLiftCertificateVerificationError>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return Err(HybridIntegerLiftCertificateVerificationError::Interrupted);
    }
    if certificate.format != HYBRID_INTEGER_LIFT_INFEASIBILITY_CERTIFICATE_FORMAT {
        return Err(HybridIntegerLiftCertificateVerificationError::InvalidFormat);
    }
    encode_hybrid_integer_lift_infeasibility_certificate_json(certificate)
        .map_err(|_| HybridIntegerLiftCertificateVerificationError::SerializationLimit)?;
    let lift = ValidatedLift::build(original, deadline, should_stop).map_err(|decline| {
        if matches!(decline, HybridIntegerLiftDecline::Deadline) || stopped(deadline, should_stop) {
            HybridIntegerLiftCertificateVerificationError::Interrupted
        } else {
            HybridIntegerLiftCertificateVerificationError::UnsupportedModel
        }
    })?;
    lift.revalidate(original, deadline, should_stop)
        .map_err(|decline| {
            if matches!(decline, HybridIntegerLiftDecline::Deadline)
                || stopped(deadline, should_stop)
            {
                HybridIntegerLiftCertificateVerificationError::Interrupted
            } else {
                HybridIntegerLiftCertificateVerificationError::UnsupportedModel
            }
        })?;
    verify_hybrid_pb_lp_infeasibility_certificate_interruptible(
        &lift.transformed,
        &certificate.transformed,
        deadline,
        should_stop,
    )
    .map_err(|_| {
        if stopped(deadline, should_stop) {
            HybridIntegerLiftCertificateVerificationError::Interrupted
        } else {
            HybridIntegerLiftCertificateVerificationError::NestedCertificateRejected
        }
    })
}

pub(crate) fn encode_hybrid_integer_lift_infeasibility_certificate_json(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Result<Vec<u8>, HybridIntegerLiftCertificateCodecError> {
    encode_hybrid_integer_lift_infeasibility_certificate_json_with_limit(
        certificate,
        MAX_HYBRID_INTEGER_LIFT_CERTIFICATE_JSON_BYTES,
    )
}

fn encode_hybrid_integer_lift_infeasibility_certificate_json_with_limit(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
    max_bytes: u64,
) -> Result<Vec<u8>, HybridIntegerLiftCertificateCodecError> {
    let mut writer = BoundedIntegerLiftCertificateWriter::new(max_bytes);
    let result = serde_json::to_writer(&mut writer, certificate);
    if writer.exceeded {
        return Err(HybridIntegerLiftCertificateCodecError::Oversized { limit: max_bytes });
    }
    result.map_err(HybridIntegerLiftCertificateCodecError::Malformed)?;
    Ok(writer.bytes)
}

pub(crate) fn decode_hybrid_integer_lift_infeasibility_certificate_json(
    encoded: &[u8],
) -> Result<HybridIntegerLiftInfeasibilityCertificate, HybridIntegerLiftCertificateCodecError> {
    if u64::try_from(encoded.len()).unwrap_or(u64::MAX)
        > MAX_HYBRID_INTEGER_LIFT_CERTIFICATE_JSON_BYTES
    {
        return Err(HybridIntegerLiftCertificateCodecError::Oversized {
            limit: MAX_HYBRID_INTEGER_LIFT_CERTIFICATE_JSON_BYTES,
        });
    }
    serde_json::from_slice(encoded).map_err(HybridIntegerLiftCertificateCodecError::Malformed)
}

struct BoundedIntegerLiftCertificateWriter {
    bytes: Vec<u8>,
    max_bytes: u64,
    exceeded: bool,
}

impl BoundedIntegerLiftCertificateWriter {
    fn new(max_bytes: u64) -> Self {
        Self {
            bytes: Vec::new(),
            max_bytes,
            exceeded: false,
        }
    }
}

impl Write for BoundedIntegerLiftCertificateWriter {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        let length = u64::try_from(self.bytes.len())
            .unwrap_or(u64::MAX)
            .checked_add(u64::try_from(buffer.len()).unwrap_or(u64::MAX));
        if length.is_none_or(|length| length > self.max_bytes) {
            self.exceeded = true;
            return Err(io::Error::other(
                "hybrid integer-lift certificate size limit",
            ));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum ColumnLift {
    Direct {
        target: Col,
    },
    Integer {
        lo: BigInt,
        hi: BigInt,
        bits: Vec<(Col, BigInt)>,
        restriction: Option<Row>,
    },
}

struct ValidatedLift {
    transformed: Model,
    columns: Vec<ColumnLift>,
    source_rows: Vec<Row>,
}

impl ValidatedLift {
    fn build<F>(
        original: &Model,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Result<Self, HybridIntegerLiftDecline>
    where
        F: FnMut() -> bool,
    {
        original
            .validate()
            .map_err(|_| HybridIntegerLiftDecline::InvalidModel)?;
        if stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        if original.num_cols() > MAX_TRANSFORMED_COLUMNS {
            return Err(HybridIntegerLiftDecline::TooManyColumns);
        }
        if original.num_rows() > MAX_TRANSFORMED_ROWS {
            return Err(HybridIntegerLiftDecline::TooManyRows);
        }

        let mut transformed = Model::new();
        transformed.inherit_ft_adoption_solve_latch(original);
        let mut columns = Vec::with_capacity(original.num_cols());
        let mut integral_columns = 0usize;
        let mut continuous_columns = 0usize;
        let mut retained_terms = 0usize;

        for column in 0..original.num_cols() {
            if column & 0x3ff == 0 && stopped(deadline, should_stop) {
                return Err(HybridIntegerLiftDecline::Deadline);
            }
            let source = Col(column as u32);
            let (lb, ub) = original.col_bounds(source);
            match original.col_kind(source) {
                ColKind::Binary => {
                    integral_columns += 1;
                    if !lb.is_finite() || !ub.is_finite() || lb < 0.0 || ub > 1.0 {
                        return Err(HybridIntegerLiftDecline::BinaryDomain { column });
                    }
                    ensure_column_capacity(&transformed, 1)?;
                    let target = transformed.add_binary_col();
                    transformed.set_col_bounds(target, lb, ub);
                    columns.push(ColumnLift::Direct { target });
                }
                ColKind::Integer => {
                    integral_columns += 1;
                    let lower =
                        exact(lb).ok_or(HybridIntegerLiftDecline::OpenIntegerDomain { column })?;
                    let upper =
                        exact(ub).ok_or(HybridIntegerLiftDecline::OpenIntegerDomain { column })?;
                    exact_value_fits(&lower)?;
                    exact_value_fits(&upper)?;
                    let lo = lower.numer().div_ceil(lower.denom());
                    let hi = upper.numer().div_floor(upper.denom());

                    if lo > hi {
                        ensure_row_capacity(&transformed, 1)?;
                        let restriction = add_exact_row(
                            &mut transformed,
                            &[],
                            Some(&BigRational::one()),
                            None,
                            deadline,
                            should_stop,
                        )?;
                        columns.push(ColumnLift::Integer {
                            lo,
                            hi,
                            bits: Vec::new(),
                            restriction: Some(restriction),
                        });
                        continue;
                    }

                    let width = &hi - &lo;
                    let mut bits = Vec::new();
                    let mut weight = BigInt::one();
                    while weight <= width {
                        if bits.len() >= MAX_RADIX_BITS_PER_COLUMN {
                            return Err(HybridIntegerLiftDecline::RadixTooWide { column });
                        }
                        ensure_column_capacity(&transformed, 1)?;
                        let bit = transformed.add_binary_col();
                        bits.push((bit, weight.clone()));
                        weight <<= 1usize;
                    }

                    let full_width = &weight - BigInt::one();
                    let restriction = if width < full_width {
                        retained_terms = retained_terms
                            .checked_add(bits.len())
                            .ok_or(HybridIntegerLiftDecline::TooManyTerms)?;
                        if retained_terms > MAX_TRANSFORMED_TERMS {
                            return Err(HybridIntegerLiftDecline::TooManyTerms);
                        }
                        ensure_row_capacity(&transformed, 1)?;
                        let terms = bits
                            .iter()
                            .map(|&(bit, ref radix)| {
                                (bit, BigRational::from_integer(radix.clone()))
                            })
                            .collect::<Vec<_>>();
                        Some(add_exact_row(
                            &mut transformed,
                            &terms,
                            None,
                            Some(&BigRational::from_integer(width)),
                            deadline,
                            should_stop,
                        )?)
                    } else {
                        None
                    };
                    columns.push(ColumnLift::Integer {
                        lo,
                        hi,
                        bits,
                        restriction,
                    });
                }
                ColKind::Continuous => {
                    continuous_columns += 1;
                    ensure_column_capacity(&transformed, 1)?;
                    let target = transformed.add_col(lb, ub);
                    columns.push(ColumnLift::Direct { target });
                }
            }
        }
        if integral_columns == 0 {
            return Err(HybridIntegerLiftDecline::NoIntegralMaster);
        }
        if continuous_columns == 0 {
            return Err(HybridIntegerLiftDecline::NoContinuousRecourse);
        }

        let mut source_rows = Vec::with_capacity(original.num_rows());
        for row_index in 0..original.num_rows() {
            if row_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                return Err(HybridIntegerLiftDecline::Deadline);
            }
            let (source_terms, lb, ub) = original.row(Row(row_index as u32));
            let mut expression = ExactAffine::default();
            for (term_index, &(column, advice)) in source_terms.iter().enumerate() {
                if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return Err(HybridIntegerLiftDecline::Deadline);
                }
                let coefficient = original.row_coeff_exact(row_index, column, advice);
                exact_value_fits(&coefficient)?;
                expression.add_scaled(&coefficient, &columns[column as usize])?;
                if expression.terms.len() > MAX_TRANSFORMED_TERMS {
                    return Err(HybridIntegerLiftDecline::TooManyTerms);
                }
            }
            retained_terms = retained_terms
                .checked_add(expression.terms.len())
                .ok_or(HybridIntegerLiftDecline::TooManyTerms)?;
            if retained_terms > MAX_TRANSFORMED_TERMS {
                return Err(HybridIntegerLiftDecline::TooManyTerms);
            }
            let lower = original
                .row_lb_exact(row_index, lb)
                .map(|bound| checked_sub(bound, &expression.constant))
                .transpose()?;
            let upper = original
                .row_ub_exact(row_index, ub)
                .map(|bound| checked_sub(bound, &expression.constant))
                .transpose()?;
            ensure_row_capacity(&transformed, 1)?;
            source_rows.push(add_exact_row(
                &mut transformed,
                &expression.into_terms(),
                lower.as_ref(),
                upper.as_ref(),
                deadline,
                should_stop,
            )?);
        }

        install_objective(
            &mut transformed,
            original,
            &columns,
            retained_terms,
            deadline,
            should_stop,
        )?;

        let lift = Self {
            transformed,
            columns,
            source_rows,
        };
        lift.revalidate(original, deadline, should_stop)?;
        Ok(lift)
    }

    fn checked_lift_point(
        &self,
        original: &Model,
        transformed_values: &[BigRational],
    ) -> Option<Vec<BigRational>> {
        self.transformed.check_point(transformed_values).ok()?;
        let mut values = Vec::with_capacity(self.columns.len());
        for map in &self.columns {
            match map {
                ColumnLift::Direct { target } => {
                    values.push(transformed_values.get(target.index())?.clone());
                }
                ColumnLift::Integer { lo, bits, .. } => {
                    let mut value = lo.clone();
                    for &(bit, ref weight) in bits {
                        let bit_value = transformed_values.get(bit.index())?;
                        if bit_value == &BigRational::one() {
                            value += weight;
                        } else if !bit_value.is_zero() {
                            return None;
                        }
                    }
                    values.push(BigRational::from_integer(value));
                }
            }
        }
        original.check_point(&values).ok()?;
        if original.objective_value_at(&values)
            != self.transformed.objective_value_at(transformed_values)
        {
            return None;
        }
        Some(values)
    }

    fn revalidate<F>(
        &self,
        original: &Model,
        deadline: Option<Instant>,
        should_stop: &mut F,
    ) -> Result<(), HybridIntegerLiftDecline>
    where
        F: FnMut() -> bool,
    {
        original
            .validate()
            .map_err(|_| HybridIntegerLiftDecline::EquivalenceCheck)?;
        self.transformed
            .validate()
            .map_err(|_| HybridIntegerLiftDecline::EquivalenceCheck)?;
        if self.columns.len() != original.num_cols()
            || self.source_rows.len() != original.num_rows()
        {
            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
        }

        let mut owned = vec![false; self.transformed.num_cols()];
        let mut owned_rows = vec![false; self.transformed.num_rows()];
        for (column, map) in self.columns.iter().enumerate() {
            if column & 0x3ff == 0 && stopped(deadline, should_stop) {
                return Err(HybridIntegerLiftDecline::Deadline);
            }
            let source = Col(column as u32);
            let (lb, ub) = original.col_bounds(source);
            match (original.col_kind(source), map) {
                (ColKind::Binary, ColumnLift::Direct { target }) => {
                    validate_direct_column(
                        &self.transformed,
                        &mut owned,
                        *target,
                        ColKind::Binary,
                        (lb, ub),
                    )?;
                }
                (ColKind::Continuous, ColumnLift::Direct { target }) => {
                    validate_direct_column(
                        &self.transformed,
                        &mut owned,
                        *target,
                        ColKind::Continuous,
                        (lb, ub),
                    )?;
                }
                (
                    ColKind::Integer,
                    ColumnLift::Integer {
                        lo,
                        hi,
                        bits,
                        restriction,
                    },
                ) => {
                    let lower = exact(lb).ok_or(HybridIntegerLiftDecline::EquivalenceCheck)?;
                    let upper = exact(ub).ok_or(HybridIntegerLiftDecline::EquivalenceCheck)?;
                    let expected_lo = lower.numer().div_ceil(lower.denom());
                    let expected_hi = upper.numer().div_floor(upper.denom());
                    if lo != &expected_lo || hi != &expected_hi {
                        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                    }
                    if lo > hi {
                        let Some(row) = *restriction else {
                            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                        };
                        mark_owned_row(&mut owned_rows, row)?;
                        if !bits.is_empty()
                            || !row_matches_exact(
                                &self.transformed,
                                row,
                                &[],
                                Some(&BigRational::one()),
                                None,
                                deadline,
                                should_stop,
                            )?
                        {
                            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                        }
                        continue;
                    }
                    let width = hi - lo;
                    let mut expected_weight = BigInt::one();
                    for &(bit, ref weight) in bits {
                        if weight != &expected_weight {
                            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                        }
                        validate_direct_column(
                            &self.transformed,
                            &mut owned,
                            bit,
                            ColKind::Binary,
                            (0.0, 1.0),
                        )?;
                        expected_weight <<= 1usize;
                    }
                    let expected_bits = radix_bits(&width);
                    if bits.len() != expected_bits {
                        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                    }
                    let full_width = &expected_weight - BigInt::one();
                    if width < full_width {
                        let terms = bits
                            .iter()
                            .map(|&(bit, ref weight)| {
                                (bit, BigRational::from_integer(weight.clone()))
                            })
                            .collect::<Vec<_>>();
                        let Some(row) = *restriction else {
                            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                        };
                        mark_owned_row(&mut owned_rows, row)?;
                        if !row_matches_exact(
                            &self.transformed,
                            row,
                            &terms,
                            None,
                            Some(&BigRational::from_integer(width.clone())),
                            deadline,
                            should_stop,
                        )? {
                            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                        }
                    } else if restriction.is_some() {
                        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
                    }
                }
                _ => return Err(HybridIntegerLiftDecline::EquivalenceCheck),
            }
        }
        if owned.iter().any(|&is_owned| !is_owned) {
            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
        }

        for row_index in 0..original.num_rows() {
            if row_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                return Err(HybridIntegerLiftDecline::Deadline);
            }
            let (source_terms, lb, ub) = original.row(Row(row_index as u32));
            let mut expression = ExactAffine::default();
            for (term_index, &(column, advice)) in source_terms.iter().enumerate() {
                if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return Err(HybridIntegerLiftDecline::Deadline);
                }
                let coefficient = original.row_coeff_exact(row_index, column, advice);
                expression.add_scaled(&coefficient, &self.columns[column as usize])?;
            }
            let lower = original
                .row_lb_exact(row_index, lb)
                .map(|bound| checked_sub(bound, &expression.constant))
                .transpose()?;
            let upper = original
                .row_ub_exact(row_index, ub)
                .map(|bound| checked_sub(bound, &expression.constant))
                .transpose()?;
            mark_owned_row(&mut owned_rows, self.source_rows[row_index])?;
            if !row_matches_exact(
                &self.transformed,
                self.source_rows[row_index],
                &expression.into_terms(),
                lower.as_ref(),
                upper.as_ref(),
                deadline,
                should_stop,
            )? {
                return Err(HybridIntegerLiftDecline::EquivalenceCheck);
            }
        }
        if owned_rows.iter().any(|&is_owned| !is_owned) {
            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
        }
        objective_matches(
            original,
            &self.transformed,
            &self.columns,
            deadline,
            should_stop,
        )?;
        Ok(())
    }
}

#[derive(Default)]
struct ExactAffine {
    constant: BigRational,
    terms: BTreeMap<usize, BigRational>,
}

impl ExactAffine {
    fn add_term(
        &mut self,
        column: usize,
        coefficient: BigRational,
    ) -> Result<(), HybridIntegerLiftDecline> {
        if coefficient.is_zero() {
            return Ok(());
        }
        exact_value_fits(&coefficient)?;
        let remove = {
            let entry = self.terms.entry(column).or_insert_with(BigRational::zero);
            *entry += coefficient;
            exact_value_fits(entry)?;
            entry.is_zero()
        };
        if remove {
            self.terms.remove(&column);
        }
        Ok(())
    }

    fn add_scaled(
        &mut self,
        scale: &BigRational,
        map: &ColumnLift,
    ) -> Result<(), HybridIntegerLiftDecline> {
        if scale.is_zero() {
            return Ok(());
        }
        match map {
            ColumnLift::Direct { target } => self.add_term(target.index(), scale.clone()),
            ColumnLift::Integer { lo, bits, .. } => {
                self.constant += scale * BigRational::from_integer(lo.clone());
                exact_value_fits(&self.constant)?;
                for &(bit, ref weight) in bits {
                    self.add_term(
                        bit.index(),
                        scale * BigRational::from_integer(weight.clone()),
                    )?;
                }
                Ok(())
            }
        }
    }

    fn into_terms(self) -> Vec<(Col, BigRational)> {
        self.terms
            .into_iter()
            .map(|(column, coefficient)| (Col(column as u32), coefficient))
            .collect()
    }
}

fn install_objective<F>(
    transformed: &mut Model,
    original: &Model,
    columns: &[ColumnLift],
    retained_terms: usize,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<(), HybridIntegerLiftDecline>
where
    F: FnMut() -> bool,
{
    let mut expression = ExactAffine {
        constant: original.obj_offset_exact(),
        terms: BTreeMap::new(),
    };
    exact_value_fits(&expression.constant)?;
    for (column, map) in columns.iter().enumerate() {
        if column & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        let source = Col(column as u32);
        let advice = original.obj_coeff(source);
        let coefficient = original.obj_coeff_exact_at(column as u32, advice);
        // Model::objective_value_at deliberately skips stored zero advice, so
        // such an override cannot be represented faithfully by either model.
        if advice == 0.0 && !coefficient.is_zero() {
            return Err(HybridIntegerLiftDecline::ObjectiveAdvice);
        }
        exact_value_fits(&coefficient)?;
        expression.add_scaled(&coefficient, map)?;
    }
    if retained_terms
        .checked_add(expression.terms.len())
        .is_none_or(|total| total > MAX_TRANSFORMED_TERMS)
    {
        return Err(HybridIntegerLiftDecline::TooManyTerms);
    }
    if !original.has_objective() {
        if !expression.terms.is_empty() || !expression.constant.is_zero() {
            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
        }
        return Ok(());
    }

    let ExactAffine {
        constant: offset,
        terms,
    } = expression;
    let mut stored = Vec::with_capacity(terms.len());
    let mut overrides = Vec::new();
    for (term_index, (column, coefficient)) in terms.into_iter().enumerate() {
        if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        let column = Col(column as u32);
        let advice =
            coefficient_advice(&coefficient).ok_or(HybridIntegerLiftDecline::ObjectiveAdvice)?;
        stored.push((column, advice));
        if exact(advice).as_ref() != Some(&coefficient) {
            overrides.push((column.0, coefficient));
        }
    }
    transformed.set_objective(&stored, original.sense());
    let offset_advice = bound_advice(&offset).ok_or(HybridIntegerLiftDecline::ObjectiveAdvice)?;
    transformed.set_objective_offset(offset_advice);
    for (term_index, (column, coefficient)) in overrides.into_iter().enumerate() {
        if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        transformed.record_inexact_obj_coeff(column, coefficient);
    }
    if exact(offset_advice).as_ref() != Some(&offset) {
        transformed.record_inexact_obj_offset(offset);
    }
    Ok(())
}

fn objective_matches<F>(
    original: &Model,
    transformed: &Model,
    columns: &[ColumnLift],
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<(), HybridIntegerLiftDecline>
where
    F: FnMut() -> bool,
{
    if transformed.has_objective() != original.has_objective()
        || transformed.sense() != original.sense()
    {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    let mut expected = ExactAffine {
        constant: original.obj_offset_exact(),
        terms: BTreeMap::new(),
    };
    for (column, map) in columns.iter().enumerate() {
        if column & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        let source = Col(column as u32);
        let coefficient = original.obj_coeff_exact_at(column as u32, original.obj_coeff(source));
        exact_value_fits(&coefficient)?;
        expected.add_scaled(&coefficient, map)?;
    }
    if transformed.obj_offset_exact() != expected.constant {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    if expected
        .terms
        .keys()
        .any(|&column| column >= transformed.num_cols())
    {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    for column in 0..transformed.num_cols() {
        if column & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        let target = Col(column as u32);
        let actual = transformed.obj_coeff_exact_at(column as u32, transformed.obj_coeff(target));
        let wanted = expected
            .terms
            .get(&column)
            .cloned()
            .unwrap_or_else(BigRational::zero);
        if actual != wanted {
            return Err(HybridIntegerLiftDecline::EquivalenceCheck);
        }
    }
    Ok(())
}

fn add_exact_row<F>(
    model: &mut Model,
    terms: &[(Col, BigRational)],
    lb: Option<&BigRational>,
    ub: Option<&BigRational>,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<Row, HybridIntegerLiftDecline>
where
    F: FnMut() -> bool,
{
    if terms.len() > MAX_TRANSFORMED_TERMS {
        return Err(HybridIntegerLiftDecline::TooManyTerms);
    }
    let mut stored = Vec::with_capacity(terms.len());
    let mut overrides = Vec::new();
    for (term_index, &(column, ref coefficient)) in terms.iter().enumerate() {
        if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        exact_value_fits(coefficient)?;
        let advice =
            coefficient_advice(coefficient).ok_or(HybridIntegerLiftDecline::CoefficientAdvice)?;
        stored.push((column, advice));
        if exact(advice).as_ref() != Some(coefficient) {
            overrides.push((column.0, coefficient.clone()));
        }
    }
    let lb_advice = match lb {
        Some(value) => {
            exact_value_fits(value)?;
            bound_advice(value).ok_or(HybridIntegerLiftDecline::BoundAdvice)?
        }
        None => f64::NEG_INFINITY,
    };
    let ub_advice = match ub {
        Some(value) => {
            exact_value_fits(value)?;
            bound_advice(value).ok_or(HybridIntegerLiftDecline::BoundAdvice)?
        }
        None => f64::INFINITY,
    };
    let row = model.add_row(lb_advice, ub_advice, &stored);
    for (term_index, (column, coefficient)) in overrides.into_iter().enumerate() {
        if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        model.record_inexact_row_coeff(row, column, coefficient);
    }
    if let Some(value) = lb {
        if exact(lb_advice).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, true, value.clone());
        }
    }
    if let Some(value) = ub {
        if exact(ub_advice).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, false, value.clone());
        }
    }
    if !row_matches_exact(model, row, terms, lb, ub, deadline, should_stop)? {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    Ok(row)
}

fn row_matches_exact<F>(
    model: &Model,
    row: Row,
    expected_terms: &[(Col, BigRational)],
    expected_lb: Option<&BigRational>,
    expected_ub: Option<&BigRational>,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<bool, HybridIntegerLiftDecline>
where
    F: FnMut() -> bool,
{
    let (actual_terms, lb, ub) = model.row(row);
    if actual_terms.len() != expected_terms.len() {
        return Ok(false);
    }
    for (term_index, (&(column, advice), (expected_column, expected))) in
        actual_terms.iter().zip(expected_terms).enumerate()
    {
        if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
            return Err(HybridIntegerLiftDecline::Deadline);
        }
        if column != expected_column.0
            || model.row_coeff_exact(row.index(), column, advice) != *expected
        {
            return Ok(false);
        }
    }
    Ok(model.row_lb_exact(row.index(), lb).as_ref() == expected_lb
        && model.row_ub_exact(row.index(), ub).as_ref() == expected_ub)
}

fn validate_direct_column(
    model: &Model,
    owned: &mut [bool],
    target: Col,
    kind: ColKind,
    bounds: (f64, f64),
) -> Result<(), HybridIntegerLiftDecline> {
    let slot = owned
        .get_mut(target.index())
        .ok_or(HybridIntegerLiftDecline::EquivalenceCheck)?;
    if *slot || model.col_kind(target) != kind || model.col_bounds(target) != bounds {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    *slot = true;
    Ok(())
}

fn mark_owned_row(owned: &mut [bool], row: Row) -> Result<(), HybridIntegerLiftDecline> {
    let slot = owned
        .get_mut(row.index())
        .ok_or(HybridIntegerLiftDecline::EquivalenceCheck)?;
    if *slot {
        return Err(HybridIntegerLiftDecline::EquivalenceCheck);
    }
    *slot = true;
    Ok(())
}

fn ensure_column_capacity(
    model: &Model,
    additional: usize,
) -> Result<(), HybridIntegerLiftDecline> {
    let total = model
        .num_cols()
        .checked_add(additional)
        .ok_or(HybridIntegerLiftDecline::TooManyColumns)?;
    if total > MAX_TRANSFORMED_COLUMNS || total > i32::MAX as usize {
        return Err(HybridIntegerLiftDecline::TooManyColumns);
    }
    Ok(())
}

fn ensure_row_capacity(model: &Model, additional: usize) -> Result<(), HybridIntegerLiftDecline> {
    let total = model
        .num_rows()
        .checked_add(additional)
        .ok_or(HybridIntegerLiftDecline::TooManyRows)?;
    if total > MAX_TRANSFORMED_ROWS || total > u32::MAX as usize {
        return Err(HybridIntegerLiftDecline::TooManyRows);
    }
    Ok(())
}

fn exact_value_fits(value: &BigRational) -> Result<(), HybridIntegerLiftDecline> {
    if value.numer().bits() > MAX_EXACT_VALUE_BITS || value.denom().bits() > MAX_EXACT_VALUE_BITS {
        return Err(HybridIntegerLiftDecline::ExactValueTooLarge);
    }
    Ok(())
}

fn checked_sub(
    lhs: BigRational,
    rhs: &BigRational,
) -> Result<BigRational, HybridIntegerLiftDecline> {
    let value = lhs - rhs;
    exact_value_fits(&value)?;
    Ok(value)
}

fn coefficient_advice(value: &BigRational) -> Option<f64> {
    if value.is_zero() {
        return Some(0.0);
    }
    value
        .to_f64()
        .filter(|advice| advice.is_finite() && *advice != 0.0)
}

fn bound_advice(value: &BigRational) -> Option<f64> {
    value.to_f64().filter(|advice| advice.is_finite())
}

fn radix_bits(width: &BigInt) -> usize {
    let mut bits = 0usize;
    let mut weight = BigInt::one();
    while &weight <= width {
        bits += 1;
        weight <<= 1usize;
    }
    bits
}

fn stopped<F>(deadline: Option<Instant>, should_stop: &mut F) -> bool
where
    F: FnMut() -> bool,
{
    should_stop() || deadline.is_some_and(|end| Instant::now() >= end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Sense;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(value.into())
    }

    fn assignments(n: usize) -> impl Iterator<Item = Vec<BigRational>> {
        (0usize..(1usize << n)).map(move |mask| {
            (0..n)
                .map(|bit| integer(if mask & (1usize << bit) != 0 { 1 } else { 0 }))
                .collect()
        })
    }

    #[test]
    fn exhaustive_non_power_of_two_domain_is_bijective() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 2.0);
        model.add_row(1.0, 3.0, &[(x, 1.0), (y, 1.0)]);

        let lift = ValidatedLift::build(&model, None, &mut || false).expect("validated lift");
        assert_eq!(lift.transformed.num_cols(), 3, "two radix bits plus y");
        let integer_values = assignments(2);
        for bits in integer_values {
            for y_value in [integer(0), BigRational::new(1.into(), 2.into()), integer(2)] {
                let mut transformed = bits.clone();
                transformed.push(y_value);
                let transformed_feasible = lift.transformed.check_point(&transformed).is_ok();
                let lifted = lift.checked_lift_point(&model, &transformed);
                assert_eq!(transformed_feasible, lifted.is_some(), "{transformed:?}");
                if let Some(point) = lifted {
                    assert!((0..=2).any(|value| point[x.index()] == integer(value)));
                    model.check_point(&point).expect("original point");
                }
            }
        }
    }

    #[test]
    fn fractional_integer_bounds_round_inward_exactly() {
        let mut model = Model::new();
        let x = model.add_int_col(-1.2, 2.8);
        let y = model.add_col(0.0, 1.0);
        model.add_row(f64::NEG_INFINITY, 2.0, &[(x, 1.0), (y, 1.0)]);
        let lift = ValidatedLift::build(&model, None, &mut || false).expect("finite domain");
        let ColumnLift::Integer { lo, hi, .. } = &lift.columns[x.index()] else {
            panic!("integer radix");
        };
        assert_eq!(lo, &BigInt::from(-1));
        assert_eq!(hi, &BigInt::from(2));
    }

    #[test]
    fn lifted_minimum_preserves_value_and_point() {
        let mut model = Model::new();
        let x = model.add_int_col(-2.0, 2.0);
        let y = model.add_col(0.0, 5.0);
        model.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.set_objective(&[(y, 1.0)], Sense::Minimize);

        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = try_solve(&model, None).expect("hybrid optimum")
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, integer(1));
        assert_eq!(model_values[x.index()], integer(2));
        assert_eq!(model_values[y.index()], integer(1));
        model.check_point(&model_values).expect("original witness");
    }

    #[test]
    fn lifted_maximum_preserves_value_and_point() {
        let mut model = Model::new();
        let x = model.add_int_col(-2.0, 2.0);
        let y = model.add_col(0.0, 5.0);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(y, 1.0), (x, -1.0)]);
        model.set_objective(&[(y, 1.0)], Sense::Maximize);

        let HybridPbLpDecision::Optimal {
            value,
            model_values,
        } = try_solve(&model, None).expect("hybrid optimum")
        else {
            panic!("expected optimum");
        };
        assert_eq!(value, integer(5));
        assert_eq!(model_values[x.index()], integer(2));
        assert_eq!(model_values[y.index()], integer(5));
        model.check_point(&model_values).expect("original witness");
    }

    #[test]
    fn transformed_infeasibility_is_promoted_only_after_equivalence_check() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        model.add_row(4.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);

        assert!(matches!(
            try_solve(&model, None),
            Some(HybridPbLpDecision::Infeasible)
        ));
    }

    #[test]
    fn lifted_infeasibility_certificate_round_trips_and_rebuilds_transform() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        model.add_row(4.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);

        let CertifiedHybridIntegerLiftDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified lifted result")
        else {
            panic!("expected certified lifted infeasibility");
        };
        verify_hybrid_integer_lift_infeasibility_certificate(&model, &certificate)
            .expect("rebuild exact radix lift and replay nested proof");
        let encoded = encode_hybrid_integer_lift_infeasibility_certificate_json(&certificate)
            .expect("bounded lifted artifact");
        let decoded = decode_hybrid_integer_lift_infeasibility_certificate_json(&encoded)
            .expect("decode lifted artifact");
        assert_eq!(decoded, certificate);
        verify_hybrid_integer_lift_infeasibility_certificate(&model, &decoded)
            .expect("decoded lifted proof");
    }

    #[test]
    fn lifted_certificate_is_bound_to_original_model_and_nested_proof() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        model.add_row(4.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        let CertifiedHybridIntegerLiftDecision::Infeasible(mut certificate) =
            try_solve_certified(&model, None).expect("certified lifted result")
        else {
            panic!("expected certified lifted infeasibility");
        };

        let mut changed = Model::new();
        let changed_x = changed.add_int_col(0.0, 2.0);
        let changed_y = changed.add_col(0.0, 1.0);
        changed.add_row(2.0, f64::INFINITY, &[(changed_x, 1.0), (changed_y, 1.0)]);
        assert_eq!(
            verify_hybrid_integer_lift_infeasibility_certificate(&changed, &certificate),
            Err(HybridIntegerLiftCertificateVerificationError::NestedCertificateRejected)
        );

        certificate.transformed.master_refutation.format = "forged".to_owned();
        assert_eq!(
            verify_hybrid_integer_lift_infeasibility_certificate(&model, &certificate),
            Err(HybridIntegerLiftCertificateVerificationError::NestedCertificateRejected)
        );
    }

    #[test]
    fn lifted_certificate_codec_and_interruption_fail_closed() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        model.add_row(4.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        let CertifiedHybridIntegerLiftDecision::Infeasible(certificate) =
            try_solve_certified(&model, None).expect("certified lifted result")
        else {
            panic!("expected certified lifted infeasibility");
        };

        assert!(matches!(
            encode_hybrid_integer_lift_infeasibility_certificate_json_with_limit(&certificate, 1),
            Err(HybridIntegerLiftCertificateCodecError::Oversized { limit: 1 })
        ));
        assert_eq!(
            verify_hybrid_integer_lift_infeasibility_certificate_interruptible(
                &model,
                &certificate,
                None,
                &mut || true,
            ),
            Err(HybridIntegerLiftCertificateVerificationError::Interrupted)
        );
        assert!(try_solve_certified_interruptible(&model, None, || true).is_none());
    }

    #[test]
    fn exact_side_store_survives_substitution() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 2.0);
        let third = BigRational::new(1.into(), 3.into());
        let advice = third.to_f64().expect("finite");
        let row = model.add_row(1.0, f64::INFINITY, &[(x, advice), (y, 1.0)]);
        model.record_inexact_row_coeff(row, x.0, third.clone());
        model.set_objective(&[(x, advice), (y, 1.0)], Sense::Minimize);
        model.record_inexact_obj_coeff(x.0, third);

        let lift = ValidatedLift::build(&model, None, &mut || false).expect("exact lift");
        lift.revalidate(&model, None, &mut || false)
            .expect("exact side-store equivalence");
        assert!(lift.transformed.has_inexact_coeffs());
    }

    #[test]
    fn open_and_excessive_integer_domains_decline() {
        let mut open = Model::new();
        open.add_int_col(0.0, f64::INFINITY);
        open.add_col(0.0, 1.0);
        assert_eq!(
            ValidatedLift::build(&open, None, &mut || false).err(),
            Some(HybridIntegerLiftDecline::OpenIntegerDomain { column: 0 })
        );

        let mut excessive = Model::new();
        excessive.add_int_col(0.0, f64::MAX);
        excessive.add_col(0.0, 1.0);
        assert_eq!(
            ValidatedLift::build(&excessive, None, &mut || false).err(),
            Some(HybridIntegerLiftDecline::RadixTooWide { column: 0 })
        );
    }

    #[test]
    fn malformed_binary_domain_declines() {
        let mut model = Model::new();
        let binary = model.add_binary_col();
        model.fix_col(binary, 2.0);
        model.add_col(0.0, 1.0);
        assert_eq!(
            ValidatedLift::build(&model, None, &mut || false).err(),
            Some(HybridIntegerLiftDecline::BinaryDomain { column: 0 })
        );
    }

    #[test]
    fn empty_effective_integer_domain_is_an_exact_contradiction() {
        let mut model = Model::new();
        model.add_int_col(0.2, 0.8);
        let y = model.add_col(0.0, 1.0);
        model.add_row(0.0, f64::INFINITY, &[(y, 1.0)]);
        let lift = ValidatedLift::build(&model, None, &mut || false).expect("empty lift");
        assert!(lift.revalidate(&model, None, &mut || false).is_ok());
        assert!(lift.transformed.check_point(&[integer(0)]).is_err());
    }

    #[test]
    fn unusable_nonzero_proxy_declines() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        let row = model.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.record_inexact_row_coeff(
            row,
            x.0,
            BigRational::from_integer(BigInt::one() << 20_000usize),
        );
        assert_eq!(
            ValidatedLift::build(&model, None, &mut || false).err(),
            Some(HybridIntegerLiftDecline::ExactValueTooLarge)
        );
    }
}
