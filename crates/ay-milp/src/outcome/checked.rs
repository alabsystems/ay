// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-authoritative evidence shapes and exact model-bound outcome checks.

use std::fmt;

use num_rational::BigRational;
use num_traits::Zero;

use super::Outcome;
use crate::cert::{CertificateError, OptimalityCertificate};
use crate::model::{Col, Model, PointViolation, Sense};
use crate::ModelError;

/// Whether an [`Outcome`] contains fields that could independently establish
/// all of its claims.
///
/// This is deliberately a *shape*, not an authority judgment. In particular,
/// [`EvidenceShape::FieldsPresent`] says only that the required point or proof
/// object is present. It does not say that a point has the right arity, that it
/// is feasible, that it attains the reported objective, or that a certificate
/// belongs to this model. Use [`Outcome::check_against`] for those checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvidenceShape {
    /// Every claim has a corresponding field with an exact verification path.
    FieldsPresent,
    /// At least one claim lacks independently checkable evidence.
    MissingFields {
        /// The claim or artifact that is missing.
        why: &'static str,
    },
}

impl EvidenceShape {
    /// Whether every claim has the fields required for exact checking.
    ///
    /// This does not perform the checks. It must never be treated as a proof
    /// verdict; use [`Outcome::check_against`] and then
    /// [`CheckedOutcome::is_rim_closed`].
    #[must_use]
    pub fn has_required_fields(self) -> bool {
        matches!(self, Self::FieldsPresent)
    }
}

/// An outcome borrowed together with the exact model it was checked against.
///
/// The fields are private, so external code cannot fabricate this token. Its
/// borrows also prevent either input from being mutated while the token is in
/// use. Construction re-checks every represented point, objective value, and
/// attached certificate with exact arithmetic. Search-only claims never
/// produce this token: [`Outcome::check_against`] returns
/// [`OutcomeCheckError::MissingEvidence`] for them after checking any fields
/// they do carry.
#[must_use = "a CheckedOutcome is the sealed rim-closed result of exact model validation"]
#[derive(Clone, Copy)]
pub struct CheckedOutcome<'outcome, 'model> {
    outcome: &'outcome Outcome,
    model: &'model Model,
}

impl fmt::Debug for CheckedOutcome<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckedOutcome")
            .field("outcome", self.outcome)
            .finish_non_exhaustive()
    }
}

impl<'outcome> CheckedOutcome<'outcome, '_> {
    /// The validated source outcome.
    pub fn outcome(self) -> &'outcome Outcome {
        self.outcome
    }

    /// Confirm that exact validation established every claim from exported data.
    ///
    /// A checked feasible point and a verified infeasibility artifact close
    /// directly. Optimality closes only when a verified certificate for the
    /// model's own objective meets the checked primal value exactly. In
    /// particular, an integral solve whose dual bound trails its incumbent is
    /// still search-dependent.
    #[must_use]
    pub fn is_rim_closed(self) -> bool {
        debug_assert!(self
            .outcome
            .evidence_shape(self.model)
            .has_required_fields());
        true
    }
}

/// Why an [`Outcome`] failed exact validation against a [`Model`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum OutcomeCheckError {
    /// The model itself is not valid for solving or exact replay.
    #[error(transparent)]
    Model(#[from] ModelError),
    /// A point did not contain one value per model column.
    #[error("point has {actual} values for a {expected}-column model")]
    PointArity {
        /// Number of values required by the model.
        expected: usize,
        /// Number of values supplied by the outcome.
        actual: usize,
    },
    /// A point violates a model bound, row, or integrality condition.
    #[error("outcome point is infeasible: {violation:?}")]
    PointRejected {
        /// The first exact feasibility violation.
        violation: PointViolation,
    },
    /// An optimal point does not attain the reported value.
    #[error("point attains {attained}, not the reported optimum {reported}")]
    ObjectiveMismatch {
        /// Exact objective value attained by the point.
        attained: Box<BigRational>,
        /// Objective value carried by the outcome.
        reported: Box<BigRational>,
    },
    /// An optimality claim was paired with a feasibility-only model.
    #[error("an Optimal outcome requires a model with an explicit objective")]
    OptimalityWithoutObjective,
    /// An optimality certificate uses a different objective direction.
    #[error("optimality certificate uses {actual:?}, but the model uses {expected:?}")]
    OptimalitySenseMismatch {
        /// Direction of the model objective.
        expected: Sense,
        /// Direction named by the certificate.
        actual: Sense,
    },
    /// An optimality certificate proves a bound for a different objective.
    #[error("optimality certificate does not target the model objective")]
    OptimalityObjectiveMismatch,
    /// Exact replay rejected the optimality certificate.
    #[error("optimality certificate does not verify: {source}")]
    OptimalityCertificateRejected {
        /// Exact certificate replay failure.
        #[source]
        source: CertificateError,
    },
    /// A certified optimality bound contradicts the checked primal point.
    #[error("certified dual bound {bound} crosses the primal value {value}")]
    OptimalityBoundCrosses {
        /// Certified bound in the model objective's offset frame.
        bound: Box<BigRational>,
        /// Checked primal value.
        value: Box<BigRational>,
    },
    /// A continuous optimum's certificate does not meet its primal value.
    #[error("certified dual bound {bound} does not meet continuous primal value {value}")]
    ContinuousOptimalityGap {
        /// Certified bound in the model objective's offset frame.
        bound: Box<BigRational>,
        /// Checked primal value.
        value: Box<BigRational>,
    },
    /// An interrupted-tree bound contradicts its checked incumbent.
    #[error("dual bound {bound} crosses incumbent value {value}")]
    FeasibleBoundCrosses {
        /// Claimed dual bound.
        bound: Box<BigRational>,
        /// Exact objective value attained by the incumbent.
        value: Box<BigRational>,
    },
    /// Exact replay rejected an attached root-LP infeasibility certificate.
    #[error("Farkas certificate does not verify: {source}")]
    FarkasCertificateRejected {
        /// Exact certificate replay failure.
        #[source]
        source: CertificateError,
    },
    /// Exact replay rejected an attached whole-tree certificate.
    #[error("tree certificate does not verify: {source}")]
    TreeCertificateRejected {
        /// Exact certificate replay failure.
        #[source]
        source: CertificateError,
    },
    /// The outcome has a claim for which it carries no checkable artifact.
    #[error("outcome cannot be sealed: {why}")]
    MissingEvidence {
        /// The claim or artifact missing from the outcome.
        why: &'static str,
    },
}

impl Outcome {
    /// Classify which claims have an exact checking route from this shape.
    ///
    /// This method performs no validation. Public `Outcome` fields can be
    /// fabricated or recombined, so even [`EvidenceShape::FieldsPresent`] is not
    /// authoritative. Call [`Self::check_against`] before relying on a claim.
    #[must_use]
    pub fn evidence_shape(&self, model: &Model) -> EvidenceShape {
        match self {
            Self::Optimal {
                value,
                cert: Some(cert),
                ..
            } if certificate_meets(cert, value, model) => EvidenceShape::FieldsPresent,
            Self::Optimal { cert: Some(_), .. } => EvidenceShape::MissingFields {
                why: "the exported dual bound does not meet the claimed primal value; the gap is \
                      closed only by search",
            },
            Self::Optimal { cert: None, .. } => EvidenceShape::MissingFields {
                why: "optimality has no exported dual-bound certificate",
            },
            Self::Feasible {
                dual_bound: None, ..
            } => EvidenceShape::FieldsPresent,
            Self::Feasible {
                dual_bound: Some(_),
                ..
            } => EvidenceShape::MissingFields {
                why: "the point is checkable, but the interrupted-tree bound has no artifact",
            },
            Self::Infeasible { cert, tree_cert } if cert.is_some() || tree_cert.is_some() => {
                EvidenceShape::FieldsPresent
            }
            Self::Infeasible { .. } => EvidenceShape::MissingFields {
                why: "infeasibility has neither a Farkas nor a tree certificate",
            },
            Self::Bound { rigorous: true, .. } => EvidenceShape::MissingFields {
                why: "the rigorous internal bound has no exported artifact",
            },
            Self::Bound {
                rigorous: false, ..
            } => EvidenceShape::MissingFields {
                why: "the bound is explicitly non-rigorous",
            },
            Self::Unbounded => EvidenceShape::MissingFields {
                why: "unboundedness has no exported ray",
            },
            Self::Unknown { .. } => EvidenceShape::MissingFields {
                why: "no verdict is claimed",
            },
        }
    }

    /// Re-check this outcome against `model` using exact arithmetic.
    ///
    /// This validates point arity and feasibility, re-derives model-objective
    /// values, binds optimality certificates to the model's own objective, and
    /// replays every attached certificate. It does not turn an unexported
    /// search argument into evidence: a claim without an exported checking path
    /// returns [`OutcomeCheckError::MissingEvidence`], never a checked token.
    pub fn check_against<'outcome, 'model>(
        &'outcome self,
        model: &'model Model,
    ) -> Result<CheckedOutcome<'outcome, 'model>, OutcomeCheckError> {
        model.validate()?;
        validate_outcome(self, model)?;
        match self.evidence_shape(model) {
            EvidenceShape::FieldsPresent => Ok(CheckedOutcome {
                outcome: self,
                model,
            }),
            EvidenceShape::MissingFields { why } => Err(OutcomeCheckError::MissingEvidence { why }),
        }
    }
}

fn certificate_meets(cert: &OptimalityCertificate, value: &BigRational, model: &Model) -> bool {
    cert.bound.clone() + model.obj_offset_exact() == *value
}

fn validate_outcome(outcome: &Outcome, model: &Model) -> Result<(), OutcomeCheckError> {
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => validate_optimal(value, model_values, cert.as_ref(), model),
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => validate_feasible(model_values, dual_bound.as_ref(), model),
        Outcome::Infeasible { cert, tree_cert } => {
            if let Some(cert) = cert {
                cert.verify(model)
                    .map_err(|source| OutcomeCheckError::FarkasCertificateRejected { source })?;
            }
            if let Some(cert) = tree_cert {
                cert.verify(model)
                    .map_err(|source| OutcomeCheckError::TreeCertificateRejected { source })?;
            }
            Ok(())
        }
        Outcome::Unbounded | Outcome::Bound { .. } | Outcome::Unknown { .. } => Ok(()),
    }
}

fn validate_point(values: &[BigRational], model: &Model) -> Result<(), OutcomeCheckError> {
    if values.len() != model.num_cols() {
        return Err(OutcomeCheckError::PointArity {
            expected: model.num_cols(),
            actual: values.len(),
        });
    }
    model
        .check_point(values)
        .map_err(|violation| OutcomeCheckError::PointRejected { violation })
}

fn validate_optimal(
    value: &BigRational,
    values: &[BigRational],
    cert: Option<&OptimalityCertificate>,
    model: &Model,
) -> Result<(), OutcomeCheckError> {
    if !model.has_objective() {
        return Err(OutcomeCheckError::OptimalityWithoutObjective);
    }
    validate_point(values, model)?;
    let attained = model.objective_value_at(values);
    if &attained != value {
        return Err(OutcomeCheckError::ObjectiveMismatch {
            attained: Box::new(attained),
            reported: Box::new(value.clone()),
        });
    }
    if let Some(cert) = cert {
        validate_optimality_certificate(cert, value, model)?;
    }
    Ok(())
}

fn validate_optimality_certificate(
    cert: &OptimalityCertificate,
    value: &BigRational,
    model: &Model,
) -> Result<(), OutcomeCheckError> {
    if cert.sense != model.sense() {
        return Err(OutcomeCheckError::OptimalitySenseMismatch {
            expected: model.sense(),
            actual: cert.sense,
        });
    }
    if cert.objective != exact_model_objective(model) {
        return Err(OutcomeCheckError::OptimalityObjectiveMismatch);
    }
    cert.verify(model)
        .map_err(|source| OutcomeCheckError::OptimalityCertificateRejected { source })?;
    let bound = cert.bound.clone() + model.obj_offset_exact();
    let crosses = match model.sense() {
        Sense::Minimize => &bound > value,
        Sense::Maximize => &bound < value,
    };
    if crosses {
        return Err(OutcomeCheckError::OptimalityBoundCrosses {
            bound: Box::new(bound),
            value: Box::new(value.clone()),
        });
    }
    if !model.has_integrality() && &bound != value {
        return Err(OutcomeCheckError::ContinuousOptimalityGap {
            bound: Box::new(bound),
            value: Box::new(value.clone()),
        });
    }
    Ok(())
}

fn exact_model_objective(model: &Model) -> Vec<(u32, BigRational)> {
    (0..model.num_cols())
        .filter_map(|index| {
            let column = index as u32;
            let coefficient = model.obj_coeff_exact_at(column, model.obj_coeff(Col(column)));
            (!coefficient.is_zero()).then_some((column, coefficient))
        })
        .collect()
}

fn validate_feasible(
    values: &[BigRational],
    dual_bound: Option<&BigRational>,
    model: &Model,
) -> Result<(), OutcomeCheckError> {
    validate_point(values, model)?;
    let Some(bound) = dual_bound else {
        return Ok(());
    };
    let value = model.objective_value_at(values);
    let crosses = match model.sense() {
        Sense::Minimize => bound > &value,
        Sense::Maximize => bound < &value,
    };
    if crosses {
        Err(OutcomeCheckError::FeasibleBoundCrosses {
            bound: Box::new(bound.clone()),
            value: Box::new(value),
        })
    } else {
        Ok(())
    }
}
